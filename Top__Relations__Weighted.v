(*
  Copyright 2023-2026 Michael Fillippini

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
  implied.  See the License for the specific language governing
  permissions and limitations under the License.

  SPDX-License-Identifier: Apache-2.0
*)

(*
  +==========================================================================+
  |                                                                          |
  |                    Top__Relations__Weighted.v                            |
  |                                                                          |
  |            Signed, Graded, Overlapping (Multiplex) Relations             |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-26                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Extend the UCF/GUTT relational framework with weighted         |
  |  relations that support:                                                 |
  |    - GRADED MAGNITUDE: relation strength as a continuous value           |
  |    - SIGNED DIRECTION: positive (harmony) vs negative (conflict)         |
  |    - OVERLAPPING CHANNELS: multiplex relations across types/domains      |
  |                                                                          |
  |  ARCHITECTURE:                                                           |
  |    Layer 0 (existing): R : U -> U -> Prop  (support/existence)           |
  |    Layer 1 (this file): StOr : U -> U -> Q (signed graded strength)      |
  |    Layer 2 (future): Dynamic update laws for NRT evolution               |
  |                                                                          |
  |  KEY INSIGHT: Binary relations are thresholded support projections       |
  |  of graded relation strength. This preserves all existing proofs         |
  |  while enabling richer modeling of real-world relational dynamics.       |
  |                                                                          |
  |  RELATIONAL ONTOLOGY:                                                    |
  |    - Magnitude reflects relational intensity/coupling strength           |
  |    - Sign reflects relational polarity (cooperation vs antagonism)       |
  |    - Overlap reflects multi-channel simultaneous influences              |
  |    - Support (Ã¢â€°Â  0) reflects existence of relation                        |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Weighted Relation Structure                               |
  |    SECTION 2:  Support Projections (existence, harmony, conflict)        |
  |    SECTION 3:  Magnitude and Sign Operations                             |
  |    SECTION 4:  Multiplex Relations (multi-channel)                       |
  |    SECTION 5:  Composition Rules for Weighted Relations                  |
  |    SECTION 6:  Lifting from Prop to Weighted                             |
  |    SECTION 7:  Weighted WholeCompletion Integration                      |
  |    SECTION 8:  WR Module - Public API                                    |
  |    SECTION 9:  Hint Databases & Tactics                                  |
  |    SECTION 10: Examples                                                  |
  |    SECTION 11: Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                            |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

(* Import UCF/GUTT extension framework *)
Require Import Top__Extensions__Prelude.

(* Import Q arithmetic utilities *)
Require Import Top__Numbers__UCF_Lia.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

Open Scope Q_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: WEIGHTED RELATION STRUCTURE                  *)
(*                                                                            *)
(* ========================================================================== *)

(**
  A weighted relation assigns a rational-valued strength to each pair.
  
  RELATIONAL INTERPRETATION:
    - StOr a b > 0: cooperative/harmonic relation from a to b
    - StOr a b < 0: antagonistic/conflicting relation from a to b  
    - StOr a b = 0: no direct relation from a to b
    - |StOr a b|: magnitude/intensity of the relation
    
  This is Layer 1 in the UCF/GUTT architecture, sitting above the
  binary Prop relations (Layer 0) and below dynamic evolution (Layer 2).
*)

(** A weighted relation on a universe U. *)
Definition WeightedRel (U : Type) := U -> U -> Q.

(** The zero weighted relation (no relations). *)
Definition wr_zero {U : Type} : WeightedRel U := fun _ _ => 0.

(** A constant weighted relation (uniform strength). *)
Definition wr_const {U : Type} (w : Q) : WeightedRel U := fun _ _ => w.

(** Pointwise negation (flip polarity). *)
Definition wr_neg {U : Type} (W : WeightedRel U) : WeightedRel U :=
  fun a b => - W a b.

(** Pointwise absolute value (magnitude only). *)
Definition wr_abs {U : Type} (W : WeightedRel U) : WeightedRel U :=
  fun a b => Qabs (W a b).

(** Pointwise addition (combine weights). *)
Definition wr_add {U : Type} (W1 W2 : WeightedRel U) : WeightedRel U :=
  fun a b => W1 a b + W2 a b.

(** Pointwise multiplication (scale weights). *)
Definition wr_mul {U : Type} (W1 W2 : WeightedRel U) : WeightedRel U :=
  fun a b => W1 a b * W2 a b.

(** Scalar multiplication. *)
Definition wr_scale {U : Type} (k : Q) (W : WeightedRel U) : WeightedRel U :=
  fun a b => k * W a b.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: SUPPORT PROJECTIONS                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Support projections extract binary (Prop) relations from weighted relations.
  
  This is the key bridge between Layer 1 (weighted) and Layer 0 (Prop).
  It allows all existing WholeCompletion, Composition, etc. machinery
  to work unchanged on the projected support relations.
*)

(** Support: does a relation exist at all? (nonzero weight) *)
Definition R_support {U : Type} (W : WeightedRel U) (a b : U) : Prop :=
  ~ W a b == 0.

(** Positive/cooperative: is the relation harmonic? *)
Definition R_pos {U : Type} (W : WeightedRel U) (a b : U) : Prop :=
  0 < W a b.

(** Negative/antagonistic: is the relation conflicting? *)
Definition R_neg {U : Type} (W : WeightedRel U) (a b : U) : Prop :=
  W a b < 0.

(** Nonnegative: harmonic or neutral *)
Definition R_nonneg {U : Type} (W : WeightedRel U) (a b : U) : Prop :=
  0 <= W a b.

(** Nonpositive: antagonistic or neutral *)
Definition R_nonpos {U : Type} (W : WeightedRel U) (a b : U) : Prop :=
  W a b <= 0.

(** Strong: magnitude exceeds threshold *)
Definition R_strong {U : Type} (threshold : Q) (W : WeightedRel U) (a b : U) : Prop :=
  threshold < Qabs (W a b).

(** Weak: magnitude below threshold *)
Definition R_weak {U : Type} (threshold : Q) (W : WeightedRel U) (a b : U) : Prop :=
  Qabs (W a b) <= threshold.

(* -------------------------------------------------------------------------- *)
(*                    Support Projection Lemmas                               *)
(* -------------------------------------------------------------------------- *)

Section SupportLemmas.
  Variable U : Type.
  Variable W : WeightedRel U.
  Variable a b : U.

  (** Positive implies support. *)
  Lemma pos_implies_support : R_pos W a b -> R_support W a b.
  Proof.
    unfold R_pos, R_support.
    intros Hpos Heq.
    rewrite Heq in Hpos.
    apply (Qlt_irrefl 0). exact Hpos.
  Qed.

  (** Negative implies support. *)
  Lemma neg_implies_support : R_neg W a b -> R_support W a b.
  Proof.
    unfold R_neg, R_support.
    intros Hneg Heq.
    rewrite Heq in Hneg.
    apply (Qlt_irrefl 0). exact Hneg.
  Qed.

  (** Support is equivalent to positive or negative. *)
  Lemma support_iff_pos_or_neg : 
    R_support W a b <-> (R_pos W a b \/ R_neg W a b).
  Proof.
    unfold R_support, R_pos, R_neg.
    split.
    - intro Hneq.
      destruct (Q_dec (W a b) 0) as [[Hlt | Hgt] | Heq].
      + right. exact Hlt.
      + left. exact Hgt.
      + exfalso. apply Hneq. exact Heq.
    - intros [Hpos | Hneg] Heq.
      + rewrite Heq in Hpos. apply (Qlt_irrefl 0). exact Hpos.
      + rewrite Heq in Hneg. apply (Qlt_irrefl 0). exact Hneg.
  Qed.

  (** No support means zero weight. *)
  Lemma no_support_iff_zero : ~ R_support W a b <-> W a b == 0.
  Proof.
    unfold R_support.
    split.
    - intro H. destruct (Qeq_dec (W a b) 0) as [Heq | Hneq].
      + exact Heq.
      + exfalso. apply H. exact Hneq.
    - intros Heq Hneq. apply Hneq. exact Heq.
  Qed.

End SupportLemmas.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: MAGNITUDE AND SIGN OPERATIONS                *)
(*                                                                            *)
(* ========================================================================== *)

(** Extract the sign of a relation: +1, 0, or -1 *)
Definition wr_sign {U : Type} (W : WeightedRel U) : WeightedRel U :=
  fun a b => 
    match Qcompare (W a b) 0 with
    | Lt => -1
    | Eq => 0
    | Gt => 1
    end.

(** Sign is idempotent on signs. *)
Lemma wr_sign_idempotent {U : Type} (W : WeightedRel U) (a b : U) :
  wr_sign (wr_sign W) a b == wr_sign W a b.
Proof.
  unfold wr_sign.
  destruct (Qcompare (W a b) 0) eqn:Hcmp;
  simpl; reflexivity.
Qed.

(** Magnitude times sign recovers original (for nonzero). *)
Lemma abs_sign_recover {U : Type} (W : WeightedRel U) (a b : U) :
  R_support W a b -> 
  wr_abs W a b * wr_sign W a b == W a b.
Proof.
  unfold R_support, wr_abs, wr_sign.
  intro Hneq.
  destruct (Qcompare (W a b) 0) eqn:Hcmp.
  - (* Eq: contradiction with Hneq *)
    assert (Heq : W a b == 0).
    { apply Qeq_alt. exact Hcmp. }
    exfalso. apply Hneq. exact Heq.
  - (* Lt: W a b < 0 *)
    assert (Hlt : W a b < 0).
    { apply Qlt_alt. exact Hcmp. }
    rewrite Qabs_neg.
    + ring.
    + apply Qlt_le_weak. exact Hlt.
  - (* Gt: W a b > 0 *)
    assert (Hgt : 0 < W a b).
    { apply Qgt_alt. exact Hcmp. }
    rewrite Qabs_pos.
    + ring.
    + apply Qlt_le_weak. exact Hgt.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: MULTIPLEX RELATIONS (MULTI-CHANNEL)          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Multiplex relations allow OVERLAP: multiple simultaneous relational
  channels between the same pair of entities.
  
  EXAMPLES:
    - Social: friendship, professional, familial channels
    - Physical: gravitational, electromagnetic, strong/weak nuclear
    - Economic: trade, investment, debt channels
    
  Each channel K has its own weight function W_K : U -> U -> Q.
  The aggregate relation combines all channels.
*)

(** A multiplex weighted relation indexed by channel type K. *)
Definition MultiplexRel (K U : Type) := K -> WeightedRel U.

(** Project to a single channel. *)
Definition mpx_channel {K U : Type} (M : MultiplexRel K U) (k : K) : WeightedRel U :=
  M k.

(** Aggregate by summing over all channels (given a list of channels). *)
Definition mpx_sum {K U : Type} (M : MultiplexRel K U) (channels : list K) : WeightedRel U :=
  fun a b => fold_right Qplus 0 (map (fun k => M k a b) channels).

(** Max of two rationals. *)
Definition Qmax (a b : Q) : Q := if Qle_bool a b then b else a.

(** Aggregate by taking maximum absolute value. *)
Definition mpx_max_abs {K U : Type} (M : MultiplexRel K U) (channels : list K) : WeightedRel U :=
  fun a b => fold_right (fun w acc => Qmax (Qabs w) acc) 0 (map (fun k => M k a b) channels).

(** Support on any channel. *)
Definition R_any_support {K U : Type} (M : MultiplexRel K U) (channels : list K) (a b : U) : Prop :=
  exists k, In k channels /\ R_support (M k) a b.

(** Support on all channels. *)
Definition R_all_support {K U : Type} (M : MultiplexRel K U) (channels : list K) (a b : U) : Prop :=
  forall k, In k channels -> R_support (M k) a b.

(** Conflict: positive on one channel, negative on another. *)
Definition R_conflict {K U : Type} (M : MultiplexRel K U) (channels : list K) (a b : U) : Prop :=
  (exists k1, In k1 channels /\ R_pos (M k1) a b) /\
  (exists k2, In k2 channels /\ R_neg (M k2) a b).

(** Harmony: all channels have same sign (all positive or all negative). *)
Definition R_harmony {K U : Type} (M : MultiplexRel K U) (channels : list K) (a b : U) : Prop :=
  (forall k, In k channels -> R_support (M k) a b -> R_pos (M k) a b) \/
  (forall k, In k channels -> R_support (M k) a b -> R_neg (M k) a b).

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: COMPOSITION RULES FOR WEIGHTED RELATIONS     *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Relational composition for weighted relations.
  
  RELATIONAL INTERPRETATION:
    If a relates to b with weight w1, and b relates to c with weight w2,
    the composed relation a->c has weight w1 * w2 (multiplicative).
    
  For additive aggregation over intermediate paths, use path summation.
*)

(** Sequential composition (multiplicative, max over intermediates). *)
(** Note: For finite U, this would sum/max over all b. Here we parameterize. *)
Definition wr_compose {U : Type} 
  (W1 W2 : WeightedRel U) 
  (witness : U -> U -> U)  (* function that picks intermediate for each pair *)
  : WeightedRel U :=
  fun a c => 
    let b := witness a c in
    W1 a b * W2 b c.

(** Composition with explicit intermediate. *)
Definition wr_compose_via {U : Type} 
  (W1 W2 : WeightedRel U) (b : U) : WeightedRel U :=
  fun a c => W1 a b * W2 b c.

(** Reflexive closure: add self-loops with weight 1. 
    Note: Requires decidable equality on U. *)
Definition wr_reflexive {U : Type} (eq_dec : forall x y : U, {x = y} + {x <> y})
  (W : WeightedRel U) : WeightedRel U :=
  fun a b => 
    match eq_dec a b with
    | left _ => if Qeq_bool (W a b) 0 then 1 else W a b
    | right _ => W a b
    end.

(** Negative times negative is positive. *)
Lemma Q_mul_neg_neg : forall a b : Q, a < 0 -> b < 0 -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  assert (H1 : 0 < -a).
  { unfold Qlt, Qopp in *. simpl in *. lia. }
  assert (H2 : 0 < -b).
  { unfold Qlt, Qopp in *. simpl in *. lia. }
  assert (Hab : 0 < (-a) * (-b)).
  { apply UCF.Q_mul_pos_pos; assumption. }
  unfold Qlt, Qmult, Qopp in *. simpl in *.
  lia.
Qed.

(** Positive times negative is negative. *)
Lemma Q_mul_pos_neg : forall a b : Q, 0 < a -> b < 0 -> a * b < 0.
Proof.
  intros a b Ha Hb.
  assert (H2 : 0 < -b).
  { unfold Qlt, Qopp in *. simpl in *. lia. }
  assert (Hab : 0 < a * (-b)).
  { apply UCF.Q_mul_pos_pos; assumption. }
  unfold Qlt, Qmult, Qopp in *. simpl in *.
  lia.
Qed.

(** Negative times positive is negative. *)
Lemma Q_mul_neg_pos : forall a b : Q, a < 0 -> 0 < b -> a * b < 0.
Proof.
  intros a b Ha Hb.
  rewrite Qmult_comm. apply Q_mul_pos_neg; assumption.
Qed.

(** Sign composition follows multiplication rules:
    pos * pos = pos, neg * neg = pos, pos * neg = neg, neg * pos = neg *)
Lemma sign_compose {U : Type} (W1 W2 : WeightedRel U) (a b c : U) :
  (R_pos W1 a b /\ R_pos W2 b c -> R_pos (wr_compose_via W1 W2 b) a c) /\
  (R_neg W1 a b /\ R_neg W2 b c -> R_pos (wr_compose_via W1 W2 b) a c) /\
  (R_pos W1 a b /\ R_neg W2 b c -> R_neg (wr_compose_via W1 W2 b) a c) /\
  (R_neg W1 a b /\ R_pos W2 b c -> R_neg (wr_compose_via W1 W2 b) a c).
Proof.
  unfold R_pos, R_neg, wr_compose_via.
  repeat split; intros [H1 H2].
  - apply UCF.Q_mul_pos_pos; assumption.
  - apply Q_mul_neg_neg; assumption.
  - apply Q_mul_pos_neg; assumption.
  - apply Q_mul_neg_pos; assumption.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: LIFTING FROM PROP TO WEIGHTED                *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Convert a binary Prop relation to a weighted relation.
  
  This allows existing Prop-based relations to participate in
  weighted relation operations.
*)

(** Lift a Prop relation to weighted with unit weight. *)
Definition lift_prop {U : Type} (R : U -> U -> Prop) 
  (dec : forall a b, {R a b} + {~ R a b}) : WeightedRel U :=
  fun a b => if dec a b then 1 else 0.

(** Lift with specified positive weight. *)
Definition lift_prop_weighted {U : Type} (R : U -> U -> Prop) (w : Q)
  (dec : forall a b, {R a b} + {~ R a b}) : WeightedRel U :=
  fun a b => if dec a b then w else 0.

(** Lifted relation has support iff original holds (for positive weight). *)
Lemma lift_support_iff {U : Type} (R : U -> U -> Prop) (w : Q)
  (dec : forall a b, {R a b} + {~ R a b})
  (Hw : 0 < w) (a b : U) :
  R_support (lift_prop_weighted R w dec) a b <-> R a b.
Proof.
  unfold R_support, lift_prop_weighted.
  destruct (dec a b) as [HR | HnR].
  - split.
    + intros _H. exact HR.
    + intros _H Heq.
      assert (Hneq : ~ w == 0).
      { intro Hcontra. rewrite Hcontra in Hw. apply (Qlt_irrefl 0). exact Hw. }
      apply Hneq. exact Heq.
  - split.
    + intro H. exfalso. apply H. reflexivity.
    + intro HR'. exfalso. apply HnR. exact HR'.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: WEIGHTED WHOLECOMPLETION INTEGRATION         *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Extend weighted relations to WholeCompletion.
  
  DESIGN CHOICES:
    - elem a relates to Whole with maximal positive weight (Ã¢Ë†Å¾ Ã¢â€ â€™ use large constant)
    - Whole relates to itself with unit weight (terminal self-loop)
    - Whole does not relate backward to elements (point_terminal)
*)

(** Weight for seriality to Whole. We use a designated "maximal" constant. *)
Definition whole_weight : Q := 1.  (* Can be customized *)

(** Lift a weighted relation to WholeCompletion carrier. *)
Definition wr_lift {U : Type} (W : WeightedRel U) : WeightedRel (UE.Carrier U) :=
  fun x y =>
    match x, y with
    | Some a, Some b => W a b
    | Some _, None => whole_weight  (* elem -> Whole: seriality *)
    | None, None => whole_weight    (* Whole -> Whole: self-loop *)
    | None, Some _ => 0             (* Whole -> elem: blocked *)
    end.

(** The lifted relation's support projection matches UE.lift. *)
Lemma wr_lift_support_conservative {U : Type} (W : WeightedRel U) (a b : U) :
  R_support (wr_lift W) (UE.elem a) (UE.elem b) <-> R_support W a b.
Proof.
  unfold wr_lift, UE.elem, R_support.
  simpl. reflexivity.
Qed.

(** Seriality: every element has positive relation to Whole. *)
Lemma wr_lift_serial {U : Type} (W : WeightedRel U) (x : UE.Carrier U) :
  0 < whole_weight -> R_pos (wr_lift W) x UE.Whole.
Proof.
  unfold wr_lift, UE.Whole, R_pos.
  intro Hw.
  destruct x; exact Hw.
Qed.

(** Point terminal: Whole doesn't reach back to elements. *)
Lemma wr_lift_point_terminal {U : Type} (W : WeightedRel U) (a : U) :
  ~ R_support (wr_lift W) UE.Whole (UE.elem a).
Proof.
  unfold wr_lift, UE.Whole, UE.elem, R_support.
  simpl. intro H. apply H. reflexivity.
Qed.

(** Whole has a self-loop. *)
Lemma wr_lift_point_self_loop {U : Type} (W : WeightedRel U) :
  0 < whole_weight -> R_pos (wr_lift W) UE.Whole UE.Whole.
Proof.
  unfold wr_lift, UE.Whole, R_pos.
  simpl. intro Hw. exact Hw.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: WR MODULE - PUBLIC API                       *)
(*                                                                            *)
(* ========================================================================== *)

(**
  WR: The canonical public API for weighted relations.
  
  This module provides stable, memorable names for downstream use.
  
  NAMING CONVENTIONS:
    - Types use UpperCamelCase: WeightedRel, MultiplexRel
    - Operations use snake_case: wr_add, wr_scale
    - Projections use R_prefix: R_support, R_pos, R_neg
    - Lemmas use snake_case: pos_implies_support
*)

Module WR.
  
  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)
  
  (** A weighted relation on universe U. *)
  Definition Rel (U : Type) := WeightedRel U.
  
  (** A multiplex (multi-channel) weighted relation. *)
  Definition Multiplex (K U : Type) := MultiplexRel K U.
  
  (* ====================================================================== *)
  (*                           Constructors                                 *)
  (* ====================================================================== *)
  
  (** Zero relation (no connections). *)
  Definition zero {U : Type} : Rel U := wr_zero.
  
  (** Constant relation (uniform weight). *)
  Definition const {U : Type} (w : Q) : Rel U := wr_const w.
  
  (* ====================================================================== *)
  (*                           Operations                                   *)
  (* ====================================================================== *)
  
  (** Pointwise negation. *)
  Definition neg {U : Type} := @wr_neg U.
  
  (** Pointwise absolute value. *)
  Definition abs {U : Type} := @wr_abs U.
  
  (** Pointwise addition. *)
  Definition add {U : Type} := @wr_add U.
  
  (** Pointwise multiplication. *)
  Definition mul {U : Type} := @wr_mul U.
  
  (** Scalar multiplication. *)
  Definition scale {U : Type} := @wr_scale U.
  
  (** Sign extraction. *)
  Definition sign {U : Type} := @wr_sign U.
  
  (* ====================================================================== *)
  (*                       Support Projections                              *)
  (* ====================================================================== *)
  
  (** Has support (nonzero weight). *)
  Definition support {U : Type} := @R_support U.
  
  (** Positive (cooperative). *)
  Definition pos {U : Type} := @R_pos U.
  
  (** Negative (antagonistic). *)
  Definition negative {U : Type} := @R_neg U.
  
  (** Nonnegative. *)
  Definition nonneg {U : Type} := @R_nonneg U.
  
  (** Nonpositive. *)
  Definition nonpos {U : Type} := @R_nonpos U.
  
  (** Strong (exceeds threshold). *)
  Definition strong {U : Type} := @R_strong U.
  
  (** Weak (below threshold). *)
  Definition weak {U : Type} := @R_weak U.
  
  (* ====================================================================== *)
  (*                       Multiplex Operations                             *)
  (* ====================================================================== *)
  
  (** Single channel projection. *)
  Definition channel {K U : Type} := @mpx_channel K U.
  
  (** Sum aggregation. *)
  Definition sum_channels {K U : Type} := @mpx_sum K U.
  
  (** Max-abs aggregation. *)
  Definition max_channels {K U : Type} := @mpx_max_abs K U.
  
  (** Any channel has support. *)
  Definition any_support {K U : Type} := @R_any_support K U.
  
  (** All channels have support. *)
  Definition all_support {K U : Type} := @R_all_support K U.
  
  (** Conflict across channels. *)
  Definition conflict {K U : Type} := @R_conflict K U.
  
  (** Harmony across channels. *)
  Definition harmony {K U : Type} := @R_harmony K U.
  
  (* ====================================================================== *)
  (*                       Composition                                      *)
  (* ====================================================================== *)
  
  (** Compose via explicit intermediate. *)
  Definition compose_via {U : Type} := @wr_compose_via U.
  
  (* ====================================================================== *)
  (*                       WholeCompletion Integration                      *)
  (* ====================================================================== *)
  
  (** Lift to WholeCompletion. *)
  Definition lift {U : Type} := @wr_lift U.
  
  (** The weight assigned to seriality edges. *)
  Definition serial_weight := whole_weight.
  
  (* ====================================================================== *)
  (*                       Key Lemmas                                       *)
  (* ====================================================================== *)
  
  (** Positive implies support. *)
  Definition pos_support {U : Type} := @pos_implies_support U.
  
  (** Negative implies support. *)
  Definition neg_support {U : Type} := @neg_implies_support U.
  
  (** Support iff positive or negative. *)
  Definition support_iff {U : Type} := @support_iff_pos_or_neg U.
  
  (** Lifted relation is serial. *)
  Definition lift_serial {U : Type} := @wr_lift_serial U.
  
  (** Lifted relation has terminal Whole. *)
  Definition lift_terminal {U : Type} := @wr_lift_point_terminal U.

End WR.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: HINT DATABASES & TACTICS                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Hint database for weighted relation automation. *)
Create HintDb wr discriminated.

#[export] Hint Resolve 
  pos_implies_support
  neg_implies_support
  wr_lift_serial
  wr_lift_point_self_loop
  : wr.

#[export] Hint Extern 1 (~ R_support (wr_lift _) UE.Whole (UE.elem _)) =>
  apply wr_lift_point_terminal : wr.

(** Tactic for weighted relation goals. *)
Ltac wr_auto :=
  auto with wr;
  try (unfold R_support, R_pos, R_neg, wr_lift; simpl; try reflexivity).

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: EXAMPLES                                    *)
(*                                                                            *)
(* ========================================================================== *)

Module WRExamples.

  (** Example: Simple 3-element universe with weighted relations. *)
  Inductive Node := A | B | C.

  (** Example weighted relation: A likes B (+1), B dislikes C (-1), etc. *)
  Definition example_rel : WR.Rel Node :=
    fun x y =>
      match x, y with
      | A, B => 1        (* A -> B: positive *)
      | B, C => -1       (* B -> C: negative *)
      | A, C => 1 # 2    (* A -> C: weak positive *)
      | _, _ => 0        (* no other relations *)
      end.

  (** A has positive relation to B. *)
  Lemma A_pos_B : WR.pos example_rel A B.
  Proof. unfold WR.pos, R_pos, example_rel. reflexivity. Qed.

  (** B has negative relation to C. *)
  Lemma B_neg_C : WR.negative example_rel B C.
  Proof. unfold WR.negative, R_neg, example_rel. reflexivity. Qed.

  (** A has support to C (nonzero). *)
  Lemma A_support_C : WR.support example_rel A C.
  Proof. 
    unfold WR.support, R_support, example_rel.
    intro H. 
    unfold Qeq in H. simpl in H. lia.
  Qed.

  (** Example: Multiplex with two channels (friendship, professional). *)
  Inductive Channel := Friendship | Professional.

  Definition example_multiplex : WR.Multiplex Channel Node :=
    fun ch x y =>
      match ch with
      | Friendship =>
          match x, y with
          | A, B => 1      (* A and B are friends *)
          | B, A => 1
          | _, _ => 0
          end
      | Professional =>
          match x, y with
          | A, C => 1      (* A and C work together *)
          | C, A => 1
          | B, C => -1     (* B and C have professional conflict *)
          | C, B => -1
          | _, _ => 0
          end
      end.

  (** B and C have conflict (positive on one channel, negative on another would need both). *)
  (** Actually B->C is negative on Professional, but we need positive on some channel too. *)
  (** Let's verify A->C has harmony (positive on Professional, zero on Friendship). *)
  
  Lemma A_C_professional : WR.pos (example_multiplex Professional) A C.
  Proof. unfold WR.pos, R_pos. simpl. reflexivity. Qed.

End WRExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  AXIOM AUDIT
  ===========
  
  This file uses ZERO axioms beyond Coq's standard library.
  
  All proofs are constructive and can be inspected via:
    Print Assumptions <lemma_name>.
  
  Key dependencies:
    - QArith: stdlib rationals
    - Qabs: stdlib Q absolute value
    - Top__Extensions__Prelude: UE module for WholeCompletion
    - Top__Numbers__UCF_Lia: UCF Q arithmetic lemmas
*)

(** Verify no axioms in key theorems. *)
(* Uncomment to check: *)
(* Print Assumptions pos_implies_support. *)
(* Print Assumptions support_iff_pos_or_neg. *)
(* Print Assumptions wr_lift_serial. *)
(* Print Assumptions sign_compose. *)

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  Types:
    WR.Rel U                = U -> U -> Q (weighted relation)
    WR.Multiplex K U        = K -> WR.Rel U (multi-channel)
  
  Constructors:
    WR.zero                 = all zeros (no relations)
    WR.const w              = uniform weight w
  
  Operations:
    WR.neg W                = flip polarity
    WR.abs W                = magnitude only
    WR.add W1 W2            = combine weights
    WR.scale k W            = scalar multiply
    WR.sign W               = extract sign (-1, 0, +1)
  
  Projections to Prop:
    WR.support W a b        : ~ W a b == 0 (has relation)
    WR.pos W a b            : 0 < W a b (cooperative)
    WR.negative W a b       : W a b < 0 (antagonistic)
    WR.strong t W a b       : t < |W a b| (exceeds threshold)
  
  Multiplex:
    WR.channel M k          : project single channel
    WR.sum_channels M ks    : sum over channels
    WR.conflict M ks a b    : has both positive and negative
    WR.harmony M ks a b     : all same sign
  
  WholeCompletion:
    WR.lift W               : extend to option U
    WR.lift_serial          : seriality to Whole
    WR.lift_terminal        : Whole doesn't reach back
  
  ARCHITECTURAL POSITION
  ======================
  
  Layer 0: R : U -> U -> Prop
    (existing UCF/GUTT foundation in Top__Extensions__Prelude)
    
  Layer 1: W : U -> U -> Q  [THIS FILE]
    (signed, graded, multiplex relations)
    
  Layer 2: (future)
    (dynamic evolution, NRT update laws)
  
  INTEGRATION PATTERN
  ===================
  
  To use weighted relations with existing machinery:
  
    1. Define your weighted relation:
       Definition my_W : WR.Rel MyUniverse := fun a b => ...
    
    2. Project to Prop for existing lemmas:
       Definition my_R := WR.support my_W.
       (* Now use my_R with UE.lift, WholeCompletion, etc. *)
    
    3. Or lift directly:
       Definition my_W' := WR.lift my_W.
       (* Use WR.lift_serial, etc. for weighted WholeCompletion *)
*)
