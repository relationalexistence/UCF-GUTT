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
  |                    Top__Extensions__Adjunction.v                         |
  |                                                                          |
  |              Free/Forgetful Adjunction via Change of Base                |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-21                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Formalize the Free/Forgetful adjunction between boolean        |
  |  (0/1) relations and weighted relations. This provides a Galois          |
  |  connection on each hom-poset: U compose F = id, F compose U <= id.      |
  |                                                                          |
  |  KEY INSIGHT: The adjunction emerges from the relational foundation      |
  |  established in Proposition 01. Connectivity is PROVEN, not axiomatized. |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Abstract Change-of-Base Adjunction                        |
  |    SECTION 2:  Concrete Nat-Weighted Instantiation                       |
  |    SECTION 3:  Connection to Relational Foundation                       |
  |    SECTION 4:  Additional Properties                                     |
  |    SECTION 5:  ADJ Module - Public API                                   |
  |    SECTION 6:  Hint Databases                                            |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Core types: BoolRel, WRel, KRel                                   |
  |      - Functors: F, U (free/forgetful)                                   |
  |      - Main theorems: UF_id, FU_le, hom_adj                              |
  |      - ADJ module exports                                                |
  |    EXPERIMENTAL (may change):                                            |
  |      - Examples involving Ux                                             |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - Functors: F (free), U (forgetful/underlying)                        |
  |    - Orders: _le suffix (brel_le, wrel_le, krel_le)                      |
  |    - Identity laws: *_id or *_id_pt (pointwise)                          |
  |    - Inequality laws: *_le                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Prelude.
Require Import Top__Propositions__Prop_01.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From Coq Require Import Bool.Bool.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

Set Implicit Arguments.

(* ========================================================================== *)
(*                                                                            *)
(*               SECTION 1: ABSTRACT CHANGE-OF-BASE ADJUNCTION                *)
(*                                                                            *)
(*  Parametric adjunction between boolean relations and K-weighted            *)
(*  relations for any ordered semiring K with an embedding 2 -> K.            *)
(*                                                                            *)
(* ========================================================================== *)

Section ChangeOfBaseAdjunction.

  (** Ordered carrier K and embedding 2 <-> K *)
  Variable K  : Type.
  Variable kle : K -> K -> Prop.
  Hypothesis kle_refl  : forall k, kle k k.
  Hypothesis kle_trans : forall a b c, kle a b -> kle b c -> kle a c.

  Variable k0 : K.
  Hypothesis k0_is_bottom : forall k, kle k0 k.

  (** Embedding/projection between booleans and K *)
  Variable eta : bool -> K.
  Variable pi  : K -> bool.

  (** Scalar-level adjunction laws *)
  Hypothesis pi_eta_id : forall b : bool, pi (eta b) = b.
  Hypothesis eta_pi_le : forall k : K, kle (eta (pi k)) k.

  (** Anchor false at bottom *)
  Hypothesis eta_false_is_k0 : eta false = k0.

  (** Boolean order: b1 <= b2 iff (b1=true -> b2=true) *)
  Definition ble (b1 b2 : bool) : Prop := (b1 = true -> b2 = true).

  (** Monotonicity of scalar maps *)
  Hypothesis pi_monotone  : forall k1 k2, kle k1 k2 -> ble (pi k1) (pi k2).
  Hypothesis eta_monotone : forall b1 b2, ble b1 b2 -> kle (eta b1) (eta b2).

  (* ------------------------------------------------------------------------ *)
  (*                     Relations and Pointwise Orders                       *)
  (* ------------------------------------------------------------------------ *)

  Definition BoolRel (A B : Type) := A -> B -> bool.
  Definition KRel    (A B : Type) := A -> B -> K.

  Definition brel_le_K {A B : Type} (r1 r2 : BoolRel A B) : Prop :=
    forall x y, ble (r1 x y) (r2 x y).

  Definition krel_le {A B : Type} (s1 s2 : KRel A B) : Prop :=
    forall x y, kle (s1 x y) (s2 x y).

  Lemma ble_refl (b : bool) : ble b b.
  Proof. intros H; exact H. Qed.

  Lemma ble_trans (b1 b2 b3 : bool) :
    ble b1 b2 -> ble b2 b3 -> ble b1 b3.
  Proof. firstorder. Qed.

  Lemma brel_le_K_refl (A B : Type) (r : BoolRel A B) :
    brel_le_K r r.
  Proof. intros x y; apply ble_refl. Qed.

  Lemma brel_le_K_trans (A B : Type) (r1 r2 r3 : BoolRel A B) :
    brel_le_K r1 r2 -> brel_le_K r2 r3 -> brel_le_K r1 r3.
  Proof.
    intros H12 H23 x y; eapply ble_trans; [apply H12|apply H23].
  Qed.

  Lemma krel_le_refl (A B : Type) (s : KRel A B) :
    krel_le s s.
  Proof. intros x y; apply kle_refl. Qed.

  Lemma krel_le_trans (A B : Type) (s1 s2 s3 : KRel A B) :
    krel_le s1 s2 -> krel_le s2 s3 -> krel_le s1 s3.
  Proof.
    intros H12 H23 x y; eapply kle_trans; [apply H12|apply H23].
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                      Change-of-Base Functors F and U                     *)
  (* ------------------------------------------------------------------------ *)

  (** Free functor: embed boolean relation into K-weighted *)
  Definition F_K {A B : Type} (r : BoolRel A B) : KRel A B :=
    fun x y => eta (r x y).

  (** Forgetful functor: project K-weighted to boolean *)
  Definition U_K {A B : Type} (s : KRel A B) : BoolRel A B :=
    fun x y => pi (s x y).

  Lemma F_K_monotone (A B : Type) :
    forall (r1 r2 : BoolRel A B),
      brel_le_K r1 r2 -> krel_le (@F_K A B r1) (@F_K A B r2).
  Proof. intros r1 r2 H x y; apply eta_monotone, H. Qed.

  Lemma U_K_monotone (A B : Type) :
    forall (s1 s2 : KRel A B),
      krel_le s1 s2 -> brel_le_K (@U_K A B s1) (@U_K A B s2).
  Proof.
    intros s1 s2 H x y.
    unfold U_K.
    apply pi_monotone, H.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                      Unit/Counit Laws (Galois Connection)                *)
  (* ------------------------------------------------------------------------ *)

  (** U compose F = id (pointwise) *)
  Theorem UF_K_id_pt (A B : Type) (r : BoolRel A B) :
    forall x y, (@U_K A B (@F_K A B r)) x y = r x y.
  Proof. intros x y; unfold U_K, F_K; now rewrite pi_eta_id. Qed.

  (** F compose U <= id *)
  Theorem FU_K_le (A B : Type) (s : KRel A B) :
    krel_le (@F_K A B (@U_K A B s)) s.
  Proof. intros x y; unfold F_K, U_K; apply eta_pi_le. Qed.

  (* ------------------------------------------------------------------------ *)
  (*                      Hom-Set Adjunction (Galois Connection)              *)
  (* ------------------------------------------------------------------------ *)

  (** The fundamental adjunction: F -| U as a Galois connection *)
  Theorem hom_adj (A B : Type) (r : BoolRel A B) (s : KRel A B) :
    krel_le (@F_K A B r) s <-> brel_le_K r (@U_K A B s).
  Proof.
    split.
    - (* -> direction *)
      intros H x y. unfold ble. intro Hrtrue.
      set (k1 := eta (r x y)).
      set (k2 := s x y).
      assert (Hle : kle k1 k2) by (subst; apply H).
      apply pi_monotone in Hle.
      replace (pi k1) with (pi (eta (r x y))) in Hle by (unfold k1; reflexivity).
      rewrite pi_eta_id in Hle.
      rewrite Hrtrue in Hle.
      apply Hle.
      reflexivity.
    - (* <- direction *)
      intros H x y.
      destruct (r x y) eqn:Rxy.
      + (* r x y = true *)
        specialize (H x y). unfold ble in H.
        assert (Hpi : pi (s x y) = true) by (apply H; exact Rxy).
        eapply kle_trans.
        * apply eta_monotone. intros _; exact Hpi.
        * apply eta_pi_le.
      + (* r x y = false *)
        change (kle (eta (r x y)) (s x y)).
        rewrite Rxy.
        rewrite eta_false_is_k0.
        apply k0_is_bottom.
  Qed.

End ChangeOfBaseAdjunction.

(* ========================================================================== *)
(*                                                                            *)
(*              SECTION 2: CONCRETE NAT-WEIGHTED INSTANTIATION                *)
(*                                                                            *)
(*  Instantiate the abstract adjunction with K = nat, giving the              *)
(*  standard Free/Forgetful adjunction between 0/1 graphs and weighted        *)
(*  graphs with natural number weights.                                       *)
(*                                                                            *)
(* ========================================================================== *)

Section NatWeightedAdjunction.

  Definition RelObj := Type.
  Definition WRel (A B : RelObj) := A -> B -> nat.
  Definition BRel (A B : RelObj) := A -> B -> bool.

  (* ------------------------------------------------------------------------ *)
  (*                            Nat-Weighted Functors                         *)
  (* ------------------------------------------------------------------------ *)

  (** Forgetful U: weighted -> 0/1 (true iff weight > 0) *)
  Definition U {A B} (R : WRel A B) : BRel A B :=
    fun x y => Nat.ltb 0 (R x y).

  (** Free F: 0/1 -> weighted (true |-> 1, false |-> 0) *)
  Definition F {A B} (G : BRel A B) : WRel A B :=
    fun x y => if G x y then 1 else 0.

  (* ------------------------------------------------------------------------ *)
  (*                         Orders on Relations                              *)
  (* ------------------------------------------------------------------------ *)

  Definition brel_le {A B} (r1 r2 : BRel A B) : Prop :=
    forall x y, (r1 x y = true -> r2 x y = true).

  Definition wrel_le {A B} (s1 s2 : WRel A B) : Prop :=
    forall x y, s1 x y <= s2 x y.

  Lemma brel_le_refl {A B} (r : BRel A B) : brel_le r r.
  Proof. intros x y H; exact H. Qed.

  Lemma brel_le_trans {A B} (r1 r2 r3 : BRel A B) :
    brel_le r1 r2 -> brel_le r2 r3 -> brel_le r1 r3.
  Proof. intros H12 H23 x y Hr1; apply H23, H12, Hr1. Qed.

  Lemma wrel_le_refl {A B} (s : WRel A B) : wrel_le s s.
  Proof. intros x y; lia. Qed.

  Lemma wrel_le_trans {A B} (s1 s2 s3 : WRel A B) :
    wrel_le s1 s2 -> wrel_le s2 s3 -> wrel_le s1 s3.
  Proof. intros H12 H23 x y; etransitivity; [apply H12 | apply H23]. Qed.

  (* ------------------------------------------------------------------------ *)
  (*                       Unit/Counit Laws for Nat                           *)
  (* ------------------------------------------------------------------------ *)

  (** U compose F = id on 0/1 morphisms (pointwise) *)
  Lemma U_F_id_pt {A B} (G : BRel A B) :
    forall x y, U (F G) x y = G x y.
  Proof.
    intros x y. unfold U, F.
    destruct (G x y); simpl; reflexivity.
  Qed.

  (** F compose U <= id on weighted morphisms *)
  Lemma F_U_le {A B} (R : WRel A B) :
    forall x y, F (U R) x y <= R x y.
  Proof.
    intros x y. unfold F, U.
    destruct (Nat.ltb 0 (R x y)) eqn:H.
    - apply Nat.ltb_lt in H. simpl; lia.
    - apply Nat.ltb_ge in H. simpl; lia.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                         Functional Form Lemmas                           *)
  (* ------------------------------------------------------------------------ *)

  Definition to_bool  {A B} (f : WRel A B) : BRel A B := U f.
  Definition from_bool {A B} (g : BRel A B) : WRel A B := F g.

  Lemma to_from_roundtrip_pt {A B} (g : BRel A B) :
    forall x y, to_bool (from_bool g) x y = g x y.
  Proof.
    intros x y. unfold to_bool, from_bool. apply U_F_id_pt.
  Qed.

  Lemma from_to_minimal_pt {A B} (f : WRel A B) :
    forall x y, from_bool (to_bool f) x y <= f x y.
  Proof.
    intros x y. unfold to_bool, from_bool. apply F_U_le.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                      Additional Nat-Specific Properties                  *)
  (* ------------------------------------------------------------------------ *)

  (** Universal property for F (free functor) *)
  Lemma F_universal {A B} (g : BRel A B) (w : WRel A B) :
    (forall x y, g x y = true -> w x y > 0) ->
    wrel_le (F g) w.
  Proof.
    intros H x y.
    unfold F.
    destruct (g x y) eqn:Hg.
    - apply H in Hg. lia.
    - lia.
  Qed.

  (** Preservation property for U (forgetful functor) *)
  Lemma U_preserves_positive {A B} (w : WRel A B) :
    forall x y, w x y > 0 <-> U w x y = true.
  Proof.
    intros x y.
    unfold U.
    split; intro H.
    - apply Nat.ltb_lt. exact H.
    - apply Nat.ltb_lt in H. exact H.
  Qed.

  (** Composition property: F U F = F *)
  Lemma F_U_F_idempotent {A B} (g : BRel A B) :
    forall x y, F (U (F g)) x y = F g x y.
  Proof.
    intros x y.
    unfold F, U.
    destruct (g x y); simpl; reflexivity.
  Qed.

  (** Monotonicity of F *)
  Lemma F_monotone {A B} (g1 g2 : BRel A B) :
    brel_le g1 g2 -> wrel_le (F g1) (F g2).
  Proof.
    intros H x y.
    unfold F.
    destruct (g1 x y) eqn:Hg1; destruct (g2 x y) eqn:Hg2; try lia.
    specialize (H x y Hg1). rewrite H in Hg2. discriminate.
  Qed.

  (** Monotonicity of U *)
  Lemma U_monotone {A B} (w1 w2 : WRel A B) :
    wrel_le w1 w2 -> brel_le (U w1) (U w2).
  Proof.
    intros H x y Hu1.
    unfold U in *.
    apply Nat.ltb_lt in Hu1.
    apply Nat.ltb_lt.
    specialize (H x y). lia.
  Qed.

End NatWeightedAdjunction.

(* ========================================================================== *)
(*                                                                            *)
(*             SECTION 3: CONNECTION TO RELATIONAL FOUNDATION                 *)
(*                                                                            *)
(*  Link the Free/Forgetful adjunction to Proposition 01 (seriality).         *)
(*  Connectivity is PROVEN, not axiomatized.                                  *)
(*                                                                            *)
(* ========================================================================== *)

Section RelationalFoundation.

  Variable U_base : Type.
  Variable R_base : U_base -> U_base -> Prop.

  (** The extended universe Ux = U + {Whole} *)
  Definition E : Type := Ux U_base.

  (** The lifted relation R' on the extended universe *)
  Definition R_ext : E -> E -> Prop := R_prime R_base.

  (* ------------------------------------------------------------------------ *)
  (*                      Connectivity: PROVEN, Not Axiomatized               *)
  (* ------------------------------------------------------------------------ *)

  Definition Connectivity : Prop :=
    forall x : E, exists y : E, R_ext x y.

  (** Proven from Proposition 01 - no axiom! *)
  Theorem Connectivity_Holds : Connectivity.
  Proof.
    unfold Connectivity.
    intro x.
    exact (proposition_01 U_base R_base x).
  Qed.

  Theorem Connectivity_Exists : forall x : E, exists y : E, R_ext x y.
  Proof. exact Connectivity_Holds. Qed.

  (** No isolates - proven, not assumed *)
  Lemma No_Isolates : forall x : E, ~ (forall y : E, ~ R_ext x y).
  Proof.
    intros x Hnone.
    destruct (Connectivity_Exists x) as [y Hy].
    specialize (Hnone y).
    contradiction.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                Example: Adjunction Over Extended Universe                *)
  (* ------------------------------------------------------------------------ *)

  (** Example weighted relation on Ux *)
  Definition example_wrel : WRel E E :=
    fun x y => match x, y with
               | Some _, None => 1
               | None, None => 2
               | _, _ => 0
               end.

  Definition example_brel : BRel E E := U example_wrel.

  (** The adjunction preserves connectivity *)
  Lemma adjunction_preserves_connectivity :
    forall x : E, exists y : E, example_brel x y = true.
  Proof.
    intro x.
    exists None.
    unfold example_brel, U, example_wrel.
    destruct x; simpl; reflexivity.
  Qed.

  (** The adjunction respects the proven relational structure *)
  Lemma adjunction_respects_R_prime :
    forall x : E, exists y : E,
      R_ext x y /\ example_brel x y = true.
  Proof.
    intro x.
    exists None.
    split.
    - unfold R_ext, R_prime.
      apply UE.serial.
    - unfold example_brel, U, example_wrel.
      destruct x; simpl; reflexivity.
  Qed.

End RelationalFoundation.

(* ========================================================================== *)
(*                                                                            *)
(*                   SECTION 4: ADDITIONAL PROPERTIES                         *)
(*                                                                            *)
(* ========================================================================== *)

Section AdditionalProperties.

  (** F is left adjoint to U (categorical statement) *)
  Remark F_left_adjoint_remark :
    forall (A B : Type) (g : BRel A B) (w : WRel A B),
      wrel_le (F g) w <-> brel_le g (U w).
  Proof.
    intros A B g w.
    split.
    - (* F g <= w  ->  g <= U w *)
      intros H x y Hg.
      unfold U.
      apply Nat.ltb_lt.
      specialize (H x y).
      unfold F in H.
      rewrite Hg in H.
      lia.
    - (* g <= U w  ->  F g <= w *)
      intros H x y.
      unfold F.
      destruct (g x y) eqn:Hg.
      + specialize (H x y Hg).
        unfold U in H.
        apply Nat.ltb_lt in H.
        lia.
      + lia.
  Qed.

  (** Characterization: F g is the minimal weighted extension of g *)
  Lemma F_minimal {A B} (g : BRel A B) (w : WRel A B) :
    (forall x y, g x y = true -> w x y > 0) ->
    (forall x y, g x y = false -> w x y = 0) ->
    forall x y, F g x y = w x y.
  Proof.
    intros Htrue Hfalse x y.
    unfold F.
    destruct (g x y) eqn:Hg.
    - specialize (Htrue x y Hg).
      (* F g x y = 1, w x y > 0, but we need w x y = 1 for equality *)
      (* This only holds if w is exactly the characteristic function *)
      (* The lemma as stated is too strong; let's adjust *)
  Abort.

  (** Weaker characterization: F g is bounded by any extension *)
  Lemma F_bounded_by_extension {A B} (g : BRel A B) (w : WRel A B) :
    (forall x y, g x y = true -> w x y >= 1) ->
    (forall x y, g x y = false -> w x y >= 0) ->
    wrel_le (F g) w.
  Proof.
    intros Htrue Hfalse x y.
    unfold F.
    destruct (g x y) eqn:Hg.
    - apply Htrue. exact Hg.
    - lia.
  Qed.

End AdditionalProperties.

(* ========================================================================== *)
(*                                                                            *)
(*                   SECTION 5: ADJ MODULE - PUBLIC API                       *)
(*                                                                            *)
(* ========================================================================== *)

Module ADJ.

  (** Types *)
  Definition WRel := WRel.
  Definition BRel := BRel.

  (** Functors *)
  Definition free {A B} := @F A B.
  Definition forgetful {A B} := @U A B.

  (** Orders *)
  Definition wrel_le {A B} := @wrel_le A B.
  Definition brel_le {A B} := @brel_le A B.

  (** Main theorems *)
  Definition unit_id {A B} := @U_F_id_pt A B.
  Definition counit_le {A B} := @F_U_le A B.
  Definition adjunction {A B} := @F_left_adjoint_remark A B.

  (** Monotonicity *)
  Definition free_mono {A B} := @F_monotone A B.
  Definition forgetful_mono {A B} := @U_monotone A B.

  (** Idempotence *)
  Definition FUF_idem {A B} := @F_U_F_idempotent A B.

  (** Universal property *)
  Definition free_universal {A B} := @F_universal A B.

  (** Preservation *)
  Definition forgetful_positive {A B} := @U_preserves_positive A B.

End ADJ.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: HINT DATABASES                               *)
(*                                                                            *)
(* ========================================================================== *)

Create HintDb adjunction discriminated.

#[export] Hint Resolve brel_le_refl : adjunction.
#[export] Hint Resolve wrel_le_refl : adjunction.
#[export] Hint Resolve F_monotone : adjunction.
#[export] Hint Resolve U_monotone : adjunction.
#[export] Hint Resolve U_F_id_pt : adjunction.
#[export] Hint Resolve F_U_le : adjunction.

(* Merge with ucf database for unified automation *)
#[export] Hint Resolve brel_le_refl wrel_le_refl : ucf.
#[export] Hint Resolve Connectivity_Holds : ucf.

(* ========================================================================== *)
(*                                                                            *)
(*                           SUMMARY                                          *)
(*                                                                            *)
(* ========================================================================== *)

(*
  ACHIEVED:
  
  1. [ok] Abstract change-of-base adjunction (Section 1)
     - Parametric in ordered semiring K
     - Galois connection: F -| U
     - Full hom_adj theorem
  
  2. [ok] Concrete nat-weighted instantiation (Section 2)
     - F: bool -> nat (true |-> 1, false |-> 0)
     - U: nat -> bool (n > 0 |-> true)
     - U o F = id (exact)
     - F o U <= id (minimal enrichment)
  
  3. [ok] Connection to relational foundation (Section 3)
     - Uses proven Proposition 01
     - Connectivity is PROVEN, not axiomatized
     - No_Isolates lemma
     - Examples over Ux
  
  4. [ok] Library quality
     - ZERO AXIOMS
     - ZERO ADMITS
     - Public API via ADJ module
     - Hint databases for automation
     - Follows project naming conventions
  
  DEPENDENCIES:
    - Top__Extensions__Prelude (for UE module)
    - Top__Propositions__Prop_01 (for proven seriality)
    - Coq.Arith.PeanoNat
    - Coq.micromega.Lia
    - Coq.Bool.Bool
  
  COMPILATION:
    coqc -R . "" Top__Extensions__Adjunction.v
    (after compiling dependencies)
*)

(** Axiom audit — must print "Closed under the global context." *)
Print Assumptions hom_adj.
Print Assumptions F_U_le.
Print Assumptions Connectivity_Holds.
