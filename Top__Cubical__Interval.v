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
  |                    Top__Cubical__Interval.v                              |
  |                                                                          |
  |              The Relational Interval: Derived from WholeCompletion       |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-03-09                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                        |
  |                                                                          |
  |  PURPOSE: Derive the cubical interval I_R from WholeCompletion of unit.  |
  |  Unlike standard cubical type theory, the interval here is NOT a new     |
  |  primitive — it is a THEOREM: the canonical two-point serial extension   |
  |  of the unit type.                                                       |
  |                                                                          |
  |  KEY INSIGHT: I_R := option unit                                         |
  |    - i0 := Some tt  (source endpoint, embedded element)                 |
  |    - i1 := None     (target endpoint, the Whole / terminal sink)         |
  |    - i0 ≠ i1        (proved constructively, no axiom)                   |
  |    - Every point relates to i1 (seriality = Kan filling in dim 1)       |
  |                                                                          |
  |  COMPARISON TO STANDARD CTT:                                             |
  |    Standard CTT: "Let I be a type with i0, i1 : I and ..."  (axiom)     |
  |    UCF/GUTT:     "I_R := option unit"                        (derived)   |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Core Interval Definitions                                 |
  |    SECTION 2:  Face Maps (δ⁰, δ¹)                                       |
  |    SECTION 3:  Degeneracy Map (ε)                                        |
  |    SECTION 4:  Connection Operators (∧_I, ∨_I)                          |
  |    SECTION 5:  Interval Properties                                       |
  |    SECTION 6:  Lift to Relation Lifting                                  |
  |    SECTION 7:  Iterated Interval (I_R^n via iter_carrier)                |
  |    SECTION 8:  INT Module — Public API                                   |
  |    SECTION 9:  Hint Databases & Tactics                                  |
  |    SECTION 10: Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                           |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Prelude.

Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE INTERVAL DEFINITIONS                    *)
(*                                                                            *)
(*  The interval is the WholeCompletion of unit.                              *)
(*  It has exactly two inhabitants: Some tt and None.                         *)
(*                                                                            *)
(* ========================================================================== *)

(** The Relational Interval: WholeCompletion of unit.
    This is NOT an axiom — it is a derived type. *)
Definition I_R : Type := option unit.

(** Source endpoint: the embedded element. *)
Definition i0 : I_R := Some tt.

(** Target endpoint: the Whole (terminal sink). *)
Definition i1 : I_R := None.

(** The interval has exactly two points. *)
Lemma I_R_exhaustive : forall x : I_R, x = i0 \/ x = i1.
Proof.
  intro x. destruct x as [[]|].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** The two endpoints are distinct. *)
Lemma i0_neq_i1 : i0 <> i1.
Proof.
  unfold i0, i1. intro H. discriminate H.
Qed.

(** Symmetric: i1 ≠ i0. *)
Lemma i1_neq_i0 : i1 <> i0.
Proof.
  intro H. apply i0_neq_i1. symmetry. exact H.
Qed.

(** The interval IS the WholeCompletion carrier of unit. *)
Lemma I_R_is_WholeCompletion : I_R = WholeCompletion.carrier unit.
Proof. reflexivity. Qed.

(** i0 is the injection of tt. *)
Lemma i0_is_inject : i0 = WholeCompletion.inject tt.
Proof. reflexivity. Qed.

(** i1 is the Whole (point). *)
Lemma i1_is_whole : i1 = WholeCompletion.point (U := unit).
Proof. reflexivity. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: FACE MAPS (δ⁰, δ¹)                          *)
(*                                                                            *)
(*  Face maps select an endpoint of the interval.                             *)
(*  δ⁰ : unit → I_R selects i0.                                              *)
(*  δ¹ : unit → I_R selects i1.                                              *)
(*                                                                            *)
(* ========================================================================== *)

(** δ⁰: the i0-face map. *)
Definition face_i0 : unit -> I_R := fun _ => i0.

(** δ¹: the i1-face map. *)
Definition face_i1 : unit -> I_R := fun _ => i1.

(** The two face maps are distinct. *)
Lemma face_maps_distinct : face_i0 tt <> face_i1 tt.
Proof.
  unfold face_i0, face_i1. exact i0_neq_i1.
Qed.

(** Face map i0 lands at the injection. *)
Lemma face_i0_is_inject : forall u : unit, face_i0 u = WholeCompletion.inject u.
Proof.
  intro u. destruct u. reflexivity.
Qed.

(** Face map i1 lands at the Whole. *)
Lemma face_i1_is_whole : forall u : unit, face_i1 u = WholeCompletion.point (U := unit).
Proof.
  intro u. destruct u. reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: DEGENERACY MAP (ε)                           *)
(*                                                                            *)
(*  The degeneracy map ε : I_R → unit collapses the interval.                *)
(*  It is the unique function from I_R to unit.                               *)
(*                                                                            *)
(* ========================================================================== *)

(** ε: the degeneracy (collapse) map. *)
Definition degen : I_R -> unit := fun _ => tt.

(** Degeneracy after face i0 is identity on unit. *)
Lemma degen_face_i0 : forall u : unit, degen (face_i0 u) = u.
Proof. intro u. destruct u. reflexivity. Qed.

(** Degeneracy after face i1 is identity on unit. *)
Lemma degen_face_i1 : forall u : unit, degen (face_i1 u) = u.
Proof. intro u. destruct u. reflexivity. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: CONNECTION OPERATORS                         *)
(*                                                                            *)
(*  In cubical type theory, connections ∧_I and ∨_I make I a De Morgan       *)
(*  algebra, enabling square-filling (Kan composition in higher dimensions). *)
(*  Here they are DERIVED from the option type structure.                     *)
(*                                                                            *)
(*  Semantics (treating i1 = None as "true/top", i0 = Some tt as "false"):   *)
(*    meet x y = None iff (x = None OR y = None)  [∨ in terms of "top"]      *)
(*    join x y = None iff (x = None AND y = None)  [∧ in terms of "top"]     *)
(*                                                                            *)
(*  Equivalently (treating i0 as 0 and i1 as 1):                             *)
(*    I_meet x y = min(x,y)                                                   *)
(*    I_join x y = max(x,y)                                                   *)
(*                                                                            *)
(* ========================================================================== *)

(** Meet (min): i0 ∧ anything = i0. *)
Definition I_meet (x y : I_R) : I_R :=
  match x with
  | Some _ => Some tt   (** i0 absorbs: 0 ∧ y = 0 *)
  | None   => y          (** i1 is unit: 1 ∧ y = y *)
  end.

(** Join (max): i1 ∨ anything = i1. *)
Definition I_join (x y : I_R) : I_R :=
  match x with
  | None   => None        (** i1 absorbs: 1 ∨ y = 1 *)
  | Some _ => y            (** i0 is unit: 0 ∨ y = y *)
  end.

(** Complement / negation: swap endpoints. *)
Definition I_neg (x : I_R) : I_R :=
  match x with
  | Some _ => None
  | None   => Some tt
  end.

Lemma I_meet_i0_left : forall y, I_meet i0 y = i0.
Proof. intro y. destruct y as [[]|]; reflexivity. Qed.

Lemma I_meet_i1_left : forall y, I_meet i1 y = y.
Proof. intro y. destruct y as [[]|]; reflexivity. Qed.

Lemma I_meet_comm : forall x y, I_meet x y = I_meet y x.
Proof. intros x y. destruct x as [[]|], y as [[]|]; reflexivity. Qed.

Lemma I_meet_assoc : forall x y z, I_meet x (I_meet y z) = I_meet (I_meet x y) z.
Proof. intros x y z. destruct x as [[]|], y as [[]|], z as [[]|]; reflexivity. Qed.

Lemma I_join_i1_left : forall y, I_join i1 y = i1.
Proof. intro y. destruct y as [[]|]; reflexivity. Qed.

Lemma I_join_i0_left : forall y, I_join i0 y = y.
Proof. intro y. destruct y as [[]|]; reflexivity. Qed.

Lemma I_join_comm : forall x y, I_join x y = I_join y x.
Proof. intros x y. destruct x as [[]|], y as [[]|]; reflexivity. Qed.

Lemma I_neg_i0 : I_neg i0 = i1.
Proof. reflexivity. Qed.

Lemma I_neg_i1 : I_neg i1 = i0.
Proof. reflexivity. Qed.

Lemma I_neg_involutive : forall x, I_neg (I_neg x) = x.
Proof. intro x. destruct x as [[]|]; reflexivity. Qed.

(** De Morgan laws hold. *)
Lemma I_de_morgan_meet : forall x y,
  I_neg (I_meet x y) = I_join (I_neg x) (I_neg y).
Proof.
  intros x y. destruct x as [[]|], y as [[]|]; reflexivity.
Qed.

Lemma I_de_morgan_join : forall x y,
  I_neg (I_join x y) = I_meet (I_neg x) (I_neg y).
Proof.
  intros x y. destruct x as [[]|], y as [[]|]; reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: INTERVAL PROPERTIES                          *)
(*                                                                            *)
(* ========================================================================== *)

(** Seriality: every interval point has a path to i1 (the Whole). *)
Lemma I_R_serial :
  Serial (WholeCompletion.lift_rel (fun _ _ : unit => True)).
Proof.
  apply WholeCompletion.weak_serial.
Qed.

(** Directly: every x : I_R relates to i1 under any lifted relation. *)
Lemma I_R_to_i1 : forall (R : unit -> unit -> Prop) (x : I_R),
  WholeCompletion.lift_rel R x i1.
Proof.
  intros R x.
  unfold i1.
  apply WholeCompletion.serial.
Qed.

(** i0 → i1 is always provable (the canonical path). *)
Lemma I_R_canonical_path : forall (R : unit -> unit -> Prop),
  WholeCompletion.lift_rel R i0 i1.
Proof.
  intro R. apply I_R_to_i1.
Qed.

(** i1 does not relate back to i0 (asymmetry / termination). *)
Lemma I_R_no_reverse : forall (R : unit -> unit -> Prop),
  ~ WholeCompletion.lift_rel R i1 i0.
Proof.
  intros R H.
  unfold i0, i1, WholeCompletion.lift_rel in H.
  exact H.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: LIFT TO RELATION LIFTING                     *)
(*                                                                            *)
(*  The interval acts as the base case for lifting relations.                 *)
(*  lift_at_I R = WholeCompletion.lift_rel R : I_R → I_R → Prop              *)
(*                                                                            *)
(* ========================================================================== *)

(** Lift a relation over unit to a relation over I_R. *)
Definition lift_at_I (R : unit -> unit -> Prop) : I_R -> I_R -> Prop :=
  WholeCompletion.lift_rel R.

(** Conservative: lift_at_I R i0 i0 ↔ R tt tt. *)
Lemma lift_at_I_conservative : forall (R : unit -> unit -> Prop),
  lift_at_I R i0 i0 <-> R tt tt.
Proof.
  intro R.
  unfold lift_at_I, i0.
  apply WholeCompletion.lift_conservative.
Qed.

(** Seriality: lift_at_I R x i1 always holds. *)
Lemma lift_at_I_serial : forall (R : unit -> unit -> Prop) (x : I_R),
  lift_at_I R x i1.
Proof.
  intros R x. unfold lift_at_I.
  apply WholeCompletion.serial.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: ITERATED INTERVAL (I_R^n)                    *)
(*                                                                            *)
(*  Applying WholeCompletion n times to unit gives the n-dimensional          *)
(*  interval carrier: I_R^n = iter_carrier n unit                             *)
(*    I_R^0 = unit                                                            *)
(*    I_R^1 = option unit       = I_R                                         *)
(*    I_R^2 = option (option unit)  (a "square" of interval points)           *)
(*    I_R^n = option^n unit                                                   *)
(*                                                                            *)
(* ========================================================================== *)

(** n-dimensional interval carrier. *)
Definition I_R_n (n : nat) : Type := SerialComposition.iter_carrier n unit.

(** The endpoints at each level. *)
Definition I_R_n_i0 (n : nat) : I_R_n (S n) :=
  SerialComposition.iter_inject (S n) unit tt.

Definition I_R_n_i1 (n : nat) : I_R_n (S n) :=
  SerialComposition.iter_point n unit.

(** Endpoints are distinct at each level. *)
Lemma I_R_n_endpoints_distinct : forall n,
  I_R_n_i0 n <> I_R_n_i1 n.
Proof.
  intro n.
  unfold I_R_n_i0, I_R_n_i1.
  apply SerialComposition.iter_point_fresh.
Qed.

(** I_R^1 = I_R. *)
Lemma I_R_1_is_I_R : I_R_n 1 = I_R.
Proof. reflexivity. Qed.

(** The standard i0 and i1 match I_R_n at level 1. *)
Lemma I_R_1_i0 : I_R_n_i0 0 = i0.
Proof. reflexivity. Qed.

Lemma I_R_1_i1 : I_R_n_i1 0 = i1.
Proof. reflexivity. Qed.

(** Every element at level n+1 relates to the Whole at level n. *)
Lemma I_R_n_serial : forall n (R : unit -> unit -> Prop) (x : I_R_n (S n)),
  SerialComposition.iter_lift (S n) unit R x (I_R_n_i1 n).
Proof.
  intros n R x.
  unfold I_R_n_i1.
  apply SerialComposition.iter_serial.
Qed.

(** Fractal connectivity: every element reaches every Whole at every level. *)
Lemma I_R_n_fractal : forall n (R : unit -> unit -> Prop) (level : nat),
  level <= n ->
  match SerialComposition.whole_at_level n level unit with
  | Some w => SerialComposition.iter_lift (S n) unit R
                (SerialComposition.iter_inject (S n) unit tt) w
  | None => True
  end.
Proof.
  intros n R level Hlevel.
  apply SerialComposition.fractal_connectivity.
  exact Hlevel.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: INT MODULE — PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

Module INT.

  (** The interval type. *)
  Definition Interval : Type := I_R.

  (** The two endpoints. *)
  Definition src : Interval := i0.
  Definition tgt : Interval := i1.

  (** Endpoints are distinct. *)
  Definition endpoints_distinct : src <> tgt := i0_neq_i1.

  (** Every point has a canonical path to tgt. *)
  Definition to_tgt : forall (R : unit -> unit -> Prop) (x : Interval),
    WholeCompletion.lift_rel R x tgt
    := I_R_to_i1.

  (** Meet and join on the interval. *)
  Definition meet : Interval -> Interval -> Interval := I_meet.
  Definition join : Interval -> Interval -> Interval := I_join.
  Definition neg  : Interval -> Interval             := I_neg.

  (** Iterated interval for n-dimensional cubes. *)
  Definition I_n : nat -> Type := I_R_n.
  Definition src_n : forall n, I_n (S n) := I_R_n_i0.
  Definition tgt_n : forall n, I_n (S n) := I_R_n_i1.

  (** n-dimensional fractal connectivity. *)
  Definition fractal_reach := I_R_n_fractal.

End INT.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: HINT DATABASES & TACTICS                     *)
(*                                                                            *)
(* ========================================================================== *)

#[export] Hint Resolve
  i0_neq_i1
  i1_neq_i0
  I_R_to_i1
  I_R_canonical_path
  I_R_no_reverse
  I_R_n_endpoints_distinct
  : interval.

#[export] Hint Rewrite
  I_neg_involutive
  I_meet_comm
  I_join_comm
  : interval_rw.

Ltac interval_simpl :=
  unfold i0, i1, I_R, face_i0, face_i1, degen;
  autorewrite with interval_rw;
  auto with interval.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: AXIOM AUDIT                                 *)
(*                                                                            *)
(*  AXIOM STATUS                                                              *)
(*  ============                                                              *)
(*  This file uses ZERO additional axioms beyond Coq's standard library.     *)
(*  All definitions are inductive (option, unit) or definitional.            *)
(*  All theorems are proved by case analysis and reflexivity.                *)
(*                                                                            *)
(*  Print Assumptions i0_neq_i1.          --> Closed under global context    *)
(*  Print Assumptions I_R_n_fractal.       --> Closed under global context    *)
(*  Print Assumptions I_de_morgan_meet.    --> Closed under global context    *)
(*                                                                            *)
(* ========================================================================== *)
