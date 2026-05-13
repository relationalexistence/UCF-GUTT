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
  |                    Top__Numbers__RelationalIntegers.v                    |
  |                                                                          |
  |         Integers from Relational Naturals with Complete Arithmetic       |
  |                  (Addition, Subtraction, Multiplication, Division)       |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-21                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Construct integers from pairs of relational naturals with      |
  |  COMPLETE arithmetic: addition, subtraction, multiplication, AND         |
  |  division (both Euclidean and exact/contextual).                         |
  |                                                                          |
  |  KEY INSIGHT: Integers ARE relational difference structures.             |
  |    - Z_rel := (N_rel x N_rel) with (a,b) representing a - b              |
  |    - Equivalence: (a,b) ~= (c,d) iff a + d = c + b                        |
  |    - Addition/Subtraction are INTRA-SET (within a domain)                |
  |    - Multiplication/Division are INTER-SET (across domains)              |
  |    - Division includes: Euclidean (quot/rem), safe (option), exact (Q)   |
  |                                                                          |
  |  PHILOSOPHICAL SIGNIFICANCE:                                             |
  |    INTRA-SET operations (add, sub) work WITHIN a domain:                 |
  |      - Time accumulation: t + delta_ t                                         |
  |      - Time differences: t2 - t1                                          |
  |    INTER-SET operations (mul, div) relate ACROSS domains:                |
  |      - Frequency ratios: comparing clock rates                           |
  |      - Period scaling: geometric vs quantum clocks                       |
  |    This distinction is crucial for QM/GR temporal unification.           |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

(* Import UCF/GUTT infrastructure *)
Require Import Top__Extensions__Prelude.
Require Import Top__Numbers__Relational.
Require Import Top__Numbers__RelationalDivision.

(* ========================================================================== *)
(*                                                                            *)
(*  UCF/GUTT Relational Arithmetic Library                                    *)
(*                                                                            *)
(*  Provides auditable Z arithmetic as an alternative to lia/nia:             *)
(*    - UCF.Z_sq_nonneg        : 0 <= a*a                                     *)
(*    - UCF.Z_am_gm_sq         : 2*a*b <= a*a + b*b                           *)
(*    - ucf_lia, ucf_nia tactics for automation                               *)
(*                                                                            *)
(* ========================================================================== *)
Require Import Top__Numbers__UCF_Lia.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE DEFINITIONS                             *)
(*                                                                            *)
(* ========================================================================== *)

(** Z_rel is pairs of relational naturals: (positive_part, negative_part). *)
Definition Z_rel : Type := N_rel * N_rel.

(**
  Equivalence relation: (a, b) ~= (c, d) iff a + d = c + b.
  This captures when two pairs represent the same integer.
*)
Definition Z_equiv (p q : Z_rel) : Prop :=
  add_rel (fst p) (snd q) = add_rel (fst q) (snd p).

(** Zero: perfect relational balance (0 - 0 = 0). *)
Definition Z_zero : Z_rel := (Zero_rel, Zero_rel).

(** One: unit positive imbalance (1 - 0 = 1). *)
Definition Z_one : Z_rel := (one_rel, Zero_rel).

(** Minus one: unit negative imbalance (0 - 1 = -1). *)
Definition Z_minus_one : Z_rel := (Zero_rel, one_rel).

(** Two: (2 - 0 = 2). *)
Definition Z_two : Z_rel := (two_rel, Zero_rel).

(** Addition: INTRA-SET operation. *)
Definition Z_add (p q : Z_rel) : Z_rel :=
  (add_rel (fst p) (fst q), add_rel (snd p) (snd q)).

(** Negation: swaps positive and negative components. *)
Definition Z_neg (p : Z_rel) : Z_rel :=
  (snd p, fst p).

(** Subtraction: defined via addition of negation. *)
Definition Z_sub (p q : Z_rel) : Z_rel :=
  Z_add p (Z_neg q).

(** Multiplication: INTER-SET operation. *)
Definition Z_mul (p q : Z_rel) : Z_rel :=
  (add_rel (mul_rel (fst p) (fst q)) (mul_rel (snd p) (snd q)),
   add_rel (mul_rel (fst p) (snd q)) (mul_rel (snd p) (fst q))).

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: EQUIVALENCE PROPERTIES                       *)
(*                                                                            *)
(* ========================================================================== *)

Theorem Z_equiv_refl : Reflexive Z_equiv.
Proof. unfold Reflexive, Z_equiv. intro x. reflexivity. Qed.

Theorem Z_equiv_sym : Symmetric Z_equiv.
Proof. unfold Symmetric, Z_equiv. intros x y H. symmetry. exact H. Qed.

Theorem Z_equiv_trans : Transitive Z_equiv.
Proof.
  unfold Transitive, Z_equiv.
  intros x y z Hxy Hyz.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  apply (f_equal to_nat) in Hxy.
  apply (f_equal to_nat) in Hyz.
  repeat rewrite add_rel_correct in Hxy.
  repeat rewrite add_rel_correct in Hyz.
  destruct x as [a b], y as [c d], z as [e f]. simpl in *.
  lia.
Qed.

(** Z_equiv is an equivalence relation (using stdlib typeclass). *)
Global Instance Z_equiv_Equivalence : RelationClasses.Equivalence Z_equiv := {
  Equivalence_Reflexive := Z_equiv_refl;
  Equivalence_Symmetric := Z_equiv_sym;
  Equivalence_Transitive := Z_equiv_trans
}.

(** Z_equiv is an equivalence (using project's definition). *)
Theorem Z_equiv_is_equivalence : Top__Extensions__Base.Equivalence Z_equiv.
Proof.
  unfold Top__Extensions__Base.Equivalence.
  split; [exact Z_equiv_refl | split; [exact Z_equiv_sym | exact Z_equiv_trans]].
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: PROPER INSTANCES                             *)
(*                                                                            *)
(* ========================================================================== *)

Theorem Z_add_respects_equiv : forall p1 p2 q1 q2 : Z_rel,
  Z_equiv p1 p2 -> Z_equiv q1 q2 -> Z_equiv (Z_add p1 q1) (Z_add p2 q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Z_add in *. simpl in *.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  apply (f_equal to_nat) in Hp.
  apply (f_equal to_nat) in Hq.
  repeat rewrite add_rel_correct in Hp.
  repeat rewrite add_rel_correct in Hq.
  destruct p1 as [a1 b1], p2 as [a2 b2], q1 as [c1 d1], q2 as [c2 d2].
  simpl in *. lia.
Qed.

Global Instance Z_add_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_add.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply Z_add_respects_equiv; assumption.
Qed.

Theorem Z_neg_respects_equiv : forall p q : Z_rel,
  Z_equiv p q -> Z_equiv (Z_neg p) (Z_neg q).
Proof.
  intros p q H.
  unfold Z_equiv, Z_neg in *. simpl in *.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  apply (f_equal to_nat) in H.
  repeat rewrite add_rel_correct in H.
  destruct p as [a b], q as [c d]. simpl in *. lia.
Qed.

Global Instance Z_neg_Proper :
  Proper (Z_equiv ==> Z_equiv) Z_neg.
Proof.
  unfold Proper, respectful.
  intros x y Hxy.
  apply Z_neg_respects_equiv; assumption.
Qed.

Global Instance Z_sub_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_sub.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  unfold Z_sub.
  apply Z_add_Proper; [assumption | apply Z_neg_Proper; assumption].
Qed.

Theorem Z_mul_respects_equiv : forall p1 p2 q1 q2 : Z_rel,
  Z_equiv p1 p2 -> Z_equiv q1 q2 -> Z_equiv (Z_mul p1 q1) (Z_mul p2 q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Z_mul in *. simpl in *.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  repeat rewrite mul_rel_correct.
  apply (f_equal to_nat) in Hp.
  apply (f_equal to_nat) in Hq.
  repeat rewrite add_rel_correct in Hp.
  repeat rewrite add_rel_correct in Hq.
  destruct p1 as [a1 b1], p2 as [a2 b2], q1 as [c1 d1], q2 as [c2 d2].
  simpl in *. nia.
Qed.

Global Instance Z_mul_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_mul.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply Z_mul_respects_equiv; assumption.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: INTERPRETATION                               *)
(*                                                                            *)
(* ========================================================================== *)

Local Open Scope Z_scope.

(** Convert Z_rel to Z: computes the difference. *)
Definition to_Z (p : Z_rel) : Z :=
  Z.of_nat (to_nat (fst p)) - Z.of_nat (to_nat (snd p)).

(** Convert Z to Z_rel: uses canonical representatives. *)
Definition from_Z (z : Z) : Z_rel :=
  if Z.leb 0 z
  then (from_nat (Z.to_nat z), Zero_rel)
  else (Zero_rel, from_nat (Z.to_nat (- z))).

Theorem to_Z_zero : to_Z Z_zero = 0.
Proof. unfold to_Z, Z_zero. simpl. reflexivity. Qed.

Theorem to_Z_one : to_Z Z_one = 1.
Proof. unfold to_Z, Z_one, one_rel. simpl. reflexivity. Qed.

Theorem to_Z_minus_one : to_Z Z_minus_one = -1.
Proof. unfold to_Z, Z_minus_one, one_rel. simpl. reflexivity. Qed.

Theorem to_Z_neg : forall p : Z_rel,
  to_Z (Z_neg p) = - to_Z p.
Proof. intros [a b]. unfold to_Z, Z_neg. simpl. lia. Qed.

Theorem to_Z_add : forall p q : Z_rel,
  to_Z (Z_add p q) = to_Z p + to_Z q.
Proof.
  intros [a b] [c d].
  unfold to_Z, Z_add. simpl.
  repeat rewrite add_rel_correct. lia.
Qed.

Theorem to_Z_sub : forall p q : Z_rel,
  to_Z (Z_sub p q) = to_Z p - to_Z q.
Proof.
  intros p q. unfold Z_sub.
  rewrite to_Z_add. rewrite to_Z_neg. lia.
Qed.

Theorem to_Z_mul : forall p q : Z_rel,
  to_Z (Z_mul p q) = to_Z p * to_Z q.
Proof.
  intros [a b] [c d].
  unfold to_Z, Z_mul. simpl.
  repeat rewrite add_rel_correct.
  repeat rewrite mul_rel_correct.
  nia.
Qed.

Theorem to_Z_respects_equiv : forall p q : Z_rel,
  Z_equiv p q -> to_Z p = to_Z q.
Proof.
  intros [a b] [c d] H.
  unfold Z_equiv in H. simpl in H.
  unfold to_Z. simpl.
  apply (f_equal to_nat) in H.
  repeat rewrite add_rel_correct in H.
  lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: RING ALGEBRA                                 *)
(*                                                                            *)
(* ========================================================================== *)

(** Helper lemma: equal integers have equivalent representations. *)
Lemma to_Z_faithful : forall p q : Z_rel,
  to_Z p = to_Z q -> Z_equiv p q.
Proof.
  intros [a b] [c d] H.
  unfold to_Z in H. simpl in H.
  unfold Z_equiv. simpl.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  lia.
Qed.

Theorem Z_add_assoc : forall p q r : Z_rel,
  Z_equiv (Z_add (Z_add p q) r) (Z_add p (Z_add q r)).
Proof.
  intros p q r.
  unfold Z_equiv, Z_add. simpl.
  destruct p as [a b], q as [c d], r as [e f]. simpl.
  repeat rewrite add_rel_assoc.
  reflexivity.
Qed.

Theorem Z_add_comm : forall p q : Z_rel,
  Z_equiv (Z_add p q) (Z_add q p).
Proof.
  intros p q.
  unfold Z_equiv, Z_add. simpl.
  destruct p as [a b], q as [c d]. simpl.
  f_equal; apply add_rel_comm.
Qed.

Theorem Z_add_zero_l : forall p : Z_rel,
  Z_equiv (Z_add Z_zero p) p.
Proof.
  intro p.
  unfold Z_equiv, Z_add, Z_zero. simpl.
  destruct p as [a b]. simpl.
  repeat rewrite add_rel_zero_l.
  reflexivity.
Qed.

Theorem Z_add_zero_r : forall p : Z_rel,
  Z_equiv (Z_add p Z_zero) p.
Proof.
  intro p.
  unfold Z_equiv, Z_add, Z_zero. simpl.
  destruct p as [a b]. simpl.
  repeat rewrite add_rel_zero_r.
  reflexivity.
Qed.

Theorem Z_add_neg_l : forall p : Z_rel,
  Z_equiv (Z_add (Z_neg p) p) Z_zero.
Proof.
  intro p.
  unfold Z_equiv, Z_add, Z_neg, Z_zero. simpl.
  destruct p as [a b]. simpl.
  repeat rewrite add_rel_zero_l.
  repeat rewrite add_rel_zero_r.
  apply add_rel_comm.
Qed.

Theorem Z_add_neg_r : forall p : Z_rel,
  Z_equiv (Z_add p (Z_neg p)) Z_zero.
Proof.
  intro p.
  unfold Z_equiv, Z_add, Z_neg, Z_zero. simpl.
  destruct p as [a b]. simpl.
  repeat rewrite add_rel_zero_l.
  repeat rewrite add_rel_zero_r.
  apply add_rel_comm.
Qed.

Theorem Z_mul_assoc : forall p q r : Z_rel,
  Z_equiv (Z_mul (Z_mul p q) r) (Z_mul p (Z_mul q r)).
Proof.
  intros p q r.
  apply to_Z_faithful.
  repeat rewrite to_Z_mul.
  ring.
Qed.

Theorem Z_mul_comm : forall p q : Z_rel,
  Z_equiv (Z_mul p q) (Z_mul q p).
Proof.
  intros p q.
  apply to_Z_faithful.
  repeat rewrite to_Z_mul.
  ring.
Qed.

Theorem Z_mul_one_l : forall p : Z_rel,
  Z_equiv (Z_mul Z_one p) p.
Proof.
  intro p. apply to_Z_faithful.
  rewrite to_Z_mul. rewrite to_Z_one. ring.
Qed.

Theorem Z_mul_one_r : forall p : Z_rel,
  Z_equiv (Z_mul p Z_one) p.
Proof.
  intro p. apply to_Z_faithful.
  rewrite to_Z_mul. rewrite to_Z_one. ring.
Qed.

Theorem Z_mul_zero_l : forall p : Z_rel,
  Z_equiv (Z_mul Z_zero p) Z_zero.
Proof.
  intro p. apply to_Z_faithful.
  rewrite to_Z_mul. rewrite to_Z_zero. ring.
Qed.

Theorem Z_mul_zero_r : forall p : Z_rel,
  Z_equiv (Z_mul p Z_zero) Z_zero.
Proof.
  intro p. apply to_Z_faithful.
  rewrite to_Z_mul. rewrite to_Z_zero. ring.
Qed.

Theorem Z_mul_add_distr_l : forall p q r : Z_rel,
  Z_equiv (Z_mul p (Z_add q r)) (Z_add (Z_mul p q) (Z_mul p r)).
Proof.
  intros p q r. apply to_Z_faithful.
  rewrite to_Z_mul.
  repeat rewrite to_Z_add.
  repeat rewrite to_Z_mul. ring.
Qed.

Theorem Z_mul_add_distr_r : forall p q r : Z_rel,
  Z_equiv (Z_mul (Z_add p q) r) (Z_add (Z_mul p r) (Z_mul q r)).
Proof.
  intros p q r. apply to_Z_faithful.
  rewrite to_Z_mul.
  repeat rewrite to_Z_add.
  repeat rewrite to_Z_mul. ring.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: ISOMORPHISM                                  *)
(*                                                                            *)
(* ========================================================================== *)

Theorem from_Z_to_Z : forall z : Z,
  to_Z (from_Z z) = z.
Proof.
  intro z.
  unfold to_Z, from_Z.
  destruct (Z.leb 0 z) eqn:Hle.
  - apply Z.leb_le in Hle. simpl.
    rewrite to_nat_from_nat_id.
    rewrite Z2Nat.id; lia.
  - apply Z.leb_gt in Hle. simpl.
    rewrite to_nat_from_nat_id.
    rewrite Z2Nat.id; lia.
Qed.

Theorem to_Z_surjective : forall z : Z,
  exists p : Z_rel, to_Z p = z.
Proof.
  intro z. exists (from_Z z). apply from_Z_to_Z.
Qed.

(** Master isomorphism theorem. *)
Theorem Z_rel_isomorphic_to_Z :
  (forall z : Z, exists r : Z_rel, to_Z r = z) /\
  (forall r s : Z_rel, to_Z r = to_Z s <-> Z_equiv r s) /\
  (forall r s : Z_rel, to_Z (Z_add r s) = to_Z r + to_Z s) /\
  (forall r s : Z_rel, to_Z (Z_mul r s) = to_Z r * to_Z s) /\
  (forall r : Z_rel, to_Z (Z_neg r) = - to_Z r).
Proof.
  split. { exact to_Z_surjective. }
  split. { intros r s. split. apply to_Z_faithful. apply to_Z_respects_equiv. }
  split. { exact to_Z_add. }
  split. { exact to_Z_mul. }
  { exact to_Z_neg. }
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: ORDER RELATIONS                              *)
(*                                                                            *)
(* ========================================================================== *)

Definition Z_le (p q : Z_rel) : Prop := (to_Z p <= to_Z q)%Z.
Definition Z_lt (p q : Z_rel) : Prop := (to_Z p < to_Z q)%Z.
Definition Z_ge (p q : Z_rel) : Prop := (to_Z p >= to_Z q)%Z.
Definition Z_gt (p q : Z_rel) : Prop := (to_Z p > to_Z q)%Z.

Theorem Z_le_refl : forall p : Z_rel, Z_le p p.
Proof. intro p. unfold Z_le. lia. Qed.

Theorem Z_le_trans : forall p q r : Z_rel,
  Z_le p q -> Z_le q r -> Z_le p r.
Proof. intros p q r. unfold Z_le. lia. Qed.

Theorem Z_le_antisym : forall p q : Z_rel,
  Z_le p q -> Z_le q p -> Z_equiv p q.
Proof.
  intros p q Hpq Hqp.
  apply to_Z_faithful. unfold Z_le in *. lia.
Qed.

Theorem Z_le_total : forall p q : Z_rel,
  Z_le p q \/ Z_le q p.
Proof. intros p q. unfold Z_le. lia. Qed.

Theorem Z_le_dec : forall p q : Z_rel, {Z_le p q} + {~ Z_le p q}.
Proof.
  intros p q. unfold Z_le.
  destruct (Z_le_gt_dec (to_Z p) (to_Z q)) as [H|H].
  - left. exact H.
  - right. lia.
Defined.

Theorem Z_lt_irrefl : forall p : Z_rel, ~ Z_lt p p.
Proof. intro p. unfold Z_lt. lia. Qed.

Theorem Z_lt_trans : forall p q r : Z_rel,
  Z_lt p q -> Z_lt q r -> Z_lt p r.
Proof. intros p q r. unfold Z_lt. lia. Qed.

Theorem Z_lt_le_incl : forall p q : Z_rel,
  Z_lt p q -> Z_le p q.
Proof. intros p q. unfold Z_lt, Z_le. lia. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: EUCLIDEAN DIVISION                           *)
(*                                                                            *)
(* ========================================================================== *)

(** Quotient: integer division truncated toward zero. *)
Definition Z_quot (p q : Z_rel) : Z_rel :=
  from_Z (Z.quot (to_Z p) (to_Z q)).

(** Remainder: what's left after division. *)
Definition Z_rem (p q : Z_rel) : Z_rel :=
  from_Z (Z.rem (to_Z p) (to_Z q)).

(** Division by zero returns zero. *)
Theorem Z_quot_zero_r : forall p : Z_rel,
  Z_equiv (Z_quot p Z_zero) Z_zero.
Proof.
  intro p. apply to_Z_faithful.
  unfold Z_quot.
  rewrite from_Z_to_Z.
  rewrite to_Z_zero.
  apply Z.quot_0_r_ext.
  reflexivity.
Qed.

(** Quotient of zero is zero (when divisor is nonzero). *)
Theorem Z_quot_zero_l : forall q : Z_rel,
  ~ Z_equiv q Z_zero ->
  Z_equiv (Z_quot Z_zero q) Z_zero.
Proof.
  intros q Hneq. apply to_Z_faithful.
  unfold Z_quot.
  rewrite from_Z_to_Z.
  rewrite to_Z_zero.
  apply Z.quot_0_l.
  intro H. apply Hneq.
  apply to_Z_faithful.
  rewrite H. apply to_Z_zero.
Qed.

(** Remainder by zero is the dividend. *)
Theorem Z_rem_zero_r : forall p : Z_rel,
  Z_equiv (Z_rem p Z_zero) p.
Proof.
  intro p. apply to_Z_faithful.
  unfold Z_rem.
  rewrite from_Z_to_Z.
  rewrite to_Z_zero.
  apply Z.rem_0_r_ext.
  reflexivity.
Qed.

(** Division identity: a = (a quot b) * b + (a rem b). *)
Theorem Z_quot_rem_spec : forall p q : Z_rel,
  Z_equiv p (Z_add (Z_mul (Z_quot p q) q) (Z_rem p q)).
Proof.
  intros p q. apply to_Z_faithful.
  rewrite to_Z_add.
  rewrite to_Z_mul.
  unfold Z_quot, Z_rem.
  repeat rewrite from_Z_to_Z.
  pose proof (Z.quot_rem' (to_Z p) (to_Z q)) as H.
  lia.
Qed.

(** Self-division gives one (when non-zero). *)
Theorem Z_quot_self : forall p : Z_rel,
  ~ Z_equiv p Z_zero -> Z_equiv (Z_quot p p) Z_one.
Proof.
  intros p Hneq. apply to_Z_faithful.
  unfold Z_quot.
  rewrite from_Z_to_Z.
  rewrite to_Z_one.
  apply Z.quot_same.
  intro H. apply Hneq.
  apply to_Z_faithful.
  rewrite H. apply to_Z_zero.
Qed.

Global Instance Z_quot_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_quot.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply to_Z_faithful.
  unfold Z_quot.
  repeat rewrite from_Z_to_Z.
  f_equal.
  - apply to_Z_respects_equiv. exact Hxy.
  - apply to_Z_respects_equiv. exact Hab.
Qed.

Global Instance Z_rem_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_rem.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply to_Z_faithful.
  unfold Z_rem.
  repeat rewrite from_Z_to_Z.
  f_equal.
  - apply to_Z_respects_equiv. exact Hxy.
  - apply to_Z_respects_equiv. exact Hab.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: SAFE DIVISION                                *)
(*                                                                            *)
(* ========================================================================== *)

Definition Z_safe_quot (p q : Z_rel) : option Z_rel :=
  if Z.eqb (to_Z q) 0 then None else Some (Z_quot p q).

Definition Z_safe_rem (p q : Z_rel) : option Z_rel :=
  if Z.eqb (to_Z q) 0 then None else Some (Z_rem p q).

Theorem Z_safe_quot_nonzero : forall p q : Z_rel,
  ~ Z_equiv q Z_zero -> Z_safe_quot p q = Some (Z_quot p q).
Proof.
  intros p q Hneq.
  unfold Z_safe_quot.
  destruct (Z.eqb (to_Z q) 0) eqn:E.
  - apply Z.eqb_eq in E.
    exfalso. apply Hneq.
    apply to_Z_faithful. rewrite E. apply to_Z_zero.
  - reflexivity.
Qed.

Theorem Z_safe_quot_zero : forall p : Z_rel,
  Z_safe_quot p Z_zero = None.
Proof.
  intro p. unfold Z_safe_quot.
  rewrite to_Z_zero. simpl. reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: EXACT DIVISION (EMBEDDING TO Q)             *)
(*                                                                            *)
(* ========================================================================== *)

Local Close Scope Z_scope.
Local Open Scope Q_scope.

(** Embed Z_rel into Q (rationals). *)
Definition to_Q (p : Z_rel) : Q :=
  inject_Z (to_Z p).

(** Exact division via rationals. *)
Definition Z_exact_div (ctx : RelCtx) (p q : Z_rel) : ExtQ :=
  Q_contextual_div ctx (to_Q p) (to_Q q).

Theorem Z_exact_div_nonzero : forall ctx p q,
  ~ Z_equiv q Z_zero ->
  Z_exact_div ctx p q = FiniteQ (to_Q p / to_Q q).
Proof.
  intros ctx p q Hneq.
  unfold Z_exact_div.
  apply Q_contextual_div_conservative.
  unfold to_Q. intro H.
  apply Hneq.
  apply to_Z_faithful.
  unfold Qeq in H. simpl in H.
  rewrite Z.mul_1_r in H.
  rewrite to_Z_zero.
  exact H.
Qed.

Local Theorem to_Q_add : forall p q : Z_rel,
  to_Q (Z_add p q) == to_Q p + to_Q q.
Proof.
  intros p q. unfold to_Q.
  rewrite to_Z_add.
  rewrite inject_Z_plus.
  reflexivity.
Qed.

Local Theorem to_Q_mul : forall p q : Z_rel,
  to_Q (Z_mul p q) == to_Q p * to_Q q.
Proof.
  intros p q. unfold to_Q.
  rewrite to_Z_mul.
  rewrite inject_Z_mult.
  reflexivity.
Qed.

Local Theorem to_Q_neg : forall p : Z_rel,
  to_Q (Z_neg p) == - to_Q p.
Proof.
  intro p. unfold to_Q.
  rewrite to_Z_neg.
  rewrite inject_Z_opp.
  reflexivity.
Qed.

Local Close Scope Q_scope.
Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: N_REL EMBEDDING                             *)
(*                                                                            *)
(* ========================================================================== *)

Definition embed_N (n : N_rel) : Z_rel := (n, Zero_rel).

Theorem embed_N_to_Z : forall n : N_rel,
  to_Z (embed_N n) = Z.of_nat (to_nat n).
Proof.
  intro n. unfold embed_N, to_Z. simpl. lia.
Qed.

Theorem embed_N_add : forall m n : N_rel,
  Z_equiv (embed_N (add_rel m n)) (Z_add (embed_N m) (embed_N n)).
Proof.
  intros m n.
  unfold embed_N, Z_equiv, Z_add. simpl.
  apply to_nat_injective.
  repeat rewrite add_rel_correct. simpl. lia.
Qed.

Theorem embed_N_mul : forall m n : N_rel,
  Z_equiv (embed_N (mul_rel m n)) (Z_mul (embed_N m) (embed_N n)).
Proof.
  intros m n.
  unfold embed_N, Z_equiv, Z_mul. simpl.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  repeat rewrite mul_rel_correct. simpl. lia.
Qed.

Theorem embed_N_le : forall m n : N_rel,
  le_rel m n <-> Z_le (embed_N m) (embed_N n).
Proof.
  intros m n.
  unfold le_rel, Z_le.
  repeat rewrite embed_N_to_Z.
  lia.
Qed.

Theorem embed_N_injective : forall m n : N_rel,
  Z_equiv (embed_N m) (embed_N n) -> m = n.
Proof.
  intros m n H.
  apply to_Z_respects_equiv in H.
  repeat rewrite embed_N_to_Z in H.
  apply to_nat_injective.
  lia.
Qed.

Local Close Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: ZR MODULE - PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

Module ZR.
  Definition Z := Z_rel.
  Definition equiv := Z_equiv.
  Definition zero := Z_zero.
  Definition one := Z_one.
  Definition minus_one := Z_minus_one.
  Definition two := Z_two.
  Definition add := Z_add.
  Definition neg := Z_neg.
  Definition sub := Z_sub.
  Definition mul := Z_mul.
  Definition quot := Z_quot.
  Definition rem := Z_rem.
  Definition safe_quot := Z_safe_quot.
  Definition exact_div := Z_exact_div.
  Definition toZ := to_Z.
  Definition fromZ := from_Z.
  Definition toQ := to_Q.
  Definition from_N := embed_N.
  Definition le := Z_le.
  Definition lt := Z_lt.
  Definition ge := Z_ge.
  Definition gt := Z_gt.
  Definition le_dec := Z_le_dec.
  Definition equiv_refl := Z_equiv_refl.
  Definition equiv_sym := Z_equiv_sym.
  Definition equiv_trans := Z_equiv_trans.
  Definition isomorphism := Z_rel_isomorphic_to_Z.
  Definition add_assoc := Z_add_assoc.
  Definition add_comm := Z_add_comm.
  Definition add_zero_l := Z_add_zero_l.
  Definition add_zero_r := Z_add_zero_r.
  Definition add_neg_l := Z_add_neg_l.
  Definition add_neg_r := Z_add_neg_r.
  Definition mul_assoc := Z_mul_assoc.
  Definition mul_comm := Z_mul_comm.
  Definition mul_one_l := Z_mul_one_l.
  Definition mul_one_r := Z_mul_one_r.
  Definition mul_zero_l := Z_mul_zero_l.
  Definition mul_zero_r := Z_mul_zero_r.
  Definition distr_l := Z_mul_add_distr_l.
  Definition distr_r := Z_mul_add_distr_r.
  Definition quot_rem := Z_quot_rem_spec.
  Definition quot_zero_r := Z_quot_zero_r.
  Definition quot_self := Z_quot_self.
End ZR.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: HINT DATABASES & TACTICS                    *)
(*                                                                            *)
(* ========================================================================== *)

#[export] Hint Resolve
  Z_equiv_refl Z_equiv_sym Z_le_refl Z_le_trans
  Z_lt_irrefl Z_lt_trans
  Z_add_zero_l Z_add_zero_r Z_add_neg_l Z_add_neg_r
  Z_mul_one_l Z_mul_one_r Z_mul_zero_l Z_mul_zero_r
  : zrel.

#[export] Hint Rewrite
  to_Z_zero to_Z_one to_Z_neg to_Z_add to_Z_sub to_Z_mul
  from_Z_to_Z : zrel.

Ltac zrel_simpl :=
  unfold Z_equiv, Z_add, Z_neg, Z_sub, Z_mul, Z_zero, Z_one,
         Z_le, Z_lt, to_Z, from_Z; simpl.

(**
  zrel_lia: Tactic for Z_rel algebraic goals.
  Uses ucf_lia for auditable Z arithmetic (falls back to lia if needed).
*)
Ltac zrel_lia :=
  match goal with
  | |- Z_equiv ?p ?q => apply to_Z_faithful; autorewrite with zrel; try ucf_lia
  | |- Z_le ?p ?q => unfold Z_le; autorewrite with zrel; try ucf_lia
  | |- Z_lt ?p ?q => unfold Z_lt; autorewrite with zrel; try ucf_lia
  | _ => autorewrite with zrel; try ucf_lia
  end.

(**
  zrel_auto: Combined automation tactic.
  Integrates with UCF hint databases (ucf_z, ucf_arith).
*)
Ltac zrel_auto := auto with zrel ucf_z ucf_arith; try zrel_simpl; try zrel_lia.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 14: NOTATION SCOPES                             *)
(*                                                                            *)
(* ========================================================================== *)

Declare Scope zrel_scope.
Delimit Scope zrel_scope with zr.

(* Convenient ASCII notations for the relational integers.  All firing only
   inside the [%zr] scope, so they never collide with Coq's standard Z_scope
   operators on raw [Z].  Replaces an earlier mojibake-encoded UTF-8 block. *)
Notation "p == q"  := (Z_equiv p q) (at level 70, no associativity)    : zrel_scope.
Notation "p + q"   := (Z_add p q)   (at level 50, left associativity)  : zrel_scope.
Notation "- p"     := (Z_neg p)     (at level 35, right associativity) : zrel_scope.
Notation "p - q"   := (Z_sub p q)   (at level 50, left associativity)  : zrel_scope.
Notation "p * q"   := (Z_mul p q)   (at level 40, left associativity)  : zrel_scope.
Notation "p / q"   := (Z_quot p q)  (at level 40, left associativity)  : zrel_scope.
Notation "p 'mod' q" := (Z_rem p q) (at level 40, q at next level, no associativity)  : zrel_scope.
Notation "p <= q"  := (Z_le p q)    (at level 70, no associativity)    : zrel_scope.
Notation "p < q"   := (Z_lt p q)    (at level 70, no associativity)    : zrel_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 15: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.
  Local Open Scope Z_scope.

  Definition test_zero : to_Z Z_zero = 0 := eq_refl.
  Definition test_one : to_Z Z_one = 1 := eq_refl.
  Definition test_minus_one : to_Z Z_minus_one = (-1) := eq_refl.
  Definition test_add : to_Z (Z_add Z_one Z_one) = 2 := eq_refl.
  Definition test_neg : to_Z (Z_neg Z_one) = (-1) := eq_refl.
  Definition test_sub : to_Z (Z_sub Z_one Z_one) = 0 := eq_refl.
  Definition test_mul : to_Z (Z_mul Z_two Z_two) = 4 := eq_refl.

  Example test_quot_6_2 : to_Z (Z_quot (from_Z 6) (from_Z 2)) = 3.
  Proof. unfold Z_quot. rewrite from_Z_to_Z. reflexivity. Qed.

  Example test_rem_7_3 : to_Z (Z_rem (from_Z 7) (from_Z 3)) = 1.
  Proof. unfold Z_rem. rewrite from_Z_to_Z. reflexivity. Qed.

  Example test_quot_neg : to_Z (Z_quot (from_Z (-7)) (from_Z 3)) = (-2).
  Proof. unfold Z_quot. rewrite from_Z_to_Z. reflexivity. Qed.
End AxiomAudit.

Print Assumptions Z_rel_isomorphic_to_Z.
Print Assumptions Z_quot_rem_spec.
Print Assumptions Z_exact_div_nonzero.

(*
  SUMMARY
  =======

  This file provides:
  - Z_rel: Integers as pairs of relational naturals
  - Complete arithmetic: +, -, x, / (Euclidean), exact division via Q
  - Ring structure with all algebraic laws proven
  - Isomorphism with Coq's Z
  - Integration with contextual division from RelationalDivision

  AXIOM STATUS: ZERO AXIOMS
  ADMIT STATUS: ZERO ADMITS
*)
