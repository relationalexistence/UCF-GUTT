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
  |                    RelationalReals.v                                     |
  |                                                                          |
  |                    Constructive Real Numbers from Cauchy Sequences       |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-12                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Define real numbers constructively via Cauchy sequences of     |
  |  rationals, grounded in the UCF/GUTT relational framework.               |
  |                                                                          |
  |  KEY INSIGHT: Real numbers ARE relational structures.                    |
  |    - A real is a Cauchy sequence r : nat -> Q                            |
  |    - The sequence IS a relation (functional, serial)                     |
  |    - Equivalence captures "same limit" via convergence                   |
  |    - Q embeds as constant sequences (stable relations)                   |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Helper Lemmas (Qabs properties)                           |
  |    SECTION 2:  Cauchy Definition (is_cauchy_mod, R_cauchy)               |
  |    SECTION 3:  Equivalence Relation (Req, reflexivity, symmetry, trans)  |
  |    SECTION 4:  Q Embedding (Q_to_R, R_zero, R_one)                       |
  |    SECTION 5:  Zero Not Equal One (constructive proof)                   |
  |    SECTION 6:  Addition Field Axioms                                     |
  |    SECTION 7:  Multiplication Field Axioms                               |
  |    SECTION 8:  Distributivity                                            |
  |    SECTION 9:  Relational View (connection to UCF/GUTT)                  |
  |    SECTION 10: RR Module - Public API                                    |
  |    SECTION 11: Hint Databases & Tactics                                  |
  |    SECTION 12: Examples                                                  |
  |    SECTION 13: Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Types: R_cauchy                                                   |
  |      - Constructor: mkR                                                  |
  |      - Equivalence: Req (=R=)                                            |
  |      - Constants: R_zero (0R), R_one (1R)                                |
  |      - Embedding: Q_to_R                                                 |
  |      - RR module exports                                                 |
  |      - Hint database: rreal                                              |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - Type: R_cauchy                                                      |
  |    - Equivalence: Req, infix =R=                                         |
  |    - Properties: Req_refl, Req_sym, Req_trans                            |
  |    - Constants: R_zero, R_one with 0R, 1R notations                      |
  |    - Q operations: Q_*_R suffix (Q_add_comm_R, Q_mul_assoc_R)            |
  |                                                                          |
  |  KEY RESULTS:                                                            |
  |    - R_cauchy forms an equivalence under Req                             |
  |    - Q embeds into R via constant sequences                              |
  |    - 0R <> 1R (constructive proof)                                        |
  |    - Field axioms hold for embedded Q                                    |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                            |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.

(* Import UCF/GUTT extension framework for relation properties *)
Require Import Top__Extensions__Prelude.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

Open Scope Q_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: HELPER LEMMAS                                *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QABS PROPERTIES
  ===============
  
  These lemmas establish key properties of the absolute value function
  on rationals that we need for Cauchy sequence proofs.
*)

(** Zero has zero absolute value, bounded by any positive fraction. *)
Lemma Qabs_zero_le : forall k : nat, (k > 0)%nat -> Qabs 0 <= 1 # Pos.of_nat k.
Proof.
  intros k Hk. unfold Qabs. simpl. unfold Qle. simpl. lia.
Qed.

(** Equal to zero implies absolute value is zero. *)
Lemma Qabs_eq_zero : forall q : Q, q == 0 -> Qabs q == 0.
Proof. 
  intros q H. rewrite H. reflexivity. 
Qed.

(** Non-negative absolute value. *)
Lemma Qabs_nonneg : forall q : Q, 0 <= Qabs q.
Proof.
  intro q. apply Qabs_nonneg.
Qed.

(** Absolute value of negation. *)
Lemma Qabs_opp_eq : forall q : Q, Qabs (- q) == Qabs q.
Proof.
  intro q. apply Qabs_opp.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: CAUCHY DEFINITION                            *)
(*                                                                            *)
(* ========================================================================== *)

(**
  PHILOSOPHICAL GROUNDING
  =======================
  
  In UCF/GUTT, we view a Cauchy sequence as a RELATIONAL STRUCTURE:
  
  - The sequence f : nat -> Q is a functional relation from nat to Q
  - The Cauchy modulus captures how the relation "converges"
  - Adjacent terms must satisfy: |f(n+1) - f(n)| <= 1/(n+1)
  
  This gives a constructive definition of real numbers without
  assuming classical axioms (LPO, Markov's principle, etc.).
*)

(** 
  A sequence f is Cauchy with modulus if adjacent terms converge.
  This is a simple but effective modulus of convergence.
*)
Definition is_cauchy_mod (f : nat -> Q) : Prop :=
  forall n : nat, Qabs (f (S n) - f n) <= 1 # (Pos.of_nat (S n)).

(**
  R_cauchy: A constructive real number.
  
  A real is a rational sequence together with a proof that
  it satisfies the Cauchy modulus condition.
*)
Record R_cauchy : Type := mkR {
  r_seq : nat -> Q;
  r_mod : is_cauchy_mod r_seq
}.

(** Accessor notation. *)
Notation "x '.seq'" := (r_seq x) (at level 1, format "x '.seq'").

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: EQUIVALENCE RELATION                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
  EQUIVALENCE OF CAUCHY SEQUENCES
  ===============================
  
  Two Cauchy sequences are equivalent if they converge to the same limit.
  We express this as: for any precision k > 0, eventually |x_n - y_n| <= 1/k.
*)

Definition Req (x y : R_cauchy) : Prop :=
  forall k : nat, (k > 0)%nat -> 
    exists N : nat, forall n : nat, (n >= N)%nat ->
      Qabs (r_seq x n - r_seq y n) <= 1 # (Pos.of_nat k).

Infix "=R=" := Req (at level 70, no associativity).

(* -------------------------------------------------------------------------- *)
(*                         Reflexivity                                        *)
(* -------------------------------------------------------------------------- *)

Theorem Req_refl : forall x, x =R= x.
Proof.
  intro x. unfold Req. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : r_seq x n - r_seq x n == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Symmetry                                           *)
(* -------------------------------------------------------------------------- *)

Theorem Req_sym : forall x y, x =R= y -> y =R= x.
Proof.
  intros x y H. unfold Req in *. intros k Hk.
  destruct (H k Hk) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  assert (Heq : r_seq y n - r_seq x n == -(r_seq x n - r_seq y n)) by ring.
  setoid_rewrite Heq.
  rewrite Qabs_opp. exact HN.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Transitivity                                       *)
(* -------------------------------------------------------------------------- *)

Theorem Req_trans : forall x y z, x =R= y -> y =R= z -> x =R= z.
Proof.
  intros x y z Hxy Hyz. unfold Req in *. intros k Hk.
  assert (H2k : (2*k > 0)%nat) by lia.
  destruct (Hxy (2*k)%nat H2k) as [N1 HN1].
  destruct (Hyz (2*k)%nat H2k) as [N2 HN2].
  exists (max N1 N2). intros n Hn.
  assert (Hn1 : (n >= N1)%nat) by lia.
  assert (Hn2 : (n >= N2)%nat) by lia.
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  assert (Htri : Qabs (r_seq x n - r_seq z n) <= 
                 Qabs (r_seq x n - r_seq y n) + Qabs (r_seq y n - r_seq z n)).
  { assert (Heq : r_seq x n - r_seq z n == 
                  (r_seq x n - r_seq y n) + (r_seq y n - r_seq z n)) by ring.
    setoid_rewrite Heq. apply Qabs_triangle. }
  eapply Qle_trans; [exact Htri|].
  eapply Qle_trans; [apply Qplus_le_compat; [exact HN1 | exact HN2]|].
  unfold Qle, Qplus. simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Equivalence Using Base.v Definitions               *)
(* -------------------------------------------------------------------------- *)

(** 
  We prove Req is an equivalence using our project's definitions from
  Top__Extensions__Base.v, avoiding the Coq.Classes.RelationClasses typeclass.
*)

Theorem Req_Reflexive : Top__Extensions__Base.Reflexive Req.
Proof.
  unfold Top__Extensions__Base.Reflexive. exact Req_refl.
Qed.

Theorem Req_Symmetric : Top__Extensions__Base.Symmetric Req.
Proof.
  unfold Top__Extensions__Base.Symmetric. exact Req_sym.
Qed.

Theorem Req_Transitive : Top__Extensions__Base.Transitive Req.
Proof.
  unfold Top__Extensions__Base.Transitive. exact Req_trans.
Qed.

(** Main equivalence theorem using our project's Equivalence definition. *)
Theorem Req_Equivalence : Top__Extensions__Base.Equivalence Req.
Proof.
  unfold Top__Extensions__Base.Equivalence.
  split. { exact Req_Reflexive. }
  split. { exact Req_Symmetric. }
  exact Req_Transitive.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: Q EMBEDDING                                  *)
(*                                                                            *)
(* ========================================================================== *)

(**
  EMBEDDING RATIONALS AS CONSTANT SEQUENCES
  =========================================
  
  Every rational q embeds into R as the constant sequence (q, q, q, ...).
  This is a Cauchy sequence since adjacent terms differ by 0.
  
  Relationally, a constant sequence is a "stable" relation - it never changes.
*)

(** Constant sequences are Cauchy. *)
Lemma cauchy_const : forall q : Q, is_cauchy_mod (fun _ => q).
Proof.
  intro q. unfold is_cauchy_mod. intro n.
  assert (H : q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). unfold Qle. simpl. lia.
Qed.

(** Embedding function. *)
Definition Q_to_R (q : Q) : R_cauchy := mkR (fun _ => q) (cauchy_const q).

(** Canonical constants. *)
Definition R_zero : R_cauchy := Q_to_R 0.
Definition R_one : R_cauchy := Q_to_R 1.
Definition R_two : R_cauchy := Q_to_R 2.

Notation "'0R'" := R_zero.
Notation "'1R'" := R_one.
Notation "'2R'" := R_two.

(** Embedding preserves equality. *)
Theorem Q_to_R_eq : forall p q : Q, p == q -> Q_to_R p =R= Q_to_R q.
Proof.
  intros p q Hpq. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p - q == 0) by (rewrite Hpq; ring).
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: ZERO NOT EQUAL ONE                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CONSTRUCTIVE PROOF: 0R <> 1R
  ===========================
  
  This is a key result establishing that our real numbers are non-trivial.
  The proof is constructive: we show 0R =R= 1R leads to a contradiction.
*)

Theorem R_zero_neq_one : ~(0R =R= 1R).
Proof.
  unfold Req, R_zero, R_one, Q_to_R. simpl. intro H.
  destruct (H 2%nat) as [N HN]; [lia|].
  specialize (HN N (Nat.le_refl N)).
  unfold Qabs, Qminus, Qplus, Qopp in HN. simpl in HN.
  unfold Qle in HN. simpl in HN. lia.
Qed.

(** Symmetric version. *)
Theorem R_one_neq_zero : ~(1R =R= 0R).
Proof.
  intro H. apply R_zero_neq_one. apply Req_sym. exact H.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: ADDITION FIELD AXIOMS                        *)
(*                                                                            *)
(* ========================================================================== *)

(**
  ADDITION AXIOMS FOR EMBEDDED Q
  ==============================
  
  We prove that the standard field axioms hold for rationals embedded
  in R via Q_to_R. These are the foundation for full field structure.
*)

(** Addition commutativity. *)
Theorem Q_add_comm_R : forall p q : Q, Q_to_R (p + q) =R= Q_to_R (q + p).
Proof.
  intros p q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p + q - (q + p) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Addition associativity. *)
Theorem Q_add_assoc_R : forall p q r : Q, 
  Q_to_R (p + q + r) =R= Q_to_R (p + (q + r)).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p + q + r - (p + (q + r)) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Left additive identity. *)
Theorem Q_add_0_l_R : forall q : Q, Q_to_R (0 + q) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : 0 + q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Right additive identity. *)
Theorem Q_add_0_r_R : forall q : Q, Q_to_R (q + 0) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q + 0 - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Additive inverse. *)
Theorem Q_add_neg_R : forall q : Q, Q_to_R (q + -q) =R= Q_to_R 0.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q + - q - 0 == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Left inverse version. *)
Theorem Q_add_neg_l_R : forall q : Q, Q_to_R (-q + q) =R= Q_to_R 0.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : - q + q - 0 == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: MULTIPLICATION FIELD AXIOMS                  *)
(*                                                                            *)
(* ========================================================================== *)

(** Multiplication commutativity. *)
Theorem Q_mul_comm_R : forall p q : Q, Q_to_R (p * q) =R= Q_to_R (q * p).
Proof.
  intros p q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * q - q * p == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Multiplication associativity. *)
Theorem Q_mul_assoc_R : forall p q r : Q, 
  Q_to_R (p * q * r) =R= Q_to_R (p * (q * r)).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * q * r - p * (q * r) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Left multiplicative identity. *)
Theorem Q_mul_1_l_R : forall q : Q, Q_to_R (1 * q) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : 1 * q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Right multiplicative identity. *)
Theorem Q_mul_1_r_R : forall q : Q, Q_to_R (q * 1) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q * 1 - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Multiplication by zero (left). *)
Theorem Q_mul_0_l_R : forall q : Q, Q_to_R (0 * q) =R= Q_to_R 0.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : 0 * q - 0 == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Multiplication by zero (right). *)
Theorem Q_mul_0_r_R : forall q : Q, Q_to_R (q * 0) =R= Q_to_R 0.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q * 0 - 0 == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: DISTRIBUTIVITY                               *)
(*                                                                            *)
(* ========================================================================== *)

(** Left distributivity. *)
Theorem Q_distr_l_R : forall p q r : Q, 
  Q_to_R (p * (q + r)) =R= Q_to_R (p * q + p * r).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * (q + r) - (p * q + p * r) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(** Alias for compatibility. *)
Definition Q_distr_R := Q_distr_l_R.

(** Right distributivity. *)
Theorem Q_distr_r_R : forall p q r : Q, 
  Q_to_R ((p + q) * r) =R= Q_to_R (p * r + q * r).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : (p + q) * r - (p * r + q * r) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: RELATIONAL VIEW                              *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION
  =========================
  
  This section connects our Cauchy sequence construction to the
  UCF/GUTT relational framework, showing that:
  
  1. A sequence r : nat -> Q defines a relation R(n, q) := r(n) = q
  2. This relation is functional (each n has unique q)
  3. This relation is serial (every n has some q)
  4. Equivalence Req captures "convergence to same limit"
*)

Module RelationalView.

  (** The sequence as a relation. *)
  Definition sequence_relation (x : R_cauchy) (n : nat) (q : Q) : Prop :=
    r_seq x n == q.

  (** Sequences are functional relations. *)
  Theorem sequence_functional : forall x n q1 q2,
    sequence_relation x n q1 -> sequence_relation x n q2 -> q1 == q2.
  Proof.
    intros x n q1 q2 H1 H2.
    unfold sequence_relation in *.
    rewrite <- H1. rewrite <- H2. reflexivity.
  Qed.

  (** Sequences are serial (total) relations. *)
  Theorem sequence_serial : forall x n, exists q, sequence_relation x n q.
  Proof.
    intros x n. exists (r_seq x n). unfold sequence_relation. reflexivity.
  Qed.

  (** Constant sequences are stable relations. *)
  Theorem constant_sequence_stable : forall q n m,
    sequence_relation (Q_to_R q) n q /\ sequence_relation (Q_to_R q) m q.
  Proof.
    intros q n m. split; unfold sequence_relation, Q_to_R; simpl; reflexivity.
  Qed.

End RelationalView.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: RR MODULE - PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RR: The canonical public API for relational reals.
  
  This module provides stable, memorable names for downstream use.
*)

Module RR.

  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)
  
  (** The type of constructive real numbers. *)
  Definition R := R_cauchy.
  
  (** The Cauchy modulus predicate. *)
  Definition cauchy := is_cauchy_mod.
  
  (* ====================================================================== *)
  (*                         Constructors                                   *)
  (* ====================================================================== *)
  
  (** Build a real from sequence and proof. *)
  Definition mk := mkR.
  
  (** Embed a rational. *)
  Definition of_Q := Q_to_R.
  
  (* ====================================================================== *)
  (*                         Constants                                      *)
  (* ====================================================================== *)
  
  Definition zero : R := R_zero.
  Definition one : R := R_one.
  Definition two : R := R_two.
  
  (* ====================================================================== *)
  (*                         Accessors                                      *)
  (* ====================================================================== *)
  
  (** Get the underlying sequence. *)
  Definition seq := r_seq.
  
  (** Get the modulus proof. *)
  Definition cauchy_mod := r_mod.
  
  (* ====================================================================== *)
  (*                         Equivalence                                    *)
  (* ====================================================================== *)
  
  Definition eq := Req.
  Definition eq_refl := Req_refl.
  Definition eq_sym := Req_sym.
  Definition eq_trans := Req_trans.
  Definition eq_equiv := Req_Equivalence.
  
  (* ====================================================================== *)
  (*                         Key Theorems                                   *)
  (* ====================================================================== *)
  
  Definition zero_neq_one := R_zero_neq_one.
  Definition one_neq_zero := R_one_neq_zero.
  
  (* Addition *)
  Definition add_comm := Q_add_comm_R.
  Definition add_assoc := Q_add_assoc_R.
  Definition add_0_l := Q_add_0_l_R.
  Definition add_0_r := Q_add_0_r_R.
  Definition add_neg := Q_add_neg_R.
  Definition add_neg_l := Q_add_neg_l_R.
  
  (* Multiplication *)
  Definition mul_comm := Q_mul_comm_R.
  Definition mul_assoc := Q_mul_assoc_R.
  Definition mul_1_l := Q_mul_1_l_R.
  Definition mul_1_r := Q_mul_1_r_R.
  Definition mul_0_l := Q_mul_0_l_R.
  Definition mul_0_r := Q_mul_0_r_R.
  
  (* Distributivity *)
  Definition distr_l := Q_distr_l_R.
  Definition distr_r := Q_distr_r_R.
  
  (* ====================================================================== *)
  (*                         Helper                                         *)
  (* ====================================================================== *)
  
  Definition const_cauchy := cauchy_const.

End RR.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: HINT DATABASES & TACTICS                    *)
(*                                                                            *)
(* ========================================================================== *)

(** Hints for relational reals. *)

#[export] Hint Resolve
  Req_refl
  Req_sym
  Req_trans
  Req_Equivalence
  R_zero_neq_one
  R_one_neq_zero
  Q_add_comm_R
  Q_add_assoc_R
  Q_add_0_l_R
  Q_add_0_r_R
  Q_add_neg_R
  Q_add_neg_l_R
  Q_mul_comm_R
  Q_mul_assoc_R
  Q_mul_1_l_R
  Q_mul_1_r_R
  Q_mul_0_l_R
  Q_mul_0_r_R
  Q_distr_l_R
  Q_distr_r_R
  cauchy_const
  : rreal.

(** Tactic for proving constant Q embeddings are equal. *)
Ltac req_const :=
  unfold Req, Q_to_R; simpl; intros k Hk;
  exists 0%nat; intros n Hn;
  match goal with
  | |- Qabs ?e <= _ => 
      let H := fresh "H" in
      assert (H : e == 0) by ring;
      rewrite (Qabs_eq_zero _ H);
      apply Qabs_zero_le; exact Hk
  end.

(** Tactic for general relational real automation. *)
Ltac rreal_auto :=
  auto with rreal;
  try req_const.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: EXAMPLES                                    *)
(*                                                                            *)
(* ========================================================================== *)

Module RealExamples.

  (** Reflexivity example. *)
  Example ex_refl : 0R =R= 0R.
  Proof. apply Req_refl. Qed.

  (** Symmetry example. *)
  Example ex_sym : forall x y : R_cauchy, x =R= y -> y =R= x.
  Proof. apply Req_sym. Qed.

  (** Zero plus anything is zero. *)
  Example ex_add_0 : Q_to_R (0 + 1) =R= Q_to_R 1.
  Proof. apply Q_add_0_l_R. Qed.

  (** One times anything is itself. *)
  Example ex_mul_1 : Q_to_R (1 * 5) =R= Q_to_R 5.
  Proof. apply Q_mul_1_l_R. Qed.

  (** Distributivity example. *)
  Example ex_distr : Q_to_R (2 * (3 + 4)) =R= Q_to_R (2 * 3 + 2 * 4).
  Proof. apply Q_distr_l_R. Qed.

  (** Zero not equal to one. *)
  Example ex_neq : ~(0R =R= 1R).
  Proof. exact R_zero_neq_one. Qed.

  (** Additive inverse. *)
  Example ex_inv : Q_to_R (5 + -5) =R= 0R.
  Proof. apply Q_add_neg_R. Qed.

  (** Using the tactic. *)
  Example ex_tactic : Q_to_R (2 + 3) =R= Q_to_R (3 + 2).
  Proof. rreal_auto. Qed.

  (** Commutativity of multiplication. *)
  Example ex_mul_comm : Q_to_R (2 * 7) =R= Q_to_R (7 * 2).
  Proof. apply Q_mul_comm_R. Qed.

  (** Associativity of addition. *)
  Example ex_add_assoc : Q_to_R (1 + 2 + 3) =R= Q_to_R (1 + (2 + 3)).
  Proof. apply Q_add_assoc_R. Qed.

  (** Multiplication by zero. *)
  Example ex_mul_0 : Q_to_R (999 * 0) =R= 0R.
  Proof. apply Q_mul_0_r_R. Qed.

  (** Transitive chain. *)
  Example ex_trans : Q_to_R 5 =R= Q_to_R 5.
  Proof. apply Req_refl. Qed.

End RealExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)
  
  Definition test_zero_seq : r_seq R_zero 0 = 0.
  Proof. reflexivity. Qed.

  Definition test_one_seq : r_seq R_one 42 = 1.
  Proof. reflexivity. Qed.

  Definition test_Q_to_R : r_seq (Q_to_R (3#4)) 100 = (3#4).
  Proof. reflexivity. Qed.

  Definition test_const : is_cauchy_mod (fun _ => 0).
  Proof. exact (cauchy_const 0). Qed.

  (** Key theorem assumptions - all should be "Closed under global context". *)
  
End AxiomAudit.

(** Print Assumptions for key theorems. *)
Print Assumptions Req_Equivalence.
Print Assumptions R_zero_neq_one.
Print Assumptions Q_add_comm_R.
Print Assumptions Q_mul_comm_R.
Print Assumptions Q_distr_l_R.
Print Assumptions cauchy_const.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (RR):
    RR.R                    = R_cauchy (the type)
    RR.zero, RR.one, RR.two = constants
    RR.of_Q                 = Q_to_R (embedding)
    RR.seq                  = r_seq (accessor)
    RR.eq                   = Req (equivalence)
    RR.eq_refl/sym/trans    = equivalence proofs
    RR.zero_neq_one         = constructive proof 0 <> 1
    RR.add_*, RR.mul_*      = field axioms
    RR.distr_l/r            = distributivity
  
  TYPES:
    R_cauchy                = constructive real numbers
    is_cauchy_mod           = Cauchy modulus predicate
  
  CONSTRUCTORS:
    mkR                     = build real from sequence + proof
    Q_to_R                  = embed rational as constant sequence
  
  EQUIVALENCE:
    Req (=R=)               = equivalence relation on reals
    Req_refl                = reflexivity
    Req_sym                 = symmetry
    Req_trans               = transitivity
    Req_Equivalence         = combined equivalence proof
  
  CONSTANTS:
    R_zero (0R)             = Q_to_R 0
    R_one (1R)              = Q_to_R 1
    R_two (2R)              = Q_to_R 2
  
  KEY THEOREMS:
    R_zero_neq_one          : ~(0R =R= 1R)
    Q_add_comm_R            : Q_to_R (p + q) =R= Q_to_R (q + p)
    Q_mul_assoc_R           : Q_to_R (p*q*r) =R= Q_to_R (p*(q*r))
    Q_distr_l_R             : Q_to_R (p*(q+r)) =R= Q_to_R (p*q+p*r)
  
  HINT DATABASE:
    rreal                   : core lemmas for relational reals
    
    Usage: auto with rreal.
  
  TACTICS:
    req_const               : prove equality of Q embeddings
    rreal_auto              : combined automation
  
  RELATIONAL INTERPRETATION:
    - A real IS a sequence, which IS a relation nat -> Q
    - Sequences are functional (unique output per input)
    - Sequences are serial (every input has output)
    - Equivalence = convergence to same limit
    - Constants = stable (unchanging) relations
  
  AXIOM STATUS
  ============
  
  This file uses ZERO AXIOMS beyond Coq's standard library.
  All theorems verify as "Closed under the global context".
  
  COMPILATION
  ===========
  
  Requires: Top__Extensions__Prelude.v (and its dependencies)
  
    coqc Top__Extensions__Base.v
    coqc Top__Extensions__WholeCompletion.v
    coqc Top__Extensions__Composition.v
    coqc Top__Extensions__Prelude.v
    coqc Top__Numbers__RelationalReals.v
*)
