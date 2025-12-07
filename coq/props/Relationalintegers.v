(* ============================================================================ *)
(*                          Relational Integers                                *)
(*    UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
  See LICENSE, NOTICE, and TRADEMARKS in the repo root.
 *)
(* This file constructs integers from relational primitives, building on       *)
(* RelationalNaturals_proven.v. We represent integers as equivalence classes   *)
(* of pairs of naturals (a, b) representing the "difference" a - b.            *)
(*                                                                              *)
(* Key Results:                                                                 *)
(*   - ℤ_rel =~ Z (constructive isomorphism)                                   *)
(*   - Ring structure: addition, subtraction, multiplication proven            *)
(*   - Negation and absolute value                                             *)
(*   - Embedding of ℕ_rel into ℤ_rel                                           *)
(*   - Connection to RelationalArithmetic                                      *)
(*   - Total ordering with decidability                                        *)
(*   - NO NEW AXIOMS - all constructions proven                                *)
(*                                                                              *)
(* Relational Interpretation:                                                  *)
(*   Integers represent "signed relational differences" - the directed         *)
(*   distance between two relational entities. Positive = excess,              *)
(*   Negative = deficit, Zero = balance.                                       *)
(*                                                                              *)
(* File: proofs/RelationalIntegers.v                                           *)
(* Dependencies: RelationalNaturals_proven.v, Coq standard library             *)
(* ============================================================================ *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(* We'll use explicit scope annotations instead of opening Z_scope globally *)

(* ============================================================================ *)
(*                        PART 1: REPRESENTATION                               *)
(* ============================================================================ *)

(**
   RELATIONAL INTERPRETATION OF INTEGERS
   
   Integers emerge from the need to represent "differences" between
   relational entities. If entity A has strength m and entity B has
   strength n, the integer (m, n) represents the signed difference m - n.
   
   Two pairs (a, b) and (c, d) represent the same integer when:
     a - b = c - d   iff   a + d = c + b
   
   This is the classic Grothendieck construction for group completion.
*)

(** Raw representation: pair of natural numbers *)
Definition Z_raw : Type := (nat * nat).

(** Equivalence relation: (a, b) ~ (c, d) iff a + d = c + b *)
Definition Z_equiv (p q : Z_raw) : Prop :=
  (fst p + snd q = fst q + snd p)%nat.

Notation "p ≈ q" := (Z_equiv p q) (at level 70).

(** Proof that ≈ is an equivalence relation *)

Theorem Z_equiv_refl : Reflexive Z_equiv.
Proof.
  unfold Reflexive, Z_equiv.
  intro x. reflexivity.
Qed.

Theorem Z_equiv_sym : Symmetric Z_equiv.
Proof.
  unfold Symmetric, Z_equiv.
  intros x y H. symmetry. exact H.
Qed.

Theorem Z_equiv_trans : Transitive Z_equiv.
Proof.
  unfold Transitive, Z_equiv.
  intros x y z Hxy Hyz.
  destruct x as [a b], y as [c d], z as [e f]. simpl in *.
  lia.
Qed.

(** Register as Equivalence *)
Global Instance Z_equiv_Equivalence : Equivalence Z_equiv := {
  Equivalence_Reflexive := Z_equiv_refl;
  Equivalence_Symmetric := Z_equiv_sym;
  Equivalence_Transitive := Z_equiv_trans
}.

(* ============================================================================ *)
(*                    PART 2: CANONICAL REPRESENTATIVES                        *)
(* ============================================================================ *)

(**
   Each equivalence class has a canonical representative:
   - Positive n: (n, 0)
   - Zero:       (0, 0)
   - Negative n: (0, n)
   
   We define functions to normalize and check canonical form.
*)

(** Normalize a pair to canonical form *)
Definition normalize (p : Z_raw) : Z_raw :=
  let a := fst p in
  let b := snd p in
  if Nat.leb b a then ((a - b)%nat, 0%nat) else (0%nat, (b - a)%nat).

(** Check if in canonical form *)
Definition is_canonical (p : Z_raw) : Prop :=
  fst p = 0 \/ snd p = 0.

(** Normalization produces equivalent pair *)
Theorem normalize_equiv : forall p : Z_raw,
  p ≈ normalize p.
Proof.
  intro p.
  unfold Z_equiv, normalize.
  destruct p as [a b]. simpl.
  destruct (Nat.leb b a) eqn:Hle.
  - apply Nat.leb_le in Hle. simpl. lia.
  - apply Nat.leb_gt in Hle. simpl. lia.
Qed.

(** Normalization produces canonical form *)
Theorem normalize_is_canonical : forall p : Z_raw,
  is_canonical (normalize p).
Proof.
  intro p.
  unfold is_canonical, normalize.
  destruct p as [a b]. simpl.
  destruct (Nat.leb b a) eqn:Hle; simpl; auto.
Qed.

(** Equivalent pairs normalize to same canonical form *)
Theorem equiv_same_canonical : forall p q : Z_raw,
  p ≈ q -> normalize p = normalize q.
Proof.
  intros p q H.
  unfold Z_equiv, normalize in *.
  destruct p as [a b], q as [c d]. simpl in *.
  destruct (Nat.leb b a) eqn:Hab, (Nat.leb d c) eqn:Hcd.
  - apply Nat.leb_le in Hab. apply Nat.leb_le in Hcd.
    f_equal; lia.
  - apply Nat.leb_le in Hab. apply Nat.leb_gt in Hcd.
    exfalso. lia.
  - apply Nat.leb_gt in Hab. apply Nat.leb_le in Hcd.
    exfalso. lia.
  - apply Nat.leb_gt in Hab. apply Nat.leb_gt in Hcd.
    f_equal; lia.
Qed.

(* ============================================================================ *)
(*                        PART 3: ISOMORPHISM WITH Z                           *)
(* ============================================================================ *)



(** Convert raw representation to standard Z *)
Definition to_Z (p : Z_raw) : Z :=
  Z.of_nat (fst p) - Z.of_nat (snd p).

(** Convert standard Z to canonical representation *)
Definition from_Z (z : Z) : Z_raw :=
  if Z.leb 0 z then (Z.to_nat z, 0) else (0, Z.to_nat (- z)).

(** Equivalent pairs map to same Z *)
Theorem to_Z_respects_equiv : forall p q : Z_raw,
  p ≈ q -> to_Z p = to_Z q.
Proof.
  intros p q H.
  unfold Z_equiv, to_Z in *.
  destruct p as [a b], q as [c d]. simpl in *.
  lia.
Qed.

(** Round-trip 1: from_Z ∘ to_Z ≈ id *)
Theorem from_Z_to_Z_equiv : forall p : Z_raw,
  p ≈ from_Z (to_Z p).
Proof.
  intro p.
  unfold Z_equiv, to_Z, from_Z.
  destruct p as [a b]. simpl.
  destruct (Z.leb 0 (Z.of_nat a - Z.of_nat b)) eqn:Hle.
  - apply Z.leb_le in Hle. simpl.
    assert (Hz: Z.to_nat (Z.of_nat a - Z.of_nat b) = a - b) by lia.
    rewrite Hz. lia.
  - apply Z.leb_gt in Hle. simpl.
    assert (Hz: Z.to_nat (- (Z.of_nat a - Z.of_nat b)) = b - a) by lia.
    rewrite Hz. lia.
Qed.

(** Round-trip 2: to_Z ∘ from_Z = id *)
Theorem to_Z_from_Z_id : forall z : Z,
  to_Z (from_Z z) = z.
Proof.
  intro z.
  unfold to_Z, from_Z.
  destruct (Z.leb 0 z) eqn:Hle.
  - apply Z.leb_le in Hle. simpl.
    rewrite Z2Nat.id; lia.
  - apply Z.leb_gt in Hle. simpl.
    rewrite Z2Nat.id; lia.
Qed.

(** Injectivity up to equivalence *)
Theorem from_Z_injective : forall z1 z2 : Z,
  from_Z z1 = from_Z z2 -> z1 = z2.
Proof.
  intros z1 z2 H.
  rewrite <- (to_Z_from_Z_id z1).
  rewrite <- (to_Z_from_Z_id z2).
  f_equal. exact H.
Qed.

(** Surjectivity *)
Theorem to_Z_surjective : forall z : Z,
  exists p : Z_raw, to_Z p = z.
Proof.
  intro z.
  exists (from_Z z).
  apply to_Z_from_Z_id.
Qed.



(* ============================================================================ *)
(*                        PART 4: ARITHMETIC OPERATIONS                        *)
(* ============================================================================ *)



(**
   RELATIONAL INTERPRETATION:
   
   Addition: Combining relational strengths
   - (a, b) + (c, d) = (a+c, b+d)
   - Represents: (a-b) + (c-d) = (a+c) - (b+d)
   
   Negation: Reversing relational direction
   - -(a, b) = (b, a)
   - Represents: -(a-b) = b-a
   
   Subtraction: Finding relational difference
   - (a, b) - (c, d) = (a+d, b+c)
   - Represents: (a-b) - (c-d) = (a+d) - (b+c)
   
   Multiplication: Scaling relational strength
   - Uses distributive expansion
*)

(** Addition *)
Definition Zadd_raw (p q : Z_raw) : Z_raw :=
  (fst p + fst q, snd p + snd q).

Notation "p +ᵣ q" := (Zadd_raw p q) (at level 50, left associativity).

(** Negation *)
Definition Zneg_raw (p : Z_raw) : Z_raw :=
  (snd p, fst p).

Notation "-ᵣ p" := (Zneg_raw p) (at level 35, right associativity).

(** Subtraction *)
Definition Zsub_raw (p q : Z_raw) : Z_raw :=
  p +ᵣ (-ᵣ q).

Notation "p -ᵣ q" := (Zsub_raw p q) (at level 50, left associativity).

(** Multiplication *)
Definition Zmul_raw (p q : Z_raw) : Z_raw :=
  (fst p * fst q + snd p * snd q,
   fst p * snd q + snd p * fst q).

Notation "p *ᵣ q" := (Zmul_raw p q) (at level 40, left associativity).

(** Zero and One *)
Definition Z_zero : Z_raw := (0, 0).
Definition Z_one : Z_raw := (1, 0).
Definition Z_neg_one : Z_raw := (0, 1).

Notation "0ᵣ" := Z_zero.
Notation "1ᵣ" := Z_one.



(* ============================================================================ *)
(*                PART 5: OPERATIONS RESPECT EQUIVALENCE                       *)
(* ============================================================================ *)



(** Addition respects equivalence *)
Theorem Zadd_respects_equiv : forall p1 p2 q1 q2 : Z_raw,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 +ᵣ q1) ≈ (p2 +ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Zadd_raw in *. simpl.
  lia.
Qed.

(** Negation respects equivalence *)
Theorem Zneg_respects_equiv : forall p q : Z_raw,
  p ≈ q -> (-ᵣ p) ≈ (-ᵣ q).
Proof.
  intros p q H.
  unfold Z_equiv, Zneg_raw in *. simpl.
  lia.
Qed.

(** Subtraction respects equivalence *)
Theorem Zsub_respects_equiv : forall p1 p2 q1 q2 : Z_raw,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 -ᵣ q1) ≈ (p2 -ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Zsub_raw.
  apply Zadd_respects_equiv.
  - exact Hp.
  - apply Zneg_respects_equiv. exact Hq.
Qed.

(** Multiplication respects equivalence *)
Theorem Zmul_respects_equiv : forall p1 p2 q1 q2 : Z_raw,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 *ᵣ q1) ≈ (p2 *ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Zmul_raw in *. simpl.
  destruct p1 as [a1 b1], p2 as [a2 b2], q1 as [c1 d1], q2 as [c2 d2].
  simpl in *.
  (* Hp: a1 + b2 = a2 + b1 *)
  (* Hq: c1 + d2 = c2 + d1 *)
  (* Goal: a1*c1 + b1*d1 + (a2*d2 + b2*c2) = a2*c2 + b2*d2 + (a1*d1 + b1*c1) *)
  nia.
Qed.



(* ============================================================================ *)
(*                    PART 6: CORRESPONDENCE WITH Z                            *)
(* ============================================================================ *)



(** Addition corresponds to Z.add *)
Theorem Zadd_correct : forall p q : Z_raw,
  to_Z (p +ᵣ q) = (to_Z p + to_Z q)%Z.
Proof.
  intros p q.
  unfold to_Z, Zadd_raw. simpl.
  lia.
Qed.

(** Negation corresponds to Z.opp *)
Theorem Zneg_correct : forall p : Z_raw,
  to_Z (-ᵣ p) = (- to_Z p)%Z.
Proof.
  intro p.
  unfold to_Z, Zneg_raw. simpl.
  lia.
Qed.

(** Subtraction corresponds to Z.sub *)
Theorem Zsub_correct : forall p q : Z_raw,
  to_Z (p -ᵣ q) = (to_Z p - to_Z q)%Z.
Proof.
  intros p q.
  unfold Zsub_raw.
  rewrite Zadd_correct.
  rewrite Zneg_correct.
  lia.
Qed.

(** Multiplication corresponds to Z.mul *)
Theorem Zmul_correct : forall p q : Z_raw,
  to_Z (p *ᵣ q) = (to_Z p * to_Z q)%Z.
Proof.
  intros p q.
  unfold to_Z, Zmul_raw. simpl.
  destruct p as [a b], q as [c d]. simpl.
  lia.
Qed.

(** Zero corresponds *)
Theorem Z_zero_correct : to_Z Z_zero = 0%Z.
Proof.
  reflexivity.
Qed.

(** One corresponds *)
Theorem Z_one_correct : to_Z Z_one = 1%Z.
Proof.
  reflexivity.
Qed.



(* ============================================================================ *)
(*                    PART 7: RING PROPERTIES                                  *)
(* ============================================================================ *)



(**
   We prove that (Z_raw / ≈, +ᵣ, *ᵣ, 0ᵣ, 1ᵣ) forms a ring.
   The proofs use the isomorphism with Z.
*)

(** Addition is commutative *)
Theorem Zadd_comm : forall p q : Z_raw,
  (p +ᵣ q) ≈ (q +ᵣ p).
Proof.
  intros p q.
  unfold Z_equiv, Zadd_raw. simpl.
  lia.
Qed.

(** Addition is associative *)
Theorem Zadd_assoc : forall p q r : Z_raw,
  ((p +ᵣ q) +ᵣ r) ≈ (p +ᵣ (q +ᵣ r)).
Proof.
  intros p q r.
  unfold Z_equiv, Zadd_raw. simpl.
  lia.
Qed.

(** Zero is additive identity (left) *)
Theorem Zadd_0_l : forall p : Z_raw,
  (0ᵣ +ᵣ p) ≈ p.
Proof.
  intro p.
  unfold Z_equiv, Zadd_raw, Z_zero. simpl.
  lia.
Qed.

(** Zero is additive identity (right) *)
Theorem Zadd_0_r : forall p : Z_raw,
  (p +ᵣ 0ᵣ) ≈ p.
Proof.
  intro p.
  unfold Z_equiv, Zadd_raw, Z_zero. simpl.
  lia.
Qed.

(** Negation gives additive inverse *)
Theorem Zadd_neg : forall p : Z_raw,
  (p +ᵣ (-ᵣ p)) ≈ 0ᵣ.
Proof.
  intro p.
  unfold Z_equiv, Zadd_raw, Zneg_raw, Z_zero. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** Multiplication is commutative *)
Theorem Zmul_comm : forall p q : Z_raw,
  (p *ᵣ q) ≈ (q *ᵣ p).
Proof.
  intros p q.
  unfold Z_equiv, Zmul_raw. simpl.
  destruct p as [a b], q as [c d]. simpl.
  lia.
Qed.

(** Multiplication is associative *)
Theorem Zmul_assoc : forall p q r : Z_raw,
  ((p *ᵣ q) *ᵣ r) ≈ (p *ᵣ (q *ᵣ r)).
Proof.
  intros p q r.
  unfold Z_equiv, Zmul_raw. simpl.
  destruct p as [a b], q as [c d], r as [e f]. simpl.
  nia.
Qed.

(** One is multiplicative identity (left) *)
Theorem Zmul_1_l : forall p : Z_raw,
  (1ᵣ *ᵣ p) ≈ p.
Proof.
  intro p.
  unfold Z_equiv, Zmul_raw, Z_one. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** One is multiplicative identity (right) *)
Theorem Zmul_1_r : forall p : Z_raw,
  (p *ᵣ 1ᵣ) ≈ p.
Proof.
  intro p.
  unfold Z_equiv, Zmul_raw, Z_one. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** Distributivity (left) *)
Theorem Zmul_add_distr_l : forall p q r : Z_raw,
  (p *ᵣ (q +ᵣ r)) ≈ ((p *ᵣ q) +ᵣ (p *ᵣ r)).
Proof.
  intros p q r.
  unfold Z_equiv, Zmul_raw, Zadd_raw. simpl.
  destruct p as [a b], q as [c d], r as [e f]. simpl.
  nia.
Qed.

(** Distributivity (right) *)
Theorem Zmul_add_distr_r : forall p q r : Z_raw,
  ((p +ᵣ q) *ᵣ r) ≈ ((p *ᵣ r) +ᵣ (q *ᵣ r)).
Proof.
  intros p q r.
  unfold Z_equiv, Zmul_raw, Zadd_raw. simpl.
  destruct p as [a b], q as [c d], r as [e f]. simpl.
  nia.
Qed.

(** Zero annihilates (left) *)
Theorem Zmul_0_l : forall p : Z_raw,
  (0ᵣ *ᵣ p) ≈ 0ᵣ.
Proof.
  intro p.
  unfold Z_equiv, Zmul_raw, Z_zero. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** Zero annihilates (right) *)
Theorem Zmul_0_r : forall p : Z_raw,
  (p *ᵣ 0ᵣ) ≈ 0ᵣ.
Proof.
  intro p.
  unfold Z_equiv, Zmul_raw, Z_zero. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** Negation via multiplication by -1 *)
Theorem Zneg_mul : forall p : Z_raw,
  (Z_neg_one *ᵣ p) ≈ (-ᵣ p).
Proof.
  intro p.
  unfold Z_equiv, Zmul_raw, Zneg_raw, Z_neg_one. simpl.
  destruct p as [a b]. simpl. lia.
Qed.

(** Double negation *)
Theorem Zneg_neg : forall p : Z_raw,
  (-ᵣ (-ᵣ p)) ≈ p.
Proof.
  intro p.
  unfold Z_equiv, Zneg_raw. simpl.
  destruct p as [a b]. simpl. lia.
Qed.



(* ============================================================================ *)
(*                    PART 8: ORDER RELATION                                   *)
(* ============================================================================ *)



(** Define order in terms of to_Z *)
Definition Zle_raw (p q : Z_raw) : Prop :=
  (to_Z p <= to_Z q)%Z.

Definition Zlt_raw (p q : Z_raw) : Prop :=
  (to_Z p < to_Z q)%Z.

Notation "p ≤ᵣ q" := (Zle_raw p q) (at level 70).
Notation "p <ᵣ q" := (Zlt_raw p q) (at level 70).

(** Order respects equivalence *)
Theorem Zle_respects_equiv : forall p1 p2 q1 q2 : Z_raw,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 ≤ᵣ q1 <-> p2 ≤ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Zle_raw.
  rewrite (to_Z_respects_equiv _ _ Hp).
  rewrite (to_Z_respects_equiv _ _ Hq).
  reflexivity.
Qed.

(** Reflexivity *)
Theorem Zle_refl : forall p : Z_raw, p ≤ᵣ p.
Proof.
  intro p. unfold Zle_raw. lia.
Qed.

(** Transitivity *)
Theorem Zle_trans : forall p q r : Z_raw,
  p ≤ᵣ q -> q ≤ᵣ r -> p ≤ᵣ r.
Proof.
  intros p q r Hpq Hqr. unfold Zle_raw in *. lia.
Qed.

(** Antisymmetry (up to equivalence) *)
Theorem Zle_antisym : forall p q : Z_raw,
  p ≤ᵣ q -> q ≤ᵣ p -> p ≈ q.
Proof.
  intros p q Hpq Hqp.
  unfold Zle_raw, Z_equiv, to_Z in *.
  destruct p as [a b], q as [c d]. simpl in *. lia.
Qed.

(** Totality *)
Theorem Zle_total : forall p q : Z_raw, p ≤ᵣ q \/ q ≤ᵣ p.
Proof.
  intros p q. unfold Zle_raw. lia.
Qed.

(** Strict order is irreflexive *)
Theorem Zlt_irrefl : forall p : Z_raw, ~ (p <ᵣ p).
Proof.
  intro p. unfold Zlt_raw. lia.
Qed.

(** Trichotomy *)
Theorem Z_trichotomy : forall p q : Z_raw,
  p <ᵣ q \/ p ≈ q \/ q <ᵣ p.
Proof.
  intros p q.
  unfold Zlt_raw, Z_equiv, to_Z.
  destruct p as [a b], q as [c d]. simpl. lia.
Qed.

(** Order compatible with addition *)
Theorem Zle_add_compat : forall p q r : Z_raw,
  p ≤ᵣ q -> (p +ᵣ r) ≤ᵣ (q +ᵣ r).
Proof.
  intros p q r Hpq.
  unfold Zle_raw in *.
  repeat rewrite Zadd_correct. lia.
Qed.

(** Order compatible with multiplication by positive *)
Theorem Zle_mul_pos : forall p q r : Z_raw,
  p ≤ᵣ q -> 0ᵣ ≤ᵣ r -> (p *ᵣ r) ≤ᵣ (q *ᵣ r).
Proof.
  intros p q r Hpq Hr.
  unfold Zle_raw in *.
  repeat rewrite Zmul_correct.
  rewrite Z_zero_correct in Hr.
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.



(* ============================================================================ *)
(*                PART 9: EMBEDDING OF NATURALS                                *)
(* ============================================================================ *)



(**
   Natural numbers embed into integers via n ↦ (n, 0).
   This is the standard inclusion ℕ ⊂ ℤ.
*)

Definition nat_to_Z (n : nat) : Z_raw := (n, 0).

(** Embedding preserves zero *)
Theorem nat_to_Z_zero : nat_to_Z 0 ≈ 0ᵣ.
Proof.
  unfold nat_to_Z, Z_zero, Z_equiv. simpl. lia.
Qed.

(** Embedding preserves successor *)
Theorem nat_to_Z_succ : forall n : nat,
  nat_to_Z (S n) ≈ (nat_to_Z n +ᵣ 1ᵣ).
Proof.
  intro n.
  unfold nat_to_Z, Z_one, Zadd_raw, Z_equiv. simpl. lia.
Qed.

(** Embedding preserves addition *)
Theorem nat_to_Z_add : forall m n : nat,
  nat_to_Z (m + n) ≈ (nat_to_Z m +ᵣ nat_to_Z n).
Proof.
  intros m n.
  unfold nat_to_Z, Zadd_raw, Z_equiv. simpl. lia.
Qed.

(** Embedding preserves multiplication *)
Theorem nat_to_Z_mul : forall m n : nat,
  nat_to_Z (m * n) ≈ (nat_to_Z m *ᵣ nat_to_Z n).
Proof.
  intros m n.
  unfold nat_to_Z, Zmul_raw, Z_equiv. simpl. lia.
Qed.

(** Embedding preserves order *)
Theorem nat_to_Z_le : forall m n : nat,
  m <= n <-> nat_to_Z m ≤ᵣ nat_to_Z n.
Proof.
  intros m n.
  unfold nat_to_Z, Zle_raw, to_Z. simpl.
  split; intro H; lia.
Qed.

(** Embedding is injective *)
Theorem nat_to_Z_injective : forall m n : nat,
  nat_to_Z m ≈ nat_to_Z n -> m = n.
Proof.
  intros m n H.
  unfold nat_to_Z, Z_equiv in H. simpl in H. lia.
Qed.

(** Characterization: p is a natural iff p >= 0 and snd(normalize p) = 0 *)
Definition is_natural (p : Z_raw) : Prop :=
  0ᵣ ≤ᵣ p.

Theorem nat_is_natural : forall n : nat,
  is_natural (nat_to_Z n).
Proof.
  intro n.
  unfold is_natural, Zle_raw, to_Z, nat_to_Z, Z_zero. simpl. lia.
Qed.



(* ============================================================================ *)
(*              PART 10: ABSOLUTE VALUE AND SIGN                               *)
(* ============================================================================ *)



(** Absolute value *)
Definition Zabs_raw (p : Z_raw) : Z_raw :=
  if Z.leb 0 (to_Z p) then p else (-ᵣ p).

(** Sign: -1, 0, or 1 *)
Definition Zsign_raw (p : Z_raw) : Z_raw :=
  if Z.ltb (to_Z p) 0 then Z_neg_one
  else if Z.ltb 0 (to_Z p) then Z_one
  else Z_zero.

(** Absolute value is non-negative *)
Theorem Zabs_nonneg : forall p : Z_raw,
  0ᵣ ≤ᵣ Zabs_raw p.
Proof.
  intro p.
  unfold Zabs_raw, Zle_raw, Z_zero, to_Z.
  destruct (Z.leb 0 (Z.of_nat (fst p) - Z.of_nat (snd p))) eqn:H.
  - apply Z.leb_le in H. simpl. exact H.
  - apply Z.leb_gt in H. 
    unfold Zneg_raw. simpl. lia.
Qed.

(** |p| = 0 iff p ≈ 0 *)
Theorem Zabs_zero : forall p : Z_raw,
  Zabs_raw p ≈ 0ᵣ <-> p ≈ 0ᵣ.
Proof.
  intro p.
  unfold Zabs_raw.
  destruct (Z.leb 0 (to_Z p)) eqn:H.
  - reflexivity.
  - split; intro Heq.
    + unfold Z_equiv in *. 
      destruct p as [a b]. simpl in *.
      unfold Zneg_raw in Heq. simpl in Heq. lia.
    + unfold Z_equiv in *.
      destruct p as [a b]. simpl in *.
      unfold Zneg_raw. simpl. lia.
Qed.

(** Absolute value of product *)
Theorem Zabs_mul : forall p q : Z_raw,
  Zabs_raw (p *ᵣ q) ≈ (Zabs_raw p *ᵣ Zabs_raw q).
Proof.
  intros p q.
  unfold Z_equiv, Zabs_raw, Zmul_raw, Zneg_raw, to_Z.
  destruct p as [a b], q as [c d]. simpl.
  destruct (Z.leb 0 (Z.of_nat a - Z.of_nat b)) eqn:Hp;
  destruct (Z.leb 0 (Z.of_nat c - Z.of_nat d)) eqn:Hq;
  destruct (Z.leb 0 (Z.of_nat (a * c + b * d) - Z.of_nat (a * d + b * c))) eqn:Hpq;
  simpl.
  all: try (apply Z.leb_le in Hp);
       try (apply Z.leb_gt in Hp);
       try (apply Z.leb_le in Hq);
       try (apply Z.leb_gt in Hq);
       try (apply Z.leb_le in Hpq);
       try (apply Z.leb_gt in Hpq).
  all: try nia.
Qed.



(* ============================================================================ *)
(*                    PART 11: DECIDABILITY                                    *)
(* ============================================================================ *)



(** Decidable equivalence *)
Theorem Z_equiv_dec : forall p q : Z_raw, {p ≈ q} + {~ p ≈ q}.
Proof.
  intros p q.
  unfold Z_equiv.
  destruct (Nat.eq_dec (fst p + snd q) (fst q + snd p)).
  - left. exact e.
  - right. exact n.
Defined.

(** Decidable order *)
Theorem Zle_dec : forall p q : Z_raw, {p ≤ᵣ q} + {~ p ≤ᵣ q}.
Proof.
  intros p q.
  unfold Zle_raw.
  destruct (Z_le_gt_dec (to_Z p) (to_Z q)) as [H|H].
  - left. exact H.
  - right. lia.
Defined.

Theorem Zlt_dec : forall p q : Z_raw, {p <ᵣ q} + {~ p <ᵣ q}.
Proof.
  intros p q.
  unfold Zlt_raw.
  destruct (Z_lt_ge_dec (to_Z p) (to_Z q)) as [H|H].
  - left. exact H.
  - right. lia.
Defined.



(* ============================================================================ *)
(*              PART 12: CONNECTION TO RelationalArithmetic                    *)
(* ============================================================================ *)



(**
   RelationalArithmetic.v defines:
   - RNum := Z
   - radd := Z.add
   - rmul := Z.mul
   
   Our to_Z function provides the bridge:
   - to_Z : Z_raw → Z
   - Operations correspond exactly
*)

(** Our addition = RelationalArithmetic addition via to_Z *)
Theorem radd_corresponds : forall p q : Z_raw,
  to_Z (p +ᵣ q) = Z.add (to_Z p) (to_Z q).
Proof.
  exact Zadd_correct.
Qed.

(** Our multiplication = RelationalArithmetic multiplication via to_Z *)
Theorem rmul_corresponds : forall p q : Z_raw,
  to_Z (p *ᵣ q) = Z.mul (to_Z p) (to_Z q).
Proof.
  exact Zmul_correct.
Qed.

(** Complete isomorphism statement *)
Theorem integers_isomorphic_to_Z :
  (* Bijection *)
  (forall z : Z, exists p : Z_raw, to_Z p = z) /\
  (forall p q : Z_raw, to_Z p = to_Z q <-> p ≈ q) /\
  (* Preserves addition *)
  (forall p q : Z_raw, to_Z (p +ᵣ q) = (to_Z p + to_Z q)%Z) /\
  (* Preserves multiplication *)
  (forall p q : Z_raw, to_Z (p *ᵣ q) = (to_Z p * to_Z q)%Z) /\
  (* Preserves order *)
  (forall p q : Z_raw, p ≤ᵣ q <-> (to_Z p <= to_Z q)%Z).
Proof.
  split. { exact to_Z_surjective. }
  split. { 
    intros x y. split.
    - intro H. unfold Z_equiv, to_Z in *.
      destruct x as [a b], y as [c d]. simpl in *. lia.
    - intro H. apply to_Z_respects_equiv. exact H.
  }
  split. { exact Zadd_correct. }
  split. { exact Zmul_correct. }
  intros x y. unfold Zle_raw. reflexivity.
Qed.



(* ============================================================================ *)
(*                        PART 13: EXAMPLES                                    *)
(* ============================================================================ *)



(** Basic arithmetic *)

Example ex_add : to_Z ((2, 0) +ᵣ (3, 0)) = 5%Z.
Proof. reflexivity. Qed.

Example ex_sub : to_Z ((5, 0) -ᵣ (3, 0)) = 2%Z.
Proof. reflexivity. Qed.

Example ex_neg : to_Z (-ᵣ (3, 0)) = (-3)%Z.
Proof. reflexivity. Qed.

Example ex_mul : to_Z ((2, 0) *ᵣ (3, 0)) = 6%Z.
Proof. reflexivity. Qed.

Example ex_mul_neg : to_Z ((2, 0) *ᵣ (0, 3)) = (-6)%Z.
Proof. reflexivity. Qed.

Example ex_mul_neg_neg : to_Z ((0, 2) *ᵣ (0, 3)) = 6%Z.
Proof. reflexivity. Qed.

(** Equivalence examples *)

Example ex_equiv_1 : (3, 1) ≈ (5, 3).  (* 3-1 = 5-3 = 2 *)
Proof. unfold Z_equiv. simpl. reflexivity. Qed.

Example ex_equiv_2 : (0, 2) ≈ (1, 3).  (* 0-2 = 1-3 = -2 *)
Proof. unfold Z_equiv. simpl. reflexivity. Qed.

(** Normalization *)

Example ex_normalize : normalize (5, 3) = (2, 0).
Proof. reflexivity. Qed.

Example ex_normalize_neg : normalize (3, 5) = (0, 2).
Proof. reflexivity. Qed.

(** Ring properties in action *)

Example ex_comm : (2, 0) +ᵣ (3, 0) ≈ (3, 0) +ᵣ (2, 0).
Proof. apply Zadd_comm. Qed.

Example ex_distr : 
  (2, 0) *ᵣ ((3, 0) +ᵣ (4, 0)) ≈ ((2, 0) *ᵣ (3, 0)) +ᵣ ((2, 0) *ᵣ (4, 0)).
Proof. apply Zmul_add_distr_l. Qed.

Example ex_neg_cancel : (5, 0) +ᵣ (-ᵣ (5, 0)) ≈ 0ᵣ.
Proof. apply Zadd_neg. Qed.



(* ============================================================================ *)
(*                        DOCUMENTATION & SUMMARY                              *)
(* ============================================================================ *)

(**
   SUMMARY OF ACHIEVEMENTS
   
   [X] Integers as equivalence classes of natural pairs
   [X] Equivalence relation proven reflexive, symmetric, transitive
   [X] Canonical form and normalization
   [X] Isomorphism with Z (both directions, with correspondence proofs)
   [X] Arithmetic: addition, negation, subtraction, multiplication
   [X] All operations respect equivalence
   [X] All operations correspond to Z operations via to_Z
   [X] Ring properties: commutativity, associativity, identity, inverse, distributivity
   [X] Order relation: reflexive, transitive, antisymmetric, total
   [X] Order compatible with arithmetic
   [X] Natural number embedding with property preservation
   [X] Absolute value and sign
   [X] Decidability of equivalence and order
   [X] Connection to RelationalArithmetic.v
   [X] NO NEW AXIOMS - all constructions proven
   
   RELATIONAL INTERPRETATION:
   
   ┌─────────────────┬────────────────────────────────────────────────────┐
   │ Integer Concept │ Relational Interpretation                          │
   ├─────────────────┼────────────────────────────────────────────────────┤
   │ Pair (a, b)     │ Signed difference between relational strengths    │
   │ Equivalence ≈   │ Same net relational effect                        │
   │ Addition        │ Combining relational differences                  │
   │ Negation        │ Reversing relational direction                    │
   │ Multiplication  │ Scaling relational effect                         │
   │ Zero            │ Perfect relational balance                        │
   │ Positive n      │ Excess of n relational units                      │
   │ Negative n      │ Deficit of n relational units                     │
   │ Order ≤         │ "Less or equal relational strength"               │
   │ Absolute value  │ Magnitude of relational imbalance                 │
   └─────────────────┴────────────────────────────────────────────────────┘
   
   DEPENDENCIES:
   - Coq standard library (nat, Z, lia, nia)
   - No external UCF/GUTT files required (self-contained)
   - Conceptually builds on RelationalNaturals_proven.v
   - Provides foundation for RelationalArithmetic.v
   
   AXIOM COUNT: 0 (zero new axioms introduced)
   ADMIT COUNT: 0 (all proofs complete)
*)

(** * COPYRIGHT
   
   Copyright 2023-2025 Michael Fillippini. All Rights Reserved.
   UCF/GUTT Research & Evaluation License v1.1
   
   Document Version: 1.0 (Production)
   Last Updated: December 2025
   Status: PROVEN - ZERO AXIOMS - ZERO ADMITS
   Achievement: Integers from Relational Primitives
*)