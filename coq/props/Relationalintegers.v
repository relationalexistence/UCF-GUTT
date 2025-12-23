(* ============================================================================ *)
(*                     Relational Integers v2                                  *)
(*    UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial)            *)
(*    © 2023–2025 Michael Fillippini. All Rights Reserved.                     *)
(* ============================================================================ *)
(*                                                                              *)
(* KEY INSIGHT - Intra-Set vs Inter-Set Operations:                            *)
(*                                                                              *)
(*   INTRA-SET OPERATIONS (within a single relational domain):                 *)
(*     - Addition: combining elements within a set                             *)
(*     - Subtraction: finding differences within a set                         *)
(*                                                                              *)
(*   INTER-SET OPERATIONS (across different relational domains):               *)
(*     - Multiplication: relating two domains to produce a third               *)
(*     - Division: decomposing cross-domain relations                          *)
(*     - Exponentiation: iterated cross-domain scaling                         *)
(*                                                                              *)
(* Structure:                                                                   *)
(*   Part A: Pre-quotient operations on Z_rel                                  *)
(*   Part B: Proper instances (operations respect equivalence)                 *)
(*   Part C: Interpretation homomorphisms (correspondence with Coq Z)          *)
(*   Part D: Ring algebra (ring laws proven)                                   *)
(*   Part E: Isomorphism (surjectivity + faithfulness)                         *)
(*   Part F: Order                                                              *)
(*   Part G: Relational grounding                                              *)
(* ============================================================================ *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.ArithRing.

Require Import N_rel_adapter.

(* ============================================================================ *)
(*                              PART A: PRE-OPS                                 *)
(* ============================================================================ *)

Import N_rel_Adapter.
Import RelationalNaturals_proven.

(** Z_rel is pairs of relational naturals *)
Definition Z_rel : Type := N_rel * N_rel.

(** Equivalence: (a, b) ~ (c, d) iff a + d = c + b *)
Definition Z_equiv (p q : Z_rel) : Prop :=
  add_rel (fst p) (snd q) = add_rel (fst q) (snd p).

Notation "p ≈ q" := (Z_equiv p q) (at level 70).

(** Zero: perfect relational balance *)
Definition Z_zero : Z_rel := (Zero_rel, Zero_rel).

(** One: unit positive imbalance *)
Definition Z_one : Z_rel := (one_rel, Zero_rel).

(** Addition: INTRA-SET - combining within the domain *)
Definition Z_add (p q : Z_rel) : Z_rel :=
  (add_rel (fst p) (fst q), add_rel (snd p) (snd q)).

(** Negation: reversing direction *)
Definition Z_neg (p : Z_rel) : Z_rel :=
  (snd p, fst p).

(** Subtraction: difference of differences *)
Definition Z_sub (p q : Z_rel) : Z_rel :=
  Z_add p (Z_neg q).

(** Multiplication: INTER-SET - cross-domain relation *)
Definition Z_mul (p q : Z_rel) : Z_rel :=
  (add_rel (mul_rel (fst p) (fst q)) (mul_rel (snd p) (snd q)),
   add_rel (mul_rel (fst p) (snd q)) (mul_rel (snd p) (fst q))).

Notation "0ᵣ" := Z_zero.
Notation "1ᵣ" := Z_one.
Notation "p +ᵣ q" := (Z_add p q) (at level 50, left associativity).
Notation "-ᵣ p" := (Z_neg p) (at level 35, right associativity).
Notation "p -ᵣ q" := (Z_sub p q) (at level 50, left associativity).
Notation "p *ᵣ q" := (Z_mul p q) (at level 40, left associativity).

(* ============================================================================ *)
(*                            PART B: PROPER                                   *)
(* ============================================================================ *)

Theorem Z_equiv_refl : Reflexive Z_equiv.
Proof. unfold Reflexive, Z_equiv. intro x. reflexivity. Qed.

Theorem Z_equiv_sym : Symmetric Z_equiv.
Proof. unfold Symmetric, Z_equiv. intros x y H. symmetry. exact H. Qed.

Theorem Z_equiv_trans : Transitive Z_equiv.
Proof.
  unfold Transitive, Z_equiv.
  intros x y z Hxy Hyz.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  apply (f_equal to_nat) in Hxy.
  apply (f_equal to_nat) in Hyz.
  repeat rewrite add_corresponds in Hxy.
  repeat rewrite add_corresponds in Hyz.
  destruct x as [a b], y as [c d], z as [e f]. simpl in *.
  lia.
Qed.

Global Instance Z_equiv_Equivalence : Equivalence Z_equiv := {
  Equivalence_Reflexive := Z_equiv_refl;
  Equivalence_Symmetric := Z_equiv_sym;
  Equivalence_Transitive := Z_equiv_trans
}.

Theorem Z_add_respects_equiv : forall p1 p2 q1 q2 : Z_rel,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 +ᵣ q1) ≈ (p2 +ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Z_add in *. simpl in *.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  apply (f_equal to_nat) in Hp.
  apply (f_equal to_nat) in Hq.
  repeat rewrite add_corresponds in Hp.
  repeat rewrite add_corresponds in Hq.
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
  p ≈ q -> (-ᵣ p) ≈ (-ᵣ q).
Proof.
  intros p q H.
  unfold Z_equiv, Z_neg in *. simpl in *.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  apply (f_equal to_nat) in H.
  repeat rewrite add_corresponds in H.
  destruct p as [a b], q as [c d]. simpl in *. lia.
Qed.

Global Instance Z_neg_Proper :
  Proper (Z_equiv ==> Z_equiv) Z_neg.
Proof.
  unfold Proper, respectful.
  intros x y Hxy.
  apply Z_neg_respects_equiv; assumption.
Qed.

Theorem Z_mul_respects_equiv : forall p1 p2 q1 q2 : Z_rel,
  p1 ≈ p2 -> q1 ≈ q2 -> (p1 *ᵣ q1) ≈ (p2 *ᵣ q2).
Proof.
  intros p1 p2 q1 q2 Hp Hq.
  unfold Z_equiv, Z_mul in *. simpl in *.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  apply (f_equal to_nat) in Hp.
  apply (f_equal to_nat) in Hq.
  repeat rewrite add_corresponds in Hp.
  repeat rewrite add_corresponds in Hq.
  destruct p1 as [a1 b1], p2 as [a2 b2], q1 as [c1 d1], q2 as [c2 d2].
  simpl in *.
  (* Hp: to_nat a1 + to_nat b2 = to_nat a2 + to_nat b1 *)
  (* Hq: to_nat c1 + to_nat d2 = to_nat c2 + to_nat d1 *)
  (* Goal involves products - use nlinarith or careful manipulation *)
  remember (to_nat a1) as A1.
  remember (to_nat b1) as B1.
  remember (to_nat a2) as A2.
  remember (to_nat b2) as B2.
  remember (to_nat c1) as C1.
  remember (to_nat d1) as D1.
  remember (to_nat c2) as C2.
  remember (to_nat d2) as D2.
  (* Now Hp: A1 + B2 = A2 + B1, Hq: C1 + D2 = C2 + D1 *)
  (* Goal: A1*C1 + B1*D1 + (A2*D2 + B2*C2) = A2*C2 + B2*D2 + (A1*D1 + B1*C1) *)
  (* This is a polynomial identity given the linear constraints *)
  nia.
Qed.

Global Instance Z_mul_Proper :
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_mul.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply Z_mul_respects_equiv; assumption.
Qed.

(* ============================================================================ *)
(*                         PART C: INTERPRETATION                              *)
(* ============================================================================ *)

Local Open Scope Z_scope.

Definition to_Z (p : Z_rel) : Z :=
  Z.of_nat (to_nat (fst p)) - Z.of_nat (to_nat (snd p)).

Definition from_Z (z : Z) : Z_rel :=
  if Z.leb 0 z 
  then (from_nat (Z.to_nat z), Zero_rel)
  else (Zero_rel, from_nat (Z.to_nat (- z))).

Theorem to_Z_zero : to_Z Z_zero = 0.
Proof. 
  unfold to_Z, Z_zero. simpl. 
  reflexivity. 
Qed.

Theorem to_Z_one : to_Z Z_one = 1.
Proof.
  unfold to_Z, Z_one, one_rel. simpl.
  reflexivity.
Qed.

Theorem to_Z_neg : forall p : Z_rel,
  to_Z (-ᵣ p) = - to_Z p.
Proof.
  intro p. unfold to_Z, Z_neg. simpl. lia.
Qed.

Theorem to_Z_add : forall p q : Z_rel,
  to_Z (p +ᵣ q) = to_Z p + to_Z q.
Proof.
  intros [a b] [c d].
  unfold to_Z, Z_add. simpl.
  repeat rewrite add_corresponds. lia.
Qed.

Theorem to_Z_mul : forall p q : Z_rel,
  to_Z (p *ᵣ q) = to_Z p * to_Z q.
Proof.
  intros [a b] [c d].
  unfold to_Z, Z_mul. simpl.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  lia.
Qed.

Theorem to_Z_respects_equiv : forall p q : Z_rel,
  p ≈ q -> to_Z p = to_Z q.
Proof.
  intros p q H.
  unfold Z_equiv in H.
  apply (f_equal to_nat) in H.
  repeat rewrite add_corresponds in H.
  unfold to_Z.
  destruct p as [a b], q as [c d]. simpl in *.
  lia.
Qed.

(* ============================================================================ *)
(*                           PART D: ALGEBRA                                   *)
(* ============================================================================ *)

Local Close Scope Z_scope.

Theorem Z_add_comm : forall p q : Z_rel,
  (p +ᵣ q) ≈ (q +ᵣ p).
Proof.
  intros [a b] [c d].
  unfold Z_equiv, Z_add. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds. lia.
Qed.

Theorem Z_add_assoc : forall p q r : Z_rel,
  ((p +ᵣ q) +ᵣ r) ≈ (p +ᵣ (q +ᵣ r)).
Proof.
  intros [a b] [c d] [e f].
  unfold Z_equiv, Z_add. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds. lia.
Qed.

Theorem Z_add_zero_l : forall p : Z_rel,
  (Z_zero +ᵣ p) ≈ p.
Proof.
  intros [a b].
  unfold Z_equiv, Z_add, Z_zero. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  simpl. lia.
Qed.

Theorem Z_add_neg_l : forall p : Z_rel,
  ((-ᵣ p) +ᵣ p) ≈ Z_zero.
Proof.
  intros [a b].
  unfold Z_equiv, Z_add, Z_neg, Z_zero. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  simpl. lia.
Qed.

Theorem Z_mul_comm : forall p q : Z_rel,
  (p *ᵣ q) ≈ (q *ᵣ p).
Proof.
  intros [a b] [c d].
  unfold Z_equiv, Z_mul. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds. lia.
Qed.

Theorem Z_mul_assoc : forall p q r : Z_rel,
  ((p *ᵣ q) *ᵣ r) ≈ (p *ᵣ (q *ᵣ r)).
Proof.
  intros [a b] [c d] [e f].
  unfold Z_equiv, Z_mul. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  set (A := to_nat a). set (B := to_nat b).
  set (C := to_nat c). set (D := to_nat d).
  set (E := to_nat e). set (F := to_nat f).
  ring.
Qed.

Theorem Z_mul_one_l : forall p : Z_rel,
  (Z_one *ᵣ p) ≈ p.
Proof.
  intros [a b].
  unfold Z_equiv, Z_mul, Z_one, one_rel. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  simpl. lia.
Qed.

Theorem Z_mul_zero_l : forall p : Z_rel,
  (Z_zero *ᵣ p) ≈ Z_zero.
Proof.
  intros [a b].
  unfold Z_equiv, Z_mul, Z_zero. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  simpl. lia.
Qed.

Theorem Z_mul_add_distr_l : forall p q r : Z_rel,
  (p *ᵣ (q +ᵣ r)) ≈ ((p *ᵣ q) +ᵣ (p *ᵣ r)).
Proof.
  intros [a b] [c d] [e f].
  unfold Z_equiv, Z_mul, Z_add. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  set (A := to_nat a). set (B := to_nat b).
  set (C := to_nat c). set (D := to_nat d).
  set (E := to_nat e). set (F := to_nat f).
  ring.
Qed.

(* ============================================================================ *)
(*                         PART E: ISOMORPHISM                                 *)
(* ============================================================================ *)

Local Open Scope Z_scope.

Theorem from_Z_to_Z : forall z : Z,
  to_Z (from_Z z) = z.
Proof.
  intro z.
  unfold to_Z, from_Z.
  destruct (Z.leb 0 z) eqn:Hle.
  - apply Z.leb_le in Hle. simpl.
    rewrite iso_roundtrip_2.
    rewrite Z2Nat.id; lia.
  - apply Z.leb_gt in Hle. simpl.
    rewrite iso_roundtrip_2.
    rewrite Z2Nat.id; lia.
Qed.

Theorem to_Z_surjective : forall z : Z,
  exists p : Z_rel, to_Z p = z.
Proof.
  intro z. exists (from_Z z). apply from_Z_to_Z.
Qed.

Theorem to_Z_faithful : forall p q : Z_rel,
  to_Z p = to_Z q -> p ≈ q.
Proof.
  intros [a b] [c d] H.
  unfold to_Z in H. simpl in H.
  unfold Z_equiv. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  (* H is in Z: Z.of_nat (to_nat a) - Z.of_nat (to_nat b) = 
                Z.of_nat (to_nat c) - Z.of_nat (to_nat d) *)
  (* Goal: to_nat a + to_nat d = to_nat c + to_nat b *)
  lia.
Qed.

Theorem Z_rel_isomorphic_to_Z :
  (forall z : Z, exists r : Z_rel, to_Z r = z) /\
  (forall r s : Z_rel, to_Z r = to_Z s <-> r ≈ s) /\
  (forall r s : Z_rel, to_Z (r +ᵣ s) = to_Z r + to_Z s) /\
  (forall r s : Z_rel, to_Z (r *ᵣ s) = to_Z r * to_Z s) /\
  (forall r : Z_rel, to_Z (-ᵣ r) = - to_Z r).
Proof.
  split. { exact to_Z_surjective. }
  split. { intros r s. split. apply to_Z_faithful. apply to_Z_respects_equiv. }
  split. { exact to_Z_add. }
  split. { exact to_Z_mul. }
  { exact to_Z_neg. }
Qed.

(* ============================================================================ *)
(*                           PART F: ORDER                                     *)
(* ============================================================================ *)

Definition Z_le (p q : Z_rel) : Prop := to_Z p <= to_Z q.
Definition Z_lt (p q : Z_rel) : Prop := to_Z p < to_Z q.

Notation "p ≤ᵣ q" := (Z_le p q) (at level 70).
Notation "p <ᵣ q" := (Z_lt p q) (at level 70).

Theorem Z_le_refl : forall p : Z_rel, p ≤ᵣ p.
Proof. intro p. unfold Z_le. lia. Qed.

Theorem Z_le_trans : forall p q r : Z_rel,
  p ≤ᵣ q -> q ≤ᵣ r -> p ≤ᵣ r.
Proof. intros p q r. unfold Z_le. lia. Qed.

Theorem Z_le_antisym : forall p q : Z_rel,
  p ≤ᵣ q -> q ≤ᵣ p -> p ≈ q.
Proof.
  intros p q Hpq Hqp.
  apply to_Z_faithful.
  unfold Z_le in *. lia.
Qed.

Theorem Z_le_total : forall p q : Z_rel,
  p ≤ᵣ q \/ q ≤ᵣ p.
Proof. intros p q. unfold Z_le. lia. Qed.

Theorem Z_le_dec : forall p q : Z_rel, {p ≤ᵣ q} + {~ p ≤ᵣ q}.
Proof.
  intros p q. unfold Z_le.
  destruct (Z_le_gt_dec (to_Z p) (to_Z q)) as [H|H].
  - left. exact H.
  - right. lia.
Defined.

(* ============================================================================ *)
(*                        PART G: RELATIONAL GROUNDING                         *)
(* ============================================================================ *)

Local Close Scope Z_scope.

(** Embed N_rel into Z_rel *)
Definition embed_N (n : N_rel) : Z_rel := (n, Zero_rel).

Theorem embed_N_add : forall m n : N_rel,
  embed_N (add_rel m n) ≈ (embed_N m +ᵣ embed_N n).
Proof.
  intros m n.
  unfold embed_N, Z_equiv, Z_add. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  simpl. lia.
Qed.

Theorem embed_N_mul : forall m n : N_rel,
  embed_N (mul_rel m n) ≈ (embed_N m *ᵣ embed_N n).
Proof.
  intros m n.
  unfold embed_N, Z_equiv, Z_mul. simpl.
  apply to_nat_inj.
  repeat rewrite add_corresponds.
  repeat rewrite mul_corresponds.
  simpl. lia.
Qed.

Theorem integers_grounding_complete :
  (exists U : Type, exists R : U -> U -> Prop, 
     (forall x, exists y, R x y)) /\
  (forall n : N_rel, from_nat (to_nat n) = n) /\
  (forall n : nat, to_nat (from_nat n) = n) /\
  Equivalence Z_equiv /\
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_add /\
  Proper (Z_equiv ==> Z_equiv) Z_neg /\
  Proper (Z_equiv ==> Z_equiv ==> Z_equiv) Z_mul.
Proof.
  split. { 
    (* Seriality from Prop 1 *)
    exists N_rel. exists (fun x y => exists z, add_rel x z = y).
    intro n. 
    (* We need: exists y, (exists z, n +r z = y) *)
    (* Take y = n, z = Zero_rel: n +r Zero_rel = n *)
    exists n. exists Zero_rel. apply add_rel_zero_r.
  }
  split. { exact iso_roundtrip_1. }
  split. { exact iso_roundtrip_2. }
  split. { exact Z_equiv_Equivalence. }
  split. { exact Z_add_Proper. }
  split. { exact Z_neg_Proper. }
  { exact Z_mul_Proper. }
Qed.

(* ============================================================================ *)
(*                       DOCUMENTATION & SUMMARY                               *)
(* ============================================================================ *)

(**
   RELATIONALINTEGERS_V2.V - COMPLETE SUMMARY
   ==========================================
   
   KEY RELATIONAL INSIGHT:
   
   ┌─────────────────────────────────────────────────────────────────────────┐
   │ INTRA-SET OPERATIONS (Addition, Subtraction)                           │
   │   - Operate WITHIN a single relational domain                          │
   │   - Combine elements that share the same domain membership             │
   │   - (a,b) + (c,d) = (a+c, b+d): components stay in their domains      │
   │                                                                         │
   │ INTER-SET OPERATIONS (Multiplication, Division, Exponentiation)        │
   │   - Relate elements ACROSS different relational domains                │
   │   - Create new relations between previously unrelated domains          │
   │   - (a,b) * (c,d) = cross-products: mixing positive/negative domains  │
   │                                                                         │
   │ DISTRIBUTIVITY bridges intra-set and inter-set:                        │
   │   p * (q + r) ≈ (p * q) + (p * r)                                      │
   │   "Scaling a sum equals the sum of scalings"                           │
   └─────────────────────────────────────────────────────────────────────────┘
   
   PROVEN RESULTS:
   
   [Part A] PreOps - Operations on representatives
     - Z_rel := N_rel × N_rel ✓
     - Z_equiv: equivalence relation ✓
     - Intra-set: Z_add, Z_neg, Z_sub ✓
     - Inter-set: Z_mul ✓
   
   [Part B] Proper_Instances - Well-definedness
     - Z_equiv is Equivalence ✓
     - Z_add_Proper ✓
     - Z_neg_Proper ✓
     - Z_mul_Proper ✓
   
   [Part C] Interpretation - Homomorphism to Z
     - to_Z_zero ✓
     - to_Z_one ✓
     - to_Z_add ✓
     - to_Z_mul ✓
     - to_Z_neg ✓
     - to_Z_respects_equiv ✓
   
   [Part D] Algebra - Ring laws
     - Additive group: assoc, comm, identity, inverse ✓
     - Multiplicative monoid: assoc, comm, identity ✓
     - Distributivity ✓
   
   [Part E] Isomorphism - Full equivalence with Z
     - Surjectivity: to_Z_surjective ✓
     - Faithfulness: to_Z_faithful ✓
     - Z_rel_isomorphic_to_Z ✓
   
   [Part F] Order
     - Z_le, Z_lt definitions ✓
     - Reflexive, transitive, antisymmetric, total ✓
     - Decidability ✓
   
   [Part G] RelationalGrounding
     - Complete grounding chain from Proposition 1 ✓
     - Natural embedding N_rel → Z_rel ✓
   
   DEPENDENCIES:
     - N_rel_adapter.v
     - RelationalNaturals_proven.v
     - Proposition_01_proven.v (via adapter)
   
   AXIOM COUNT: 0 (zero new axioms - fully proven)
   ADMIT COUNT: 0 (all proofs complete)
   
   Copyright 2023-2025 Michael Fillippini. All Rights Reserved.
   UCF/GUTT Research & Evaluation License v1.1
*)
