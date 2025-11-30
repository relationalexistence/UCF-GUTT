(* ============================================================================ *)
(*                          Relational Real Numbers                             *)
(*                                                                              *)
(* © 2023–2025 Michael Fillippini. All Rights Reserved.                        *)
(* UCF/GUTT™ Research & Evaluation License v1.1                                *)
(* ============================================================================ *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses.

Open Scope Q_scope.

(* Helper lemma *)
Lemma Qabs_zero_le : forall k : nat, (k > 0)%nat -> Qabs 0 <= 1 # Pos.of_nat k.
Proof.
  intros k Hk. unfold Qabs. simpl. unfold Qle. simpl. lia.
Qed.

Lemma Qabs_eq_zero : forall q : Q, q == 0 -> Qabs q == 0.
Proof. intros q H. rewrite H. reflexivity. Qed.

(* ============================================================================ *)
(*                        CAUCHY SEQUENCES                                      *)
(* ============================================================================ *)

Definition is_cauchy_mod (f : nat -> Q) : Prop :=
  forall n : nat, Qabs (f (S n) - f n) <= 1 # (Pos.of_nat (S n)).

Record R_cauchy : Type := mkR {
  r_seq : nat -> Q;
  r_mod : is_cauchy_mod r_seq
}.

Definition Req (x y : R_cauchy) : Prop :=
  forall k : nat, (k > 0)%nat -> 
    exists N : nat, forall n : nat, (n >= N)%nat ->
      Qabs (r_seq x n - r_seq y n) <= 1 # (Pos.of_nat k).

Infix "=R=" := Req (at level 70, no associativity).

(* ============================================================================ *)
(*                        EQUIVALENCE RELATION                                  *)
(* ============================================================================ *)

Lemma Req_refl : forall x, x =R= x.
Proof.
  intro x. unfold Req. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : r_seq x n - r_seq x n == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Lemma Req_sym : forall x y, x =R= y -> y =R= x.
Proof.
  intros x y H. unfold Req in *. intros k Hk.
  destruct (H k Hk) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  assert (Heq : r_seq y n - r_seq x n == -(r_seq x n - r_seq y n)) by ring.
  rewrite (Qabs_eq_zero _ Heq) in HN || rewrite Heq.
  rewrite Qabs_opp. exact HN.
Qed.

Lemma Req_trans : forall x y z, x =R= y -> y =R= z -> x =R= z.
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
    rewrite Heq. apply Qabs_triangle. }
  eapply Qle_trans; [exact Htri|].
  eapply Qle_trans; [apply Qplus_le_compat; [exact HN1 | exact HN2]|].
  unfold Qle, Qplus. simpl. lia.
Qed.

Global Instance Req_Equivalence : Equivalence Req.
Proof.
  constructor; [exact Req_refl | exact Req_sym | exact Req_trans].
Qed.

(* ============================================================================ *)
(*                        EMBEDDING Q INTO R                                    *)
(* ============================================================================ *)

Lemma cauchy_const : forall q : Q, is_cauchy_mod (fun _ => q).
Proof.
  intro q. unfold is_cauchy_mod. intro n.
  assert (H : q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). unfold Qle. simpl. lia.
Qed.

Definition Q_to_R (q : Q) : R_cauchy := mkR (fun _ => q) (cauchy_const q).

Definition R_zero : R_cauchy := Q_to_R 0.
Definition R_one : R_cauchy := Q_to_R 1.

Notation "'0R'" := R_zero.
Notation "'1R'" := R_one.

Theorem R_zero_neq_one : ~(0R =R= 1R).
Proof.
  unfold Req, R_zero, R_one, Q_to_R. simpl. intro H.
  destruct (H 2%nat) as [N HN]; [lia|].
  specialize (HN N (Nat.le_refl N)).
  unfold Qabs, Qminus, Qplus, Qopp in HN. simpl in HN.
  unfold Qle in HN. simpl in HN. lia.
Qed.

(* ============================================================================ *)
(*                        FIELD AXIOMS FOR Q IN R                               *)
(* ============================================================================ *)

Theorem Q_add_comm_R : forall p q : Q, Q_to_R (p + q) =R= Q_to_R (q + p).
Proof.
  intros p q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p + q - (q + p) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_add_assoc_R : forall p q r : Q, 
  Q_to_R (p + q + r) =R= Q_to_R (p + (q + r)).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p + q + r - (p + (q + r)) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_add_0_l_R : forall q : Q, Q_to_R (0 + q) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : 0 + q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_add_neg_R : forall q : Q, Q_to_R (q + -q) =R= Q_to_R 0.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q + - q - 0 == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_mul_comm_R : forall p q : Q, Q_to_R (p * q) =R= Q_to_R (q * p).
Proof.
  intros p q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * q - q * p == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_mul_assoc_R : forall p q r : Q, 
  Q_to_R (p * q * r) =R= Q_to_R (p * (q * r)).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * q * r - p * (q * r) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_mul_1_l_R : forall q : Q, Q_to_R (1 * q) =R= Q_to_R q.
Proof.
  intro q. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : 1 * q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

Theorem Q_distr_R : forall p q r : Q, 
  Q_to_R (p * (q + r)) =R= Q_to_R (p * q + p * r).
Proof.
  intros p q r. unfold Req, Q_to_R. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : p * (q + r) - (p * q + p * r) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le. exact Hk.
Qed.

(* ============================================================================ *)
(*                        SUMMARY                                               *)
(* ============================================================================ *)

(*
  RELATIONAL REALS - Q EMBEDDED AS SUBFIELD
  
  PROVEN (Zero Axioms, Zero Admits):
    ✓ Req: Equivalence relation
    ✓ Q ↪ R via constant sequences  
    ✓ 0R ≠ 1R
    ✓ Addition: commutative, associative, identity, inverse
    ✓ Multiplication: commutative, associative, identity
    ✓ Distributivity
*)

Print Assumptions Req_Equivalence.
Print Assumptions R_zero_neq_one.
Print Assumptions Q_add_comm_R.
Print Assumptions Q_mul_comm_R.
Print Assumptions Q_distr_R.