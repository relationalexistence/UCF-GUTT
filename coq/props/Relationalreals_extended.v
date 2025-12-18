(* ============================================================================ *)
(*                    Relational Real Numbers - COMPLETE                        *)
(*                       (Constructive & Axiom-Free)                           *)
(*                                                                              *)
(* © 2023–2025 Michael Fillippini. All Rights Reserved.                        *)
(* UCF/GUTT™ Research & Evaluation License v1.1                                *)
(*                                                                              *)
(* This version uses GEOMETRIC modulus (1/2^n) with COMPLETE proofs            *)
(* ZERO AXIOMS, ZERO ADMITS - All ring laws machine-verified                   *)
(*                                                                              *)
(* PROVEN RING STRUCTURE:                                                       *)
(*   ✓ Addition: associative, commutative, identity (0), inverses             *)
(*   ✓ Multiplication: associative, commutative, identity (1)                 *)
(*   ✓ Distributivity: x*(y+z) = x*y + x*z (both left and right)             *)
(*   ✓ 69 lemmas proven with Qed, no admits, no axioms                        *)
(*                                                                              *)
(* KEY TECHNIQUES:                                                              *)
(*   • Shift equivalence: RReq_shift proves f(n+k) ≡ f(n)                      *)
(*   • Product bounds: |abc - def| ≤ δ(BᵧBᵤ + BₓBᵤ + BₓBᵧ)                   *)
(*   • Geometric budget: (2/2^n)*C ≤ 1/2^k when n ≥ S k + bound_shift(2C)    *)
(* ============================================================================ *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.PArith.PArith.
Require Import Coq.ZArith.ZArith.

Open Scope Q_scope.

(* ============================================================================ *)
(*                        PART 1: POWER OF 2                                    *)
(* ============================================================================ *)

(* 2^n as a positive *)
Fixpoint pow2 (n : nat) : positive :=
  match n with
  | O => 1
  | S n' => 2 * pow2 n'
  end.

Lemma pow2_S : forall n, pow2 (S n) = (2 * pow2 n)%positive.
Proof. reflexivity. Qed.

(* 1/2^{n+1} + 1/2^{n+1} = 1/2^n *)
Lemma pow2_sum : forall n : nat,
  (1 # pow2 (S n)) + (1 # pow2 (S n)) == 1 # pow2 n.
Proof.
  intro n.
  unfold Qeq, Qplus. simpl.
  induction n.
  - simpl. reflexivity.
  - simpl. lia.
Qed.

(* 1/2^{n+1} <= 1/2^n *)
Lemma pow2_le : forall n : nat,
  1 # pow2 (S n) <= 1 # pow2 n.
Proof.
  intro n. unfold Qle. simpl.
  induction n.
  - simpl. lia.
  - simpl. lia.
Qed.

(* pow2 n >= 1 always *)
Lemma pow2_ge_1 : forall n : nat, (1 <= pow2 n)%positive.
Proof.
  induction n.
  - simpl. lia.
  - simpl. lia.
Qed.

(* 2^n >= n for all n (crucial for bounds) *)
Lemma pow2_ge_n : forall n : nat, (n <= Pos.to_nat (pow2 n))%nat.
Proof.
  induction n.
  - simpl. lia.
  - change (pow2 (S n)) with (2 * pow2 n)%positive.
    rewrite Pos2Nat.inj_mul.
    assert (H1 : (1 <= Pos.to_nat (pow2 n))%nat).
    { pose proof (Pos2Nat.is_pos (pow2 n)). lia. }
    lia.
Qed.

(* Power of 2 addition for indices *)
Lemma pow2_add : forall m n : nat,
  pow2 (m + n) = (pow2 m * pow2 n)%positive.
Proof.
  induction m.
  - intro n. simpl. lia.
  - intro n. simpl. rewrite IHm. lia.
Qed.

(* 1/2^{m+n} = 1/2^m * 1/2^n *)
Lemma pow2_frac_add : forall m n : nat,
  (1 # pow2 (m + n)) == (1 # pow2 m) * (1 # pow2 n).
Proof.
  intros m n. unfold Qeq, Qmult. simpl.
  rewrite pow2_add. lia.
Qed.

(* Key: 1/2^{n+s} <= 1/2^n for any s *)
Lemma pow2_shift_le : forall n s : nat,
  1 # pow2 (n + s) <= 1 # pow2 n.
Proof.
  intros n s. induction s.
  - replace (n + 0)%nat with n by lia. apply Qle_refl.
  - eapply Qle_trans; [|exact IHs].
    replace (n + S s)%nat with (S (n + s))%nat by lia.
    apply pow2_le.
Qed.

(* 2/2^{n+1} = 1/2^n *)
Lemma pow2_double : forall n : nat,
  2 # pow2 (S n) == 1 # pow2 n.
Proof.
  intro n. unfold Qeq. simpl. lia.
Qed.

(* ============================================================================ *)
(*                        PART 2: HELPER LEMMAS                                 *)
(* ============================================================================ *)

Lemma Qabs_zero_le : forall n : nat, Qabs 0 <= 1 # pow2 n.
Proof. intro n. unfold Qabs. simpl. unfold Qle. simpl. lia. Qed.

Lemma Qabs_eq_zero : forall q : Q, q == 0 -> Qabs q == 0.
Proof. intros q H. rewrite H. reflexivity. Qed.

(* Qabs respects Qeq *)
Lemma Qabs_compat : forall p q : Q, p == q -> Qabs p == Qabs q.
Proof.
  intros p q H. rewrite H. reflexivity.
Qed.

(* Absolute value and inequality *)
Lemma Qabs_le_mult : forall a b c : Q,
  0 <= a -> 0 <= c ->
  Qabs b <= c ->
  Qabs (a * b) <= a * c.
Proof.
  intros a b c Ha Hc Hbc.
  rewrite Qabs_Qmult.
  rewrite (Qabs_pos a Ha).
  apply Qmult_le_compat_nonneg.
  - split; [exact Ha | apply Qle_refl].
  - split; [apply Qabs_nonneg | exact Hbc].
Qed.

(* ============================================================================ *)
(*                        PART 3: CAUCHY SEQUENCES (GEOMETRIC MODULUS)          *)
(* ============================================================================ *)

Definition is_cauchy_geo (f : nat -> Q) : Prop :=
  forall n : nat, Qabs (f (S n) - f n) <= 1 # pow2 n.

Record RR : Type := mkRR {
  rr_seq : nat -> Q;
  rr_mod : is_cauchy_geo rr_seq
}.

Definition RReq (x y : RR) : Prop :=
  forall k : nat, 
    exists N : nat, forall n : nat, (n >= N)%nat ->
      Qabs (rr_seq x n - rr_seq y n) <= 1 # pow2 k.

Infix "=RR=" := RReq (at level 70, no associativity).

(* ============================================================================ *)
(*                        PART 4: EQUIVALENCE RELATION                          *)
(* ============================================================================ *)

Lemma RReq_refl : forall x, x =RR= x.
Proof.
  intro x. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  assert (H : rr_seq x n - rr_seq x n == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le.
Qed.

Lemma RReq_sym : forall x y, x =RR= y -> y =RR= x.
Proof.
  intros x y H. unfold RReq in *. intro k.
  destruct (H k) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  assert (Heq : rr_seq y n - rr_seq x n == -(rr_seq x n - rr_seq y n)) by ring.
  rewrite Heq. rewrite Qabs_opp. exact HN.
Qed.

Lemma RReq_trans : forall x y z, x =RR= y -> y =RR= z -> x =RR= z.
Proof.
  intros x y z Hxy Hyz. unfold RReq in *. intro k.
  destruct (Hxy (S k)) as [N1 HN1].
  destruct (Hyz (S k)) as [N2 HN2].
  exists (max N1 N2). intros n Hn.
  assert (Hn1 : (n >= N1)%nat) by lia.
  assert (Hn2 : (n >= N2)%nat) by lia.
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  assert (Htri : Qabs (rr_seq x n - rr_seq z n) <= 
                 Qabs (rr_seq x n - rr_seq y n) + Qabs (rr_seq y n - rr_seq z n)).
  { assert (Heq : rr_seq x n - rr_seq z n == 
                  (rr_seq x n - rr_seq y n) + (rr_seq y n - rr_seq z n)) by ring.
    rewrite Heq. apply Qabs_triangle. }
  eapply Qle_trans; [exact Htri|].
  eapply Qle_trans; [apply Qplus_le_compat; [exact HN1 | exact HN2]|].
  rewrite pow2_sum. apply Qle_refl.
Qed.

Global Instance RReq_Equivalence : Equivalence RReq.
Proof.
  constructor; [exact RReq_refl | exact RReq_sym | exact RReq_trans].
Qed.

(* ============================================================================ *)
(*                        PART 5: EMBEDDING Q INTO RR                           *)
(* ============================================================================ *)

Lemma cauchy_const : forall q : Q, is_cauchy_geo (fun _ => q).
Proof.
  intro q. unfold is_cauchy_geo. intro n.
  assert (H : q - q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le.
Qed.

Definition Q_to_RR (q : Q) : RR := mkRR (fun _ => q) (cauchy_const q).

Definition RR_zero : RR := Q_to_RR 0.
Definition RR_one : RR := Q_to_RR 1.

Notation "'0RR'" := RR_zero.
Notation "'1RR'" := RR_one.

Theorem RR_zero_neq_one : ~(0RR =RR= 1RR).
Proof.
  unfold RReq, RR_zero, RR_one, Q_to_RR. simpl. intro H.
  destruct (H 1%nat) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold Qabs, Qminus, Qplus, Qopp in HN. simpl in HN.
  unfold Qle in HN. simpl in HN. lia.
Qed.

(* ============================================================================ *)
(*                        PART 6: NEGATION                                      *)
(* ============================================================================ *)

Lemma cauchy_neg : forall x : RR, is_cauchy_geo (fun n => - rr_seq x n).
Proof.
  intro x. unfold is_cauchy_geo. intro n.
  assert (Hx := rr_mod x n).
  assert (Heq : - rr_seq x (S n) - - rr_seq x n == -(rr_seq x (S n) - rr_seq x n)) by ring.
  rewrite Heq. rewrite Qabs_opp. exact Hx.
Qed.

Definition RR_neg (x : RR) : RR :=
  mkRR (fun n => - rr_seq x n) (cauchy_neg x).

Notation "-RR x" := (RR_neg x) (at level 35, right associativity).

(* ============================================================================ *)
(*                        PART 7: ADDITION                                      *)
(* ============================================================================ *)

Definition seq_plus (x y : RR) (n : nat) : Q := 
  rr_seq x (S n) + rr_seq y (S n).

Lemma cauchy_add : forall x y : RR, is_cauchy_geo (seq_plus x y).
Proof.
  intros x y. unfold is_cauchy_geo, seq_plus. intro n.
  assert (Hx := rr_mod x (S n)).
  assert (Hy := rr_mod y (S n)).
  assert (Hdiff : rr_seq x (S (S n)) + rr_seq y (S (S n)) -
                  (rr_seq x (S n) + rr_seq y (S n)) ==
                  (rr_seq x (S (S n)) - rr_seq x (S n)) +
                  (rr_seq y (S (S n)) - rr_seq y (S n))) by ring.
  rewrite Hdiff.
  eapply Qle_trans; [apply Qabs_triangle|].
  eapply Qle_trans; [apply Qplus_le_compat; [exact Hx | exact Hy]|].
  rewrite pow2_sum. apply Qle_refl.
Qed.

Definition RR_add (x y : RR) : RR :=
  mkRR (seq_plus x y) (cauchy_add x y).

Infix "+RR" := RR_add (at level 50, left associativity).

Definition RR_sub (x y : RR) : RR := RR_add x (RR_neg y).

Infix "-RR" := RR_sub (at level 50, left associativity).

(* ============================================================================ *)
(*                        PART 8: ORDER RELATIONS                               *)
(* ============================================================================ *)

Definition RR_lt (x y : RR) : Prop :=
  exists (k : nat) (N : nat), 
    forall n : nat, (n >= N)%nat -> 
      rr_seq y n - rr_seq x n >= 1 # pow2 k.

Infix "<RR" := RR_lt (at level 70, no associativity).

Definition RR_le (x y : RR) : Prop := ~(y <RR x).

Infix "<=RR" := RR_le (at level 70, no associativity).

(* 0 <= 1 *)
Lemma RR_zero_le_one : RR_le RR_zero RR_one.
Proof.
  unfold RR_le, RR_lt, RR_zero, RR_one, Q_to_RR. simpl.
  intros [k [N Hsep]].
  specialize (Hsep N (Nat.le_refl N)).
  unfold Qle in Hsep. unfold Qminus in Hsep. simpl in Hsep. lia.
Qed.

(* 0 < 1 *)
Lemma RR_zero_lt_one : RR_lt RR_zero RR_one.
Proof.
  unfold RR_lt, RR_zero, RR_one, Q_to_RR. simpl.
  exists 1%nat. exists 0%nat.
  intros n Hn.
  unfold Qminus. simpl.
  unfold Qle. simpl. lia.
Qed.

(* ============================================================================ *)
(*                        PART 9: Q-EMBEDDED OPERATIONS                         *)
(* ============================================================================ *)

Lemma Q_to_RR_add : forall p q : Q, 
  Q_to_RR p +RR Q_to_RR q =RR= Q_to_RR (p + q).
Proof.
  intros p q. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_add, seq_plus, Q_to_RR. simpl.
  assert (H : p + q - (p + q) == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le.
Qed.

Lemma Q_to_RR_neg : forall q : Q,
  -RR (Q_to_RR q) =RR= Q_to_RR (-q).
Proof.
  intro q. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_neg, Q_to_RR. simpl.
  assert (H : -q - -q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le.
Qed.

Lemma Q_to_RR_le : forall p q : Q,
  p <= q -> Q_to_RR p <=RR Q_to_RR q.
Proof.
  intros p q Hle.
  unfold RR_le. intro Hlt.
  unfold RR_lt in Hlt.
  destruct Hlt as [k [N Hsep]].
  specialize (Hsep N (Nat.le_refl N)).
  unfold Q_to_RR in Hsep. simpl in Hsep.
  assert (Hneg : p - q <= 0).
  { unfold Qle, Qminus in *. simpl in *. lia. }
  assert (Hcontra : 1 # pow2 k <= 0).
  { eapply Qle_trans; [exact Hsep | exact Hneg]. }
  unfold Qle in Hcontra. simpl in Hcontra. lia.
Qed.

(* ============================================================================ *)
(*                        PART 10: DECIDABILITY FOR Q-VALUES                    *)
(* ============================================================================ *)

Lemma pos_rational_bound : forall num den : positive,
  (1 # pow2 (Pos.to_nat den)) <= (Zpos num # den).
Proof.
  intros num den.
  unfold Qle. simpl.
  assert (Hpow : (Pos.to_nat den <= Pos.to_nat (pow2 (Pos.to_nat den)))%nat).
  { apply pow2_ge_n. }
  apply Nat2Z.inj_le in Hpow.
  rewrite positive_nat_Z in Hpow.
  rewrite positive_nat_Z in Hpow.
  assert (Hnum : (1 <= Z.pos num)%Z) by lia.
  assert (Hmul : (Z.pos (pow2 (Pos.to_nat den)) <= Z.pos num * Z.pos (pow2 (Pos.to_nat den)))%Z).
  { assert (H1 : (1 * Z.pos (pow2 (Pos.to_nat den)) <= Z.pos num * Z.pos (pow2 (Pos.to_nat den)))%Z).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia. }
  lia.
Qed.

Definition RR_le_dec_Q (p q : Q) : 
  {Q_to_RR p <=RR Q_to_RR q} + {Q_to_RR q <RR Q_to_RR p}.
Proof.
  destruct (Qlt_le_dec q p) as [Hlt | Hle].
  - right.
    unfold RR_lt, Q_to_RR. simpl.
    exists (Pos.to_nat (Qden (p - q))).
    exists 0%nat.
    intros n Hn.
    unfold Qle, Qlt, Qminus, Qplus, Qopp in *. simpl in *.
    set (num := (Qnum p * Z.pos (Qden q) - Qnum q * Z.pos (Qden p))%Z).
    set (den := (Qden p * Qden q)%positive).
    assert (Hnum_pos : (0 < num)%Z) by (unfold num; lia).
    assert (Hnum_ge1 : (1 <= num)%Z) by lia.
    assert (Hpow : (Pos.to_nat den <= Pos.to_nat (pow2 (Pos.to_nat den)))%nat).
    { apply pow2_ge_n. }
    apply Nat2Z.inj_le in Hpow.
    rewrite positive_nat_Z in Hpow.
    rewrite positive_nat_Z in Hpow.
    assert (H1 : (Z.pos (pow2 (Pos.to_nat den)) <= num * Z.pos (pow2 (Pos.to_nat den)))%Z).
    { assert (Hge1 : (1 * Z.pos (pow2 (Pos.to_nat den)) <= num * Z.pos (pow2 (Pos.to_nat den)))%Z).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia. }
    lia.
  - left. apply Q_to_RR_le. exact Hle.
Defined.

(* ============================================================================ *)
(*                        PART 11: GEOMETRIC SERIES BOUND                       *)
(* ============================================================================ *)

(*
  Key telescoping identity for geometric series:
  
  |f(n) - f(0)| ≤ Σ_{k=0}^{n-1} |f(k+1) - f(k)| 
               ≤ Σ_{k=0}^{n-1} 1/2^k 
               = 2 - 1/2^{n-1}  (for n ≥ 1)
               < 2
*)

(* Telescoping bound: |f(n) - f(0)| ≤ 2 - 1/2^{n-1} for n > 0 *)
Lemma cauchy_telescope : forall (f : nat -> Q) (n : nat),
  is_cauchy_geo f ->
  (n > 0)%nat ->
  Qabs (f n - f 0%nat) <= 2 - (1 # pow2 (n - 1)).
Proof.
  intros f n Hcauchy Hn.
  induction n as [|m IH].
  - (* n = 0: contradiction *) lia.
  - destruct m as [|m'].
    + (* n = 1: |f(1) - f(0)| ≤ 1/2^0 = 1 ≤ 2 - 1 = 1 *)
      simpl.
      eapply Qle_trans; [apply (Hcauchy 0%nat)|].
      unfold Qle, Qminus. simpl. lia.
    + (* n = S (S m'): inductive case *)
      assert (Htri : Qabs (f (S (S m')) - f 0%nat) <=
                     Qabs (f (S (S m')) - f (S m')) + Qabs (f (S m') - f 0%nat)).
      { assert (Heq : f (S (S m')) - f 0%nat == 
                      (f (S (S m')) - f (S m')) + (f (S m') - f 0%nat)).
        { ring. }
        rewrite Heq. apply Qabs_triangle. }
      eapply Qle_trans; [exact Htri|].
      
      assert (Hstep : Qabs (f (S (S m')) - f (S m')) <= 1 # pow2 (S m')).
      { apply (Hcauchy (S m')). }
      
      assert (HIH : Qabs (f (S m') - f 0%nat) <= 2 - (1 # pow2 m')).
      { assert (H' : Qabs (f (S m') - f 0%nat) <= 2 - (1 # pow2 (S m' - 1))).
        { apply IH. lia. }
        replace (S m' - 1)%nat with m' in H' by lia. exact H'. }
      
      eapply Qle_trans; [apply Qplus_le_compat; [exact Hstep | exact HIH]|].
      
      (* Goal: 1/2^{S m'} + (2 - 1/2^{m'}) ≤ 2 - 1/2^{S m'} *)
      simpl (S (S m') - 1)%nat.
      change (pow2 (S m')) with (2 * pow2 m')%positive.
      unfold Qle, Qplus, Qminus, Qopp. simpl.
      lia.
Qed.

(* Corollary: |f(n) - f(0)| < 2 for all n *)
Lemma cauchy_diff_lt_2 : forall (f : nat -> Q) (n : nat),
  is_cauchy_geo f ->
  Qabs (f n - f 0%nat) < 2.
Proof.
  intros f n Hcauchy.
  destruct n as [|m].
  - (* n = 0: |f(0) - f(0)| = 0 < 2 *)
    assert (Heq : f 0%nat - f 0%nat == 0) by ring.
    rewrite (Qabs_compat _ _ Heq).
    rewrite Qabs_pos; [|unfold Qle; simpl; lia].
    unfold Qlt. simpl. lia.
  - (* n = S m: use telescope lemma *)
    assert (Hbound' : Qabs (f (S m) - f 0%nat) <= 2 - (1 # pow2 (S m - 1))).
    { apply cauchy_telescope; [exact Hcauchy | lia]. }
    assert (Hbound : Qabs (f (S m) - f 0%nat) <= 2 - (1 # pow2 m)).
    { replace (S m - 1)%nat with m in Hbound' by lia. exact Hbound'. }
    eapply Qle_lt_trans; [exact Hbound|].
    (* 2 - 1/2^m < 2 because 1/2^m > 0 *)
    unfold Qlt, Qminus, Qopp, Qplus. simpl.
    assert (H1 : (0 < Z.pos (pow2 m))%Z) by lia.
    lia.
Qed.

(* Main boundedness lemma: |f(n)| ≤ |f(0)| + 2 *)
Lemma cauchy_bounded_by_first : forall (x : RR) (n : nat),
  Qabs (rr_seq x n) <= Qabs (rr_seq x 0%nat) + 2.
Proof.
  intros x n.
  (* |f(n)| = |f(n) - f(0) + f(0)| ≤ |f(n) - f(0)| + |f(0)| via triangle *)
  
  assert (Htri : Qabs (rr_seq x n) <= 
                 Qabs (rr_seq x n - rr_seq x 0%nat) + Qabs (rr_seq x 0%nat)).
  { set (diff := rr_seq x n - rr_seq x 0%nat).
    set (base := rr_seq x 0%nat).
    assert (Heq : rr_seq x n == diff + base) by (unfold diff, base; ring).
    assert (Habs_le : Qabs (diff + base) <= Qabs diff + Qabs base).
    { apply Qabs_triangle. }
    unfold diff, base in *.
    assert (H : Qabs (rr_seq x n) == Qabs (rr_seq x n - rr_seq x 0%nat + rr_seq x 0%nat)).
    { assert (Heq2 : rr_seq x n == rr_seq x n - rr_seq x 0%nat + rr_seq x 0%nat) by ring.
      unfold Qeq in Heq2.
      unfold Qabs.
      destruct (rr_seq x n) as [n1 d1].
      destruct (rr_seq x n - rr_seq x 0%nat + rr_seq x 0%nat) as [n2 d2].
      simpl in *.
      unfold Qeq. simpl.
      lia. }
    rewrite H. exact Habs_le. }
  
  eapply Qle_trans; [exact Htri|].
  
  (* Now bound |f(n) - f(0)| < 2 *)
  assert (Hdiff : Qabs (rr_seq x n - rr_seq x 0%nat) < 2).
  { apply cauchy_diff_lt_2. apply (rr_mod x). }
  
  (* |f(n) - f(0)| + |f(0)| <= 2 + |f(0)| = |f(0)| + 2 *)
  assert (Hdiff_le : Qabs (rr_seq x n - rr_seq x 0%nat) <= 2).
  { apply Qlt_le_weak. exact Hdiff. }
  
  eapply Qle_trans.
  - apply Qplus_le_compat; [exact Hdiff_le | apply Qle_refl].
  - assert (Hcomm : 2 + Qabs (rr_seq x 0%nat) == Qabs (rr_seq x 0%nat) + 2) by ring.
    rewrite Hcomm. apply Qle_refl.
Qed.

(* The bound for any RR element *)
Definition RR_bound (x : RR) : Q := Qabs (rr_seq x 0%nat) + 3.

Lemma RR_bound_pos : forall x : RR, 0 < RR_bound x.
Proof.
  intro x. unfold RR_bound.
  assert (H : 0 <= Qabs (rr_seq x 0%nat)) by apply Qabs_nonneg.
  unfold Qlt, Qle in *. simpl in *. lia.
Qed.

Lemma RR_bounded : forall (x : RR) (n : nat),
  Qabs (rr_seq x n) <= RR_bound x.
Proof.
  intros x n. unfold RR_bound.
  eapply Qle_trans; [apply cauchy_bounded_by_first|].
  unfold Qle, Qplus. simpl. lia.
Qed.

(* ============================================================================ *)
(*                        PART 12: Q ARITHMETIC HELPERS                         *)
(* ============================================================================ *)

(* Helper: same-denominator addition *)
Lemma Qmake_add_same_denom : forall (a b : Z) (q : positive),
  (a # q) + (b # q) == ((a + b) # q).
Proof.
  intros. unfold Qeq, Qplus. simpl.
  rewrite Pos2Z.inj_mul. ring.
Qed.

(* Helper: negation of Qmake *)
Lemma Qmake_opp : forall (a : Z) (q : positive),
  - (a # q) == ((-a) # q).
Proof.
  intros. unfold Qeq, Qopp. simpl. ring.
Qed.

(* Key identity: 2/(2p) = 1/p *)
Lemma Q_half_double : forall p : positive,
  (2 # (2 * p)) == (1 # p).
Proof.
  intro p. unfold Qeq. simpl. lia.
Qed.

(* The main identity we need for geometric_sum_bound *)
Lemma sum_identity : forall n s : nat,
  (1 # pow2 (n + s)) + ((2 # pow2 n) - (2 # pow2 (n + s))) ==
  (2 # pow2 n) - (1 # pow2 (n + s)).
Proof.
  intros n s.
  unfold Qminus.
  rewrite Qmake_opp.
  rewrite Qmake_opp.
  rewrite Qplus_assoc.
  rewrite (Qplus_comm (1 # pow2 (n + s)) (2 # pow2 n)).
  rewrite <- Qplus_assoc.
  rewrite Qmake_add_same_denom.
  simpl (1 + -2)%Z.
  reflexivity.
Qed.

(* The identity we need for the inductive step *)
Lemma inductive_step_identity : forall n s : nat,
  (1 # pow2 (n + s)) + ((2 # pow2 n) - (2 # pow2 (n + s))) <=
  (2 # pow2 n) - (2 # pow2 (S (n + s))).
Proof.
  intros n s.
  unfold Qminus.
  rewrite Qmake_opp.
  assert (Hrewrite : (2 # pow2 (S (n + s))) == (1 # pow2 (n + s))).
  { change (pow2 (S (n + s))) with (2 * pow2 (n + s))%positive.
    apply Q_half_double. }
  rewrite Hrewrite.
  rewrite sum_identity.
  apply Qle_refl.
Qed.

(* ============================================================================ *)
(*                        PART 13: SHIFT INFRASTRUCTURE                         *)
(* ============================================================================ *)

(*
  KEY INSIGHT: Shifting a geometric-Cauchy sequence by any fixed offset
  yields an equivalent real number. This is the abstraction that makes
  all multiplication ring laws simple.
*)

(* Shifted sequences remain Cauchy *)
Lemma is_cauchy_geo_shift : forall (f : nat -> Q) (s : nat),
  is_cauchy_geo f -> is_cauchy_geo (fun n => f (n + s)%nat).
Proof.
  intros f s Hcauchy. unfold is_cauchy_geo in *. intro n.
  (* |f((S n)+s) - f(n+s)| = |f(S(n+s)) - f(n+s)| ≤ 1/2^{n+s} ≤ 1/2^n *)
  replace (S n + s)%nat with (S (n + s))%nat by lia.
  eapply Qle_trans; [apply (Hcauchy (n + s)%nat)|].
  apply pow2_shift_le.
Qed.

(* Shift operator on RR *)
Definition RR_shift (x : RR) (s : nat) : RR :=
  mkRR (fun n => rr_seq x (n + s)%nat) 
       (is_cauchy_geo_shift (rr_seq x) s (rr_mod x)).

(* General gap bound: |f(n+s) - f(n)| ≤ 2/2^n for any s *)
Lemma cauchy_gap_bound : forall (f : nat -> Q) (n s : nat),
  is_cauchy_geo f ->
  Qabs (f (n + s)%nat - f n) <= 2 # pow2 n.
Proof.
  intros f n s Hcauchy.
  induction s as [|s' IH].
  - (* s = 0 *)
    replace (n + 0)%nat with n by lia.
    assert (Heq : f n - f n == 0) by ring.
    rewrite (Qabs_eq_zero _ Heq).
    unfold Qle. simpl. lia.
  - (* s = S s' *)
    (* |f(n+S s') - f(n)| ≤ |f(n+S s') - f(n+s')| + |f(n+s') - f(n)| *)
    assert (Htri : Qabs (f (n + S s')%nat - f n) <=
                   Qabs (f (n + S s')%nat - f (n + s')%nat) + Qabs (f (n + s')%nat - f n)).
    { assert (Heq : f (n + S s')%nat - f n == 
                    (f (n + S s')%nat - f (n + s')%nat) + (f (n + s')%nat - f n)) by ring.
      rewrite Heq. apply Qabs_triangle. }
    eapply Qle_trans; [exact Htri|].
    
    (* First term: |f(S(n+s')) - f(n+s')| ≤ 1/2^{n+s'} ≤ 1/2^n *)
    assert (Hstep : Qabs (f (n + S s')%nat - f (n + s')%nat) <= 1 # pow2 n).
    { replace (n + S s')%nat with (S (n + s'))%nat by lia.
      eapply Qle_trans; [apply (Hcauchy (n + s')%nat)|].
      apply pow2_shift_le. }
    
    (* Second term: IH gives |f(n+s') - f(n)| ≤ 2/2^n *)
    eapply Qle_trans; [apply Qplus_le_compat; [exact Hstep | exact IH]|].
    
    (* 1/2^n + 2/2^n = 3/2^n ≤ 2/2^n? No! But we need a tighter bound. *)
    (* Actually, let's be more careful. We need |f(n+s) - f(n)| ≤ 2/2^n *)
    (* 
       Σ_{k=n}^{n+s-1} 1/2^k = 1/2^n * (1 + 1/2 + ... + 1/2^{s-1})
                             = 1/2^n * (2 - 1/2^{s-1}) 
                             < 2/2^n
    *)
    (* The step adds 1/2^{n+s'} which is ≤ 1/2^n * 1/2^{s'} *)
    (* So total is < 2/2^n *)
    
    (* Let's prove it directly: 1/2^n + 2/2^n = 3/2^n *)
    (* Hmm, that's > 2/2^n. We need a different approach. *)
    
    (* Actually the key is: Σ_{k=n}^{n+s-1} 1/2^k < 2/2^n *)
    (* Let's use strong induction with a tighter bound *)
Abort.

(* Better approach: prove the geometric series bound directly *)
Lemma geometric_sum_bound : forall (f : nat -> Q) (n s : nat),
  is_cauchy_geo f ->
  Qabs (f (n + s)%nat - f n) <= (2 # pow2 n) - (2 # pow2 (n + s)).
Proof.
  intros f n s Hcauchy.
  induction s as [|s' IH].
  - (* s = 0 *)
    replace (n + 0)%nat with n by lia.
    assert (Heq : f n - f n == 0) by ring.
    rewrite (Qabs_eq_zero _ Heq).
    (* 0 ≤ 2/2^n - 2/2^n = 0 *)
    assert (Hzero : (2 # pow2 n) - (2 # pow2 n) == 0) by ring.
    rewrite Hzero. unfold Qle. simpl. lia.
  - (* s = S s' *)
    assert (Htri : Qabs (f (n + S s')%nat - f n) <=
                   Qabs (f (n + S s')%nat - f (n + s')%nat) + Qabs (f (n + s')%nat - f n)).
    { assert (Heq : f (n + S s')%nat - f n == 
                    (f (n + S s')%nat - f (n + s')%nat) + (f (n + s')%nat - f n)) by ring.
      rewrite Heq. apply Qabs_triangle. }
    eapply Qle_trans; [exact Htri|].
    
    (* Step bound *)
    assert (Hstep : Qabs (f (n + S s')%nat - f (n + s')%nat) <= 1 # pow2 (n + s')).
    { replace (n + S s')%nat with (S (n + s'))%nat by lia.
      apply (Hcauchy (n + s')%nat). }
    
    eapply Qle_trans; [apply Qplus_le_compat; [exact Hstep | exact IH]|].
    
    (* Goal: 1/2^{n+s'} + (2/2^n - 2/2^{n+s'}) ≤ 2/2^n - 2/2^{n+S s'} *)
    replace (n + S s')%nat with (S (n + s'))%nat by lia.
    apply inductive_step_identity.
Qed.

(* High-level lemma: a - b < a when b > 0 *)
Lemma Qminus_lt_l : forall a b : Q, 0 < b -> a - b < a.
Proof.
  intros a b Hb.
  setoid_rewrite Qlt_minus_iff.
  setoid_replace (a - (a - b)) with b by ring.
  exact Hb.
Qed.

(* Helper: 2/2^n - 2/2^{n+s} < 2/2^n is equivalent to 0 < 2/2^{n+s} *)
Lemma strict_bound_helper : forall n s : nat,
  (2 # pow2 n) - (2 # pow2 (n + s)) < 2 # pow2 n.
Proof.
  intros n s.
  apply Qminus_lt_l.
  (* Goal: 0 < 2 # pow2 (n + s) *)
  unfold Qlt. simpl. lia.
Qed.

(* Corollary: |f(n+s) - f(n)| < 2/2^n *)
Lemma cauchy_gap_bound : forall (f : nat -> Q) (n s : nat),
  is_cauchy_geo f ->
  Qabs (f (n + s)%nat - f n) < 2 # pow2 n.
Proof.
  intros f n s Hcauchy.
  eapply Qle_lt_trans; [apply geometric_sum_bound; exact Hcauchy|].
  apply strict_bound_helper.
Qed.

(* Weak version for convenience *)
Lemma cauchy_gap_bound_le : forall (f : nat -> Q) (n s : nat),
  is_cauchy_geo f ->
  Qabs (f (n + s)%nat - f n) <= 2 # pow2 n.
Proof.
  intros. apply Qlt_le_weak. apply cauchy_gap_bound. assumption.
Qed.

(* Monotonicity of pow2 *)
Lemma pow2_le_mono : forall m n : nat, (m <= n)%nat -> (pow2 m <= pow2 n)%positive.
Proof.
  intros m n H.
  induction H.
  - lia.
  - simpl. 
    assert (H1 : (1 <= pow2 m0)%positive) by (clear; induction m0; simpl; lia).
    lia.
Qed.

(* THE KEY LEMMA: Shifted sequence is equivalent to original *)
Lemma RReq_shift : forall (x : RR) (s : nat), RR_shift x s =RR= x.
Proof.
  intros x s. unfold RReq, RR_shift. simpl. intro k.
  (* Need: |x(n+s) - x(n)| ≤ 1/2^k for large enough n *)
  (* From cauchy_gap_bound: |x(n+s) - x(n)| < 2/2^n *)
  (* So need 2/2^n ≤ 1/2^k, i.e., n ≥ k+1 *)
  exists (S k). intros n Hn.
  assert (Hgap : Qabs (rr_seq x (n + s)%nat - rr_seq x n) < 2 # pow2 n).
  { apply cauchy_gap_bound. apply (rr_mod x). }
  eapply Qle_trans; [apply Qlt_le_weak; exact Hgap|].
  (* 2/2^n ≤ 1/2^k when n ≥ S k *)
  (* Since pow2 (S k) = 2 * pow2 k and pow2 n >= pow2 (S k), we have *)
  (* 2/pow2 n <= 2/(2*pow2 k) = 1/pow2 k *)
  unfold Qle. simpl.
  (* Goal: 2 * pow2 k <= pow2 n *)
  assert (Hpow : (S k <= n)%nat) by lia.
  assert (Hle : (pow2 (S k) <= pow2 n)%positive).
  { apply pow2_le_mono. exact Hpow. }
  simpl in Hle. lia.
Qed.

(* Symmetry: original is equivalent to shifted *)
Lemma RReq_shift_sym : forall (x : RR) (s : nat), x =RR= RR_shift x s.
Proof.
  intros x s. apply RReq_sym. apply RReq_shift.
Qed.

(* Composing shifts *)
Lemma RR_shift_shift : forall (x : RR) (s1 s2 : nat),
  RR_shift (RR_shift x s1) s2 =RR= RR_shift x (s1 + s2).
Proof.
  intros x s1 s2. unfold RReq, RR_shift. simpl. intro k.
  exists 0%nat. intros n Hn.
  replace (n + s2 + s1)%nat with (n + (s1 + s2))%nat by lia.
  assert (Heq : rr_seq x (n + (s1 + s2))%nat - rr_seq x (n + (s1 + s2))%nat == 0) by ring.
  rewrite (Qabs_eq_zero _ Heq). apply Qabs_zero_le.
Qed.

(* ============================================================================ *)
(*                        PART 13: MULTIPLICATION                               *)
(* ============================================================================ *)

(*
  For multiplication with bounds Bx, By:
  |x(n+1)y(n+1) - x(n)y(n)| ≤ |x(n+1)||y(n+1) - y(n)| + |y(n)||x(n+1) - x(n)|
                           ≤ Bx/2^n + By/2^n = (Bx + By)/2^n
  
  Solution: Shift index by k where 2^k ≥ Bx + By to get (Bx + By)/2^{n+k} ≤ 1/2^n
*)

(* Compute sufficient shift: k = |num| + den + 1 guarantees 2^k > num/den *)
Definition bound_shift (b : Q) : nat := 
  (Z.abs_nat (Qnum b) + Pos.to_nat (Qden b) + 1)%nat.

(* Key lemma: 2^{a+b+1} >= 2^a + 2^b *)
Lemma pow2_sum_bound : forall a b : nat,
  (Pos.to_nat (pow2 a) + Pos.to_nat (pow2 b) <= Pos.to_nat (pow2 (a + b + 1)))%nat.
Proof.
  intros a b.
  replace (a + b + 1)%nat with (S (a + b))%nat by lia.
  rewrite pow2_S.
  rewrite Pos2Nat.inj_mul.
  rewrite pow2_add.
  rewrite Pos2Nat.inj_mul.
  assert (Ha : (1 <= Pos.to_nat (pow2 a))%nat).
  { pose proof (Pos2Nat.is_pos (pow2 a)). lia. }
  assert (Hb : (1 <= Pos.to_nat (pow2 b))%nat).
  { pose proof (Pos2Nat.is_pos (pow2 b)). lia. }
  nia.
Qed.

(* Corollary for Q: if Bx <= 2^a and By <= 2^b, then Bx + By <= 2^{a+b+1} *)
Lemma sum_le_pow2 : forall (Bx By : Q) (a b : nat),
  0 <= Bx -> 0 <= By ->
  Bx <= inject_Z (Z.of_nat (Pos.to_nat (pow2 a))) ->
  By <= inject_Z (Z.of_nat (Pos.to_nat (pow2 b))) ->
  Bx + By <= inject_Z (Z.of_nat (Pos.to_nat (pow2 (a + b + 1)))).
Proof.
  intros Bx By a b HBx_pos HBy_pos HBx HBy.
  eapply Qle_trans.
  - apply Qplus_le_compat; [exact HBx | exact HBy].
  - rewrite <- inject_Z_plus.
    unfold Qle, inject_Z. simpl.
    rewrite Z.mul_1_r. rewrite Z.mul_1_r.
    pose proof (pow2_sum_bound a b) as Hbound.
    lia.
Qed.

(* Key lemma: 2^k grows faster than k, so 2^{|num|+den+1} > num/den *)
Lemma pow2_ge_bound : forall b : Q, 0 <= b ->
  b <= inject_Z (Z.of_nat (Pos.to_nat (pow2 (bound_shift b)))).
Proof.
  intros b Hb.
  unfold bound_shift.
  destruct b as [num den].
  unfold Qle in Hb. simpl in Hb.
  unfold Qle. simpl.
  
  set (k := (Z.abs_nat num + Pos.to_nat den + 1)%nat).
  
  assert (Hpow_k : (k <= Pos.to_nat (pow2 k))%nat).
  { apply pow2_ge_n. }
  
  assert (Hnum_bound : (Z.abs_nat num < k)%nat) by (unfold k; lia).
  assert (Hden_bound : (Pos.to_nat den < k)%nat) by (unfold k; lia).
  
  assert (H1 : (Z.abs_nat num < Pos.to_nat (pow2 k))%nat) by lia.
  assert (H2 : (Pos.to_nat den < Pos.to_nat (pow2 k))%nat) by lia.
  
  apply Nat2Z.inj_lt in H1.
  rewrite Zabs2Nat.id_abs in H1.
  rewrite positive_nat_Z in H1.
  
  apply Nat2Z.inj_lt in H2.
  rewrite positive_nat_Z in H2.
  rewrite positive_nat_Z in H2.
  
  destruct (Z_lt_le_dec num 0) as [Hneg | Hnneg].
  - assert (Hcontra : (0 <= num * 1)%Z) by exact Hb. lia.
  - assert (Habs : Z.abs num = num) by (apply Z.abs_eq; lia).
    rewrite Habs in H1.
    rewrite positive_nat_Z.
    assert (Hden_pos : (1 <= Z.pos den)%Z) by lia.
    nia.
Qed.

(* Product sequence with appropriate shifting *)
Definition seq_mult (x y : RR) (n : nat) : Q :=
  let k := (bound_shift (RR_bound x) + bound_shift (RR_bound y) + 1)%nat in
  rr_seq x (n + k)%nat * rr_seq y (n + k)%nat.

(* The product of two Cauchy sequences is Cauchy *)
Lemma cauchy_mult : forall x y : RR, is_cauchy_geo (seq_mult x y).
Proof.
  intros x y.
  unfold is_cauchy_geo, seq_mult.
  intro n.
  
  set (k := (bound_shift (RR_bound x) + bound_shift (RR_bound y) + 1)%nat).
  set (Bx := RR_bound x).
  set (By := RR_bound y).
  
  set (xn := rr_seq x (n + k)%nat).
  set (xn1 := rr_seq x (S n + k)%nat).
  set (yn := rr_seq y (n + k)%nat).
  set (yn1 := rr_seq y (S n + k)%nat).
  
  assert (Halg : xn1 * yn1 - xn * yn == xn1 * (yn1 - yn) + yn * (xn1 - xn)).
  { unfold xn, xn1, yn, yn1. ring. }
  
  assert (Hrewrite : Qabs (xn1 * yn1 - xn * yn) == Qabs (xn1 * (yn1 - yn) + yn * (xn1 - xn))).
  { rewrite Halg. reflexivity. }
  
  assert (Htri : Qabs (xn1 * (yn1 - yn) + yn * (xn1 - xn)) <=
                 Qabs (xn1 * (yn1 - yn)) + Qabs (yn * (xn1 - xn))).
  { apply Qabs_triangle. }
  
  assert (Hterm1 : Qabs (xn1 * (yn1 - yn)) == Qabs xn1 * Qabs (yn1 - yn)).
  { apply Qabs_Qmult. }
  
  assert (Hterm2 : Qabs (yn * (xn1 - xn)) == Qabs yn * Qabs (xn1 - xn)).
  { apply Qabs_Qmult. }
  
  assert (Hcauchy_x : Qabs (xn1 - xn) <= 1 # pow2 (n + k)).
  { unfold xn, xn1.
    replace (S n + k)%nat with (S (n + k))%nat by lia.
    apply (rr_mod x). }
  
  assert (Hcauchy_y : Qabs (yn1 - yn) <= 1 # pow2 (n + k)).
  { unfold yn, yn1.
    replace (S n + k)%nat with (S (n + k))%nat by lia.
    apply (rr_mod y). }
  
  assert (Hbound_xn1 : Qabs xn1 <= Bx).
  { unfold xn1, Bx. apply RR_bounded. }
  
  assert (Hbound_yn : Qabs yn <= By).
  { unfold yn, By. apply RR_bounded. }
  
  assert (Hprod1 : Qabs xn1 * Qabs (yn1 - yn) <= Bx * (1 # pow2 (n + k))).
  { apply Qmult_le_compat_nonneg.
    - split; [apply Qabs_nonneg | exact Hbound_xn1].
    - split; [apply Qabs_nonneg | exact Hcauchy_y]. }
  
  assert (Hprod2 : Qabs yn * Qabs (xn1 - xn) <= By * (1 # pow2 (n + k))).
  { apply Qmult_le_compat_nonneg.
    - split; [apply Qabs_nonneg | exact Hbound_yn].
    - split; [apply Qabs_nonneg | exact Hcauchy_x]. }
  
  assert (Hsum : Qabs (xn1 * (yn1 - yn)) + Qabs (yn * (xn1 - xn)) <= 
                 (Bx + By) * (1 # pow2 (n + k))).
  { eapply Qle_trans.
    - apply Qplus_le_compat.
      + rewrite Hterm1. exact Hprod1.
      + rewrite Hterm2. exact Hprod2.
    - assert (Heq : Bx * (1 # pow2 (n + k)) + By * (1 # pow2 (n + k)) == 
                    (Bx + By) * (1 # pow2 (n + k))) by ring.
      rewrite Heq. apply Qle_refl. }
  
  assert (Hshift : (Bx + By) * (1 # pow2 (n + k)) <= 1 # pow2 n).
  { assert (HBx_bound : Bx <= inject_Z (Z.of_nat (Pos.to_nat (pow2 (bound_shift Bx))))).
    { apply pow2_ge_bound. unfold Bx. 
      apply Qlt_le_weak. apply RR_bound_pos. }
    
    assert (HBy_bound : By <= inject_Z (Z.of_nat (Pos.to_nat (pow2 (bound_shift By))))).
    { apply pow2_ge_bound. unfold By.
      apply Qlt_le_weak. apply RR_bound_pos. }
    
    assert (Hsum_bound : Bx + By <= inject_Z (Z.of_nat (Pos.to_nat (pow2 k)))).
    { unfold k.
      apply sum_le_pow2.
      - unfold Bx. apply Qlt_le_weak. apply RR_bound_pos.
      - unfold By. apply Qlt_le_weak. apply RR_bound_pos.
      - exact HBx_bound.
      - exact HBy_bound. }
    
    unfold Qle, Qmult. simpl.
    rewrite pow2_add.
    
    assert (HBxBy_le_k : Bx + By <= inject_Z (Z.pos (pow2 k))).
    { eapply Qle_trans; [exact Hsum_bound|].
      unfold inject_Z, Qle. simpl. rewrite Z.mul_1_r.
      rewrite positive_nat_Z. lia. }
    
    unfold Qle in HBxBy_le_k. simpl in HBxBy_le_k.
    rewrite Z.mul_1_r in HBxBy_le_k.
    
    rewrite Pos2Z.inj_mul.
    assert (Hpow_n_pos : (0 < Z.pos (pow2 n))%Z) by lia.
    nia.
  }
  
  eapply Qle_trans.
  - rewrite Hrewrite. exact Htri.
  - eapply Qle_trans; [exact Hsum | exact Hshift].
Qed.

Definition RR_mult (x y : RR) : RR :=
  mkRR (seq_mult x y) (cauchy_mult x y).

Infix "*RR" := RR_mult (at level 40, left associativity).

(* ============================================================================ *)
(*                        PART 14: MULTIPLICATION PROPERTIES                    *)
(* ============================================================================ *)

(* Multiplication by constants from Q *)
Lemma Q_to_RR_mult : forall p q : Q,
  Q_to_RR p *RR Q_to_RR q =RR= Q_to_RR (p * q).
Proof.
  intros p q. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_mult, seq_mult, Q_to_RR. simpl.
  assert (H : p * q - p * q == 0) by ring.
  rewrite (Qabs_eq_zero _ H). apply Qabs_zero_le.
Qed.

(* Zero annihilates *)
Lemma RR_mult_0_l : forall x : RR, 0RR *RR x =RR= 0RR.
Proof.
  intro x. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_mult, seq_mult, RR_zero, Q_to_RR, RR_bound. simpl.
  unfold Qabs, Qle. simpl. lia.
Qed.

Lemma RR_mult_0_r : forall x : RR, x *RR 0RR =RR= 0RR.
Proof.
  intro x. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_mult, seq_mult, RR_zero, Q_to_RR, RR_bound. simpl.
  unfold Qabs, Qle. simpl. lia.
Qed.

(* ============================================================================ *)
(*  MULTIPLICATIVE IDENTITY - COMPLETE PROOF via shift equivalence             *)
(* ============================================================================ *)

(* Helper: if x == 0, then Qabs x <= 1/2^j *)
Lemma Qabs_zero_pow2 : forall (x : Q) (j : nat), x == 0 -> Qabs x <= 1 # pow2 j.
Proof.
  intros x j Hx.
  destruct x as [xn xd].
  unfold Qeq in Hx. simpl in Hx.
  assert (Hnum : xn = 0%Z) by lia.
  unfold Qabs. simpl. rewrite Hnum. simpl.
  unfold Qle. simpl. lia.
Qed.

Lemma RR_mult_1_l : forall x : RR, 1RR *RR x =RR= x.
Proof.
  intro x.
  unfold RReq. intro j.
  
  set (k := (bound_shift (RR_bound 1RR) + bound_shift (RR_bound x) + 1)%nat).
  
  destruct (RReq_shift x k j) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  
  (* Instead of unfolding and simplifying, work at the level of rr_seq *)
  (* rr_seq (1RR *RR x) n = seq_mult 1RR x n = 1 * rr_seq x (n + k') *)
  (* where k' = bound_shift (RR_bound 1RR) + bound_shift (RR_bound x) + 1 = k *)
  
  assert (Hrr : rr_seq (1RR *RR x) n = 1 * rr_seq x (n + k)%nat).
  { unfold RR_mult, seq_mult, RR_one, Q_to_RR. simpl.
    (* The k in the goal is (bound_shift (RR_bound (Q_to_RR 1)) + bound_shift (RR_bound x) + 1) *)
    (* which equals our k by definition *)
    reflexivity. }
  
  rewrite Hrr.
  
  (* Now goal is: |1 * x(n+k) - x(n)| <= 1/2^j *)
  (* HN: |x(n+k) - x(n)| <= 1/2^j *)
  
  assert (Hleib : 1 * rr_seq x (n + k)%nat - rr_seq x n = 
                  rr_seq x (n + k)%nat - rr_seq x n).
  {
    destruct (rr_seq x (n + k)%nat) as [num den].
    unfold Qmult, Qminus, Qplus, Qopp. simpl.
    destruct num; reflexivity.
  }
  rewrite Hleib.
  exact HN.
Qed.

Lemma RR_mult_1_r : forall x : RR, x *RR 1RR =RR= x.
Proof.
  intro x.
  unfold RReq. intro j.
  
  set (k := (bound_shift (RR_bound x) + bound_shift (RR_bound 1RR) + 1)%nat).
  
  destruct (RReq_shift x k j) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  
  assert (Hrr : rr_seq (x *RR 1RR) n = rr_seq x (n + k)%nat * 1).
  { unfold RR_mult, seq_mult, RR_one, Q_to_RR. simpl. reflexivity. }
  
  rewrite Hrr.
  
  assert (Hleib : rr_seq x (n + k)%nat * 1 - rr_seq x n = 
                  rr_seq x (n + k)%nat - rr_seq x n).
  {
    destruct (rr_seq x (n + k)%nat) as [num den].
    unfold Qmult, Qminus, Qplus, Qopp. simpl.
    rewrite Z.mul_1_r.
    rewrite Pos.mul_1_r.
    reflexivity.
  }
  rewrite Hleib.
  exact HN.
Qed.

(* ============================================================================ *)
(*  COMMUTATIVITY                                                               *)
(* ============================================================================ *)

Lemma RR_mult_comm : forall x y : RR,
  x *RR y =RR= y *RR x.
Proof.
  intros x y. unfold RReq. intro k.
  exists 0%nat. intros n Hn.
  unfold RR_mult, seq_mult. simpl.
  
  set (kxy := (bound_shift (RR_bound x) + bound_shift (RR_bound y) + 1)%nat).
  set (kyx := (bound_shift (RR_bound y) + bound_shift (RR_bound x) + 1)%nat).
  
  (* kxy = kyx *)
  assert (Heq_shift : kxy = kyx) by (unfold kxy, kyx; lia).
  rewrite Heq_shift.
  
  assert (Hcomm : rr_seq x (n + kyx)%nat * rr_seq y (n + kyx)%nat -
                  rr_seq y (n + kyx)%nat * rr_seq x (n + kyx)%nat == 0) by ring.
  rewrite (Qabs_eq_zero _ Hcomm). apply Qabs_zero_le.
Qed.

(* ============================================================================ *)
(*  ASSOCIATIVITY - COMPLETE PROOF via shift equivalence                       *)
(* ============================================================================ *)

(* Triangle inequality for three terms *)
Lemma Qabs_triangle3 : forall a b c : Q,
  Qabs (a + b + c) <= Qabs a + Qabs b + Qabs c.
Proof.
  intros.
  eapply Qle_trans; [apply Qabs_triangle|].
  apply Qplus_le_compat; [apply Qabs_triangle | apply Qle_refl].
Qed.

(* Bound on product difference: |abc - def| <= delta * (BbBc + BaBc + BaBb) *)
Lemma product_diff_bound : forall a b c d e f Ba Bb Bc delta : Q,
  0 <= Ba -> 0 <= Bb -> 0 <= Bc -> 0 <= delta ->
  Qabs a <= Ba -> Qabs b <= Bb -> Qabs c <= Bc ->
  Qabs d <= Ba -> Qabs e <= Bb -> Qabs f <= Bc ->
  Qabs (a - d) <= delta -> Qabs (b - e) <= delta -> Qabs (c - f) <= delta ->
  Qabs (a * b * c - d * e * f) <= delta * (Bb * Bc + Ba * Bc + Ba * Bb).
Proof.
  intros a b c d e f Ba Bb Bc delta HBa HBb HBc Hdelta.
  intros Ha Hb Hc Hd He Hf Had Hbe Hcf.
  
  assert (Hdiff : a * b * c - d * e * f == (a - d) * b * c + d * (b - e) * c + d * e * (c - f)) by ring.
  
  assert (Htri : Qabs (a * b * c - d * e * f) <= 
                 Qabs ((a - d) * b * c) + Qabs (d * (b - e) * c) + Qabs (d * e * (c - f))).
  { rewrite Hdiff. apply Qabs_triangle3. }
  
  eapply Qle_trans; [exact Htri|].
  
  assert (Hterm1 : Qabs ((a - d) * b * c) <= delta * Bb * Bc).
  { rewrite Qabs_Qmult. rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qmult_le_0_compat; apply Qabs_nonneg|].
      apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | exact Had].
      + split; [apply Qabs_nonneg | exact Hb].
    - split; [apply Qabs_nonneg | exact Hc]. }
  
  assert (Hterm2 : Qabs (d * (b - e) * c) <= Ba * delta * Bc).
  { rewrite Qabs_Qmult. rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qmult_le_0_compat; apply Qabs_nonneg|].
      apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | exact Hd].
      + split; [apply Qabs_nonneg | exact Hbe].
    - split; [apply Qabs_nonneg | exact Hc]. }

  assert (Hterm3 : Qabs (d * e * (c - f)) <= Ba * Bb * delta).
  { rewrite Qabs_Qmult. rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qmult_le_0_compat; apply Qabs_nonneg|].
      apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | exact Hd].
      + split; [apply Qabs_nonneg | exact He].
    - split; [apply Qabs_nonneg | exact Hcf]. }
  
  eapply Qle_trans.
  { apply Qplus_le_compat.
    apply Qplus_le_compat.
    - exact Hterm1.
    - exact Hterm2.
    - exact Hterm3. }
  
  assert (Hfactor : delta * Bb * Bc + Ba * delta * Bc + Ba * Bb * delta ==
                    delta * (Bb * Bc + Ba * Bc + Ba * Bb)) by ring.
  rewrite Hfactor.
  apply Qle_refl.
Qed.

(* General gap bound between any two indices >= n *)
Lemma general_gap_bound : forall (x : RR) (i j n : nat),
  (n <= i)%nat -> (n <= j)%nat ->
  Qabs (rr_seq x i - rr_seq x j) <= 2 # pow2 n.
Proof.
  intros x i j n Hni Hnj.
  destruct (Nat.le_ge_cases i j) as [Hle | Hge].
  - (* i <= j *)
    assert (Hji : j = (i + (j - i))%nat) by lia.
    rewrite Hji.
    assert (Hsym : rr_seq x i - rr_seq x (i + (j - i))%nat == 
                   -(rr_seq x (i + (j - i))%nat - rr_seq x i)) by ring.
    rewrite Hsym. rewrite Qabs_opp.
    eapply Qle_trans; [apply cauchy_gap_bound_le; apply rr_mod|].
    unfold Qle. simpl.
    assert (Hpow : (pow2 n <= pow2 i)%positive) by (apply pow2_le_mono; exact Hni).
    lia.
  - (* j <= i *)
    assert (Hij : i = (j + (i - j))%nat) by lia.
    rewrite Hij.
    eapply Qle_trans; [apply cauchy_gap_bound_le; apply rr_mod|].
    unfold Qle. simpl.
    assert (Hpow : (pow2 n <= pow2 j)%positive) by (apply pow2_le_mono; exact Hnj).
    lia.
Qed.

(* pow2 (S k + s) = 2 * pow2 k * pow2 s *)
Lemma pow2_S_k_s : forall k s : nat, pow2 (S k + s) = (2 * pow2 k * pow2 s)%positive.
Proof.
  intros k s.
  replace (S k + s)%nat with (S (k + s))%nat by lia.
  simpl. rewrite pow2_add. lia.
Qed.

(* Key budget lemma: converts gap bound to target precision *)
Lemma geom_budget : forall (k : nat) (C : Q),
  0 <= C ->
  (2 # pow2 (S k + bound_shift (2 * C))) * C <= 1 # pow2 k.
Proof.
  intros k C HC.
  remember (bound_shift (2 * C)) as s eqn:Hs.
  
  assert (H2C_bound : 2 * C <= inject_Z (Z.of_nat (Pos.to_nat (pow2 s)))).
  { rewrite Hs. apply pow2_ge_bound. 
    apply Qmult_le_0_compat; [unfold Qle; simpl; lia | exact HC]. }
  
  rewrite pow2_S_k_s.
  
  unfold Qle in H2C_bound. simpl in H2C_bound.
  rewrite Z.mul_1_r in H2C_bound.
  rewrite positive_nat_Z in H2C_bound.
  
  unfold Qle, Qmult. simpl.
  nia.
Qed.

(* 2-factor product difference bound for distributivity *)
Lemma product2_diff_bound : forall a b c d Ba Bb delta : Q,
  0 <= Ba -> 0 <= Bb -> 0 <= delta ->
  Qabs a <= Ba -> Qabs b <= Bb ->
  Qabs c <= Ba -> Qabs d <= Bb ->
  Qabs (a - c) <= delta ->
  Qabs (b - d) <= delta ->
  Qabs (a * b - c * d) <= delta * (Bb + Ba).
Proof.
  intros a b c d Ba Bb delta HBa HBb Hdelta Ha Hb Hc Hd Hac Hbd.
  
  assert (Hdecomp : a * b - c * d == (a - c) * b + c * (b - d)) by ring.
  
  assert (Htri : Qabs (a * b - c * d) <= Qabs ((a - c) * b) + Qabs (c * (b - d))).
  { rewrite Hdecomp. apply Qabs_triangle. }
  
  eapply Qle_trans; [exact Htri|].
  
  assert (Hterm1 : Qabs ((a - c) * b) <= delta * Bb).
  { rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qabs_nonneg | exact Hac].
    - split; [apply Qabs_nonneg | exact Hb]. }
  
  assert (Hterm2 : Qabs (c * (b - d)) <= Ba * delta).
  { rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qabs_nonneg | exact Hc].
    - split; [apply Qabs_nonneg | exact Hbd]. }
  
  eapply Qle_trans.
  { apply Qplus_le_compat; [exact Hterm1 | exact Hterm2]. }
  
  assert (Hfactor : delta * Bb + Ba * delta == delta * (Bb + Ba)) by ring.
  rewrite Hfactor.
  apply Qle_refl.
Qed.

(* Extraction lemma: rr_seq of a product *)
Lemma rr_seq_mult : forall x y n,
  rr_seq (x *RR y) n = 
  let k := (bound_shift (RR_bound x) + bound_shift (RR_bound y) + 1)%nat in
  rr_seq x (n + k)%nat * rr_seq y (n + k)%nat.
Proof.
  intros. unfold RR_mult, seq_mult. simpl. reflexivity.
Qed.

(* Direct bound on associativity difference *)
Lemma assoc_bound_direct : forall (x y z : RR) (n k : nat),
  let Bx := RR_bound x in
  let By := RR_bound y in
  let Bz := RR_bound z in
  let C := By * Bz + Bx * Bz + Bx * By in
  (n >= S k + bound_shift (2 * C))%nat ->
  Qabs (rr_seq ((x *RR y) *RR z) n - rr_seq (x *RR (y *RR z)) n) <= 1 # pow2 k.
Proof.
  intros x y z n k Bx By Bz C Hn.
  
  (* Expand to get explicit Q expressions *)
  unfold RR_mult, seq_mult. simpl.
  
  (* After expansion, we have products of rr_seq values at various indices >= n *)
  (* LHS = (x_a * y_a) * z_b for some a, b >= n *)
  (* RHS = x_c * (y_d * z_d) for some c, d >= n *)
  
  (* Abstract the six rr_seq values *)
  set (xa := rr_seq x _).
  set (ya := rr_seq y _).
  set (za := rr_seq z _).
  set (xb := rr_seq x _).
  set (yb := rr_seq y _).
  set (zb := rr_seq z _).
  
  (* The goal now has form: Qabs ((xa * ya) * za - xb * (yb * zb)) <= 1/2^k *)
  
  (* By Q associativity *)
  assert (Hassoc : (xa * ya) * za - xb * (yb * zb) == xa * ya * za - xb * yb * zb).
  { ring. }
  
  assert (Hwd : Qabs ((xa * ya) * za - xb * (yb * zb)) == Qabs (xa * ya * za - xb * yb * zb)).
  { apply Qabs_wd. exact Hassoc. }
  
  rewrite Hwd. clear Hwd Hassoc.
  
  (* Bounds on all values *)
  assert (HBx_pos : 0 <= Bx) by (unfold Bx; apply Qlt_le_weak; apply RR_bound_pos).
  assert (HBy_pos : 0 <= By) by (unfold By; apply Qlt_le_weak; apply RR_bound_pos).
  assert (HBz_pos : 0 <= Bz) by (unfold Bz; apply Qlt_le_weak; apply RR_bound_pos).
  assert (Hdelta_pos : 0 <= 2 # pow2 n) by (unfold Qle; simpl; lia).
  
  assert (Hxa_bd : Qabs xa <= Bx) by (unfold xa, Bx; apply RR_bounded).
  assert (Hya_bd : Qabs ya <= By) by (unfold ya, By; apply RR_bounded).
  assert (Hza_bd : Qabs za <= Bz) by (unfold za, Bz; apply RR_bounded).
  assert (Hxb_bd : Qabs xb <= Bx) by (unfold xb, Bx; apply RR_bounded).
  assert (Hyb_bd : Qabs yb <= By) by (unfold yb, By; apply RR_bounded).
  assert (Hzb_bd : Qabs zb <= Bz) by (unfold zb, Bz; apply RR_bounded).
  
  (* Gap bounds - all indices >= n *)
  assert (Hdx : Qabs (xa - xb) <= 2 # pow2 n).
  { unfold xa, xb. apply general_gap_bound; lia. }
  assert (Hdy : Qabs (ya - yb) <= 2 # pow2 n).
  { unfold ya, yb. apply general_gap_bound; lia. }
  assert (Hdz : Qabs (za - zb) <= 2 # pow2 n).
  { unfold za, zb. apply general_gap_bound; lia. }
  
  (* Apply product_diff_bound *)
  assert (Hprod : Qabs (xa * ya * za - xb * yb * zb) <= (2 # pow2 n) * C).
  { apply product_diff_bound; assumption. }
  
  eapply Qle_trans; [exact Hprod|].
  
  (* Now use geom_budget with monotonicity *)
  assert (HC_pos : 0 <= C).
  { unfold C.
    apply Qle_trans with (0 + 0 + 0); [unfold Qle; simpl; lia|].
    repeat apply Qplus_le_compat; apply Qmult_le_0_compat; assumption. }
  
  remember (S k + bound_shift (2 * C))%nat as m eqn:Hm_eq.
  
  assert (Hm_le_n : (m <= n)%nat) by lia.
  
  assert (Hpow_mono : (pow2 m <= pow2 n)%positive).
  { apply pow2_le_mono. exact Hm_le_n. }
  
  assert (Hfrac_mono : 2 # pow2 n <= 2 # pow2 m).
  { unfold Qle. simpl. 
    assert (H : (Z.pos (pow2 m) <= Z.pos (pow2 n))%Z) by lia.
    lia. }
  
  eapply Qle_trans.
  { apply Qmult_le_compat_r; [exact Hfrac_mono | exact HC_pos]. }
  
  rewrite Hm_eq.
  apply geom_budget.
  exact HC_pos.
Qed.

Lemma RR_mult_assoc : forall x y z : RR,
  (x *RR y) *RR z =RR= x *RR (y *RR z).
Proof.
  intros x y z.
  unfold RReq. intro k.
  
  set (Bx := RR_bound x).
  set (By := RR_bound y).
  set (Bz := RR_bound z).
  set (C := By * Bz + Bx * Bz + Bx * By).
  
  exists (S k + bound_shift (2 * C))%nat.
  intros n Hn.
  
  apply assoc_bound_direct.
  exact Hn.
Qed.

(* ============================================================================ *)
(*  DISTRIBUTIVITY - COMPLETE PROOF via shift equivalence                      *)
(* ============================================================================ *)

Lemma RR_mult_plus_distr_l : forall x y z : RR,
  x *RR (y +RR z) =RR= (x *RR y) +RR (x *RR z).
Proof.
  intros x y z.
  unfold RReq. intro k.
  
  (* x * (y + z) and (xy) + (xz) both compute at shifted indices *)
  (* The shifts differ, but shift equivalence handles this *)
  
  set (Bx := RR_bound x).
  set (By := RR_bound y).
  set (Bz := RR_bound z).
  set (Byz := RR_bound (y +RR z)).
  set (Bxy := RR_bound (x *RR y)).
  set (Bxz := RR_bound (x *RR z)).
  
  (* LHS shift *)
  set (k_lhs := (bound_shift Bx + bound_shift Byz + 1)%nat).
  
  (* RHS shifts *)
  set (kxy := (bound_shift Bx + bound_shift By + 1)%nat).
  set (kxz := (bound_shift Bx + bound_shift Bz + 1)%nat).
  
  (* Addition shift for (xy + xz) *)
  (* seq_plus uses S n, so RHS at n uses indices S n *)
  
  (* For the final bound, we need n >= S k + bound_shift(2*D) where D = By + 2*Bx + Bz *)
  set (D := By + Bx + Bz + Bx).
  set (total_shift := (k_lhs + kxy + kxz + bound_shift (2 * D) + 2)%nat).
  
  exists (S k + total_shift)%nat.
  intros n Hn.
  
  unfold RR_mult, RR_add, seq_mult, seq_plus. simpl.
  
  (* LHS: x(n + k_lhs) * (y(S(n + k_lhs)) + z(S(n + k_lhs))) *)
  (* But wait - (y +RR z) is defined with seq_plus which uses S n *)
  (* So (y +RR z) at index m = y(S m) + z(S m) *)
  
  (* Actually let me re-examine the definitions *)
  (* seq_plus x y n = x(S n) + y(S n) *)
  (* So (y +RR z) has sequence fun n => y(S n) + z(S n) *)
  
  (* x *RR (y +RR z) uses seq_mult x (y +RR z) *)
  (* seq_mult u v n = u(n + k) * v(n + k) where k depends on bounds *)
  
  (* So LHS at n = x(n + k_lhs) * [y(S(n + k_lhs)) + z(S(n + k_lhs))] *)
  
  (* RHS: (x *RR y) +RR (x *RR z) *)
  (* = seq_plus (x *RR y) (x *RR z) at index n *)
  (* = (x *RR y)(S n) + (x *RR z)(S n) *)
  (* = x(S n + kxy) * y(S n + kxy) + x(S n + kxz) * z(S n + kxz) *)
  
  set (i_lhs := (n + k_lhs)%nat).
  set (i_xy := (S n + kxy)%nat).
  set (i_xz := (S n + kxz)%nat).
  
  (* LHS = x(i_lhs) * (y(S i_lhs) + z(S i_lhs)) *)
  (* RHS = x(i_xy) * y(i_xy) + x(i_xz) * z(i_xz) *)
  
  (* Expand LHS *)
  (* x(i_lhs) * y(S i_lhs) + x(i_lhs) * z(S i_lhs) *)
  
  set (lhs := rr_seq x i_lhs * (rr_seq y (S i_lhs) + rr_seq z (S i_lhs))).
  set (rhs := rr_seq x i_xy * rr_seq y i_xy + rr_seq x i_xz * rr_seq z i_xz).
  
  assert (Hlhs_expand : lhs == rr_seq x i_lhs * rr_seq y (S i_lhs) + 
                               rr_seq x i_lhs * rr_seq z (S i_lhs)).
  { unfold lhs. ring. }
  
  (* Difference: 
     x(i_lhs)*y(S i_lhs) + x(i_lhs)*z(S i_lhs) - x(i_xy)*y(i_xy) - x(i_xz)*z(i_xz)
   = [x(i_lhs)*y(S i_lhs) - x(i_xy)*y(i_xy)] + [x(i_lhs)*z(S i_lhs) - x(i_xz)*z(i_xz)]
  *)
  
  assert (Hdiff : lhs - rhs == 
    (rr_seq x i_lhs * rr_seq y (S i_lhs) - rr_seq x i_xy * rr_seq y i_xy) +
    (rr_seq x i_lhs * rr_seq z (S i_lhs) - rr_seq x i_xz * rr_seq z i_xz)).
  { unfold lhs, rhs. ring. }
  
  (* Each bracket is of the form x_a * y_b - x_c * y_d *)
  (* = (x_a - x_c) * y_b + x_c * (y_b - y_d) *)
  
  (* The gap bounds give |x_a - x_c| < 2/2^{min(a,c)} and similar for y *)
  
  (* By the same analysis as associativity, for large n these are small *)
  
  assert (Htri : Qabs (lhs - rhs) <= 
    Qabs (rr_seq x i_lhs * rr_seq y (S i_lhs) - rr_seq x i_xy * rr_seq y i_xy) +
    Qabs (rr_seq x i_lhs * rr_seq z (S i_lhs) - rr_seq x i_xz * rr_seq z i_xz)).
  { rewrite Hdiff. apply Qabs_triangle. }
  
  (* Each term bounded by O(1/2^n) * bounds *)
  (* For large n >= S k + shifts, this is <= 1/2^k *)
  
  (* The detailed arithmetic follows the same pattern as associativity *)
  (* We have the infrastructure - just need the nia computation *)
  
  (* Rather than duplicate the detailed bound chasing, we note the structure *)
  (* is identical to associativity: decompose products, use gap bounds, *)
  (* show the sum is O(1/2^n) which is <= 1/2^k for n >= S k *)
  
  eapply Qle_trans; [exact Htri|].
  
  (* Use product2_diff_bound for each term *)
  assert (HBx_pos : 0 <= Bx) by (unfold Bx; apply Qlt_le_weak; apply RR_bound_pos).
  assert (HBy_pos : 0 <= By) by (unfold By; apply Qlt_le_weak; apply RR_bound_pos).
  assert (HBz_pos : 0 <= Bz) by (unfold Bz; apply Qlt_le_weak; apply RR_bound_pos).
  assert (Hdelta_pos : 0 <= 2 # pow2 n) by (unfold Qle; simpl; lia).
  
  (* All indices >= n *)
  assert (Hi_lhs_ge : (n <= i_lhs)%nat) by (unfold i_lhs, k_lhs; lia).
  assert (Hi_xy_ge : (n <= i_xy)%nat) by (unfold i_xy, kxy; lia).
  assert (Hi_xz_ge : (n <= i_xz)%nat) by (unfold i_xz, kxz; lia).
  assert (HSi_lhs_ge : (n <= S i_lhs)%nat) by (unfold i_lhs, k_lhs; lia).
  
  (* Bound each term using product2_diff_bound *)
  assert (Hterm1 : Qabs (rr_seq x i_lhs * rr_seq y (S i_lhs) - rr_seq x i_xy * rr_seq y i_xy) <=
                   (2 # pow2 n) * (By + Bx)).
  { apply product2_diff_bound.
    - exact HBx_pos.
    - exact HBy_pos.
    - exact Hdelta_pos.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply general_gap_bound; lia.
    - apply general_gap_bound; lia. }
  
  assert (Hterm2 : Qabs (rr_seq x i_lhs * rr_seq z (S i_lhs) - rr_seq x i_xz * rr_seq z i_xz) <=
                   (2 # pow2 n) * (Bz + Bx)).
  { apply product2_diff_bound.
    - exact HBx_pos.
    - exact HBz_pos.
    - exact Hdelta_pos.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply RR_bounded.
    - apply general_gap_bound; lia.
    - apply general_gap_bound; lia. }
  
  eapply Qle_trans.
  { apply Qplus_le_compat; [exact Hterm1 | exact Hterm2]. }
  
  (* Sum of the two bounds *)
  assert (Hsum : (2 # pow2 n) * (By + Bx) + (2 # pow2 n) * (Bz + Bx) ==
                 (2 # pow2 n) * (By + Bx + Bz + Bx)) by ring.
  rewrite Hsum.
  
  (* Now apply geom_budget *)
  (* We need (2/2^n) * D <= 1/2^k *)
  (* n >= S k + total_shift, and total_shift includes bound_shift(2*D) *)
  
  assert (HD_pos : 0 <= D).
  { unfold D. 
    apply Qle_trans with (0 + 0 + 0 + 0); [unfold Qle; simpl; lia|].
    repeat apply Qplus_le_compat; assumption. }
  
  assert (Hn_ge : (n >= S k + bound_shift (2 * D))%nat).
  { unfold total_shift, k_lhs, kxy, kxz in Hn. lia. }
  
  (* Need to show (2 # pow2 n) * D <= 1 # pow2 k *)
  (* Since n >= S k + bound_shift(2*D), we can use monotonicity *)
  
  remember (S k + bound_shift (2 * D))%nat as m eqn:Hm_eq.
  
  assert (Hm_le_n : (m <= n)%nat) by lia.
  
  assert (Hpow_mono : (pow2 m <= pow2 n)%positive).
  { apply pow2_le_mono. exact Hm_le_n. }
  
  (* (2/2^n) <= (2/2^m) since m <= n, i.e., pow2 m <= pow2 n *)
  assert (Hfrac_mono : 2 # pow2 n <= 2 # pow2 m).
  { unfold Qle. simpl. 
    assert (H : (Z.pos (pow2 m) <= Z.pos (pow2 n))%Z) by lia.
    lia. }
  
  eapply Qle_trans.
  { (* (2/2^n) * D <= (2/2^m) * D *)
    apply Qmult_le_compat_r; [exact Hfrac_mono | exact HD_pos]. }
  
  rewrite Hm_eq.
  apply geom_budget.
  exact HD_pos.
Qed.

Lemma RR_mult_plus_distr_r : forall x y z : RR,
  (x +RR y) *RR z =RR= (x *RR z) +RR (y *RR z).
Proof.
  intros x y z.
  (* Use commutativity and left distributivity *)
  eapply RReq_trans.
  - apply RR_mult_comm.
  - eapply RReq_trans.
    + apply RR_mult_plus_distr_l.
    + (* (z * x) + (z * y) =RR= (x * z) + (y * z) *)
      unfold RReq. intro k.
      exists 0%nat. intros n Hn.
      unfold RR_add, seq_plus, RR_mult, seq_mult. simpl.
      
      (* Both sides compute the same thing up to commutativity in Q *)
      set (kzx := (bound_shift (RR_bound z) + bound_shift (RR_bound x) + 1)%nat).
      set (kzy := (bound_shift (RR_bound z) + bound_shift (RR_bound y) + 1)%nat).
      set (kxz := (bound_shift (RR_bound x) + bound_shift (RR_bound z) + 1)%nat).
      set (kyz := (bound_shift (RR_bound y) + bound_shift (RR_bound z) + 1)%nat).
      
      (* kzx = kxz and kzy = kyz by commutativity of addition *)
      assert (H1 : kzx = kxz) by (unfold kzx, kxz; lia).
      assert (H2 : kzy = kyz) by (unfold kzy, kyz; lia).
      
      rewrite H1, H2.
      
      (* Now the sequences are:
         LHS: z(S n + kxz) * x(S n + kxz) + z(S n + kyz) * y(S n + kyz)
         RHS: x(S n + kxz) * z(S n + kxz) + y(S n + kyz) * z(S n + kyz)
         These are equal by Q commutativity *)
      assert (Heq : 
        rr_seq z (S n + kxz)%nat * rr_seq x (S n + kxz)%nat +
        rr_seq z (S n + kyz)%nat * rr_seq y (S n + kyz)%nat -
        (rr_seq x (S n + kxz)%nat * rr_seq z (S n + kxz)%nat +
         rr_seq y (S n + kyz)%nat * rr_seq z (S n + kyz)%nat) == 0).
      { ring. }
      rewrite (Qabs_eq_zero _ Heq). apply Qabs_zero_le.
Qed.

(* ============================================================================ *)
(*                        PART 15: MORPHISM REGISTRATION                        *)
(* ============================================================================ *)

Add Parametric Relation : RR RReq
  reflexivity proved by RReq_refl
  symmetry proved by RReq_sym
  transitivity proved by RReq_trans
  as RReq_rel.

(* ============================================================================ *)
(*                        VERIFICATION                                          *)
(* ============================================================================ *)

Print Assumptions RReq_Equivalence.
Print Assumptions RR_zero_neq_one.
Print Assumptions RR_zero_lt_one.
Print Assumptions Q_to_RR_add.
Print Assumptions Q_to_RR_le.
Print Assumptions cauchy_add.
Print Assumptions RR_le_dec_Q.
Print Assumptions cauchy_bounded_by_first.
Print Assumptions Q_to_RR_mult.
Print Assumptions RR_mult_0_l.
Print Assumptions RR_mult_comm.
Print Assumptions RR_mult_1_l.
Print Assumptions RR_mult_1_r.
Print Assumptions RReq_shift.

(* Check the ring laws - all fully proven *)
Print Assumptions RR_mult_assoc.
Print Assumptions RR_mult_plus_distr_l.
Print Assumptions RR_mult_plus_distr_r.

(* ============================================================================ *)
(*                        SUMMARY                                               *)
(* ============================================================================ *)

(*
  ═══════════════════════════════════════════════════════════════════════════════
  RELATIONAL REALS - COMPLETE VERSION (GEOMETRIC MODULUS)
  ═══════════════════════════════════════════════════════════════════════════════
  
  ACHIEVEMENT: ZERO AXIOMS, ZERO ADMITS - Complete Ring Structure
  
  FULLY PROVEN:
  ✓ RReq_Equivalence: Equivalence relation on Cauchy sequences
  ✓ RR_zero_neq_one: 0 ≠ 1 in RR
  ✓ RR_zero_lt_one: 0 < 1 in RR  
  ✓ Q_to_RR_add: Q addition embeds
  ✓ Q_to_RR_le: Q order embeds
  ✓ cauchy_add: Sum of Cauchy sequences is Cauchy
  ✓ RR_le_dec_Q: Decidable comparison for Q-embedded values
  ✓ cauchy_bounded_by_first: |f(n)| ≤ |f(0)| + 2 (geometric series bound)
  ✓ Q_to_RR_mult: Q multiplication embeds
  ✓ RR_mult_0_l, RR_mult_0_r: Zero annihilates multiplication
  ✓ RR_mult_comm: Multiplication is commutative
  ✓ RR_mult_1_l, RR_mult_1_r: Multiplicative identity
  ✓ RR_mult_assoc: Multiplication is associative
  ✓ RR_mult_plus_distr_l: Left distributivity
  ✓ RR_mult_plus_distr_r: Right distributivity
  
  SHIFT INFRASTRUCTURE:
  ✓ is_cauchy_geo_shift: Shifted sequences remain Cauchy
  ✓ RR_shift: Shift operator on RR
  ✓ geometric_sum_bound: |f(n+s) - f(n)| ≤ 2/2^n - 2/2^{n+s}
  ✓ cauchy_gap_bound: |f(n+s) - f(n)| < 2/2^n
  ✓ RReq_shift: Shifted sequence equivalent to original
  
  KEY HELPER LEMMAS:
  ✓ product_diff_bound: |abc - def| ≤ δ(BᵧBᵤ + BₓBᵤ + BₓBᵧ)
  ✓ product2_diff_bound: |ab - cd| ≤ δ(Bᵦ + Bₐ)
  ✓ general_gap_bound: |f(i) - f(j)| ≤ 2/2^n when i,j ≥ n
  ✓ geom_budget: (2/2^(S k + bound_shift(2C))) * C ≤ 1/2^k
  ✓ pow2_S_k_s: pow2(S k + s) = 2 * pow2 k * pow2 s
  
  ═══════════════════════════════════════════════════════════════════════════════
  COMPLETE COMMUTATIVE RING WITH IDENTITY
  69 lemmas proven with Qed | 0 admits | 0 axioms
  ═══════════════════════════════════════════════════════════════════════════════
*)
