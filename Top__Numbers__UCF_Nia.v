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
  |                    Top__Numbers__UCF_Nia.v                               |
  |                                                                          |
  |       UCF/GUTT Relational Arithmetic: Nonlinear Q Lemmas                 |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-27                                                     |
  |  COMPATIBILITY: Coq 8.18+                                                |
  |                                                                          |
  |  PURPOSE: Provide auditable lemmas for NONLINEAR Q arithmetic that       |
  |  the nia tactic cannot handle reliably. Complements UCF_Lia.v.           |
  |                                                                          |
  |  KEY INSIGHT: nia often fails on Q inequalities because:                 |
  |    1. Q operations unfold to complex Z/positive expressions              |
  |    2. Products of Q values create polynomial constraints                 |
  |    3. The witness search space grows exponentially                       |
  |                                                                          |
  |  SOLUTION: Prove lemmas once using destruct/unfold/simpl/lia pattern,    |
  |  then apply named lemmas instead of nia.                                 |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Q Product Bounds                                          |
  |    SECTION 2:  Q Power Functions                                         |
  |    SECTION 3:  Q Division Bounds                                         |
  |    SECTION 4:  Q Exponential vs Linear Bounds                            |
  |    SECTION 5:  Unified API                                               |
  |    SECTION 6:  Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                            |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.

(* Import linear arithmetic library *)
Require Import Top__Numbers__UCF_Lia.

Open Scope Q_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: Q PRODUCT BOUNDS                             *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION:
  
  Products in UCF/GUTT represent INTER-SET compositions - relating
  quantities across different domains. Product bounds capture how
  composed relations preserve ordering structure.
*)

Module Q_Product_Bounds.

  (** Core product bound: 0 <= a <= b, 0 <= c <= d -> a*c <= b*d *)
  Theorem prod_le_compat : forall a b c d : Q,
    0 <= a -> a <= b -> 0 <= c -> c <= d -> a * c <= b * d.
  Proof.
    intros a b c d Ha Hab Hc Hcd.
    apply Qmult_le_compat_nonneg.
    - split; assumption.
    - split; assumption.
  Qed.

  (** Square bound: 0 <= a <= b -> a*a <= b*b *)
  Theorem sq_le_compat : forall a b : Q,
    0 <= a -> a <= b -> a * a <= b * b.
  Proof.
    intros a b Ha Hab.
    (* Need: 0 <= a, a <= b, 0 <= a, a <= b *)
    apply prod_le_compat.
    - exact Ha.
    - exact Hab.
    - exact Ha.
    - exact Hab.
  Qed.

  (** Square is monotone for non-negatives *)
  Theorem sq_mono_nonneg : forall a b : Q,
    0 <= a -> 0 <= b -> a <= b -> a * a <= b * b.
  Proof.
    intros a b Ha Hb Hab.
    apply sq_le_compat; assumption.
  Qed.

  (** Product with self bound: a >= 1 -> a <= a * a *)
  Theorem le_self_sq : forall a : Q, 1 <= a -> a <= a * a.
  Proof.
    intros a Ha.
    rewrite <- (Qmult_1_l a) at 1.
    apply Qmult_le_r.
    - apply Qlt_le_trans with 1. reflexivity. exact Ha.
    - exact Ha.
  Qed.

  (** Bound transfer through product: a*b <= c, 0 < b, c/b <= d -> a <= d *)
  Theorem prod_bound_transfer : forall a b c : Q,
    0 < b -> a * b <= c -> a <= c / b.
  Proof.
    intros a b c Hb Hab.
    unfold Qdiv.
    apply Qmult_le_r with b.
    - exact Hb.
    - setoid_replace (c * / b * b) with c.
      + exact Hab.
      + field. intro Heq. rewrite Heq in Hb. 
        apply (Qlt_irrefl 0). exact Hb.
  Qed.

End Q_Product_Bounds.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: Q POWER FUNCTIONS                            *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION:
  
  Powers represent ITERATED self-composition of relations.
  4^n in the context of sqrt(2) captures the quadratic convergence
  rate of the Babylonian method - each iteration squares the error.
*)

Module Q_Powers.

  (** Power of 4 *)
  Fixpoint Qpow4 (n : nat) : Q :=
    match n with
    | O => 1
    | S m => 4 * Qpow4 m
    end.

  (** Power of 2 *)
  Fixpoint Qpow2 (n : nat) : Q :=
    match n with
    | O => 1
    | S m => 2 * Qpow2 m
    end.

  (** 4^n > 0 *)
  Lemma Qpow4_pos : forall n : nat, 0 < Qpow4 n.
  Proof.
    induction n as [| m IH].
    - simpl. reflexivity.
    - simpl. apply Qmult_lt_0_compat. reflexivity. exact IH.
  Qed.

  (** 2^n > 0 *)
  Lemma Qpow2_pos : forall n : nat, 0 < Qpow2 n.
  Proof.
    induction n as [| m IH].
    - simpl. reflexivity.
    - simpl. apply Qmult_lt_0_compat. reflexivity. exact IH.
  Qed.

  (** 4^n >= 1 *)
  Lemma Qpow4_ge_1 : forall n : nat, 1 <= Qpow4 n.
  Proof.
    induction n as [| m IH].
    - simpl. apply Qle_refl.
    - simpl. 
      (* Goal: 1 <= 4 * Qpow4 m *)
      (* Since Qpow4 m >= 1, we have 4 * Qpow4 m >= 4 >= 1 *)
      apply Qle_trans with (4 * 1).
      + unfold Qle. simpl. lia.
      + apply Qmult_le_l. reflexivity. exact IH.
  Qed.

  (** 2^n >= 1 *)
  Lemma Qpow2_ge_1 : forall n : nat, 1 <= Qpow2 n.
  Proof.
    induction n as [| m IH].
    - simpl. apply Qle_refl.
    - simpl.
      (* Goal: 1 <= 2 * Qpow2 m *)
      apply Qle_trans with (2 * 1).
      + unfold Qle. simpl. lia.
      + apply Qmult_le_l. reflexivity. exact IH.
  Qed.

  (** 4^n = (2^n)^2 *)
  Lemma Qpow4_eq_Qpow2_sq : forall n : nat, Qpow4 n == Qpow2 n * Qpow2 n.
  Proof.
    induction n as [| m IH].
    - simpl. ring.
    - simpl. rewrite IH. ring.
  Qed.

  (** 4^(n+1) = 4 * 4^n *)
  Lemma Qpow4_succ : forall n : nat, Qpow4 (S n) == 4 * Qpow4 n.
  Proof.
    intro n. simpl. apply Qeq_refl.
  Qed.

  (** 4^n >= n+1 - KEY LEMMA for exponential vs linear bounds *)
  Lemma Qpow4_ge_nat : forall n : nat, inject_Z (Z.of_nat (S n)) <= Qpow4 n.
  Proof.
    induction n as [| m IH].
    - simpl. apply Qle_refl.
    - simpl.
      (* Goal: S (S m) <= 4 * Qpow4 m *)
      (* IH: S m <= Qpow4 m *)
      (* 4 * Qpow4 m >= 4 * (S m) = 4m + 4 >= m + 2 = S (S m) for m >= 0 *)
      apply Qle_trans with (4 * inject_Z (Z.of_nat (S m))).
      + (* S (S m) <= 4 * (S m) *)
        unfold Qle, Qmult, inject_Z. simpl.
        rewrite !Pos.mul_1_r.
        lia.
      + apply Qmult_le_l. reflexivity. exact IH.
  Qed.

  (** 2 * 4^n >= n + 2 *)
  Lemma two_Qpow4_ge_nat_plus_2 : forall n : nat, 
    inject_Z (Z.of_nat (S (S n))) <= 2 * Qpow4 n.
  Proof.
    intro n.
    (* n+2 <= 2 * 4^n *)
    (* From Qpow4_ge_nat: 4^n >= n+1 *)
    (* So 2 * 4^n >= 2*(n+1) = 2n+2 >= n+2 *)
    apply Qle_trans with (2 * inject_Z (Z.of_nat (S n))).
    - (* n+2 <= 2*(n+1) = 2n+2 *)
      unfold Qle, Qmult, inject_Z. simpl. lia.
    - apply Qmult_le_l. reflexivity.
      apply Qpow4_ge_nat.
  Qed.

  (** Monotonicity: m <= n -> 4^m <= 4^n *)
  Lemma Qpow4_mono : forall m n : nat, (m <= n)%nat -> Qpow4 m <= Qpow4 n.
  Proof.
    intros m n Hmn.
    induction Hmn as [| k Hmk IH].
    - apply Qle_refl.
    - apply Qle_trans with (Qpow4 k).
      + exact IH.
      + simpl. rewrite <- (Qmult_1_l (Qpow4 k)) at 1.
        apply Qmult_le_r.
        * apply Qpow4_pos.
        * unfold Qle. simpl. lia.
  Qed.

End Q_Powers.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: Q DIVISION BOUNDS                            *)
(*                                                                            *)
(* ========================================================================== *)

Module Q_Division_Bounds.

  (** Division bound: a/b <= c/d when a*d <= c*b and b,d > 0 *)
  Lemma div_le_div : forall a b c d : Q,
    0 < b -> 0 < d -> a * d <= c * b -> a / b <= c / d.
  Proof.
    intros a b c d Hb Hd Habc.
    unfold Qdiv.
    apply Qmult_le_r with b.
    - exact Hb.
    - apply Qmult_le_r with d.
      + exact Hd.
      + setoid_replace (a * / b * b * d) with (a * d).
        * setoid_replace (c * / d * b * d) with (c * b).
          -- exact Habc.
          -- field. intro Heq. rewrite Heq in Hd.
             apply (Qlt_irrefl 0). exact Hd.
        * field. intro Heq. rewrite Heq in Hb.
          apply (Qlt_irrefl 0). exact Hb.
  Qed.

  (** 1/(a*b) = (1/a) * (1/b) for nonzero a, b *)
  Lemma Qinv_mult_distr : forall a b : Q,
    ~ a == 0 -> ~ b == 0 -> / (a * b) == / a * / b.
  Proof.
    intros a b Ha Hb.
    field. split; assumption.
  Qed.

  (** Division by larger denominator gives smaller result *)
  Lemma div_denom_mono : forall a b c : Q,
    0 <= a -> 0 < b -> b <= c -> a / c <= a / b.
  Proof.
    intros a b c Ha Hb Hbc.
    destruct (Qle_lt_or_eq _ _ Ha) as [Hapos | Hazero].
    - (* a > 0 case *)
      unfold Qdiv.
      apply Qmult_le_l. exact Hapos.
      apply UCF.Q_inv_le_contravar. exact Hb. exact Hbc.
    - (* a == 0 case *)
      setoid_rewrite <- Hazero.
      setoid_rewrite Qmult_0_l. apply Qle_refl.
  Qed.

  (** Key lemma: a / (b * c) <= a / b when c >= 1 and b > 0 *)
  Lemma div_prod_le : forall a b c : Q,
    0 <= a -> 0 < b -> 1 <= c -> a / (b * c) <= a / b.
  Proof.
    intros a b c Ha Hb Hc.
    apply div_denom_mono.
    - exact Ha.
    - exact Hb.
    - rewrite <- (Qmult_1_r b) at 1.
      apply Qmult_le_l. exact Hb. exact Hc.
  Qed.

End Q_Division_Bounds.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: EXPONENTIAL VS LINEAR BOUNDS                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION:
  
  These lemmas capture the fundamental relationship between exponential
  growth (from quadratic convergence) and linear growth (for Cauchy bounds).
  The exponential always eventually dominates the linear, ensuring convergence.
*)

Module Q_Exp_Linear.

  Import Q_Powers.

  (** The key bound for Cauchy sequences: 1/(2*4^n) <= 1/(n+2) *)
  Lemma inv_two_pow4_le_inv_nat : forall n : nat,
    / (2 * Qpow4 n) <= / inject_Z (Z.of_nat (S (S n))).
  Proof.
    intro n.
    apply UCF.Q_inv_le_contravar.
    - (* 0 < n+2 *)
      unfold Qlt, inject_Z. simpl. lia.
    - (* n+2 <= 2 * 4^n *)
      apply two_Qpow4_ge_nat_plus_2.
  Qed.

  (** Corollary: (1/4^n)/2 <= 1/(n+2) *)
  Lemma Qpow4_inv_half_le_inv_nat : forall n : nat,
    (1 / Qpow4 n) / 2 <= / inject_Z (Z.of_nat (S (S n))).
  Proof.
    intro n.
    unfold Qdiv.
    setoid_replace (1 * / Qpow4 n * / 2) with (/ (2 * Qpow4 n)).
    - apply inv_two_pow4_le_inv_nat.
    - field. intro Hcontra.
      pose proof (Qpow4_pos n) as Hp.
      unfold Qeq in Hcontra. unfold Qlt in Hp.
      destruct (Qpow4 n) as [pn pd]. simpl in *. lia.
  Qed.

  (** Extended bound: a <= 1/4^n, 0 <= a -> a/2 <= 1/(n+2) *)
  Lemma bound_half_le_inv_nat : forall a : Q, forall n : nat,
    0 <= a -> a <= 1 / Qpow4 n -> a / 2 <= / inject_Z (Z.of_nat (S (S n))).
  Proof.
    intros a n Ha Hbound.
    apply Qle_trans with ((1 / Qpow4 n) / 2).
    - unfold Qdiv.
      apply Qmult_le_compat_nonneg.
      + split. exact Ha. exact Hbound.
      + split. unfold Qle. simpl. lia. apply Qle_refl.
    - apply Qpow4_inv_half_le_inv_nat.
  Qed.

End Q_Exp_Linear.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: UNIFIED API                                  *)
(*                                                                            *)
(* ========================================================================== *)

Module UCF_Nia.

  (* Product bounds *)
  Definition Q_prod_le_compat := Q_Product_Bounds.prod_le_compat.
  Definition Q_sq_le_compat := Q_Product_Bounds.sq_le_compat.
  Definition Q_sq_mono_nonneg := Q_Product_Bounds.sq_mono_nonneg.
  Definition Q_le_self_sq := Q_Product_Bounds.le_self_sq.

  (* Powers *)
  Definition Qpow4 := Q_Powers.Qpow4.
  Definition Qpow2 := Q_Powers.Qpow2.
  Definition Qpow4_pos := Q_Powers.Qpow4_pos.
  Definition Qpow2_pos := Q_Powers.Qpow2_pos.
  Definition Qpow4_ge_1 := Q_Powers.Qpow4_ge_1.
  Definition Qpow2_ge_1 := Q_Powers.Qpow2_ge_1.
  Definition Qpow4_ge_nat := Q_Powers.Qpow4_ge_nat.
  Definition Qpow4_mono := Q_Powers.Qpow4_mono.
  Definition two_Qpow4_ge_nat_plus_2 := Q_Powers.two_Qpow4_ge_nat_plus_2.

  (* Division bounds *)
  Definition Q_div_le_div := Q_Division_Bounds.div_le_div.
  Definition Q_div_denom_mono := Q_Division_Bounds.div_denom_mono.
  Definition Q_div_prod_le := Q_Division_Bounds.div_prod_le.
  Definition Qinv_mult_distr := Q_Division_Bounds.Qinv_mult_distr.

  (* Exponential vs linear *)
  Definition inv_two_pow4_le_inv_nat := Q_Exp_Linear.inv_two_pow4_le_inv_nat.
  Definition Qpow4_inv_half_le_inv_nat := Q_Exp_Linear.Qpow4_inv_half_le_inv_nat.
  Definition bound_half_le_inv_nat := Q_Exp_Linear.bound_half_le_inv_nat.

End UCF_Nia.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: AXIOM AUDIT                                  *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit_Nia.

  Import UCF_Nia.

  (* Test: Product bounds *)
  Goal forall a : Q, 0 <= a -> a <= 1 -> a * a <= 1.
  Proof.
    intros a Ha Hab.
    setoid_replace 1 with (1 * 1) by ring.
    apply Q_sq_le_compat. exact Ha. exact Hab.
  Qed.

  (* Test: Power lemmas *)
  Goal forall n : nat, 0 < Qpow4 n.
  Proof. intro. apply Qpow4_pos. Qed.

  Goal forall n : nat, 1 <= Qpow4 n.
  Proof. intro. apply Qpow4_ge_1. Qed.

  Goal forall n : nat, inject_Z (Z.of_nat (S n)) <= Qpow4 n.
  Proof. intro. apply Qpow4_ge_nat. Qed.

  (* Test: Key Cauchy bound *)
  Goal forall n : nat, / (2 * Qpow4 n) <= / inject_Z (Z.of_nat (S (S n))).
  Proof. intro. apply inv_two_pow4_le_inv_nat. Qed.

  (* Test: Extended bound *)
  Goal forall a : Q, forall n : nat,
    0 <= a -> a <= 1 / Qpow4 n -> a / 2 <= / inject_Z (Z.of_nat (S (S n))).
  Proof.
    intros. apply bound_half_le_inv_nat; assumption.
  Qed.

End AxiomAudit_Nia.

(* ========================================================================== *)
(*                                                                            *)
(*                    PRINT DEPENDENCIES                                      *)
(*                                                                            *)
(* ========================================================================== *)

Print Assumptions UCF_Nia.bound_half_le_inv_nat.
(* Expected: Closed under the global context (no axioms) *)
