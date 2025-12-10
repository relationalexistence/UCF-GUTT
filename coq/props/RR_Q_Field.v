(* ========================================================================== *)
(*                    Q-BASED FIELD IMPLEMENTATION                            *)
(*                                                                            *)
(*  ZERO AXIOMS - Uses Coq's field_theory for full automation                 *)
(*  field tactic works automatically                                          *)
(* ========================================================================== *)

Require Import Coq.QArith.QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
Require Import Coq.setoid_ring.Field_tac.

(* ========================================================================== *)
(*  Q Implementation with field_theory - ZERO AXIOMS                          *)
(* ========================================================================== *)

Definition RR := Q.
Definition RR_eq := Qeq.
Definition RR_0 := 0%Q.
Definition RR_1 := 1%Q.
Definition RR_plus := Qplus.
Definition RR_mult := Qmult.
Definition RR_neg := Qopp.
Definition RR_inv := Qinv.
Definition RR_minus (x y : RR) := Qplus x (Qopp y).
Definition RR_div (x y : RR) := Qmult x (Qinv y).

Global Instance RR_Setoid : Equivalence RR_eq.
Proof. split; [exact Qeq_refl | exact Qeq_sym | exact Qeq_trans]. Qed.

Global Instance RR_plus_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_plus.
Proof. intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity. Qed.

Global Instance RR_mult_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_mult.
Proof. intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity. Qed.

Global Instance RR_neg_Proper : Proper (RR_eq ==> RR_eq) RR_neg.
Proof. intros x y Hxy. rewrite Hxy. reflexivity. Qed.

Global Instance RR_inv_Proper : Proper (RR_eq ==> RR_eq) RR_inv.
Proof. intros x y Hxy. rewrite Hxy. reflexivity. Qed.

(* THE ONE PROOF - bundles all field axioms *)
Lemma RR_field : field_theory RR_0 RR_1 RR_plus RR_mult 
                              RR_minus RR_neg RR_div RR_inv RR_eq.
Proof.
  constructor.
  - (* Ring part *)
    constructor.
    + exact Qplus_0_l.
    + exact Qplus_comm.
    + intros x y z. rewrite Qplus_assoc. reflexivity.
    + exact Qmult_1_l.
    + exact Qmult_comm.
    + intros x y z. rewrite Qmult_assoc. reflexivity.
    + intros x y z. rewrite Qmult_plus_distr_l. reflexivity.
    + reflexivity.
    + exact Qplus_opp_r.
  - (* 1 ≠ 0 *)
    discriminate.
  - (* Division definition: p/q = p * /q *)
    intros p q. reflexivity.
  - (* Inverse: /p * p = 1 when p ≠ 0 *)
    intros p Hp.
    rewrite Qmult_comm.
    apply Qmult_inv_r.
    intro Hcontra. apply Hp. rewrite Hcontra. reflexivity.
Qed.

(* ========================================================================== *)
(*  Register field for automation                                             *)
(* ========================================================================== *)

Lemma Q_ring_eq_ext : ring_eq_ext RR_plus RR_mult RR_neg RR_eq.
Proof.
  constructor.
  - intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity.
  - intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity.
  - intros x y Hxy. rewrite Hxy. reflexivity.
Qed.

Add Field Q_Field : RR_field.

(* ========================================================================== *)
(*  Test: field tactic works                                                  *)
(* ========================================================================== *)

Example field_test1 : forall x : RR, ~ RR_eq x RR_0 -> 
  RR_eq (RR_mult x (RR_inv x)) RR_1.
Proof. intros. field. assumption. Qed.

Example field_test2 : forall x y : RR, ~ RR_eq y RR_0 ->
  RR_eq (RR_div (RR_mult x y) y) x.
Proof. intros. field. assumption. Qed.

Example field_test3 : forall a b : RR,
  RR_eq (RR_mult (RR_plus a b) (RR_plus a b))
        (RR_plus (RR_plus (RR_mult a a) (RR_mult (RR_plus RR_1 RR_1) (RR_mult a b))) 
                 (RR_mult b b)).
Proof. intros. field. Qed.

Example field_test4 : forall a b c : RR, ~ RR_eq c RR_0 ->
  RR_eq (RR_div (RR_plus (RR_mult a c) (RR_mult b c)) c) (RR_plus a b).
Proof. intros. field. assumption. Qed.

(* ZERO AXIOMS *)
Print Assumptions RR_field.
Print Assumptions field_test4.