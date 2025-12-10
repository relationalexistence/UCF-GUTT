(* ========================================================================== *)
(*                    Q-BASED RR IMPLEMENTATION                               *)
(*                                                                            *)
(*  Implements RR_Interface using rational numbers (Q)                        *)
(*  Used for lightweight testing without full Cauchy machinery               *)
(* ========================================================================== *)

Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import RelationalRR_Interface.

Module RR_Q <: RR_Interface.

  Definition RR := Q.
  Definition RR_eq := Qeq.
  Definition RR_zero := 0%Q.
  Definition RR_one := 1%Q.
  Definition RR_add := Qplus.
  Definition RR_mult := Qmult.
  Definition RR_neg := Qopp.

  (* ===== Equivalence Instance ===== *)
  
  Global Instance RR_Setoid : Equivalence RR_eq.
  Proof.
    split.
    - exact Qeq_refl.
    - exact Qeq_sym.
    - exact Qeq_trans.
  Qed.
  
  (* ===== Morphism Instances ===== *)
  
  Global Instance RR_add_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_add.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold RR_add. rewrite Hx, Hy. reflexivity.
  Qed.
  
  Global Instance RR_mult_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_mult.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold RR_mult. rewrite Hx, Hy. reflexivity.
  Qed.
  
  Global Instance RR_neg_Proper : Proper (RR_eq ==> RR_eq) RR_neg.
  Proof.
    intros x y Hxy.
    unfold RR_neg. rewrite Hxy. reflexivity.
  Qed.

  (* ===== Ring Axioms ===== *)
  
  Lemma RR_add_comm : forall x y, RR_eq (RR_add x y) (RR_add y x).
  Proof. intros. apply Qplus_comm. Qed.
  
  Lemma RR_add_assoc : forall x y z, 
    RR_eq (RR_add (RR_add x y) z) (RR_add x (RR_add y z)).
  Proof. intros. symmetry. apply Qplus_assoc. Qed.
  
  Lemma RR_add_0_l : forall x, RR_eq (RR_add RR_zero x) x.
  Proof. intros. apply Qplus_0_l. Qed.
  
  Lemma RR_add_neg_l : forall x, RR_eq (RR_add (RR_neg x) x) RR_zero.
  Proof. intros. rewrite Qplus_comm. apply Qplus_opp_r. Qed.
  
  Lemma RR_mult_comm : forall x y, RR_eq (RR_mult x y) (RR_mult y x).
  Proof. intros. apply Qmult_comm. Qed.
  
  Lemma RR_mult_assoc : forall x y z, 
    RR_eq (RR_mult (RR_mult x y) z) (RR_mult x (RR_mult y z)).
  Proof. intros. symmetry. apply Qmult_assoc. Qed.
  
  Lemma RR_mult_1_l : forall x, RR_eq (RR_mult RR_one x) x.
  Proof. intros. apply Qmult_1_l. Qed.
  
  Lemma RR_distr_l : forall x y z, 
    RR_eq (RR_mult x (RR_add y z)) (RR_add (RR_mult x y) (RR_mult x z)).
  Proof. intros. apply Qmult_plus_distr_r. Qed.

  (* ===== Derived Lemmas ===== *)
  
  Lemma RR_add_0_r : forall x, RR_eq (RR_add x RR_zero) x.
  Proof. intros. rewrite Qplus_comm. apply Qplus_0_l. Qed.
  
  Lemma RR_add_neg_r : forall x, RR_eq (RR_add x (RR_neg x)) RR_zero.
  Proof. intros. apply Qplus_opp_r. Qed.
  
  Lemma RR_mult_1_r : forall x, RR_eq (RR_mult x RR_one) x.
  Proof. intros. rewrite Qmult_comm. apply Qmult_1_l. Qed.
  
  Lemma RR_distr_r : forall x y z,
    RR_eq (RR_mult (RR_add x y) z) (RR_add (RR_mult x z) (RR_mult y z)).
  Proof. intros. apply Qmult_plus_distr_l. Qed.
  
  Lemma RR_mult_0_l : forall x, RR_eq (RR_mult RR_zero x) RR_zero.
  Proof. intros. rewrite Qmult_0_l. reflexivity. Qed.
  
  Lemma RR_mult_0_r : forall x, RR_eq (RR_mult x RR_zero) RR_zero.
  Proof. intros. rewrite Qmult_0_r. reflexivity. Qed.
  
  Lemma RR_neg_0 : RR_eq (RR_neg RR_zero) RR_zero.
  Proof. reflexivity. Qed.
  
  Lemma RR_neg_invol : forall x, RR_eq (RR_neg (RR_neg x)) x.
  Proof. intros. apply Qopp_involutive. Qed.
  
  Lemma RR_neg_add : forall x y, 
    RR_eq (RR_neg (RR_add x y)) (RR_add (RR_neg x) (RR_neg y)).
  Proof. intros. apply Qopp_plus. Qed.
  
  Lemma RR_neg_mult_l : forall x y, 
    RR_eq (RR_mult (RR_neg x) y) (RR_neg (RR_mult x y)).
  Proof. 
    intros [xn xd] [yn yd]. unfold RR_neg, RR_mult, RR_eq, Qopp, Qmult.
    unfold Qeq. simpl. ring.
  Qed.
  
  Lemma RR_neg_mult_r : forall x y, 
    RR_eq (RR_mult x (RR_neg y)) (RR_neg (RR_mult x y)).
  Proof. 
    intros [xn xd] [yn yd]. unfold RR_neg, RR_mult, RR_eq, Qopp, Qmult.
    unfold Qeq. simpl. ring.
  Qed.
  
  Lemma RR_neg_neg_mult : forall x y, 
    RR_eq (RR_mult (RR_neg x) (RR_neg y)) (RR_mult x y).
  Proof. 
    intros [xn xd] [yn yd]. unfold RR_neg, RR_mult, RR_eq, Qopp, Qmult.
    unfold Qeq. simpl. ring.
  Qed.

End RR_Q.

(* ========================================================================== *)
(*  Instantiate RC over Q for testing                                         *)
(* ========================================================================== *)

Require Import Relationalcomplex_algebraic.

Module RC_Q := RC_Algebraic(RR_Q).

(* Verification checks *)
Check RC_Q.RC.
Check RC_Q.RC_i_squared.
Check RC_Q.RC_mult_conj.

(* Example computations *)
Definition z1 : RC_Q.RC := RC_Q.mkRC (1#1)%Q (2#1)%Q.  (* 1 + 2i *)
Definition z2 : RC_Q.RC := RC_Q.mkRC (3#1)%Q (4#1)%Q.  (* 3 + 4i *)

(* z1 * z2 = (1+2i)(3+4i) = 3+4i+6i+8i^2 = 3+10i-8 = -5+10i *)
Eval compute in RC_Q.RC_mult z1 z2.

(* |z1|^2 = 1^2 + 2^2 = 5 *)
Eval compute in RC_Q.RC_norm_sq z1.

(* |z2|^2 = 3^2 + 4^2 = 25 *)
Eval compute in RC_Q.RC_norm_sq z2.