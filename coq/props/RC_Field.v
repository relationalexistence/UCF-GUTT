(* ========================================================================== *)
(*                    RELATIONAL COMPLEX NUMBERS - FIELD VERSION              *)
(*                                                                            *)
(*  Complex numbers over Q using field_theory                                 *)
(*  All algebraic proofs become ONE LINE with ring/field tactic               *)
(*  ZERO AXIOMS                                                               *)
(* ========================================================================== *)

Require Import Coq.QArith.QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
Require Import Coq.setoid_ring.Field_tac.
Require Import RR_Q_Field.

(* ========================================================================== *)
(*  Complex Number Type                                                       *)
(* ========================================================================== *)

Record RC : Type := mkRC { re : RR; im : RR }.

Definition RC_eq (z w : RC) : Prop :=
  RR_eq (re z) (re w) /\ RR_eq (im z) (im w).

Notation "z =C= w" := (RC_eq z w) (at level 70, no associativity).

Global Instance RC_Setoid : Equivalence RC_eq.
Proof.
  split; red; unfold RC_eq.
  - intros [r i]; split; reflexivity.
  - intros [r1 i1] [r2 i2] [Hr Hi]; split; symmetry; assumption.
  - intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; 
    split; etransitivity; eauto.
Qed.

(* ========================================================================== *)
(*  Constants                                                                 *)
(* ========================================================================== *)

Definition RC_0 : RC := mkRC RR_0 RR_0.
Definition RC_1 : RC := mkRC RR_1 RR_0.
Definition RC_i : RC := mkRC RR_0 RR_1.

(* ========================================================================== *)
(*  Operations                                                                *)
(* ========================================================================== *)

Definition RC_add (z w : RC) : RC :=
  mkRC (RR_plus (re z) (re w)) (RR_plus (im z) (im w)).

Definition RC_neg (z : RC) : RC :=
  mkRC (RR_neg (re z)) (RR_neg (im z)).

(* Use explicit subtraction to help field tactic *)
Definition RC_mult (z w : RC) : RC :=
  mkRC (RR_plus (RR_mult (re z) (re w)) (RR_neg (RR_mult (im z) (im w))))
       (RR_plus (RR_mult (re z) (im w)) (RR_mult (im z) (re w))).

Definition RC_conj (z : RC) : RC :=
  mkRC (re z) (RR_neg (im z)).

Definition RC_norm_sq (z : RC) : RR :=
  RR_plus (RR_mult (re z) (re z)) (RR_mult (im z) (im z)).

Notation "z +C w" := (RC_add z w) (at level 50, left associativity).
Notation "z *C w" := (RC_mult z w) (at level 40, left associativity).
Notation "-C z" := (RC_neg z) (at level 35, right associativity).

(* ========================================================================== *)
(*  ALGEBRAIC PROOFS - ALL ONE LINE WITH RING TACTIC                          *)
(* ========================================================================== *)

Lemma RC_add_comm : forall z w, z +C w =C= w +C z.
Proof. intros [zr zi] [wr wi]. unfold RC_eq, RC_add; simpl. split; ring. Qed.

Lemma RC_add_assoc : forall x y z, (x +C y) +C z =C= x +C (y +C z).
Proof. intros [xr xi] [yr yi] [zr zi]. unfold RC_eq, RC_add; simpl. split; ring. Qed.

Lemma RC_add_0_l : forall z, RC_0 +C z =C= z.
Proof. intros [zr zi]. unfold RC_eq, RC_add, RC_0; simpl. split; ring. Qed.

Lemma RC_add_neg_r : forall z, z +C (-C z) =C= RC_0.
Proof. intros [zr zi]. unfold RC_eq, RC_add, RC_neg, RC_0; simpl. split; ring. Qed.

Lemma RC_mult_comm : forall z w, z *C w =C= w *C z.
Proof. intros [zr zi] [wr wi]. unfold RC_eq, RC_mult; simpl. split; ring. Qed.

Lemma RC_mult_assoc : forall x y z, (x *C y) *C z =C= x *C (y *C z).
Proof. intros [xr xi] [yr yi] [zr zi]. unfold RC_eq, RC_mult; simpl. split; ring. Qed.

Lemma RC_mult_1_l : forall z, RC_1 *C z =C= z.
Proof. intros [zr zi]. unfold RC_eq, RC_mult, RC_1; simpl. split; ring. Qed.

Lemma RC_distr_l : forall x y z, x *C (y +C z) =C= (x *C y) +C (x *C z).
Proof. intros [xr xi] [yr yi] [zr zi]. unfold RC_eq, RC_mult, RC_add; simpl. split; ring. Qed.

(* ========================================================================== *)
(*  Key Properties - ALL ONE LINE                                             *)
(* ========================================================================== *)

Lemma RC_i_squared : RC_i *C RC_i =C= -C RC_1.
Proof. unfold RC_eq, RC_mult, RC_i, RC_1, RC_neg; simpl. split; ring. Qed.

Lemma RC_mult_conj : forall z, z *C (RC_conj z) =C= mkRC (RC_norm_sq z) RR_0.
Proof. intros [zr zi]. unfold RC_eq, RC_mult, RC_conj, RC_norm_sq; simpl. split; ring. Qed.

Lemma RC_norm_sq_mult : forall z w,
  RR_eq (RC_norm_sq (z *C w)) (RR_mult (RC_norm_sq z) (RC_norm_sq w)).
Proof. intros [zr zi] [wr wi]. unfold RC_mult, RC_norm_sq; simpl. ring. Qed.

(* ========================================================================== *)
(*  ZERO AXIOMS CHECK                                                         *)
(* ========================================================================== *)

Print Assumptions RC_mult_assoc.
Print Assumptions RC_i_squared.
Print Assumptions RC_norm_sq_mult.