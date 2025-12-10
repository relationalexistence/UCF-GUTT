(* ========================================================================== *)
(*                    RELATIONAL REALS INTERFACE                              *)
(*                                                                            *)
(*  Module type specifying the abstract interface for Relational Real Numbers *)
(*  Any implementation (Q, Cauchy sequences, Dedekind cuts) can instantiate   *)
(*                                                                            *)
(*  This is the foundation layer for the UCF/GUTT numeric tower:             *)
(*  N_rel -> Z_rel -> Q_rel -> RR -> RC -> Tensor_RC                          *)
(* ========================================================================== *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Module Type RR_Interface.

  (* ===== Carrier type and equality ===== *)
  
  Parameter RR : Type.
  Parameter RR_eq : RR -> RR -> Prop.
  
  (* ===== 1. Equivalence Relation (as Instance for rewriting) ===== *)
  
  Declare Instance RR_Setoid : Equivalence RR_eq.
  
  (* ===== 2. Constants ===== *)
  
  Parameter RR_zero : RR.
  Parameter RR_one  : RR.
  
  (* ===== 3. Operations ===== *)
  
  Parameter RR_add  : RR -> RR -> RR.
  Parameter RR_mult : RR -> RR -> RR.
  Parameter RR_neg  : RR -> RR.
  
  (* ===== Notations ===== *)
  
  Infix "=RR=" := RR_eq (at level 70, no associativity).
  Notation "0RR" := RR_zero.
  Notation "1RR" := RR_one.
  Infix "+RR" := RR_add (at level 50, left associativity).
  Infix "*RR" := RR_mult (at level 40, left associativity).
  Notation "-RR x" := (RR_neg x) (at level 35, right associativity).

  (* ===== 4. Morphisms (allows rewriting with =RR=) ===== *)
  
  Declare Instance RR_add_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_add.
  Declare Instance RR_mult_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_mult.
  Declare Instance RR_neg_Proper : Proper (RR_eq ==> RR_eq) RR_neg.

  (* ===== 5. Ring Axioms ===== *)
  
  (* Additive group *)
  Axiom RR_add_comm  : forall x y, (x +RR y) =RR= (y +RR x).
  Axiom RR_add_assoc : forall x y z, ((x +RR y) +RR z) =RR= (x +RR (y +RR z)).
  Axiom RR_add_0_l   : forall x, (0RR +RR x) =RR= x.
  Axiom RR_add_neg_l : forall x, ((-RR x) +RR x) =RR= 0RR.
  
  (* Multiplicative monoid *)
  Axiom RR_mult_comm  : forall x y, (x *RR y) =RR= (y *RR x).
  Axiom RR_mult_assoc : forall x y z, ((x *RR y) *RR z) =RR= (x *RR (y *RR z)).
  Axiom RR_mult_1_l   : forall x, (1RR *RR x) =RR= x.
  
  (* Distributivity *)
  Axiom RR_distr_l : forall x y z,
    (x *RR (y +RR z)) =RR= ((x *RR y) +RR (x *RR z)).

  (* ===== 6. Derived Lemmas (for cleaner downstream proofs) ===== *)
  
  Axiom RR_add_0_r : forall x, (x +RR 0RR) =RR= x.
  Axiom RR_add_neg_r : forall x, (x +RR (-RR x)) =RR= 0RR.
  Axiom RR_mult_1_r : forall x, (x *RR 1RR) =RR= x.
  Axiom RR_distr_r : forall x y z,
    ((x +RR y) *RR z) =RR= ((x *RR z) +RR (y *RR z)).
  
  Axiom RR_mult_0_l : forall x, (0RR *RR x) =RR= 0RR.
  Axiom RR_mult_0_r : forall x, (x *RR 0RR) =RR= 0RR.
  
  Axiom RR_neg_0 : (-RR 0RR) =RR= 0RR.
  Axiom RR_neg_invol : forall x, (-RR (-RR x)) =RR= x.
  Axiom RR_neg_add : forall x y, (-RR (x +RR y)) =RR= ((-RR x) +RR (-RR y)).
  Axiom RR_neg_mult_l : forall x y, ((-RR x) *RR y) =RR= (-RR (x *RR y)).
  Axiom RR_neg_mult_r : forall x y, (x *RR (-RR y)) =RR= (-RR (x *RR y)).
  Axiom RR_neg_neg_mult : forall x y, ((-RR x) *RR (-RR y)) =RR= (x *RR y).

End RR_Interface.

(* ========================================================================== *)
(*  FIELD EXTENSION                                                           *)
(* ========================================================================== *)

Module Type RR_Field_Interface.
  Include RR_Interface.
  
  Parameter RR_inv : RR -> RR.
  
  Definition RR_neq_zero (x : RR) : Prop := ~ (x =RR= 0RR).
  
  Axiom RR_mult_inv_r : forall x, RR_neq_zero x -> (x *RR (RR_inv x)) =RR= 1RR.
  
  Declare Instance RR_inv_Proper : Proper (RR_eq ==> RR_eq) RR_inv.

End RR_Field_Interface.