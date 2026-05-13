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
  |                    Top__Numbers__RelationalRationals.v                   |
  |                                                                          |
  |         Rational Numbers from Relational Integers: Complete Field        |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-21                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Construct rational numbers from relational integers with       |
  |  complete field structure, extending the relational number tower:        |
  |    N_rel -> Z_rel -> Q_rel -> R_cauchy                                   |
  |                                                                          |
  |  KEY INSIGHT: Rationals ARE relational ratio structures.                 |
  |    - Q_rel := { (n, d) : Z x Z       } with (a,b) representing a/b           |
  |    - Equivalence: (a,b) ~= (c,d) iff a*d = c*b (cross-multiplication)    |
  |    - Addition: INTRA-domain (combining quantities)                       |
  |    - Multiplication: INTER-domain (scaling/ratios)                       |
  |    - Division: Uses contextual handling from RelationalDivision          |
  |                                                                          |
  |  STRATEGY: Leverage Coq's stdlib Q via to_Q/from_Q (like Z_rel/Z).       |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Core Definitions (Q_rel, qeq)                             |
  |    SECTION 2:  Conversion to/from stdlib Q                               |
  |    SECTION 3:  Equivalence Relation                                      |
  |    SECTION 4:  Constants                                                 |
  |    SECTION 5:  Arithmetic Operations                                     |
  |    SECTION 6:  Proper Instances (operations respect equivalence)         |
  |    SECTION 7:  Field Axioms                                              |
  |    SECTION 8:  Order Structure                                           |
  |    SECTION 9:  Integer Embedding (Z         Q)                                 |
  |    SECTION 10: Archimedean Property & Density                            |
  |    SECTION 11: Division with Contextual Handling                         |
  |    SECTION 12: Absolute Value                                            |
  |    SECTION 13: QR Module - Public API                                    |
  |    SECTION 14: Hint Databases & Tactics                                  |
  |    SECTION 15: Notation Scopes                                           |
  |    SECTION 16: Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

(* Import UCF/GUTT infrastructure *)
Require Import Top__Extensions__Prelude.
Require Import Top__Numbers__Relational.
Require Import Top__Numbers__RelationalIntegers.
Require Import Top__Numbers__RelationalDivision.

(* ========================================================================== *)
(*                                                                            *)
(*  CRITICAL IMPORT: UCF/GUTT Relational Arithmetic Library                   *)
(*                                                                            *)
(*  This provides auditable Q arithmetic where lia/nia COMPLETELY FAIL:       *)
(*    - UCF.Q_mul_pos_pos      : 0 < a -> 0 < b -> 0 < a*b                    *)
(*    - UCF.Q_add_pos_nonneg   : 0 < a -> 0 <= b -> 0 < a+b                   *)
(*    - UCF.Q_inv_pos          : 0 < a -> 0 < /a                              *)
(*    - UCF.Q_sq_nonneg        : 0 <= a*a                                     *)
(*    - ucf_lia, ucf_nia, ucf_qia tactics for automation                      *)
(*    - Hint databases: ucf_z, ucf_q, ucf_arith                               *)
(*                                                                            *)
(* ========================================================================== *)
Require Import Top__Numbers__UCF_Lia.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE DEFINITIONS                             *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIONAL RATIONAL NUMBERS
  ===========================

  A rational is a pair (numerator, denominator) where denominator > 0.
  This construction views rationals as RATIO relations:

  - The numerator represents "how many" relational steps
  - The denominator represents "per how many" reference steps
  - Together they form a RATIO between relational quantities

  The positive denominator constraint ensures:
  - Canonical orientation (avoiding +/-a/+/-b ambiguity)
  - Well-defined sign (sign lives in numerator)
  - Consistent ordering
*)

(** The carrier type: pairs with positive denominator *)
Record Q_rel : Type := mkQ {
  qnum : Z;           (** numerator: signed count *)
  qden : Z;           (** denominator: positive reference *)
  qden_pos : qden > 0 (** positivity proof *)
}.

(**
  Equivalence relation: a/b ~ c/d iff a*d = b*c

  This is the fundamental cross-multiplication criterion.
  Relationally: two ratios are equivalent if they represent
  the same proportional relationship.
*)
Definition qeq (p q : Q_rel) : Prop :=
  qnum p * qden q = qnum q * qden p.

Infix "=Q=" := qeq (at level 70, no associativity).

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: CONVERSION TO/FROM STDLIB Q                  *)
(*                                                                            *)
(* ========================================================================== *)

(**
  INTERPRETATION VIA STDLIB Q
  ===========================

  Like Z_rel uses to_Z/from_Z for complex proofs,
  Q_rel uses to_Q/from_Q to leverage stdlib Q.
*)

Local Open Scope Q_scope.

(** Convert Q_rel to stdlib Q *)
Definition to_Q (p : Q_rel) : Q :=
  Qmake (qnum p) (Z.to_pos (qden p)).

(** Convert stdlib Q to Q_rel *)
Program Definition from_Q (q : Q) : Q_rel :=
  mkQ (Qnum q) (Z.pos (Qden q)) _.
Next Obligation. lia. Qed.

(** Conversion is faithful: qeq iff Qeq *)
Theorem to_Q_faithful : forall p q, p =Q= q <-> Qeq (to_Q p) (to_Q q).
Proof.
  intros p q.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq].
  unfold qeq, to_Q, Qeq. simpl.
  rewrite !Z2Pos.id by lia.
  reflexivity.
Qed.

(** Round-trip properties *)
Theorem from_to_Q : forall p, from_Q (to_Q p) =Q= p.
Proof.
  intro p. destruct p as [np dp Hdp].
  unfold qeq, from_Q, to_Q. simpl.
  rewrite Z2Pos.id by lia.
  ring.
Qed.

Theorem to_from_Q : forall q, Qeq (to_Q (from_Q q)) q.
Proof.
  intro q. destruct q as [nq dq].
  unfold to_Q, from_Q, Qeq. simpl.
  reflexivity.
Qed.

Local Close Scope Q_scope.
Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: EQUIVALENCE RELATION                         *)
(*                                                                            *)
(* ========================================================================== *)

Theorem qeq_refl : forall p, p =Q= p.
Proof. intro p. unfold qeq. ring. Qed.

Theorem qeq_sym : forall p q, p =Q= q -> q =Q= p.
Proof. intros p q H. unfold qeq in *. lia. Qed.

Theorem qeq_trans : forall p q r, p =Q= q -> q =Q= r -> p =Q= r.
Proof.
  intros p q r Hpq Hqr.
  apply to_Q_faithful.
  apply to_Q_faithful in Hpq.
  apply to_Q_faithful in Hqr.
  rewrite Hpq. exact Hqr.
Qed.

(** qeq is an equivalence relation (stdlib typeclass) *)
Global Instance qeq_Equivalence : RelationClasses.Equivalence qeq := {
  Equivalence_Reflexive := qeq_refl;
  Equivalence_Symmetric := qeq_sym;
  Equivalence_Transitive := qeq_trans
}.

(** qeq is an equivalence (project's definition) *)
Theorem qeq_is_equivalence : Top__Extensions__Base.Equivalence qeq.
Proof.
  unfold Top__Extensions__Base.Equivalence.
  split; [exact qeq_refl | split; [exact qeq_sym | exact qeq_trans]].
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: CONSTANTS                                    *)
(*                                                                            *)
(* ========================================================================== *)

Program Definition Q_zero : Q_rel := mkQ 0 1 _.
Next Obligation. lia. Qed.

Program Definition Q_one : Q_rel := mkQ 1 1 _.
Next Obligation. lia. Qed.

Program Definition Q_two : Q_rel := mkQ 2 1 _.
Next Obligation. lia. Qed.

Program Definition Q_minus_one : Q_rel := mkQ (-1) 1 _.
Next Obligation. lia. Qed.

Program Definition Q_half : Q_rel := mkQ 1 2 _.
Next Obligation. lia. Qed.

Notation "'0Q'" := Q_zero.
Notation "'1Q'" := Q_one.
Notation "'2Q'" := Q_two.

(** Conversion of constants *)
Local Open Scope Q_scope.

Lemma to_Q_zero : Qeq (to_Q 0Q) 0.
Proof. reflexivity. Qed.

Lemma to_Q_one : Qeq (to_Q 1Q) 1.
Proof. reflexivity. Qed.

Local Close Scope Q_scope.
Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: ARITHMETIC OPERATIONS                        *)
(*                                                                            *)
(* ========================================================================== *)

(** Addition: a/b + c/d = (a*d + b*c) / (b*d) *)
Program Definition qadd (p q : Q_rel) : Q_rel :=
  mkQ (qnum p * qden q + qnum q * qden p) (qden p * qden q) _.
Next Obligation.
  destruct p as [np dp Hp]. destruct q as [nq dq Hq]. simpl.
  (* Product of positive denominators is positive *)
  (* Hp : dp > 0, Hq : dq > 0, Goal: dp * dq > 0 *)
  (* Use Z.lt_gt to convert between < and > *)
  apply Z.lt_gt.
  apply UCF.Z_mul_pos; apply Z.gt_lt; assumption.
Qed.

Infix "+Q" := qadd (at level 50, left associativity).

(** Negation: -(a/b) = (-a)/b *)
Program Definition qneg (p : Q_rel) : Q_rel := mkQ (- qnum p) (qden p) _.
Next Obligation. destruct p as [np dp Hp]. simpl. exact Hp. Qed.

Notation "-Q p" := (qneg p) (at level 35, right associativity).

(** Subtraction *)
Definition qsub (p q : Q_rel) : Q_rel := qadd p (qneg q).
Infix "-Q" := qsub (at level 50, left associativity).

(** Multiplication: a/b * c/d = (a*c) / (b*d) *)
Program Definition qmul (p q : Q_rel) : Q_rel :=
  mkQ (qnum p * qnum q) (qden p * qden q) _.
Next Obligation.
  destruct p as [np dp Hp]. destruct q as [nq dq Hq]. simpl.
  (* Product of positive denominators is positive *)
  apply Z.lt_gt.
  apply UCF.Z_mul_pos; apply Z.gt_lt; assumption.
Qed.

Infix "*Q" := qmul (at level 40, left associativity).

(** Inverse: (a/b)      ^1 = sign(a)*b / |a| when a <>   0 *)
Program Definition qinv (p : Q_rel) (Hne : qnum p <> 0) : Q_rel :=
  mkQ (Z.sgn (qnum p) * qden p) (Z.abs (qnum p)) _.
Next Obligation.
  destruct p as [np dp Hp]. simpl in *.
  apply Z.lt_gt. apply Z.abs_pos. assumption.
Qed.

(** Division: a / b = a * b      ^1 *)
Definition qdiv (p q : Q_rel) (Hne : qnum q <> 0) : Q_rel := qmul p (qinv q Hne).

(** Conversion preserves operations *)
Local Open Scope Q_scope.

Local Lemma to_Q_add : forall p q, Qeq (to_Q (p +Q q)) (Qplus (to_Q p) (to_Q q)).
Proof.
  intros p q.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq].
  unfold to_Q, qadd, Qeq, Qplus. simpl.
  rewrite !Z2Pos.id by nia.
  rewrite Pos2Z.inj_mul.
  rewrite !Z2Pos.id by lia.
  ring.
Qed.

Local Lemma to_Q_neg : forall p, Qeq (to_Q (-Q p)) (Qopp (to_Q p)).
Proof.
  intro p. destruct p as [np dp Hdp].
  unfold to_Q, qneg, Qeq, Qopp. simpl.
  rewrite Z2Pos.id by lia. ring.
Qed.

Local Lemma to_Q_mul : forall p q, Qeq (to_Q (p *Q q)) (Qmult (to_Q p) (to_Q q)).
Proof.
  intros p q.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq].
  unfold to_Q, qmul, Qeq, Qmult. simpl.
  rewrite !Z2Pos.id by nia.
  rewrite Pos2Z.inj_mul.
  rewrite !Z2Pos.id by lia.
  ring.
Qed.

Local Close Scope Q_scope.
Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: PROPER INSTANCES                             *)
(*                                                                            *)
(* ========================================================================== *)

Theorem qadd_respects_qeq : forall p p' q q',
  p =Q= p' -> q =Q= q' -> (p +Q q) =Q= (p' +Q q').
Proof.
  intros p p' q q' Hp Hq.
  apply to_Q_faithful.
  apply to_Q_faithful in Hp.
  apply to_Q_faithful in Hq.
  rewrite !to_Q_add.
  rewrite Hp, Hq. reflexivity.
Qed.

Global Instance qadd_Proper : Proper (qeq ==> qeq ==> qeq) qadd.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply qadd_respects_qeq; assumption.
Qed.

Theorem qneg_respects_qeq : forall p p', p =Q= p' -> (-Q p) =Q= (-Q p').
Proof.
  intros p p' Hp.
  apply to_Q_faithful.
  apply to_Q_faithful in Hp.
  rewrite !to_Q_neg.
  rewrite Hp. reflexivity.
Qed.

Global Instance qneg_Proper : Proper (qeq ==> qeq) qneg.
Proof.
  unfold Proper, respectful.
  intros x y Hxy.
  apply qneg_respects_qeq; assumption.
Qed.

Global Instance qsub_Proper : Proper (qeq ==> qeq ==> qeq) qsub.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  unfold qsub.
  apply qadd_Proper; [assumption | apply qneg_Proper; assumption].
Qed.

Theorem qmul_respects_qeq : forall p p' q q',
  p =Q= p' -> q =Q= q' -> (p *Q q) =Q= (p' *Q q').
Proof.
  intros p p' q q' Hp Hq.
  apply to_Q_faithful.
  apply to_Q_faithful in Hp.
  apply to_Q_faithful in Hq.
  rewrite !to_Q_mul.
  rewrite Hp, Hq. reflexivity.
Qed.

Global Instance qmul_Proper : Proper (qeq ==> qeq ==> qeq) qmul.
Proof.
  unfold Proper, respectful.
  intros x y Hxy a b Hab.
  apply qmul_respects_qeq; assumption.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: FIELD AXIOMS                                 *)
(*                                                                            *)
(* ========================================================================== *)

(** Additive properties *)

Theorem qadd_comm : forall p q, (p +Q q) =Q= (q +Q p).
Proof. intros p q. unfold qeq, qadd. simpl. ring. Qed.

Theorem qadd_assoc : forall p q r, ((p +Q q) +Q r) =Q= (p +Q (q +Q r)).
Proof. intros p q r. unfold qeq, qadd. simpl. ring. Qed.

Theorem qadd_0_l : forall p, (0Q +Q p) =Q= p.
Proof.
  intro p. unfold qeq, qadd, Q_zero.
  destruct p as [np dp Hdp]. simpl.
  destruct dp as [|pdp|ndp]; [lia|simpl; rewrite Z.mul_1_r; reflexivity|lia].
Qed.

Theorem qadd_0_r : forall p, (p +Q 0Q) =Q= p.
Proof. intro p. rewrite qadd_comm. apply qadd_0_l. Qed.

Theorem qadd_neg_l : forall p, ((-Q p) +Q p) =Q= 0Q.
Proof.
  intro p. unfold qeq, qadd, qneg, Q_zero.
  destruct p as [np dp Hdp]. simpl.
  destruct dp as [|pdp|ndp]; [lia|simpl; ring|lia].
Qed.

Theorem qadd_neg_r : forall p, (p +Q (-Q p)) =Q= 0Q.
Proof. intro p. rewrite qadd_comm. apply qadd_neg_l. Qed.

(** Multiplicative properties *)

Theorem qmul_comm : forall p q, (p *Q q) =Q= (q *Q p).
Proof. intros p q. unfold qeq, qmul. simpl. ring. Qed.

Theorem qmul_assoc : forall p q r, ((p *Q q) *Q r) =Q= (p *Q (q *Q r)).
Proof. intros p q r. unfold qeq, qmul. simpl. ring. Qed.

Theorem qmul_1_l : forall p, (1Q *Q p) =Q= p.
Proof.
  intro p. unfold qeq, qmul, Q_one.
  destruct p as [np dp Hdp]. simpl.
  destruct dp as [|pdp|ndp]; [lia| |lia].
  destruct np; simpl; reflexivity.
Qed.

Theorem qmul_1_r : forall p, (p *Q 1Q) =Q= p.
Proof. intro p. rewrite qmul_comm. apply qmul_1_l. Qed.

Theorem qmul_0_l : forall p, (0Q *Q p) =Q= 0Q.
Proof.
  intro p. unfold qeq, qmul, Q_zero.
  destruct p as [np dp Hdp]. simpl.
  destruct dp as [|pdp|ndp]; [lia| |lia].
  destruct np; simpl; reflexivity.
Qed.

Theorem qmul_0_r : forall p, (p *Q 0Q) =Q= 0Q.
Proof. intro p. rewrite qmul_comm. apply qmul_0_l. Qed.

(** Multiplicative inverse *)
Theorem qmul_inv_l : forall p (Hne : qnum p <> 0), ((qinv p Hne) *Q p) =Q= 1Q.
Proof.
  intros p Hne. unfold qeq, qmul, qinv, Q_one. simpl.
  destruct p as [np dp Hdp]. simpl in *.
  rewrite <- Z.sgn_abs.
  destruct np as [|pn|nn]; simpl.
  - exfalso. apply Hne. reflexivity.
  - destruct dp as [|pdp|ndp]; [lia| |lia].
    simpl. f_equal. lia.
  - destruct dp as [|pdp|ndp]; [lia| |lia].
    simpl. f_equal. lia.
Qed.

Theorem qmul_inv_r : forall p (Hne : qnum p <> 0), (p *Q (qinv p Hne)) =Q= 1Q.
Proof. intros p Hne. rewrite qmul_comm. apply qmul_inv_l. Qed.

(** Distributivity *)

Theorem qmul_add_distr_l : forall p q r, (p *Q (q +Q r)) =Q= ((p *Q q) +Q (p *Q r)).
Proof.
  intros p q r. unfold qeq, qmul, qadd. simpl.
  destruct p as [np dp Hdp].
  destruct q as [nq dq Hdq].
  destruct r as [nr dr Hdr].
  simpl. ring.
Qed.

Theorem qmul_add_distr_r : forall p q r, ((p +Q q) *Q r) =Q= ((p *Q r) +Q (q *Q r)).
Proof.
  intros p q r.
  rewrite qmul_comm.
  rewrite qmul_add_distr_l.
  rewrite (qmul_comm r p).
  rewrite (qmul_comm r q).
  reflexivity.
Qed.

(** Non-triviality *)

Theorem Q_zero_neq_one : ~(0Q =Q= 1Q).
Proof. unfold qeq, Q_zero, Q_one. simpl. lia. Qed.

Theorem Q_one_neq_zero : ~(1Q =Q= 0Q).
Proof. intro H. apply Q_zero_neq_one. apply qeq_sym. exact H. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: ORDER STRUCTURE                              *)
(*                                                                            *)
(* ========================================================================== *)

Definition qle (p q : Q_rel) : Prop := qnum p * qden q <= qnum q * qden p.
Infix "<=Q" := qle (at level 70, no associativity).

Definition qlt (p q : Q_rel) : Prop := qnum p * qden q < qnum q * qden p.
Infix "<Q" := qlt (at level 70, no associativity).

Definition qge (p q : Q_rel) : Prop := qle q p.
Infix ">=Q" := qge (at level 70, no associativity).

Definition qgt (p q : Q_rel) : Prop := qlt q p.
Infix ">Q" := qgt (at level 70, no associativity).

(** Order properties - using UCF lemmas for auditability *)

Theorem qle_refl : forall p, p <=Q p.
Proof. intro p. unfold qle. apply UCF.Z_le_refl. Qed.

Theorem qle_antisym : forall p q, p <=Q q -> q <=Q p -> p =Q= q.
Proof. intros p q Hpq Hqp. unfold qle, qeq in *. apply UCF.Z_le_antisym; assumption. Qed.

Theorem qle_trans : forall p q r, p <=Q q -> q <=Q r -> p <=Q r.
Proof.
  intros p q r Hpq Hqr. unfold qle in *.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq]. destruct r as [nr dr Hdr].
  simpl in *.
  (* This requires nonlinear reasoning about products of positives *)
  nia.
Qed.

Theorem qle_total : forall p q, p <=Q q \/ q <=Q p.
Proof. intros p q. unfold qle. lia. Qed.

Theorem qlt_irrefl : forall p, ~ (p <Q p).
Proof. intro p. unfold qlt. lia. Qed.

Theorem qlt_trans : forall p q r, p <Q q -> q <Q r -> p <Q r.
Proof.
  intros p q r Hpq Hqr. unfold qlt in *.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq]. destruct r as [nr dr Hdr].
  simpl in *.
  (* This requires nonlinear reasoning about products of positives *)
  nia.
Qed.

(** Trichotomy - uses UCF.Z_trichotomy with conversion *)
Theorem qlt_trichotomy : forall p q, p <Q q \/ p =Q= q \/ q <Q p.
Proof.
  intros p q. unfold qlt, qeq.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq]. simpl.
  (* UCF.Z_trichotomy gives: a < b \/ a = b \/ a > b *)
  (* We need: a < b \/ a = b \/ b < a *)
  destruct (UCF.Z_trichotomy (np * dq) (nq * dp)) as [Hlt | [Heq | Hgt]].
  - left. exact Hlt.
  - right. left. exact Heq.
  - right. right. apply Z.gt_lt. exact Hgt.
Qed.

(** Decidability *)
Theorem qle_dec : forall p q, {p <=Q q} + {~ (p <=Q q)}.
Proof.
  intros p q. unfold qle.
  destruct (Z.leb (qnum p * qden q) (qnum q * qden p)) eqn:E.
  - left. apply Z.leb_le. exact E.
  - right. intro H. apply Z.leb_le in H. rewrite H in E. discriminate.
Defined.

Theorem qlt_dec : forall p q, {p <Q q} + {~ (p <Q q)}.
Proof.
  intros p q. unfold qlt.
  destruct (Z.ltb (qnum p * qden q) (qnum q * qden p)) eqn:E.
  - left. apply Z.ltb_lt. exact E.
  - right. intro H. apply Z.ltb_lt in H. rewrite H in E. discriminate.
Defined.

Theorem qeq_dec : forall p q, {p =Q= q} + {~ (p =Q= q)}.
Proof.
  intros p q. unfold qeq.
  destruct (Z.eqb (qnum p * qden q) (qnum q * qden p)) eqn:E.
  - left. apply Z.eqb_eq. exact E.
  - right. intro H. apply Z.eqb_eq in H. rewrite H in E. discriminate.
Defined.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: INTEGER EMBEDDING (Z         Q)                    *)
(*                                                                            *)
(* ========================================================================== *)

Program Definition Z_to_Q (n : Z) : Q_rel := mkQ n 1 _.
Next Obligation. lia. Qed.

Theorem Z_to_Q_add : forall n m, Z_to_Q (n + m) =Q= (Z_to_Q n +Q Z_to_Q m).
Proof. intros n m. unfold qeq, Z_to_Q, qadd. simpl. ring. Qed.

Theorem Z_to_Q_sub : forall n m, Z_to_Q (n - m) =Q= (Z_to_Q n -Q Z_to_Q m).
Proof. intros n m. unfold qeq, Z_to_Q, qsub, qadd, qneg. simpl. ring. Qed.

Theorem Z_to_Q_mul : forall n m, Z_to_Q (n * m) =Q= (Z_to_Q n *Q Z_to_Q m).
Proof. intros n m. unfold qeq, Z_to_Q, qmul. simpl. ring. Qed.

Theorem Z_to_Q_neg : forall n, Z_to_Q (- n) =Q= (-Q (Z_to_Q n)).
Proof. intro n. unfold qeq, Z_to_Q, qneg. simpl. ring. Qed.

Theorem Z_to_Q_le : forall n m, (n <= m)%Z <-> (Z_to_Q n <=Q Z_to_Q m).
Proof. intros n m. unfold qle, Z_to_Q. simpl. lia. Qed.

Theorem Z_to_Q_lt : forall n m, (n < m)%Z <-> (Z_to_Q n <Q Z_to_Q m).
Proof. intros n m. unfold qlt, Z_to_Q. simpl. lia. Qed.

Theorem Z_to_Q_injective : forall n m, Z_to_Q n =Q= Z_to_Q m -> n = m.
Proof. intros n m H. unfold qeq, Z_to_Q in H. simpl in H. lia. Qed.

Theorem Z_to_Q_0 : Z_to_Q 0 =Q= 0Q.
Proof. unfold qeq, Z_to_Q, Q_zero. simpl. ring. Qed.

Theorem Z_to_Q_1 : Z_to_Q 1 =Q= 1Q.
Proof. unfold qeq, Z_to_Q, Q_one. simpl. ring. Qed.

(** Embedding from Z_rel *)
Definition Zrel_to_Q (z : Z_rel) : Q_rel := Z_to_Q (to_Z z).

Theorem Zrel_to_Q_add : forall p q,
  Zrel_to_Q (Z_add p q) =Q= (Zrel_to_Q p +Q Zrel_to_Q q).
Proof.
  intros p q. unfold Zrel_to_Q.
  rewrite to_Z_add.
  apply Z_to_Q_add.
Qed.

Theorem Zrel_to_Q_mul : forall p q,
  Zrel_to_Q (Z_mul p q) =Q= (Zrel_to_Q p *Q Zrel_to_Q q).
Proof.
  intros p q. unfold Zrel_to_Q.
  rewrite to_Z_mul.
  apply Z_to_Q_mul.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: ARCHIMEDEAN PROPERTY & DENSITY              *)
(*                                                                            *)
(* ========================================================================== *)

Theorem Q_archimedean : forall p,
  0Q <Q p -> exists n : Z, (n > 0)%Z /\ p <Q Z_to_Q n.
Proof.
  intros p Hpos. destruct p as [np dp Hdp].
  unfold qlt, Q_zero, Z_to_Q in *. simpl in *.
  assert (Hnp_pos : np > 0) by lia.
  exists (np + 1). split; [lia | simpl; nia].
Qed.

(** Density: between any two rationals lies another *)
Theorem Q_dense : forall p q, p <Q q -> exists r, p <Q r /\ r <Q q.
Proof.
  intros p q Hpq.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq].
  unfold qlt in *. simpl in *.
  assert (Hden_pos : 2 * dp * dq > 0) by nia.
  exists (mkQ (np * dq + nq * dp) (2 * dp * dq) Hden_pos).
  simpl.
  (* Destruct dp and dq to eliminate match expressions *)
  destruct dp as [|pdp|ndp]; [lia| |lia].
  destruct dq as [|pdq|ndq]; [lia| |lia].
  simpl. split; nia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: DIVISION WITH CONTEXTUAL HANDLING           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CONTEXTUAL DIVISION FROM RELATIONAL DIVISION
  =============================================

  We integrate with Top__Numbers__RelationalDivision to provide
  contextual division handling for boundary cases (division by zero).
*)

Local Open Scope Q_scope.

(** Convert Q_rel to stdlib Q for RelationalDivision functions *)
Definition qrel_contextual_div (ctx : RelCtx) (num denom : Q_rel) : ExtQ :=
  Q_contextual_div ctx (to_Q num) (to_Q denom).

(** Safe division: returns None if denominator is zero *)
Definition qrel_safe_div (num denom : Q_rel) : option Q :=
  Q_safe_div (to_Q num) (to_Q denom).

(** For nonzero denominator, contextual division is conservative *)
Theorem qrel_contextual_conservative : forall ctx num denom,
  qnum denom <> 0%Z ->
  qrel_contextual_div ctx num denom = FiniteQ (to_Q num / to_Q denom).
Proof.
  intros ctx num denom Hne.
  unfold qrel_contextual_div.
  apply Q_contextual_div_conservative.
  destruct denom as [nd dd Hdd]. simpl in *.
  intro Heq. apply Hne.
  unfold to_Q in Heq. simpl in Heq.
  unfold Qeq in Heq. simpl in Heq. lia.
Qed.

(** Space context maps zero denominator to +infinity *)
Theorem qrel_space_infty : forall num denom,
  qnum denom = 0%Z ->
  qrel_contextual_div RC_Space num denom = PinftyQ.
Proof.
  intros num denom Heq.
  unfold qrel_contextual_div.
  apply Q_contextual_space_infty.
  destruct denom as [nd dd Hdd]. simpl in *.
  subst. unfold to_Q, Qeq. simpl. reflexivity.
Qed.

(** Time context maps zero denominator to 0 *)
Theorem qrel_time_zero : forall num denom,
  qnum denom = 0%Z ->
  qrel_contextual_div RC_Time num denom = FiniteQ 0.
Proof.
  intros num denom Heq.
  unfold qrel_contextual_div.
  apply Q_contextual_time_zero.
  destruct denom as [nd dd Hdd]. simpl in *.
  subst. unfold to_Q, Qeq. simpl. reflexivity.
Qed.

(** Info context maps zero denominator to NaN *)
Theorem qrel_info_nan : forall num denom,
  qnum denom = 0%Z ->
  qrel_contextual_div RC_Info num denom = ExtNaNQ.
Proof.
  intros num denom Heq.
  unfold qrel_contextual_div.
  apply Q_contextual_info_nan.
  destruct denom as [nd dd Hdd]. simpl in *.
  subst. unfold to_Q, Qeq. simpl. reflexivity.
Qed.

Local Close Scope Q_scope.
Local Open Scope Z_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: ABSOLUTE VALUE                              *)
(*                                                                            *)
(* ========================================================================== *)

Program Definition qabs (p : Q_rel) : Q_rel := mkQ (Z.abs (qnum p)) (qden p) _.
Next Obligation. destruct p as [np dp Hdp]. simpl. exact Hdp. Qed.

Notation "|Q p |" := (qabs p) (at level 35, format "|Q  p  |").

Theorem qabs_nonneg : forall p, 0Q <=Q |Q p |.
Proof.
  intro p. unfold qle, qabs, Q_zero. simpl.
  destruct p as [np dp Hdp]. simpl.
  (* UCF.Z_abs_nonneg: absolute value is non-negative *)
  assert (H: 0 <= Z.abs np) by (apply UCF.Z_abs_nonneg).
  nia.
Qed.

Theorem qabs_zero : forall p, |Q p | =Q= 0Q <-> p =Q= 0Q.
Proof.
  intro p. destruct p as [np dp Hdp].
  unfold qeq, qabs, Q_zero. simpl.
  rewrite !Z.mul_1_r.
  split; intro H.
  - apply Z.abs_0_iff. exact H.
  - rewrite H. reflexivity.
Qed.

Theorem qabs_neg : forall p, |Q (-Q p) | =Q= |Q p |.
Proof.
  intro p. destruct p as [np dp Hdp].
  unfold qeq, qabs, qneg. simpl.
  rewrite Z.abs_opp. ring.
Qed.

Theorem qabs_mul : forall p q, |Q p *Q q | =Q= (|Q p | *Q |Q q |).
Proof.
  intros p q.
  destruct p as [np dp Hdp]. destruct q as [nq dq Hdq].
  unfold qeq, qabs, qmul. simpl.
  (* UCF.Z_abs_mul: |a*b| = |a|*|b| *)
  rewrite UCF.Z_abs_mul. ring.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: QR MODULE - PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

Module QR.

  (** Types *)
  Definition Q := Q_rel.

  (** Equivalence *)
  Definition eq := qeq.
  Definition eq_refl := qeq_refl.
  Definition eq_sym := qeq_sym.
  Definition eq_trans := qeq_trans.
  Definition eq_dec := qeq_dec.

  (** Constants *)
  Definition zero := Q_zero.
  Definition one := Q_one.
  Definition two := Q_two.
  Definition half := Q_half.

  (** Arithmetic *)
  Definition add := qadd.
  Definition neg := qneg.
  Definition sub := qsub.
  Definition mul := qmul.
  Definition inv := qinv.
  Definition div := qdiv.
  Definition abs := qabs.

  (** Order *)
  Definition le := qle.
  Definition lt := qlt.
  Definition ge := qge.
  Definition gt := qgt.
  Definition le_dec := qle_dec.
  Definition lt_dec := qlt_dec.

  (** Conversions *)
  Definition of_Z := Z_to_Q.
  Definition of_Zrel := Zrel_to_Q.
  Definition toQ := to_Q.
  Definition fromQ := from_Q.

  (** Contextual Division (from RelationalDivision) *)
  Definition ctx_div := qrel_contextual_div.
  Definition safe_div := qrel_safe_div.

  (** Field axioms *)
  Definition add_comm := qadd_comm.
  Definition add_assoc := qadd_assoc.
  Definition add_zero_l := qadd_0_l.
  Definition add_zero_r := qadd_0_r.
  Definition add_neg_l := qadd_neg_l.
  Definition add_neg_r := qadd_neg_r.
  Definition mul_comm := qmul_comm.
  Definition mul_assoc := qmul_assoc.
  Definition mul_one_l := qmul_1_l.
  Definition mul_one_r := qmul_1_r.
  Definition mul_zero_l := qmul_0_l.
  Definition mul_zero_r := qmul_0_r.
  Definition mul_inv_l := qmul_inv_l.
  Definition mul_inv_r := qmul_inv_r.
  Definition distr_l := qmul_add_distr_l.
  Definition distr_r := qmul_add_distr_r.
  Definition zero_neq_one := Q_zero_neq_one.

  (** Order properties *)
  Definition le_refl := qle_refl.
  Definition le_trans := qle_trans.
  Definition le_antisym := qle_antisym.
  Definition le_total := qle_total.
  Definition lt_irrefl := qlt_irrefl.
  Definition lt_trans := qlt_trans.
  Definition trichotomy := qlt_trichotomy.

  (** Special properties *)
  Definition archimedean := Q_archimedean.
  Definition dense := Q_dense.

End QR.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 14: HINT DATABASES & TACTICS                    *)
(*                                                                            *)
(* ========================================================================== *)

#[export] Hint Resolve
  qeq_refl qeq_sym qle_refl qle_trans
  qlt_irrefl qlt_trans
  qadd_0_l qadd_0_r qadd_neg_l qadd_neg_r
  qmul_1_l qmul_1_r qmul_0_l qmul_0_r
  qabs_nonneg
  : qrel.

#[export] Hint Rewrite
  Z_to_Q_add Z_to_Q_mul Z_to_Q_neg Z_to_Q_0 Z_to_Q_1
  : qrel.

Ltac qrel_simpl :=
  unfold qeq, qadd, qneg, qsub, qmul, qabs, qle, qlt,
         Q_zero, Q_one, Q_two, Z_to_Q; simpl.

(**
  qrel_ring: Tactic for Q_rel algebraic goals.
  Now integrates ucf_lia for order goals (auditable).
*)
Ltac qrel_ring :=
  match goal with
  | |- qeq ?p ?q => unfold qeq; simpl; ring
  | |- qle ?p ?q => unfold qle; simpl; try ucf_lia
  | |- qlt ?p ?q => unfold qlt; simpl; try ucf_lia
  | _ => simpl; try ring; try ucf_lia
  end.

(**
  qrel_auto: Combined automation tactic.
  Leverages both qrel hints and UCF hint databases (ucf_z, ucf_q, ucf_arith).
*)
Ltac qrel_auto :=
  auto with qrel ucf_z ucf_q ucf_arith;
  try qrel_simpl;
  try qrel_ring;
  try ucf_auto.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 15: NOTATION SCOPES                             *)
(*                                                                            *)
(* ========================================================================== *)

Declare Scope qrel_scope.
Delimit Scope qrel_scope with qr.

(* Convenient ASCII notations for the relational rationals.  All firing only
   inside the [%qr] scope, so they never collide with Coq's standard Q_scope
   operators on raw [Q].  Replaces an earlier mojibake-encoded UTF-8 block. *)
Notation "p == q"  := (qeq p q)  (at level 70, no associativity)    : qrel_scope.
Notation "p + q"   := (qadd p q) (at level 50, left associativity)  : qrel_scope.
Notation "- p"     := (qneg p)   (at level 35, right associativity) : qrel_scope.
Notation "p - q"   := (qsub p q) (at level 50, left associativity)  : qrel_scope.
Notation "p * q"   := (qmul p q) (at level 40, left associativity)  : qrel_scope.
Notation "p <= q"  := (qle p q)  (at level 70, no associativity)    : qrel_scope.
Notation "p < q"   := (qlt p q)  (at level 70, no associativity)    : qrel_scope.
Notation "p >= q"  := (qge p q)  (at level 70, no associativity)    : qrel_scope.
Notation "p > q"   := (qgt p q)  (at level 70, no associativity)    : qrel_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 16: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - verify definitions compute *)
  Definition test_zero_num : qnum Q_zero = 0 := eq_refl.
  Definition test_zero_den : qden Q_zero = 1 := eq_refl.
  Definition test_one_num : qnum Q_one = 1 := eq_refl.
  Definition test_one_den : qden Q_one = 1 := eq_refl.

  (** Verify field identity laws *)
  Example test_add_zero : qadd Q_zero Q_one =Q= Q_one.
  Proof. apply qadd_0_l. Qed.

  Example test_mul_one : qmul Q_one Q_two =Q= Q_two.
  Proof. apply qmul_1_l. Qed.

  (** Verify arithmetic *)
  Example test_one_plus_one : (Q_one +Q Q_one) =Q= Q_two.
  Proof. unfold qeq, qadd, Q_one, Q_two. simpl. ring. Qed.

  Example test_two_times_half : (Q_two *Q Q_half) =Q= Q_one.
  Proof. unfold qeq, qmul, Q_two, Q_half, Q_one. simpl. ring. Qed.

  (** Verify Z embedding *)
  Example test_Z_embed_5 : Z_to_Q 5 =Q= (Q_one +Q Q_one +Q Q_one +Q Q_one +Q Q_one).
  Proof. unfold qeq, Z_to_Q, qadd, Q_one. simpl. ring. Qed.

  (** Verify contextual division *)
  Example test_ctx_div_space :
    qrel_contextual_div RC_Space Q_one Q_zero = PinftyQ.
  Proof. apply qrel_space_infty. reflexivity. Qed.

  Example test_ctx_div_time :
    qrel_contextual_div RC_Time Q_one Q_zero = FiniteQ 0.
  Proof. apply qrel_time_zero. reflexivity. Qed.

  Example test_ctx_div_info :
    qrel_contextual_div RC_Info Q_one Q_zero = ExtNaNQ.
  Proof. apply qrel_info_nan. reflexivity. Qed.

End AxiomAudit.

(** Print assumptions for key theorems *)
Print Assumptions qeq_trans.
Print Assumptions qmul_inv_r.
Print Assumptions qle_trans.
Print Assumptions Z_to_Q_injective.
Print Assumptions Q_archimedean.
Print Assumptions Q_dense.
Print Assumptions qrel_contextual_conservative.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(*
  RELATIONAL RATIONALS - COMPLETE FIELD FROM RELATIONAL FOUNDATIONS
  ==================================================================

  CONSTRUCTION:
    Q_rel = { (n, d) : Z x Z | d > 0 }
    (a,b) =Q= (c,d) iff a*d = b*c

  FIELD AXIOMS PROVEN:
    [v] Addition: commutative, associative, identity (0), inverses (-p)
    [v] Multiplication: commutative, associative, identity (1), inverses (p      ^1)
    [v] Distributivity: p*(q+r) = p*q + p*r
    [v] Non-triviality: 0 <>   1

  ORDER STRUCTURE:
    [v] Total order: <= is reflexive, transitive, antisymmetric, total
    [v] Dense: between any two rationals lies another
    [v] Archimedean: no infinitesimals

  EMBEDDINGS:
    [v] Z         Q via n         n/1
    [v] Z_rel         Q via to_Z then embed
    [v] Q_rel          Coq's Q (isomorphism via to_Q/from_Q)

  CONTEXTUAL DIVISION (from RelationalDivision):
    [v] RC_Space: zero denominator         +infinity
    [v] RC_Time:  zero denominator         0
    [v] RC_Info:  zero denominator         NaN

  INTEGRATION:
    - Imports Top__Extensions__Prelude (UCF/GUTT infrastructure)
    - Imports Top__Numbers__Relational (N_rel)
    - Imports Top__Numbers__RelationalIntegers (Z_rel, to_Z)
    - Imports Top__Numbers__RelationalDivision (contextual division)

  RELATIONAL CHAIN:
    N_rel         Z_rel         Q_rel         R_cauchy

     nat     Z       Q     Cauchy seqs

  AXIOM COUNT: 0 (beyond Coq standard library)
  ADMIT COUNT: 0
*)
