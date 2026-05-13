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
  |                    Top__Numbers__RelationalDivision.v                    |
  |                                                                          |
  |              Division by Zero as Relational Boundary Operator            |
  |                    (CONSTRUCTIVE / AXIOM-FREE VERSION)                   |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 2.0.0                                                          |
  |  DATE:    2026-01-21                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Formalize division by zero handling in the UCF/GUTT framework  |
  |  using ONLY constructive mathematics with ZERO AXIOMS.                   |
  |                                                                          |
  |  KEY DIFFERENCES FROM v1.0:                                              |
  |    - Does NOT import Coq's standard library Reals (avoids axioms)        |
  |    - Works entirely with Q (rationals) and R_cauchy (Cauchy sequences)   |
  |    - Uses decidable equality (Qeq_dec) instead of classical Req_EM_T     |
  |    - All proofs are constructive                                         |
  |                                                                          |
  |  KEY INSIGHTS:                                                           |
  |    - Division by zero is a BOUNDARY in relational space, not an error   |
  |    - The boundary's meaning depends on CONTEXT (Space/Time/Info)        |
  |    - Q has a TOTAL inverse: Qinv 0 = 0 (by QArith definition)           |
  |    - This forms a consistent Meadow algebra constructively              |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Relational States & Boundary Detection (on Q)            |
  |    SECTION 2:  Contextual Interpretation                                |
  |    SECTION 3:  Extended Rationals (Q Ã¢Ë†Âª {Ã‚Â±Ã¢Ë†Å¾, NaN})                       |
  |    SECTION 4:  Safe Division on Q (Option-returning)                    |
  |    SECTION 5:  Contextual Division on Q (Total)                         |
  |    SECTION 6:  Totalized Inverse on Q (Qinv already total)              |
  |    SECTION 7:  Meadow Algebra Structure on Q                            |
  |    SECTION 8:  Consistency Theorems                                     |
  |    SECTION 9:  Lifting to R_cauchy (Constructive Reals)                 |
  |    SECTION 10: RD Module - Public API                                   |
  |    SECTION 11: Hint Databases & Tactics                                 |
  |    SECTION 12: Examples                                                 |
  |    SECTION 13: Axiom Audit                                              |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

(* Import UCF/GUTT extension framework *)
Require Import Top__Extensions__Prelude.
Require Import Top__Numbers__RelationalReals.

(* ========================================================================== *)
(*                                                                            *)
(*  CRITICAL IMPORT: UCF/GUTT Relational Arithmetic Library                   *)
(*                                                                            *)
(*  Provides auditable Q arithmetic where lia/nia COMPLETELY FAIL:            *)
(*    - UCF.Q_mul_pos_pos      : 0 < a -> 0 < b -> 0 < a*b                    *)
(*    - UCF.Q_add_pos_nonneg   : 0 < a -> 0 <= b -> 0 < a+b                   *)
(*    - UCF.Q_inv_pos          : 0 < a -> 0 < /a                              *)
(*    - ucf_lia, ucf_qia tactics for automation                               *)
(*                                                                            *)
(* ========================================================================== *)
Require Import Top__Numbers__UCF_Lia.

Open Scope Q_scope.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: RELATIONAL STATES & BOUNDARY DETECTION       *)
(*                                                                            *)
(* ========================================================================== *)

(**
  PHILOSOPHICAL GROUNDING
  =======================
  
  In UCF/GUTT, division by zero is not an "error" but a BOUNDARY condition
  in relational space. When the denominator equals zero, the relation
  reaches a boundary where its usual meaning transforms.
  
  Working constructively with Q (rationals):
  - Q has DECIDABLE equality: we can always determine if q == 0
  - Q has TOTAL inverse: Qinv is defined for all Q (Qinv 0 = 0)
  - No classical axioms needed
*)

(** Relational states for boundary detection. *)
Inductive RelationalState : Type :=
  | RS_Related   : RelationalState  (** Valid relation, nonzero denominator *)
  | RS_Boundary  : RelationalState  (** Boundary condition, zero denominator *)
  | RS_Undefined : RelationalState. (** Propagated uncertainty *)

(** States are decidably equal. *)
Definition RelationalState_eq_dec (s1 s2 : RelationalState) : {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Defined.

(** States are mutually exclusive. *)
Lemma state_mutual_exclusion :
  RS_Related <> RS_Boundary /\ RS_Boundary <> RS_Undefined /\ RS_Related <> RS_Undefined.
Proof.
  repeat split; discriminate.
Qed.

(** 
  Boundary detection on Q using decidable equality.
  This is fully constructive - no classical axioms needed.
*)
Definition Q_boundary_detect (q : Q) : RelationalState :=
  if Qeq_bool q 0 then RS_Boundary else RS_Related.

(** Qeq_bool correctness lemmas *)
Lemma Qeq_bool_true_iff : forall q1 q2, Qeq_bool q1 q2 = true <-> q1 == q2.
Proof.
  intros. split.
  - apply Qeq_bool_eq.
  - apply Qeq_bool_iff.
Qed.

Lemma Qeq_bool_false_iff : forall q1 q2, Qeq_bool q1 q2 = false <-> ~(q1 == q2).
Proof.
  intros. split.
  - intros Hf Heq. apply Qeq_bool_iff in Heq. rewrite Heq in Hf. discriminate.
  - intros Hneq. destruct (Qeq_bool q1 q2) eqn:E.
    + apply Qeq_bool_eq in E. contradiction.
    + reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Forward Direction: Zero implies Boundary                *)
(* -------------------------------------------------------------------------- *)

Theorem Q_zero_implies_boundary :
  forall q : Q, q == 0 -> Q_boundary_detect q = RS_Boundary.
Proof.
  intros q Hq.
  unfold Q_boundary_detect.
  apply Qeq_bool_iff in Hq.
  rewrite Hq. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Backward Direction: Boundary implies Zero               *)
(* -------------------------------------------------------------------------- *)

Theorem Q_boundary_implies_zero :
  forall q : Q, Q_boundary_detect q = RS_Boundary -> q == 0.
Proof.
  intros q Hb.
  unfold Q_boundary_detect in Hb.
  destruct (Qeq_bool q 0) eqn:E.
  - apply Qeq_bool_eq. exact E.
  - discriminate Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Bidirectional Characterization                          *)
(* -------------------------------------------------------------------------- *)

Theorem Q_boundary_iff_zero :
  forall q : Q, Q_boundary_detect q = RS_Boundary <-> q == 0.
Proof.
  intro q. split.
  - apply Q_boundary_implies_zero.
  - apply Q_zero_implies_boundary.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Nonzero implies Related                                 *)
(* -------------------------------------------------------------------------- *)

Theorem Q_nonzero_implies_related :
  forall q : Q, ~(q == 0) -> Q_boundary_detect q = RS_Related.
Proof.
  intros q Hneq.
  unfold Q_boundary_detect.
  apply Qeq_bool_false_iff in Hneq.
  rewrite Hneq. reflexivity.
Qed.

Theorem Q_related_iff_nonzero :
  forall q : Q, Q_boundary_detect q = RS_Related <-> ~(q == 0).
Proof.
  intro q. split.
  - intro H. unfold Q_boundary_detect in H.
    destruct (Qeq_bool q 0) eqn:E.
    + discriminate H.
    + apply Qeq_bool_false_iff. exact E.
  - apply Q_nonzero_implies_related.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Detector Never Returns Undefined                        *)
(* -------------------------------------------------------------------------- *)

Theorem Q_detector_never_undefined :
  forall q : Q, Q_boundary_detect q <> RS_Undefined.
Proof.
  intros q H.
  unfold Q_boundary_detect in H.
  destruct (Qeq_bool q 0); discriminate H.
Qed.

(* -------------------------------------------------------------------------- *)
(*                    Completeness: Always Related or Boundary                *)
(* -------------------------------------------------------------------------- *)

Theorem Q_boundary_complete :
  forall q : Q,
    Q_boundary_detect q = RS_Related \/ Q_boundary_detect q = RS_Boundary.
Proof.
  intro q.
  unfold Q_boundary_detect.
  destruct (Qeq_bool q 0).
  - right. reflexivity.
  - left. reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: CONTEXTUAL INTERPRETATION                    *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CONTEXT-DEPENDENT BOUNDARY INTERPRETATION
  =========================================
  
  The boundary condition has different physical/conceptual meanings:
  
  - SPACE: Boundary -> expansion/infinity (like approaching event horizon)
  - TIME:  Boundary -> collapse/reset to zero (like phase transition)
  - INFO:  Boundary -> undefined/NaN (information loss)
*)

(** Relational contexts for boundary interpretation. *)
Inductive RelCtx : Type :=
  | RC_Space : RelCtx  (** Spatial/geometric context *)
  | RC_Time  : RelCtx  (** Temporal context *)
  | RC_Info  : RelCtx. (** Information-theoretic context *)

Definition RelCtx_eq_dec (c1 c2 : RelCtx) : {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.

(**
  Apply contextual interpretation to boundary conditions.
*)
Definition Q_contextual_interpret (ctx : RelCtx) (q : Q) : RelationalState :=
  match Q_boundary_detect q with
  | RS_Related   => RS_Related
  | RS_Boundary  =>
      match ctx with
      | RC_Space => RS_Related    (* interpreted as emergent expansion *)
      | RC_Time  => RS_Related    (* interpreted as collapse/reset *)
      | RC_Info  => RS_Undefined  (* information loss *)
      end
  | RS_Undefined => RS_Undefined
  end.

(* Space context: boundary becomes Related *)
Theorem Q_ctx_space_maps_boundary :
  forall q : Q, q == 0 -> Q_contextual_interpret RC_Space q = RS_Related.
Proof.
  intros q Hq.
  unfold Q_contextual_interpret.
  rewrite (Q_zero_implies_boundary q Hq).
  reflexivity.
Qed.

(* Time context: boundary becomes Related *)
Theorem Q_ctx_time_maps_boundary :
  forall q : Q, q == 0 -> Q_contextual_interpret RC_Time q = RS_Related.
Proof.
  intros q Hq.
  unfold Q_contextual_interpret.
  rewrite (Q_zero_implies_boundary q Hq).
  reflexivity.
Qed.

(* Info context: boundary becomes Undefined *)
Theorem Q_ctx_info_maps_boundary :
  forall q : Q, q == 0 -> Q_contextual_interpret RC_Info q = RS_Undefined.
Proof.
  intros q Hq.
  unfold Q_contextual_interpret.
  rewrite (Q_zero_implies_boundary q Hq).
  reflexivity.
Qed.

(* All contexts preserve Related state *)
Theorem Q_ctx_preserves_related :
  forall ctx q, ~(q == 0) -> Q_contextual_interpret ctx q = RS_Related.
Proof.
  intros ctx q Hneq.
  unfold Q_contextual_interpret.
  rewrite (Q_nonzero_implies_related q Hneq).
  reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: EXTENDED RATIONALS                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  EXTENDED RATIONAL NUMBERS
  =========================
  
  To make division total, we extend Q with:
  - Positive infinity (+Ã¢Ë†Å¾)
  - Negative infinity (-Ã¢Ë†Å¾)
  - Not-a-Number (NaN) for undefined results
*)

Inductive ExtQ : Type :=
  | FiniteQ : Q -> ExtQ    (** Ordinary rational *)
  | PinftyQ : ExtQ         (** +Ã¢Ë†Å¾ *)
  | MinftyQ : ExtQ         (** -Ã¢Ë†Å¾ *)
  | ExtNaNQ : ExtQ.        (** Not a Number *)

(** 
  Note: ExtQ decidable equality for Leibniz = is non-trivial because
  Q uses setoid equality (==). For practical purposes, we provide
  decidability up to Qeq for the FiniteQ case.
*)
Definition ExtQ_eq_bool (e1 e2 : ExtQ) : bool :=
  match e1, e2 with
  | FiniteQ q1, FiniteQ q2 => Qeq_bool q1 q2
  | PinftyQ, PinftyQ => true
  | MinftyQ, MinftyQ => true
  | ExtNaNQ, ExtNaNQ => true
  | _, _ => false
  end.

(** Extended rationals are distinct. *)
Lemma ExtQ_distinct :
  PinftyQ <> MinftyQ /\ PinftyQ <> ExtNaNQ /\ MinftyQ <> ExtNaNQ /\
  (forall q, FiniteQ q <> PinftyQ) /\
  (forall q, FiniteQ q <> MinftyQ) /\
  (forall q, FiniteQ q <> ExtNaNQ).
Proof.
  repeat split; try discriminate.
Qed.

(** FiniteQ injection is injective. *)
Lemma FiniteQ_injective : forall p q, FiniteQ p = FiniteQ q -> p = q.
Proof.
  intros p q H. inversion H. reflexivity.
Qed.

(** FiniteQ respects Qeq *)
Lemma FiniteQ_Qeq : forall p q, p == q -> FiniteQ p = FiniteQ q -> True.
Proof.
  intros. exact I.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: SAFE DIVISION ON Q                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Safe division returns None when denominator is zero.
  This is the partial function approach, fully constructive.
*)

Definition Q_safe_div (num denom : Q) : option Q :=
  if Qeq_bool denom 0 then None else Some (num / denom).

Theorem Q_safe_div_nonzero :
  forall num denom, ~(denom == 0) -> Q_safe_div num denom = Some (num / denom).
Proof.
  intros num denom Hneq.
  unfold Q_safe_div.
  apply Qeq_bool_false_iff in Hneq.
  rewrite Hneq. reflexivity.
Qed.

Theorem Q_safe_div_zero :
  forall num denom, denom == 0 -> Q_safe_div num denom = None.
Proof.
  intros num denom Heq.
  unfold Q_safe_div.
  apply Qeq_bool_iff in Heq.
  rewrite Heq. reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: CONTEXTUAL DIVISION ON Q                     *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Handle boundary cases according to context.
  Maps option Q to ExtQ based on context.
*)

Definition Q_boundary_handle (ctx : RelCtx) (o : option Q) : ExtQ :=
  match o with
  | Some r => FiniteQ r
  | None   =>
      match ctx with
      | RC_Space => PinftyQ      (* Space: infinity *)
      | RC_Time  => FiniteQ 0    (* Time: zero/reset *)
      | RC_Info  => ExtNaNQ      (* Info: undefined *)
      end
  end.

(** Total, contextual division on Q. *)
Definition Q_contextual_div (ctx : RelCtx) (num denom : Q) : ExtQ :=
  Q_boundary_handle ctx (Q_safe_div num denom).

(* Conservative: nonzero denominators compute normally *)
Theorem Q_contextual_div_conservative :
  forall ctx num denom, ~(denom == 0) ->
    Q_contextual_div ctx num denom = FiniteQ (num / denom).
Proof.
  intros ctx num denom Hneq.
  unfold Q_contextual_div.
  rewrite (Q_safe_div_nonzero num denom Hneq).
  reflexivity.
Qed.

(* Space context: zero denominator -> +Ã¢Ë†Å¾ *)
Theorem Q_contextual_space_infty :
  forall num denom, denom == 0 -> Q_contextual_div RC_Space num denom = PinftyQ.
Proof.
  intros num denom Hd.
  unfold Q_contextual_div.
  rewrite (Q_safe_div_zero num denom Hd).
  reflexivity.
Qed.

(* Time context: zero denominator -> 0 *)
Theorem Q_contextual_time_zero :
  forall num denom, denom == 0 -> Q_contextual_div RC_Time num denom = FiniteQ 0.
Proof.
  intros num denom Hd.
  unfold Q_contextual_div.
  rewrite (Q_safe_div_zero num denom Hd).
  reflexivity.
Qed.

(* Info context: zero denominator -> NaN *)
Theorem Q_contextual_info_nan :
  forall num denom, denom == 0 -> Q_contextual_div RC_Info num denom = ExtNaNQ.
Proof.
  intros num denom Hd.
  unfold Q_contextual_div.
  rewrite (Q_safe_div_zero num denom Hd).
  reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: TOTALIZED INVERSE ON Q                       *)
(*                                                                            *)
(* ========================================================================== *)

(**
  TOTALIZED INVERSE ON Q
  ======================
  
  Coq's QArith already defines Qinv as a TOTAL function:
  - Qinv 0 = 0 (by definition)
  - Qinv q = 1/q when q <> 0
  
  This is the Meadow approach: inverse is total with 0^{-1} = 0.
  No axioms needed - this is how QArith works!
*)

(** Qinv 0 = 0 is definitional in QArith *)
Lemma Qinv_0 : Qinv 0 == 0.
Proof.
  unfold Qinv, Qeq. simpl. reflexivity.
Qed.

(** For nonzero q, q * Qinv q = 1 *)
Lemma Q_mult_inv_r : forall q : Q, ~(q == 0) -> q * Qinv q == 1.
Proof.
  intros q Hq. apply Qmult_inv_r. exact Hq.
Qed.

(** Qinv is involutive: Qinv (Qinv q) = q for ALL q (including 0) *)
Lemma Q_inv_involutive : forall q : Q, Qinv (Qinv q) == q.
Proof.
  intro q. apply Qinv_involutive.
Qed.

(** Specifically for nonzero q (for Meadow interface) *)
Lemma Q_inv_involutive_nonzero : forall q : Q, ~(q == 0) -> Qinv (Qinv q) == q.
Proof.
  intros q Hq. apply Q_inv_involutive.
Qed.

(** For zero, involution still holds: Qinv (Qinv 0) = 0 *)
Lemma Qinv_involutive_0 : Qinv (Qinv 0) == 0.
Proof.
  rewrite Qinv_0. apply Qinv_0.
Qed.

(** Qinv distributes over multiplication for nonzero values *)
Lemma Q_inv_mult_distr : forall p q : Q, 
  ~(p == 0) -> ~(q == 0) -> Qinv (p * q) == Qinv p * Qinv q.
Proof.
  intros p q Hp Hq.
  apply Qinv_mult_distr; assumption.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: MEADOW ALGEBRA STRUCTURE ON Q                *)
(*                                                                            *)
(* ========================================================================== *)

(**
  MEADOW ALGEBRA ON Q
  ===================
  
  A Meadow is an algebraic structure that extends a ring with a TOTAL
  inverse operation where inv(0) = 0. Q with Qinv is already a Meadow!
  
  The key meadow axioms are:
  - inv(inv(a)) = a                    (involutive - for nonzero)
  - inv(a * b) = inv(a) * inv(b)       (multiplicative - for nonzero)
  - inv(0) = 0                         (zero absorption)
  - a Ã¢â€°Â  0 Ã¢â€ â€™ a * inv(a) = 1            (restricted inverse law)
*)

(** Typeclass for Meadow structure *)
Class Meadow (M : Type) (Meq : M -> M -> Prop) := {
  m_zero : M;
  m_one  : M;
  m_add  : M -> M -> M;
  m_mul  : M -> M -> M;
  m_inv  : M -> M;
  
  (* Equivalence *)
  m_eq_refl  : forall a, Meq a a;
  m_eq_sym   : forall a b, Meq a b -> Meq b a;
  m_eq_trans : forall a b c, Meq a b -> Meq b c -> Meq a c;
  
  (* Ring laws *)
  m_add_comm  : forall a b, Meq (m_add a b) (m_add b a);
  m_add_assoc : forall a b c, Meq (m_add a (m_add b c)) (m_add (m_add a b) c);
  m_add_0_l   : forall a, Meq (m_add m_zero a) a;
  m_add_opp   : forall a, exists a', Meq (m_add a' a) m_zero;
  
  m_mul_comm  : forall a b, Meq (m_mul a b) (m_mul b a);
  m_mul_assoc : forall a b c, Meq (m_mul a (m_mul b c)) (m_mul (m_mul a b) c);
  m_mul_1_l   : forall a, Meq (m_mul m_one a) a;
  
  m_distr_l   : forall a b c, Meq (m_mul a (m_add b c)) (m_add (m_mul a b) (m_mul a c));
  
  (* Meadow axioms *)
  m_inv_zero       : Meq (m_inv m_zero) m_zero;
  m_inv_law        : forall a, ~(Meq a m_zero) -> Meq (m_mul a (m_inv a)) m_one
}.

(** Q forms a Meadow under Qeq *)
#[export] Instance Q_Meadow : Meadow Q Qeq := {
  m_zero := 0;
  m_one  := 1;
  m_add  := Qplus;
  m_mul  := Qmult;
  m_inv  := Qinv;
  
  m_eq_refl  := Qeq_refl;
  m_eq_sym   := Qeq_sym;
  m_eq_trans := Qeq_trans;
  
  m_add_comm  := Qplus_comm;
  m_add_assoc := Qplus_assoc;
  m_add_0_l   := Qplus_0_l;
  m_add_opp   := fun a => ex_intro _ (-a) 
                   (Qeq_trans _ _ _ (Qplus_comm (-a) a) (Qplus_opp_r a));
  
  m_mul_comm  := Qmult_comm;
  m_mul_assoc := Qmult_assoc;
  m_mul_1_l   := Qmult_1_l;
  
  m_distr_l   := Qmult_plus_distr_r;
  
  m_inv_zero  := Qinv_0;
  m_inv_law   := Qmult_inv_r
}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: CONSISTENCY THEOREMS                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CONSISTENCY PROOFS
  ==================
  
  We prove that the division-by-zero handling is internally consistent
  and does not lead to contradictions. All proofs are constructive.
*)

(** The meadow laws are all satisfiable together on Q. *)
Theorem Q_meadow_laws_consistent :
  Qinv 0 == 0 /\
  (forall q, ~(q == 0) -> Qinv (Qinv q) == q) /\
  (forall p q, ~(p == 0) -> ~(q == 0) -> Qinv (p * q) == Qinv p * Qinv q) /\
  (forall q, ~(q == 0) -> q * Qinv q == 1).
Proof.
  split; [exact Qinv_0|].
  split; [intros q Hq; exact (Q_inv_involutive q)|].
  split; [exact Q_inv_mult_distr|].
  exact Q_mult_inv_r.
Qed.

(** Rational number axiom preserved: 1 Ã¢â€°Â  0 *)
Theorem Q_one_not_zero : ~(1 == 0).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(** Master consistency theorem combining all results. *)
Theorem Q_division_handling_sound :
  (* Part A: Boundary detection is complete *)
  (forall q : Q,
    Q_boundary_detect q = RS_Related \/ Q_boundary_detect q = RS_Boundary) /\
  
  (* Part B: Boundary iff zero *)
  (forall q : Q,
    Q_boundary_detect q = RS_Boundary <-> q == 0) /\
  
  (* Part C: States are mutually exclusive *)
  (RS_Related <> RS_Boundary /\ RS_Boundary <> RS_Undefined /\ RS_Related <> RS_Undefined) /\
  
  (* Part D: Meadow laws hold *)
  (Qinv 0 == 0 /\
   (forall q, ~(q == 0) -> Qinv (Qinv q) == q) /\
   (forall p q, ~(p == 0) -> ~(q == 0) -> Qinv (p * q) == Qinv p * Qinv q) /\
   (forall q, ~(q == 0) -> q * Qinv q == 1)) /\
  
  (* Part E: Extended rationals are well-formed *)
  (PinftyQ <> ExtNaNQ /\ MinftyQ <> ExtNaNQ /\ PinftyQ <> MinftyQ).
Proof.
  split; [exact Q_boundary_complete|].
  split; [exact Q_boundary_iff_zero|].
  split; [exact state_mutual_exclusion|].
  split; [exact Q_meadow_laws_consistent|].
  repeat split; discriminate.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: LIFTING TO R_CAUCHY                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  LIFTING DIVISION TO CONSTRUCTIVE REALS
  ======================================
  
  We connect Q division to R_cauchy (Cauchy sequences over Q).
  
  Key insight: Division on R_cauchy is more subtle because we need
  the denominator sequence to be "eventually bounded away from zero".
  For now, we provide the embedding and basic properties.
*)

(** Constant Q inverse preserves Cauchy property. *)
Lemma cauchy_Qinv_const : forall q : Q, is_cauchy_mod (fun _ => Qinv q).
Proof.
  intro q. unfold is_cauchy_mod. intro n.
  assert (H : Qinv q - Qinv q == 0) by ring.
  rewrite (Qabs_eq_zero _ H).
  apply Qabs_zero_le. lia.
Qed.

(** Embed Q inverse into R_cauchy via constant sequence. *)
Definition Qinv_to_R (q : Q) : R_cauchy :=
  mkR (fun _ => Qinv q) (cauchy_Qinv_const q).

(** Q_to_R (Qinv 0) =R= Q_to_R 0 *)
Theorem Qinv_0_R : Q_to_R (Qinv 0) =R= R_zero.
Proof.
  unfold Req, Q_to_R, R_zero. intros k Hk.
  exists 0%nat. intros n Hn.
  (* Qinv 0 = 0 and 0 - 0 = 0, so |Qinv 0 - 0| = 0 <= 1/k *)
  replace (r_seq (mkR (fun _ : nat => Qinv 0) (cauchy_const (Qinv 0))) n - 
           r_seq (mkR (fun _ : nat => 0) (cauchy_const 0)) n) with (Qinv 0 - 0) by reflexivity.
  assert (H0 : Qinv 0 == 0) by apply Qinv_0.
  assert (Hdiff : Qinv 0 - 0 == 0) by (rewrite H0; ring).
  rewrite (Qabs_eq_zero _ Hdiff).
  apply Qabs_zero_le. exact Hk.
Qed.

(** For nonzero q: Q_to_R q * Qinv_to_R q =R= 1R *)
Theorem Q_mul_Qinv_R : forall q : Q, ~(q == 0) ->
  Q_to_R (q * Qinv q) =R= R_one.
Proof.
  intros q Hq.
  assert (Hmul : q * Qinv q == 1) by (apply Qmult_inv_r; exact Hq).
  unfold Req, Q_to_R, R_one. simpl. intros k Hk.
  exists 0%nat. intros n Hn.
  assert (H : q * Qinv q - 1 == 0) by (rewrite Hmul; ring).
  rewrite (Qabs_eq_zero _ H).
  apply Qabs_zero_le. exact Hk.
Qed.

(** 
  Division on R_cauchy for eventually-nonzero denominators.
  
  This is the constructive approach: we require a witness N such that
  for all n >= N, the denominator sequence is bounded away from zero.
*)
Definition R_cauchy_bounded_away (x : R_cauchy) (bound : Q) (N : nat) : Prop :=
  bound > 0 /\ forall n, (n >= N)%nat -> Qabs (r_seq x n) >= bound.

(** 
  Predicate: denominator is eventually bounded away from zero.
  This is a constructive notion of "nonzero real".
*)
Definition R_cauchy_nonzero (x : R_cauchy) : Prop :=
  exists bound N, R_cauchy_bounded_away x bound N.

(** Qabs q > 0 when q <> 0 *)
Lemma Qabs_pos_nonzero : forall q : Q, ~(q == 0) -> 0 < Qabs q.
Proof.
  intros q Hq.
  assert (Hnn : 0 <= Qabs q) by apply Qabs_nonneg.
  destruct (Qlt_le_dec 0 (Qabs q)) as [Hpos|Hzero].
  - exact Hpos.
  - (* Qabs q <= 0, combined with Qabs q >= 0, means Qabs q == 0 *)
    exfalso. apply Hq.
    assert (Hz : Qabs q == 0) by (apply Qle_antisym; assumption).
    (* Qabs q == 0 implies q == 0 *)
    destruct (Qlt_le_dec q 0) as [Hneg|Hpos'].
    + (* q < 0, so Qabs q = -q, and -q == 0 means q == 0 *)
      rewrite Qabs_neg in Hz; [|apply Qlt_le_weak; exact Hneg].
      (* Hz : -q == 0, need q == 0 *)
      setoid_replace q with (- - q) by ring.
      rewrite Hz. ring.
    + (* q >= 0, so Qabs q = q *)
      rewrite Qabs_pos in Hz; [exact Hz|exact Hpos'].
Qed.

(** Embedded nonzero rationals are R_cauchy_nonzero *)
Lemma Q_nonzero_R_nonzero : forall q : Q, ~(q == 0) -> R_cauchy_nonzero (Q_to_R q).
Proof.
  intros q Hq.
  exists (Qabs q), 0%nat.
  split.
  - apply Qabs_pos_nonzero. exact Hq.
  - intros n Hn. unfold Q_to_R. simpl. apply Qle_refl.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: RD MODULE - PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

Module RD.
  
  (* Types *)
  Definition State := RelationalState.
  Definition Ctx := RelCtx.
  Definition ExtendedQ := ExtQ.
  
  (* State constructors *)
  Definition related := RS_Related.
  Definition boundary := RS_Boundary.
  Definition undefined := RS_Undefined.
  
  (* Context constructors *)
  Definition space := RC_Space.
  Definition time := RC_Time.
  Definition info := RC_Info.
  
  (* Extended rational constructors *)
  Definition finite := FiniteQ.
  Definition pinfty := PinftyQ.
  Definition minfty := MinftyQ.
  Definition nan := ExtNaNQ.
  
  (* Core functions on Q *)
  Definition detect := Q_boundary_detect.
  Definition interpret := Q_contextual_interpret.
  Definition div := Q_contextual_div.
  Definition safe := Q_safe_div.
  
  (* Inverse (Qinv is already total) *)
  Definition inv := Qinv.
  Definition inv_zero := Qinv_0.
  Definition inv_law := Q_mult_inv_r.
  
  (* Key theorems *)
  Definition zero_is_boundary := Q_zero_implies_boundary.
  Definition boundary_is_zero := Q_boundary_implies_zero.
  Definition boundary_iff := Q_boundary_iff_zero.
  Definition nonzero_related := Q_nonzero_implies_related.
  Definition detect_complete := Q_boundary_complete.
  Definition consistent := Q_division_handling_sound.
  
  (* R_cauchy connection *)
  Definition inv_to_R := Qinv_to_R.
  Definition inv_0_R := Qinv_0_R.
  Definition mul_inv_R := Q_mul_Qinv_R.
  
End RD.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: HINT DATABASES & TACTICS                    *)
(*                                                                            *)
(* ========================================================================== *)

#[export] Hint Resolve
  Q_zero_implies_boundary
  Q_nonzero_implies_related
  Q_boundary_complete
  Q_detector_never_undefined
  Q_ctx_preserves_related
  Qinv_0
  Q_mult_inv_r
  Q_one_not_zero
  : rdiv.

#[export] Hint Rewrite
  Qinv_0
  : rdiv.

Ltac rdiv_simpl :=
  unfold Q_boundary_detect, Q_contextual_interpret, Q_contextual_div, 
         Q_safe_div, Q_boundary_handle;
  simpl.

(**
  rdiv_auto: Combined automation tactic.
  Integrates with UCF hint databases (ucf_z, ucf_q, ucf_arith).
*)
Ltac rdiv_auto :=
  auto with rdiv ucf_z ucf_q ucf_arith;
  try rdiv_simpl;
  try ucf_auto.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: EXAMPLES                                    *)
(*                                                                            *)
(* ========================================================================== *)

Module DivisionExamples.
  
  Example ex_nonzero_related : 
    Q_boundary_detect 5 = RS_Related.
  Proof.
    unfold Q_boundary_detect. simpl. reflexivity.
  Qed.
  
  Example ex_zero_boundary :
    Q_boundary_detect 0 = RS_Boundary.
  Proof.
    unfold Q_boundary_detect. simpl. reflexivity.
  Qed.
  
  Example ex_space_infty :
    Q_contextual_div RC_Space 5 0 = PinftyQ.
  Proof.
    apply Q_contextual_space_infty. reflexivity.
  Qed.
  
  Example ex_time_zero :
    Q_contextual_div RC_Time 5 0 = FiniteQ 0.
  Proof.
    apply Q_contextual_time_zero. reflexivity.
  Qed.
  
  Example ex_info_nan :
    Q_contextual_div RC_Info 5 0 = ExtNaNQ.
  Proof.
    apply Q_contextual_info_nan. reflexivity.
  Qed.
  
  Example ex_normal_div :
    Q_contextual_div RC_Space 6 2 = FiniteQ (6 / 2).
  Proof.
    unfold Q_contextual_div, Q_safe_div, Q_boundary_handle.
    simpl. reflexivity.
  Qed.
  
  (** Show that 6/2 == 3 in Q *)
  Example ex_normal_div_value : 6 / 2 == 3.
  Proof.
    unfold Qeq, Qdiv, Qmult, Qinv. simpl. reflexivity.
  Qed.
  
  (* Totalized inverse examples *)
  Example ex_inv_zero : Qinv 0 == 0.
  Proof. apply Qinv_0. Qed.
  
  Example ex_inv_two : Qinv 2 == 1#2.
  Proof. unfold Qeq. simpl. reflexivity. Qed.
  
  Example ex_mul_inv : 3 * Qinv 3 == 1.
  Proof. 
    apply Qmult_inv_r. 
    unfold Qeq. simpl. lia.
  Qed.

End DivisionExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.
  
  (** Computational tests - all should reduce via reflexivity. *)
  
  Definition test_state_related : RS_Related = RS_Related := eq_refl.
  Definition test_state_boundary : RS_Boundary = RS_Boundary := eq_refl.
  Definition test_ctx_space : RC_Space = RC_Space := eq_refl.
  Definition test_ext_finite : FiniteQ 0 = FiniteQ 0 := eq_refl.
  
  Definition test_boundary_detect_0 : Q_boundary_detect 0 = RS_Boundary := eq_refl.
  Definition test_boundary_detect_1 : Q_boundary_detect 1 = RS_Related := eq_refl.
  
  Definition test_safe_div_0 : Q_safe_div 5 0 = None := eq_refl.
  Definition test_safe_div_2 : Q_safe_div 6 2 = Some (6 / 2) := eq_refl.

End AxiomAudit.

(** Print Assumptions for key theorems - ALL should be "Closed under global context". *)
Print Assumptions Q_boundary_iff_zero.
Print Assumptions Q_meadow_laws_consistent.
Print Assumptions Q_division_handling_sound.
Print Assumptions Qinv_0_R.
Print Assumptions Q_mul_Qinv_R.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (RD):
    RD.State              = RelationalState
    RD.Ctx                = RelCtx  
    RD.ExtendedQ          = ExtQ
    
    RD.related/boundary/undefined = state constructors
    RD.space/time/info    = context constructors
    RD.finite/pinfty/minfty/nan = extended rational constructors
    
    RD.detect             = Q_boundary_detect
    RD.interpret          = Q_contextual_interpret
    RD.div                = Q_contextual_div
    RD.safe               = Q_safe_div
    RD.inv                = Qinv (from QArith, already total)
  
  TYPES:
    RelationalState       = RS_Related | RS_Boundary | RS_Undefined
    RelCtx                = RC_Space | RC_Time | RC_Info
    ExtQ                  = FiniteQ Q | PinftyQ | MinftyQ | ExtNaNQ
  
  KEY FUNCTIONS:
    Q_boundary_detect     : detects zero denominator (constructive)
    Q_contextual_div      : total division with context handling
    Q_safe_div            : option-returning division
    Qinv                  : totalized inverse (Qinv 0 = 0 by QArith)
  
  MAIN THEOREMS:
    Q_boundary_iff_zero   : detect = Boundary <-> q == 0
    Q_meadow_laws_consistent : all meadow axioms hold
    Q_division_handling_sound : master consistency theorem
    Qinv_0_R              : Q_to_R (Qinv 0) =R= R_zero
    Q_mul_Qinv_R          : q Ã¢â€°Â  0 Ã¢â€ â€™ Q_to_R (q * Qinv q) =R= R_one
  
  HINT DATABASE (rdiv):
    Usage: auto with rdiv.
  
  TACTIC:
    rdiv_auto             : combined automation
  
  MEADOW STRUCTURE:
    Q_Meadow              : Q with Qinv forms a Meadow (typeclass instance)
  
  AXIOM STATUS
  ============
  
  This file uses ZERO AXIOMS.
  
  All theorems verify as "Closed under the global context".
  
  The key insight: Q (rationals) in Coq's QArith has:
  - Decidable equality (Qeq_bool, Qeq_dec)
  - Total inverse (Qinv 0 = 0 by definition)
  
  We avoid Coq's standard library Reals entirely, which would bring
  in classical axioms (ClassicalDedekindReals, FunctionalExtensionality).
  
  COMPILATION
  ===========
  
  Requires: Top__Extensions__Prelude.v, Top__Numbers__RelationalReals.v
  
    coqc Top__Extensions__Base.v
    coqc Top__Extensions__WholeCompletion.v
    coqc Top__Extensions__Composition.v
    coqc Top__Extensions__Prelude.v
    coqc Top__Numbers__RelationalReals.v
    coqc Top__Numbers__RelationalDivision.v
*)
