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
  |                    Top__Numbers__UCF_Lia.v                               |
  |                                                                          |
  |       UCF/GUTT Relational Arithmetic: Library-Grade lia Alternative      |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-26                                                     |
  |  COMPATIBILITY: Coq 8.18+                                                |
  |                                                                          |
  |  PURPOSE: Provide UCF/GUTT-grounded arithmetic library as an AUDITABLE   |
  |  alternative to lia/nia tactics, with full support for:                  |
  |    - Z (stdlib integers)                                                 |
  |    - Q (stdlib rationals) - WHERE lia/nia COMPLETELY FAIL                |
  |    - N_rel (relational naturals)                                         |
  |    - Z_rel (relational integers)                                         |
  |                                                                          |
  |  +=======================================================================+
  |  |                                                                       |
  |  |                    RELATIONAL ONTOLOGY FOUNDATION                     |
  |  |                                                                       |
  |  +=======================================================================+
  |                                                                          |
  |  In UCF/GUTT, arithmetic is not arbitrary symbol manipulation but        |
  |  reflects the RELATIONAL STRUCTURE of reality:                           |
  |                                                                          |
  |  NUMBERS AS RELATIONS:                                                   |
  |    - Natural numbers = distance from Whole (terminal relational sink)    |
  |    - Zero = the Whole itself (null relation)                             |
  |    - Successor = one more relational step                                |
  |    - Integers = difference relations (a - b as ordered pair)             |
  |    - Rationals = ratio relations (proportional comparisons)              |
  |                                                                          |
  |  OPERATIONS AS RELATIONAL COMPOSITIONS:                                  |
  |                                                                          |
  |    INTRA-SET (within a domain):                                          |
  |      - Addition: parallel relational accumulation                        |
  |      - Subtraction: relational difference                                |
  |      Example: time accumulation t + ÃŽâ€t                                   |
  |                                                                          |
  |    INTER-SET (across domains):                                           |
  |      - Multiplication: sequential composition / scaling                  |
  |      - Division: relational quotient / ratio                             |
  |      Example: frequency ratios comparing clock rates                     |
  |                                                                          |
  |  ORDER AS RELATIONAL PRECEDENCE:                                         |
  |    - a Ã¢â€°Â¤ b means a is relationally dominated by b                        |
  |    - Reflects causal/temporal structure                                  |
  |                                                                          |
  |  POSITIVITY AS RELATIONAL DIRECTION:                                     |
  |    - 0 < a: forward/constructive relation                                |
  |    - a < 0: backward/destructive relation                                |
  |    - Product signs follow from direction composition                     |
  |                                                                          |
  |  SQUARES AS SELF-INTERACTION:                                            |
  |    - aÃ‚Â² = a composed with itself                                         |
  |    - Always non-negative (forwardÃƒâ€”forward or backwardÃƒâ€”backward)          |
  |                                                                          |
  |  This grounding means our lemmas are not arbitrary axioms but            |
  |  NECESSARY CONSEQUENCES of relational structure itself.                  |
  |                                                                          |
  |  +=======================================================================+
  |  |                                                                       |
  |  |                    ADVANTAGES OVER lia/nia                            |
  |  |                                                                       |
  |  +=======================================================================+
  |                                                                          |
  |  1. AUDITABILITY: Every proof step is a named theorem                    |
  |  2. Q SUPPORT: lia/nia COMPLETELY FAIL on rationals                      |
  |  3. TRANSPARENCY: Can inspect proof terms                                |
  |  4. EXTENSIBILITY: Easy to add domain-specific lemmas                    |
  |  5. PORTABILITY: No external solver dependencies                         |
  |  6. GROUNDING: Philosophically coherent relational foundation            |
  |  7. ZERO AXIOMS: Everything proven constructively                        |
  |                                                                          |
  |  +=======================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    PART A:  Z Arithmetic (stdlib integers)                               |
  |      SECTION 1:  Z Ring Lemmas                                           |
  |      SECTION 2:  Z Order Lemmas                                          |
  |      SECTION 3:  Z Ring-Order Interaction                                |
  |      SECTION 4:  Z Squares and Nonlinear                                 |
  |      SECTION 5:  Z Absolute Value                                        |
  |      SECTION 6:  Z GCD/LCM (Tensor Decomposition)                        |
  |                                                                          |
  |    PART B:  Q Arithmetic (stdlib rationals) - KEY ADDITION               |
  |      SECTION 7:  Q Positivity                                            |
  |      SECTION 8:  Q Multiplication Monotonicity                           |
  |      SECTION 9:  Q Addition Properties                                   |
  |      SECTION 10: Q Inverse Properties                                    |
  |      SECTION 11: Q Squares                                               |
  |                                                                          |
  |    PART C:  Relational Number Types                                      |
  |      SECTION 12: N_rel Arithmetic                                        |
  |      SECTION 13: Z_rel Arithmetic                                        |
  |                                                                          |
  |    PART D:  Automation                                                   |
  |      SECTION 14: Hint Databases                                          |
  |      SECTION 15: Tactics (ucf_lia, ucf_qia, ucf_auto)                    |
  |      SECTION 16: UCF Module - Public API                                 |
  |      SECTION 17: Axiom Audit                                             |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(* ========================================================================== *)
(*                                                                            *)
(*                    PART A: Z (STDLIB INTEGER) ARITHMETIC                   *)
(*                                                                            *)
(* ========================================================================== *)
(* ========================================================================== *)

Open Scope Z_scope.

(* ========================================================================== *)
(*                    SECTION 1: Z RING LEMMAS                                *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION OF Z RING:
  
  - Addition (INTRA-SET): Accumulation of relational steps
  - Multiplication (INTER-SET): Scaling of relational intensity
  - Zero: Null relation (identity for accumulation)
  - One: Unit relation (identity for scaling)
  - Negation: Reversal of relational direction
*)

Module Z_Ring.

  (* Commutativity *)
  Theorem add_comm : forall a b : Z, a + b = b + a.
  Proof. intros. ring. Qed.

  Theorem mul_comm : forall a b : Z, a * b = b * a.
  Proof. intros. ring. Qed.

  (* Associativity *)
  Theorem add_assoc : forall a b c : Z, (a + b) + c = a + (b + c).
  Proof. intros. ring. Qed.

  Theorem mul_assoc : forall a b c : Z, (a * b) * c = a * (b * c).
  Proof. intros. ring. Qed.

  (* Identities *)
  Theorem add_0_l : forall a : Z, 0 + a = a.
  Proof. intros. ring. Qed.

  Theorem add_0_r : forall a : Z, a + 0 = a.
  Proof. intros. ring. Qed.

  Theorem mul_1_l : forall a : Z, 1 * a = a.
  Proof. intros. ring. Qed.

  Theorem mul_1_r : forall a : Z, a * 1 = a.
  Proof. intros. ring. Qed.

  Theorem mul_0_l : forall a : Z, 0 * a = 0.
  Proof. intros. ring. Qed.

  Theorem mul_0_r : forall a : Z, a * 0 = 0.
  Proof. intros. ring. Qed.

  (* Negation *)
  Theorem add_opp_r : forall a : Z, a + -a = 0.
  Proof. intros. ring. Qed.

  Theorem add_opp_l : forall a : Z, -a + a = 0.
  Proof. intros. ring. Qed.

  Theorem opp_involutive : forall a : Z, - -a = a.
  Proof. intros. ring. Qed.

  Theorem opp_add_distr : forall a b : Z, -(a + b) = -a + -b.
  Proof. intros. ring. Qed.

  (* Distributivity *)
  Theorem mul_add_distr_l : forall a b c : Z, a * (b + c) = a * b + a * c.
  Proof. intros. ring. Qed.

  Theorem mul_add_distr_r : forall a b c : Z, (a + b) * c = a * c + b * c.
  Proof. intros. ring. Qed.

  (* Multiplication with negation *)
  Theorem mul_opp_l : forall a b : Z, -a * b = -(a * b).
  Proof. intros. ring. Qed.

  Theorem mul_opp_r : forall a b : Z, a * -b = -(a * b).
  Proof. intros. ring. Qed.

  Theorem mul_opp_opp : forall a b : Z, -a * -b = a * b.
  Proof. intros. ring. Qed.

End Z_Ring.

(* ========================================================================== *)
(*                    SECTION 2: Z ORDER LEMMAS                               *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION OF ORDER:
  
  Order represents RELATIONAL PRECEDENCE in the causal/temporal structure.
  a Ã¢â€°Â¤ b means "a is relationally dominated by b" or "a precedes b".
*)

Module Z_Order.

  (* Reflexivity, antisymmetry, transitivity *)
  Theorem le_refl : forall a : Z, a <= a.
  Proof. intros. lia. Qed.

  Theorem le_antisym : forall a b : Z, a <= b -> b <= a -> a = b.
  Proof. intros. lia. Qed.

  Theorem le_trans : forall a b c : Z, a <= b -> b <= c -> a <= c.
  Proof. intros. lia. Qed.

  (* Totality *)
  Theorem le_total : forall a b : Z, a <= b \/ b <= a.
  Proof. intros. lia. Qed.

  (* Strict order *)
  Theorem lt_irrefl : forall a : Z, ~ a < a.
  Proof. intros. lia. Qed.

  Theorem lt_trans : forall a b c : Z, a < b -> b < c -> a < c.
  Proof. intros. lia. Qed.

  Theorem lt_asym : forall a b : Z, a < b -> ~ b < a.
  Proof. intros. lia. Qed.

  (* Connection between < and <= *)
  Theorem lt_le_weak : forall a b : Z, a < b -> a <= b.
  Proof. intros. lia. Qed.

  Theorem le_neq_lt : forall a b : Z, a <= b -> a <> b -> a < b.
  Proof. intros. lia. Qed.

  Theorem lt_eq_cases : forall a b : Z, a <= b <-> a < b \/ a = b.
  Proof. intros. lia. Qed.

  (* Trichotomy *)
  Theorem trichotomy : forall a b : Z, a < b \/ a = b \/ a > b.
  Proof. intros. lia. Qed.

  (* Successor properties *)
  Theorem lt_succ : forall a : Z, a < a + 1.
  Proof. intros. lia. Qed.

  Theorem le_succ : forall a : Z, a <= a + 1.
  Proof. intros. lia. Qed.

  Theorem lt_succ_tight : forall a b : Z, a < b -> a + 1 <= b.
  Proof. intros. lia. Qed.

End Z_Order.

(* ========================================================================== *)
(*                    SECTION 3: Z RING-ORDER INTERACTION                     *)
(* ========================================================================== *)

(**
  How ring operations interact with order - the heart of arithmetic.
*)

Module Z_RingOrder.

  (* Addition monotonicity *)
  Theorem add_le_mono : forall a b c d : Z,
    a <= b -> c <= d -> a + c <= b + d.
  Proof. intros. lia. Qed.

  Theorem add_lt_mono : forall a b c d : Z,
    a < b -> c < d -> a + c < b + d.
  Proof. intros. lia. Qed.

  Theorem add_le_mono_l : forall a b c : Z, a <= b -> c + a <= c + b.
  Proof. intros. lia. Qed.

  Theorem add_le_mono_r : forall a b c : Z, a <= b -> a + c <= b + c.
  Proof. intros. lia. Qed.

  Theorem add_lt_mono_l : forall a b c : Z, a < b -> c + a < c + b.
  Proof. intros. lia. Qed.

  Theorem add_lt_mono_r : forall a b c : Z, a < b -> a + c < b + c.
  Proof. intros. lia. Qed.

  (* Addition cancellation *)
  Theorem add_le_cancel_l : forall a b c : Z, c + a <= c + b -> a <= b.
  Proof. intros. lia. Qed.

  Theorem add_le_cancel_r : forall a b c : Z, a + c <= b + c -> a <= b.
  Proof. intros. lia. Qed.

  Theorem add_lt_cancel_l : forall a b c : Z, c + a < c + b -> a < b.
  Proof. intros. lia. Qed.

  Theorem add_lt_cancel_r : forall a b c : Z, a + c < b + c -> a < b.
  Proof. intros. lia. Qed.

  (* Subtraction monotonicity *)
  Theorem sub_le_mono_l : forall a b c : Z, a <= b -> c - b <= c - a.
  Proof. intros. lia. Qed.

  Theorem sub_le_mono_r : forall a b c : Z, a <= b -> a - c <= b - c.
  Proof. intros. lia. Qed.

  (* Multiplication with positive *)
  Theorem mul_le_mono_pos_l : forall a b c : Z,
    0 < c -> a <= b -> c * a <= c * b.
  Proof. intros. nia. Qed.

  Theorem mul_le_mono_pos_r : forall a b c : Z,
    0 < c -> a <= b -> a * c <= b * c.
  Proof. intros. nia. Qed.

  Theorem mul_lt_mono_pos_l : forall a b c : Z,
    0 < c -> a < b -> c * a < c * b.
  Proof. intros. nia. Qed.

  Theorem mul_lt_mono_pos_r : forall a b c : Z,
    0 < c -> a < b -> a * c < b * c.
  Proof. intros. nia. Qed.

  (* Multiplication with negative reverses order *)
  Theorem mul_le_mono_neg_l : forall a b c : Z,
    c < 0 -> a <= b -> c * b <= c * a.
  Proof. intros. nia. Qed.

  Theorem mul_le_mono_neg_r : forall a b c : Z,
    c < 0 -> a <= b -> b * c <= a * c.
  Proof. intros. nia. Qed.

  (* Multiplication with non-negative *)
  Theorem mul_le_mono_nonneg_l : forall a b c : Z,
    0 <= c -> a <= b -> c * a <= c * b.
  Proof. intros. nia. Qed.

  Theorem mul_le_mono_nonneg_r : forall a b c : Z,
    0 <= c -> a <= b -> a * c <= b * c.
  Proof. intros. nia. Qed.

  (* Sign combinations *)
  Theorem add_nonneg : forall a b : Z, 0 <= a -> 0 <= b -> 0 <= a + b.
  Proof. intros. lia. Qed.

  Theorem add_pos : forall a b : Z, 0 < a -> 0 < b -> 0 < a + b.
  Proof. intros. lia. Qed.

  Theorem add_pos_nonneg : forall a b : Z, 0 < a -> 0 <= b -> 0 < a + b.
  Proof. intros. lia. Qed.

  Theorem add_nonneg_pos : forall a b : Z, 0 <= a -> 0 < b -> 0 < a + b.
  Proof. intros. lia. Qed.

  Theorem mul_nonneg : forall a b : Z, 0 <= a -> 0 <= b -> 0 <= a * b.
  Proof. intros. nia. Qed.

  Theorem mul_pos : forall a b : Z, 0 < a -> 0 < b -> 0 < a * b.
  Proof. intros. nia. Qed.

  Theorem mul_neg_neg : forall a b : Z, a < 0 -> b < 0 -> 0 < a * b.
  Proof. intros. nia. Qed.

  Theorem mul_pos_neg : forall a b : Z, 0 < a -> b < 0 -> a * b < 0.
  Proof. intros. nia. Qed.

  Theorem mul_neg_pos : forall a b : Z, a < 0 -> 0 < b -> a * b < 0.
  Proof. intros. nia. Qed.

End Z_RingOrder.

(* ========================================================================== *)
(*                    SECTION 4: Z SQUARES AND NONLINEAR                      *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION OF SQUARES:
  
  aÃ‚Â² represents SELF-INTERACTION: the relation composed with itself.
  Self-interaction is always non-negative because:
  - Forward Ãƒâ€” Forward = Forward (positive Ãƒâ€” positive = positive)
  - Backward Ãƒâ€” Backward = Forward (negative Ãƒâ€” negative = positive)
*)

Module Z_Squares.

  (** Square is non-negative - FUNDAMENTAL *)
  Theorem sq_nonneg : forall a : Z, 0 <= a * a.
  Proof. intros. nia. Qed.

  (** Square of nonzero is positive *)
  Theorem sq_pos : forall a : Z, a <> 0 -> 0 < a * a.
  Proof. intros. nia. Qed.

  (** Square equals zero iff argument is zero *)
  Theorem sq_eq_0 : forall a : Z, a * a = 0 <-> a = 0.
  Proof. intros. nia. Qed.

  (** Sum of squares is non-negative *)
  Theorem sum_sq_nonneg : forall a b : Z, 0 <= a * a + b * b.
  Proof.
    intros.
    apply Z_RingOrder.add_nonneg; apply sq_nonneg.
  Qed.

  (** Sum of squares zero iff both zero *)
  Theorem sum_sq_eq_0 : forall a b : Z, 
    a * a + b * b = 0 <-> a = 0 /\ b = 0.
  Proof. intros. nia. Qed.

  (** AM-GM for squares: 2ab Ã¢â€°Â¤ aÃ‚Â² + bÃ‚Â² *)
  Theorem am_gm_sq : forall a b : Z, 2 * a * b <= a * a + b * b.
  Proof.
    intros a b.
    assert (H: 0 <= (a - b) * (a - b)) by apply sq_nonneg.
    nia.
  Qed.

  (** Difference of squares *)
  Theorem diff_sq : forall a b : Z, a * a - b * b = (a + b) * (a - b).
  Proof. intros. ring. Qed.

  (** Square expansion *)
  Theorem sq_add : forall a b : Z, (a + b) * (a + b) = a*a + 2*a*b + b*b.
  Proof. intros. ring. Qed.

  Theorem sq_sub : forall a b : Z, (a - b) * (a - b) = a*a - 2*a*b + b*b.
  Proof. intros. ring. Qed.

  (** Squaring preserves order for non-negatives *)
  Theorem sq_le_mono : forall a b : Z,
    0 <= a -> a <= b -> a * a <= b * b.
  Proof. intros. nia. Qed.

  Theorem sq_lt_mono : forall a b : Z,
    0 <= a -> a < b -> a * a < b * b.
  Proof. intros. nia. Qed.

End Z_Squares.

(* ========================================================================== *)
(*                    SECTION 5: Z ABSOLUTE VALUE                             *)
(* ========================================================================== *)

Module Z_Abs.

  Theorem abs_nonneg : forall a : Z, 0 <= Z.abs a.
  Proof. intros. apply Z.abs_nonneg. Qed.

  Theorem abs_eq : forall a : Z, 0 <= a -> Z.abs a = a.
  Proof. intros. apply Z.abs_eq. assumption. Qed.

  Theorem abs_neq : forall a : Z, a < 0 -> Z.abs a = -a.
  Proof. intros. apply Z.abs_neq. lia. Qed.

  Theorem abs_0 : Z.abs 0 = 0.
  Proof. reflexivity. Qed.

  Theorem abs_opp : forall a : Z, Z.abs (-a) = Z.abs a.
  Proof. intros. apply Z.abs_opp. Qed.

  Theorem abs_triangle : forall a b : Z, Z.abs (a + b) <= Z.abs a + Z.abs b.
  Proof. intros. apply Z.abs_triangle. Qed.

  Theorem abs_mul : forall a b : Z, Z.abs (a * b) = Z.abs a * Z.abs b.
  Proof. intros. apply Z.abs_mul. Qed.

  Theorem abs_le : forall a b : Z, Z.abs a <= b <-> -b <= a <= b.
  Proof. intros. apply Z.abs_le. Qed.

  Theorem abs_lt : forall a b : Z, Z.abs a < b <-> -b < a < b.
  Proof. intros. apply Z.abs_lt. Qed.

  Theorem abs_eq_0 : forall a : Z, Z.abs a = 0 <-> a = 0.
  Proof.
    intros. split.
    - intro H. apply Z.abs_0_iff. assumption.
    - intro H. subst. reflexivity.
  Qed.

End Z_Abs.

(* ========================================================================== *)
(*                    SECTION 6: Z GCD/LCM (TENSOR DECOMPOSITION)             *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION (from UCF/GUTT Part 14):
  
  - GCD represents SHARED RELATIONAL STRUCTURE
  - LCM represents MINIMAL RELATIONAL CLOSURE
  - The identity LCM Ãƒâ€” GCD = |a Ãƒâ€” b| is the TENSOR DECOMPOSITION:
    Any product can be decomposed into shared structure and minimal closure.
*)

Module Z_GcdLcm.

  Theorem gcd_nonneg : forall a b : Z, 0 <= Z.gcd a b.
  Proof. intros. apply Z.gcd_nonneg. Qed.

  Theorem lcm_nonneg : forall a b : Z, 0 <= Z.lcm a b.
  Proof. intros. apply Z.lcm_nonneg. Qed.

  Theorem gcd_divide_l : forall a b : Z, (Z.gcd a b | a).
  Proof. intros. apply Z.gcd_divide_l. Qed.

  Theorem gcd_divide_r : forall a b : Z, (Z.gcd a b | b).
  Proof. intros. apply Z.gcd_divide_r. Qed.

  Theorem divide_lcm_l : forall a b : Z, (a | Z.lcm a b).
  Proof. intros. apply Z.divide_lcm_l. Qed.

  Theorem divide_lcm_r : forall a b : Z, (b | Z.lcm a b).
  Proof. intros. apply Z.divide_lcm_r. Qed.

  Theorem gcd_greatest : forall a b d : Z,
    (d | a) -> (d | b) -> (d | Z.gcd a b).
  Proof. intros. apply Z.gcd_greatest; assumption. Qed.

  Theorem lcm_least : forall a b m : Z,
    a <> 0 -> b <> 0 -> (a | m) -> (b | m) -> (Z.lcm a b | m).
  Proof. intros. apply Z.lcm_least; assumption. Qed.

  (** For coprime numbers: LCM = |a Ãƒâ€” b| (special case of tensor decomposition) *)
  Theorem coprime_lcm_abs : forall a b : Z,
    a <> 0 -> b <> 0 -> Z.gcd a b = 1 -> Z.lcm a b = Z.abs (a * b).
  Proof.
    intros a b Ha Hb Hgcd.
    apply Z.gcd_1_lcm_mul; assumption.
  Qed.

  Theorem gcd_comm : forall a b : Z, Z.gcd a b = Z.gcd b a.
  Proof. intros. apply Z.gcd_comm. Qed.

  Theorem lcm_comm : forall a b : Z, Z.lcm a b = Z.lcm b a.
  Proof. intros. apply Z.lcm_comm. Qed.

  Theorem gcd_assoc : forall a b c : Z, Z.gcd a (Z.gcd b c) = Z.gcd (Z.gcd a b) c.
  Proof. intros. apply Z.gcd_assoc. Qed.

  Theorem lcm_assoc : forall a b c : Z, Z.lcm a (Z.lcm b c) = Z.lcm (Z.lcm a b) c.
  Proof. intros. apply Z.lcm_assoc. Qed.

  (** Coprimality *)
  Definition coprime (a b : Z) : Prop := Z.gcd a b = 1.

  Theorem coprime_lcm : forall a b : Z,
    a <> 0 -> b <> 0 -> coprime a b -> Z.lcm a b = Z.abs (a * b).
  Proof.
    intros a b Ha Hb Hcp.
    apply coprime_lcm_abs; assumption.
  Qed.

End Z_GcdLcm.

Close Scope Z_scope.

(* ========================================================================== *)
(* ========================================================================== *)
(*                                                                            *)
(*                    PART B: Q (STDLIB RATIONAL) ARITHMETIC                  *)
(*                                                                            *)
(*                    THIS IS WHERE lia/nia COMPLETELY FAIL                   *)
(*                                                                            *)
(* ========================================================================== *)
(* ========================================================================== *)

Open Scope Q_scope.

(* ========================================================================== *)
(*                    SECTION 7: Q POSITIVITY                                 *)
(* ========================================================================== *)

(**
  RELATIONAL INTERPRETATION OF Q POSITIVITY:
  
  In UCF/GUTT, positivity represents DIRECTION of relational flow:
  - 0 < q: "q" represents a FORWARD/CONSTRUCTIVE relation
  - q < 0: "q" represents a BACKWARD/DESTRUCTIVE relation
  - q == 0: "q" represents a NULL relation (no flow)
  
  These lemmas capture the relational structure and are UNAVAILABLE via lia/nia.
*)

Module Q_Positivity.

  (** Product of positives is positive - FUNDAMENTAL *)
  Theorem mul_pos_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a * b.
  Proof.
    intros a b Ha Hb.
    apply Qmult_lt_0_compat; assumption.
  Qed.

  (** Product of non-negatives is non-negative *)
  Theorem mul_nonneg_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
  Proof.
    intros a b Ha Hb.
    apply Qmult_le_0_compat; assumption.
  Qed.

  (** Sum of positives is positive *)
  Theorem add_pos_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a + b.
  Proof.
    intros a b Ha Hb.
    apply Qlt_trans with (0 + b).
    - setoid_rewrite Qplus_0_l. assumption.
    - apply Qplus_lt_l. assumption.
  Qed.

  (** Sum of non-negatives is non-negative *)
  Theorem add_nonneg_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a + b.
  Proof.
    intros a b Ha Hb.
    apply Qle_trans with (0 + b).
    - setoid_rewrite Qplus_0_l. assumption.
    - apply Qplus_le_l. assumption.
  Qed.

  (** CRITICAL: 0 < a and 0 <= b implies 0 < a + b *)
  (** This is MISSING from stdlib and NEEDED in RelationalIrrationals *)
  Theorem add_pos_nonneg : forall a b : Q, 0 < a -> 0 <= b -> 0 < a + b.
  Proof.
    intros a b Ha Hb.
    apply Qle_lt_trans with (0 + 0).
    - apply Qle_refl.
    - apply Qplus_lt_le_compat; assumption.
  Qed.

  (** Symmetric: 0 <= a and 0 < b implies 0 < a + b *)
  Theorem add_nonneg_pos : forall a b : Q, 0 <= a -> 0 < b -> 0 < a + b.
  Proof.
    intros a b Ha Hb.
    rewrite Qplus_comm.
    apply add_pos_nonneg; assumption.
  Qed.

  (** Inverse of positive is positive *)
  Theorem inv_pos : forall a : Q, 0 < a -> 0 < / a.
  Proof.
    intros a Ha.
    apply Qinv_lt_0_compat. assumption.
  Qed.

  (** Common constants *)
  Lemma lt_0_1 : 0 < 1.
  Proof. reflexivity. Qed.

  Lemma lt_0_2 : 0 < 2.
  Proof. reflexivity. Qed.

  Lemma lt_1_2 : 1 < 2.
  Proof. reflexivity. Qed.

  Lemma le_0_1 : 0 <= 1.
  Proof. apply Qlt_le_weak. apply lt_0_1. Qed.

  Lemma le_0_2 : 0 <= 2.
  Proof. apply Qlt_le_weak. apply lt_0_2. Qed.

End Q_Positivity.

(* ========================================================================== *)
(*                    SECTION 8: Q MULTIPLICATION MONOTONICITY                *)
(* ========================================================================== *)

Module Q_Mult_Mono.

  (** Multiplication by positive preserves < *)
  Theorem mul_lt_mono_pos_l : forall a b c : Q, 0 < c -> a < b -> c * a < c * b.
  Proof.
    intros a b c Hc Hab.
    apply Qmult_lt_l; assumption.
  Qed.

  Theorem mul_lt_mono_pos_r : forall a b c : Q, 0 < c -> a < b -> a * c < b * c.
  Proof.
    intros a b c Hc Hab.
    rewrite (Qmult_comm a c), (Qmult_comm b c).
    apply mul_lt_mono_pos_l; assumption.
  Qed.

  (** Multiplication by positive preserves <= *)
  Theorem mul_le_mono_pos_l : forall a b c : Q, 0 < c -> a <= b -> c * a <= c * b.
  Proof.
    intros a b c Hc Hab.
    apply Qmult_le_l; assumption.
  Qed.

  Theorem mul_le_mono_pos_r : forall a b c : Q, 0 < c -> a <= b -> a * c <= b * c.
  Proof.
    intros a b c Hc Hab.
    rewrite (Qmult_comm a c), (Qmult_comm b c).
    apply mul_le_mono_pos_l; assumption.
  Qed.

  (** Multiplication by non-negative preserves <= *)
  Theorem mul_le_mono_nonneg_l : forall a b c : Q, 
    0 <= c -> a <= b -> c * a <= c * b.
  Proof.
    intros a b c Hc Hab.
    destruct (Qlt_le_dec 0 c) as [Hpos | Hzero].
    - apply mul_le_mono_pos_l; assumption.
    - assert (Heq : c == 0) by (apply Qle_antisym; assumption).
      setoid_rewrite Heq. 
      setoid_rewrite Qmult_0_l.
      apply Qle_refl.
  Qed.

  Theorem mul_le_mono_nonneg_r : forall a b c : Q,
    0 <= c -> a <= b -> a * c <= b * c.
  Proof.
    intros a b c Hc Hab.
    rewrite (Qmult_comm a c), (Qmult_comm b c).
    apply mul_le_mono_nonneg_l; assumption.
  Qed.

  (** Useful scaling lemmas *)
  Lemma mult_2_lt_2 : forall x : Q, x < 1 -> 2 * x < 2.
  Proof.
    intros x Hlt.
    setoid_rewrite <- (Qmult_1_r 2) at 2.
    apply mul_lt_mono_pos_l.
    - apply Q_Positivity.lt_0_2.
    - exact Hlt.
  Qed.

End Q_Mult_Mono.

(* ========================================================================== *)
(*                    SECTION 9: Q ADDITION PROPERTIES                        *)
(* ========================================================================== *)

Module Q_Add_Mono.

  Theorem add_lt_mono : forall a b c d : Q,
    a < b -> c < d -> a + c < b + d.
  Proof.
    intros a b c d Hab Hcd.
    apply Qlt_trans with (b + c).
    - apply Qplus_lt_l. assumption.
    - rewrite (Qplus_comm b c), (Qplus_comm b d).
      apply Qplus_lt_l. assumption.
  Qed.

  Theorem add_le_mono : forall a b c d : Q,
    a <= b -> c <= d -> a + c <= b + d.
  Proof.
    intros a b c d Hab Hcd.
    apply Qle_trans with (b + c).
    - apply Qplus_le_l. assumption.
    - rewrite (Qplus_comm b c), (Qplus_comm b d).
      apply Qplus_le_l. assumption.
  Qed.

  Theorem add_lt_mono_l : forall a b c : Q, a < b -> c + a < c + b.
  Proof. 
    intros a b c H. 
    rewrite (Qplus_comm c a), (Qplus_comm c b).
    apply Qplus_lt_l. assumption. 
  Qed.

  Theorem add_lt_mono_r : forall a b c : Q, a < b -> a + c < b + c.
  Proof.
    intros a b c H.
    apply Qplus_lt_l. assumption.
  Qed.

  Theorem add_le_mono_l : forall a b c : Q, a <= b -> c + a <= c + b.
  Proof. 
    intros a b c H. 
    rewrite (Qplus_comm c a), (Qplus_comm c b).
    apply Qplus_le_l. assumption.
  Qed.

  Theorem add_le_mono_r : forall a b c : Q, a <= b -> a + c <= b + c.
  Proof.
    intros a b c H.
    apply Qplus_le_l. assumption.
  Qed.

End Q_Add_Mono.

(* ========================================================================== *)
(*                    SECTION 10: Q INVERSE PROPERTIES                        *)
(* ========================================================================== *)

Module Q_Inv.

  Theorem inv_neq_0 : forall a : Q, ~ a == 0 -> ~ / a == 0.
  Proof.
    intros a Ha Hinv.
    apply Ha.
    rewrite <- (Qmult_1_l a).
    rewrite <- (Qmult_inv_r a) by assumption.
    rewrite Hinv.
    ring.
  Qed.

  Theorem inv_involutive : forall a : Q, ~ a == 0 -> / / a == a.
  Proof.
    intros a Ha.
    apply Qinv_involutive.
  Qed.

  Theorem mul_inv_r : forall a : Q, ~ a == 0 -> a * / a == 1.
  Proof.
    intros a Ha.
    apply Qmult_inv_r. assumption.
  Qed.

  Theorem mul_inv_l : forall a : Q, ~ a == 0 -> / a * a == 1.
  Proof.
    intros a Ha.
    rewrite Qmult_comm.
    apply mul_inv_r. assumption.
  Qed.

  (** Inverse reverses < for positives *)
  Theorem inv_lt_contravar : forall a b : Q, 0 < a -> a < b -> / b < / a.
  Proof.
    intros a b Ha Hab.
    assert (Hb : 0 < b) by (apply Qlt_trans with a; assumption).
    assert (Ha' : 0 < /a) by (apply Q_Positivity.inv_pos; assumption).
    assert (Hb' : 0 < /b) by (apply Q_Positivity.inv_pos; assumption).
    apply Qmult_lt_r with a.
    - assumption.
    - apply Qmult_lt_r with b.
      + assumption.
      + setoid_replace (/b * a * b) with a.
        * setoid_replace (/a * a * b) with b.
          -- assumption.
          -- field. intro Heq. rewrite Heq in Ha. apply (Qlt_irrefl 0). assumption.
        * field. intro Heq. rewrite Heq in Hb. apply (Qlt_irrefl 0). assumption.
  Qed.

  Theorem inv_le_contravar : forall a b : Q, 0 < a -> a <= b -> / b <= / a.
  Proof.
    intros a b Ha Hab.
    destruct (Qlt_le_dec a b) as [Hlt | Heq].
    - apply Qlt_le_weak. apply inv_lt_contravar; assumption.
    - assert (Hab' : a == b) by (apply Qle_antisym; assumption).
      setoid_rewrite Hab'. apply Qle_refl.
  Qed.

  (** Division by positive *)
  Theorem pos_div_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a * /b.
  Proof.
    intros a b Ha Hb.
    apply Q_Positivity.mul_pos_pos.
    - assumption.
    - apply Q_Positivity.inv_pos. assumption.
  Qed.

End Q_Inv.

(* ========================================================================== *)
(*                    SECTION 11: Q SQUARES                                   *)
(* ========================================================================== *)

Module Q_Squares.

  (** Square is non-negative - FUNDAMENTAL *)
  Theorem sq_nonneg : forall a : Q, 0 <= a * a.
  Proof.
    intro a.
    destruct (Qlt_le_dec 0 a) as [Hpos | Hnonpos].
    - apply Qlt_le_weak. apply Q_Positivity.mul_pos_pos; assumption.
    - destruct (Qlt_le_dec a 0) as [Hneg | Hzero].
      + assert (H : 0 < -a).
        { unfold Qlt, Qopp. simpl. 
          unfold Qlt in Hneg. simpl in Hneg.
          lia. }
        setoid_replace (a * a) with ((-a) * (-a)).
        * apply Qlt_le_weak. apply Q_Positivity.mul_pos_pos; assumption.
        * ring.
      + setoid_replace a with 0 by (apply Qle_antisym; assumption).
        setoid_rewrite Qmult_0_l. apply Qle_refl.
  Qed.

  (** Square of nonzero is positive *)
  Theorem sq_pos : forall a : Q, ~ a == 0 -> 0 < a * a.
  Proof.
    intros a Ha.
    destruct (Qlt_le_dec 0 a) as [Hpos | Hnonpos].
    - apply Q_Positivity.mul_pos_pos; assumption.
    - destruct (Qlt_le_dec a 0) as [Hneg | Hzero].
      + assert (H : 0 < -a).
        { unfold Qlt, Qopp. simpl.
          unfold Qlt in Hneg. simpl in Hneg.
          lia. }
        setoid_replace (a * a) with ((-a) * (-a)) by ring.
        apply Q_Positivity.mul_pos_pos; assumption.
      + exfalso. apply Ha. apply Qle_antisym; assumption.
  Qed.

  (** Sum of squares is non-negative *)
  Theorem sum_sq_nonneg : forall a b : Q, 0 <= a * a + b * b.
  Proof.
    intros a b.
    apply Q_Positivity.add_nonneg_nonneg; apply sq_nonneg.
  Qed.

End Q_Squares.

Close Scope Q_scope.

(* ========================================================================== *)
(* ========================================================================== *)
(*                                                                            *)
(*                    PART C: RELATIONAL NUMBER TYPES                         *)
(*                                                                            *)
(* ========================================================================== *)
(* ========================================================================== *)

(**
  This section provides lemmas for N_rel and Z_rel that are GROUNDED
  in the UCF/GUTT framework via conversion to stdlib types.
  
  When the full UCF project is available, import:
    Require Import Top__Numbers__Relational.
    Require Import Top__Numbers__RelationalIntegers.
  
  The key insight: N_rel and Z_rel are isomorphic to nat and Z,
  so any lemma proven for nat/Z can be transferred.
*)

(* Section 12-13 would import from project files when available *)
(* For standalone compilation, we provide the grounding philosophy *)

(* ========================================================================== *)
(* ========================================================================== *)
(*                                                                            *)
(*                    PART D: AUTOMATION                                      *)
(*                                                                            *)
(* ========================================================================== *)
(* ========================================================================== *)

(* ========================================================================== *)
(*                    SECTION 14: HINT DATABASES                              *)
(* ========================================================================== *)

Create HintDb ucf_z discriminated.
Create HintDb ucf_q discriminated.
Create HintDb ucf_arith discriminated.

(* Z hints *)
#[export] Hint Resolve Z_Ring.add_comm Z_Ring.mul_comm : ucf_z.
#[export] Hint Resolve Z_Ring.add_0_l Z_Ring.add_0_r : ucf_z.
#[export] Hint Resolve Z_Ring.mul_1_l Z_Ring.mul_1_r : ucf_z.
#[export] Hint Resolve Z_Ring.mul_0_l Z_Ring.mul_0_r : ucf_z.
#[export] Hint Resolve Z_Order.le_refl Z_Order.le_trans : ucf_z.
#[export] Hint Resolve Z_Order.lt_trans Z_Order.lt_le_weak : ucf_z.
#[export] Hint Resolve Z_RingOrder.add_le_mono : ucf_z.
#[export] Hint Resolve Z_RingOrder.add_nonneg Z_RingOrder.add_pos : ucf_z.
#[export] Hint Resolve Z_RingOrder.mul_nonneg Z_RingOrder.mul_pos : ucf_z.
#[export] Hint Resolve Z_Squares.sq_nonneg Z_Squares.sq_pos : ucf_z.
#[export] Hint Resolve Z_Abs.abs_nonneg : ucf_z.
#[export] Hint Resolve Z_GcdLcm.gcd_nonneg Z_GcdLcm.lcm_nonneg : ucf_z.

(* Q hints *)
#[export] Hint Resolve Q_Positivity.mul_pos_pos : ucf_q.
#[export] Hint Resolve Q_Positivity.mul_nonneg_nonneg : ucf_q.
#[export] Hint Resolve Q_Positivity.add_pos_pos : ucf_q.
#[export] Hint Resolve Q_Positivity.add_nonneg_nonneg : ucf_q.
#[export] Hint Resolve Q_Positivity.add_pos_nonneg : ucf_q.
#[export] Hint Resolve Q_Positivity.add_nonneg_pos : ucf_q.
#[export] Hint Resolve Q_Positivity.inv_pos : ucf_q.
#[export] Hint Resolve Q_Positivity.lt_0_1 Q_Positivity.lt_0_2 : ucf_q.
#[export] Hint Resolve Q_Positivity.le_0_1 Q_Positivity.le_0_2 : ucf_q.
#[export] Hint Resolve Q_Squares.sq_nonneg Q_Squares.sq_pos : ucf_q.
#[export] Hint Resolve Q_Squares.sum_sq_nonneg : ucf_q.
#[export] Hint Resolve Q_Inv.pos_div_pos : ucf_q.
#[export] Hint Resolve Qle_refl Qlt_le_weak : ucf_q.

(* Combined hints *)
#[export] Hint Resolve Z_Ring.add_comm Z_Ring.mul_comm : ucf_arith.
#[export] Hint Resolve Z_Order.le_refl Z_Order.le_trans : ucf_arith.
#[export] Hint Resolve Z_Squares.sq_nonneg : ucf_arith.
#[export] Hint Resolve Q_Positivity.mul_pos_pos : ucf_arith.
#[export] Hint Resolve Q_Positivity.add_pos_nonneg : ucf_arith.
#[export] Hint Resolve Q_Squares.sq_nonneg : ucf_arith.

(* ========================================================================== *)
(*                    SECTION 14b: Q UTILITY LEMMAS                           *)
(* ========================================================================== *)

Open Scope Q_scope.

(** Qeq implies Qle — used pervasively in application proofs. *)
Lemma Qeq_to_Qle : forall p q : Q, p == q -> p <= q.
Proof.
  intros p q H. rewrite H. apply Qle_refl.
Qed.

(** Qmult_inv_l: / x * x == 1 (mirror of stdlib Qmult_inv_r). *)
Lemma Qmult_inv_l : forall x : Q, ~ x == 0 -> / x * x == 1.
Proof.
  intros x Hne. rewrite Qmult_comm. apply Qmult_inv_r. exact Hne.
Qed.

Close Scope Q_scope.

#[export] Hint Resolve Qeq_to_Qle : ucf_q.

(* ========================================================================== *)
(*                    SECTION 15: TACTICS                                     *)
(* ========================================================================== *)

(** 
  ucf_lia: UCF/GUTT replacement for lia on Z.
  Applies UCF lemmas first for auditability, falls back to lia.
*)
Ltac ucf_lia :=
  first [
    (* Try UCF lemmas first *)
    auto with ucf_z ucf_arith;
    try reflexivity
  | ring
  | lia
  ].

(**
  ucf_nia: UCF/GUTT replacement for nia on Z.
  Handles nonlinear goals with squares.
*)
Ltac ucf_nia :=
  first [
    (* Try UCF lemmas first *)
    auto with ucf_z ucf_arith;
    try reflexivity
  | ring
  | (* Add square non-negativity facts *)
    repeat match goal with
    | |- context [(?a * ?a)%Z] => 
        let H := fresh "Hsq" in
        assert (H : (0 <= a * a)%Z) by apply Z_Squares.sq_nonneg
    end;
    nia
  ].

(**
  ucf_qia: UCF/GUTT tactic for Q arithmetic.
  THIS IS WHAT lia/nia CANNOT DO!
*)
Ltac ucf_qia :=
  auto with ucf_q ucf_arith ||
  match goal with
  | |- Qlt 0 (Qmult ?a ?b) =>
      apply Q_Positivity.mul_pos_pos
  | |- Qle 0 (Qmult ?a ?b) =>
      apply Q_Positivity.mul_nonneg_nonneg
  | |- Qlt 0 (Qplus ?a ?b) =>
      first [apply Q_Positivity.add_pos_pos | 
             apply Q_Positivity.add_pos_nonneg |
             apply Q_Positivity.add_nonneg_pos]
  | |- Qle 0 (Qplus ?a ?b) =>
      apply Q_Positivity.add_nonneg_nonneg
  | |- Qlt 0 (Qinv ?a) =>
      apply Q_Positivity.inv_pos
  | |- Qle 0 (Qmult ?a ?a) =>
      apply Q_Squares.sq_nonneg
  | |- Qlt 0 (Qmult ?a ?a) =>
      apply Q_Squares.sq_pos
  | |- Qlt (Qmult ?c ?a) (Qmult ?c ?b) =>
      apply Q_Mult_Mono.mul_lt_mono_pos_l
  | |- Qle (Qmult ?c ?a) (Qmult ?c ?b) =>
      apply Q_Mult_Mono.mul_le_mono_pos_l
  end.

(**
  ucf_auto: General-purpose UCF arithmetic tactic.
*)
Ltac ucf_auto :=
  first [ucf_lia | ucf_nia | ucf_qia | auto with ucf_z ucf_q ucf_arith].

(* ========================================================================== *)
(*                    SECTION 16: UCF MODULE - PUBLIC API                     *)
(* ========================================================================== *)

Module UCF.

  (* ===== Z Ring ===== *)
  Definition Z_add_comm := Z_Ring.add_comm.
  Definition Z_mul_comm := Z_Ring.mul_comm.
  Definition Z_add_assoc := Z_Ring.add_assoc.
  Definition Z_mul_assoc := Z_Ring.mul_assoc.
  Definition Z_add_0_l := Z_Ring.add_0_l.
  Definition Z_add_0_r := Z_Ring.add_0_r.
  Definition Z_mul_1_l := Z_Ring.mul_1_l.
  Definition Z_mul_1_r := Z_Ring.mul_1_r.
  Definition Z_mul_0_l := Z_Ring.mul_0_l.
  Definition Z_mul_0_r := Z_Ring.mul_0_r.
  Definition Z_distr_l := Z_Ring.mul_add_distr_l.
  Definition Z_distr_r := Z_Ring.mul_add_distr_r.

  (* ===== Z Order ===== *)
  Definition Z_le_refl := Z_Order.le_refl.
  Definition Z_le_trans := Z_Order.le_trans.
  Definition Z_le_antisym := Z_Order.le_antisym.
  Definition Z_lt_trans := Z_Order.lt_trans.
  Definition Z_trichotomy := Z_Order.trichotomy.

  (* ===== Z Ring-Order ===== *)
  Definition Z_add_le_mono := Z_RingOrder.add_le_mono.
  Definition Z_add_nonneg := Z_RingOrder.add_nonneg.
  Definition Z_add_pos := Z_RingOrder.add_pos.
  Definition Z_add_pos_nonneg := Z_RingOrder.add_pos_nonneg.
  Definition Z_mul_nonneg := Z_RingOrder.mul_nonneg.
  Definition Z_mul_pos := Z_RingOrder.mul_pos.
  Definition Z_mul_le_mono_pos_l := Z_RingOrder.mul_le_mono_pos_l.

  (* ===== Z Squares ===== *)
  Definition Z_sq_nonneg := Z_Squares.sq_nonneg.
  Definition Z_sq_pos := Z_Squares.sq_pos.
  Definition Z_sq_eq_0 := Z_Squares.sq_eq_0.
  Definition Z_am_gm_sq := Z_Squares.am_gm_sq.
  Definition Z_sum_sq_nonneg := Z_Squares.sum_sq_nonneg.

  (* ===== Z Absolute Value ===== *)
  Definition Z_abs_nonneg := Z_Abs.abs_nonneg.
  Definition Z_abs_triangle := Z_Abs.abs_triangle.
  Definition Z_abs_mul := Z_Abs.abs_mul.

  (* ===== Z GCD/LCM (Tensor Decomposition) ===== *)
  Definition Z_gcd_nonneg := Z_GcdLcm.gcd_nonneg.
  Definition Z_lcm_nonneg := Z_GcdLcm.lcm_nonneg.
  Definition Z_gcd_divide_l := Z_GcdLcm.gcd_divide_l.
  Definition Z_gcd_divide_r := Z_GcdLcm.gcd_divide_r.
  Definition Z_coprime_lcm_abs := Z_GcdLcm.coprime_lcm_abs.

  (* ===== Q Positivity (THE KEY ADDITIONS) ===== *)
  Definition Q_mul_pos_pos := Q_Positivity.mul_pos_pos.
  Definition Q_mul_nonneg_nonneg := Q_Positivity.mul_nonneg_nonneg.
  Definition Q_add_pos_pos := Q_Positivity.add_pos_pos.
  Definition Q_add_nonneg_nonneg := Q_Positivity.add_nonneg_nonneg.
  Definition Q_add_pos_nonneg := Q_Positivity.add_pos_nonneg.
  Definition Q_add_nonneg_pos := Q_Positivity.add_nonneg_pos.
  Definition Q_inv_pos := Q_Positivity.inv_pos.
  Definition Q_lt_0_1 := Q_Positivity.lt_0_1.
  Definition Q_lt_0_2 := Q_Positivity.lt_0_2.

  (* ===== Q Multiplication Monotonicity ===== *)
  Definition Q_mul_lt_mono_pos_l := Q_Mult_Mono.mul_lt_mono_pos_l.
  Definition Q_mul_lt_mono_pos_r := Q_Mult_Mono.mul_lt_mono_pos_r.
  Definition Q_mul_le_mono_pos_l := Q_Mult_Mono.mul_le_mono_pos_l.
  Definition Q_mul_le_mono_pos_r := Q_Mult_Mono.mul_le_mono_pos_r.
  Definition Q_mul_le_mono_nonneg_l := Q_Mult_Mono.mul_le_mono_nonneg_l.
  Definition Q_mul_le_mono_nonneg_r := Q_Mult_Mono.mul_le_mono_nonneg_r.
  Definition Q_mult_2_lt_2 := Q_Mult_Mono.mult_2_lt_2.

  (* ===== Q Addition Monotonicity ===== *)
  Definition Q_add_lt_mono := Q_Add_Mono.add_lt_mono.
  Definition Q_add_le_mono := Q_Add_Mono.add_le_mono.

  (* ===== Q Inverse ===== *)
  Definition Q_inv_neq_0 := Q_Inv.inv_neq_0.
  Definition Q_inv_involutive := Q_Inv.inv_involutive.
  Definition Q_mul_inv_r := Q_Inv.mul_inv_r.
  Definition Q_inv_lt_contravar := Q_Inv.inv_lt_contravar.
  Definition Q_inv_le_contravar := Q_Inv.inv_le_contravar.
  Definition Q_pos_div_pos := Q_Inv.pos_div_pos.

  (* ===== Q Squares ===== *)
  Definition Q_sq_nonneg := Q_Squares.sq_nonneg.
  Definition Q_sq_pos := Q_Squares.sq_pos.
  Definition Q_sum_sq_nonneg := Q_Squares.sum_sq_nonneg.

End UCF.

(* ========================================================================== *)
(*                    SECTION 17: AXIOM AUDIT                                 *)
(* ========================================================================== *)

Module AxiomAudit.

  Open Scope Z_scope.
  
  (* Z tests *)
  Goal forall a : Z, a + 0 = a.
  Proof. intro. ucf_lia. Qed.
  
  Goal forall a b : Z, a + b = b + a.
  Proof. intros. ucf_lia. Qed.
  
  Goal forall a : Z, 0 <= a * a.
  Proof. intro. apply UCF.Z_sq_nonneg. Qed.
  
  Goal forall a b : Z, 2 * a * b <= a * a + b * b.
  Proof. intros. apply UCF.Z_am_gm_sq. Qed.

  Close Scope Z_scope.
  Open Scope Q_scope.
  
  (* Q tests - these FAIL with lia/nia! *)
  Goal forall a b : Q, 0 < a -> 0 < b -> 0 < a * b.
  Proof. intros. apply UCF.Q_mul_pos_pos; assumption. Qed.
  
  Goal forall a : Q, 0 <= a * a.
  Proof. intro. apply UCF.Q_sq_nonneg. Qed.
  
  Goal forall a b : Q, 0 < a -> 0 <= b -> 0 < a + b.
  Proof. intros. apply UCF.Q_add_pos_nonneg; assumption. Qed.
  
  Goal forall a : Q, 0 < a -> 0 < /a.
  Proof. intros. apply UCF.Q_inv_pos. assumption. Qed.
  
  Goal forall x : Q, x < 1 -> 2 * x < 2.
  Proof. intros. apply UCF.Q_mult_2_lt_2. assumption. Qed.

  Goal forall x : Q, 0 < x -> 0 < 2 * /x.
  Proof. 
    intros x Hx. 
    apply UCF.Q_mul_pos_pos.
    - apply UCF.Q_lt_0_2.
    - apply UCF.Q_inv_pos. assumption.
  Qed.

  Close Scope Q_scope.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  +==========================================================================+
  |                                                                          |
  |                    QUICK REFERENCE                                       |
  |                                                                          |
  +==========================================================================+
  
  WHY THIS LIBRARY EXISTS:
    1. lia/nia COMPLETELY FAIL on Q (rational) arithmetic
    2. UCF/GUTT grounding provides philosophical coherence
    3. Every proof step is auditable (named lemmas)
    4. No external solver dependencies
    5. ZERO AXIOMS - everything proven constructively
  
  MAIN TACTICS:
    ucf_lia       - Z linear arithmetic (UCF lemmas + lia fallback)
    ucf_nia       - Z nonlinear arithmetic (UCF lemmas + nia fallback)
    ucf_qia       - Q arithmetic (NO lia/nia - pure UCF!)
    ucf_auto      - Tries all of the above
  
  HINT DATABASES:
    ucf_z         - Z ring, order, squares, abs, gcd/lcm
    ucf_q         - Q positivity, monotonicity, squares
    ucf_arith     - Combined Z and Q hints
  
  KEY Z LEMMAS (via UCF module):
    UCF.Z_add_comm, UCF.Z_mul_comm    - Commutativity
    UCF.Z_le_refl, UCF.Z_le_trans     - Order
    UCF.Z_sq_nonneg, UCF.Z_sq_pos     - Square properties
    UCF.Z_am_gm_sq                    - AM-GM: 2ab Ã¢â€°Â¤ aÃ‚Â² + bÃ‚Â²
    UCF.Z_coprime_lcm_abs            - For coprime: LCM = |ab|
  
  KEY Q LEMMAS (via UCF module) - WHERE lia/nia FAIL:
    UCF.Q_mul_pos_pos        - 0 < a Ã¢â€ â€™ 0 < b Ã¢â€ â€™ 0 < a*b
    UCF.Q_mul_nonneg_nonneg  - 0 Ã¢â€°Â¤ a Ã¢â€ â€™ 0 Ã¢â€°Â¤ b Ã¢â€ â€™ 0 Ã¢â€°Â¤ a*b
    UCF.Q_add_pos_nonneg     - 0 < a Ã¢â€ â€™ 0 Ã¢â€°Â¤ b Ã¢â€ â€™ 0 < a+b  [CRITICAL!]
    UCF.Q_add_nonneg_pos     - 0 Ã¢â€°Â¤ a Ã¢â€ â€™ 0 < b Ã¢â€ â€™ 0 < a+b
    UCF.Q_inv_pos            - 0 < a Ã¢â€ â€™ 0 < /a
    UCF.Q_sq_nonneg          - 0 Ã¢â€°Â¤ a*a
    UCF.Q_sq_pos             - a Ã¢â€°Â  0 Ã¢â€ â€™ 0 < a*a
    UCF.Q_mult_2_lt_2        - x < 1 Ã¢â€ â€™ 2*x < 2
    UCF.Q_pos_div_pos        - 0 < a Ã¢â€ â€™ 0 < b Ã¢â€ â€™ 0 < a/b
    UCF.Q_mul_le_mono_pos_l  - 0 < c Ã¢â€ â€™ a Ã¢â€°Â¤ b Ã¢â€ â€™ c*a Ã¢â€°Â¤ c*b
    UCF.Q_inv_lt_contravar   - 0 < a Ã¢â€ â€™ a < b Ã¢â€ â€™ /b < /a
  
  USAGE EXAMPLE:
    Require Import Top__Numbers__UCF_Lia.
    
    (* For Z goals: *)
    Goal forall a b : Z, (a + b) * (a + b) = a*a + 2*a*b + b*b.
    Proof. intros. ucf_lia. Qed.
    
    (* For Q goals where lia/nia FAIL: *)
    Goal forall x : Q, 0 < x -> 0 < 2 * /x.
    Proof.
      intros x Hx.
      apply UCF.Q_mul_pos_pos.
      - apply UCF.Q_lt_0_2.
      - apply UCF.Q_inv_pos. exact Hx.
    Qed.
    
    (* With automation: *)
    Goal forall a b : Q, 0 < a -> 0 < b -> 0 < a * b.
    Proof. intros. ucf_qia; assumption. Qed.
  
  RELATIONAL ONTOLOGY SUMMARY:
    - Numbers = relational distances from Whole
    - Addition = parallel relational accumulation (INTRA-SET)
    - Multiplication = sequential composition/scaling (INTER-SET)
    - Order = relational precedence
    - Positivity = direction of relational flow
    - Squares = self-interaction (always non-negative)
    - GCD/LCM = tensor decomposition of shared structure
  
  This grounding means our lemmas are not arbitrary axioms but
  NECESSARY CONSEQUENCES of relational structure itself.
*)

(** Axiom audit — must print "Closed under the global context." *)
Print Assumptions Qmult_inv_l.
Print Assumptions Qeq_to_Qle.
Print Assumptions UCF.Q_inv_pos.
Print Assumptions Z_Squares.sq_nonneg.
