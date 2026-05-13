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
  |              Top__Propositions__ClockHierarchyCoherence.v                |
  |                                                                          |
  |         Hierarchical Clock Systems from Relational Foundations           |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.3.0                                                          |
  |  DATE:    2026-02-05                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                        |
  |                                                                          |
  |  PURPOSE: Construct hierarchical clock systems where:                    |
  |    - Clock ticks are relational steps (N_rel successor)                  |
  |    - Time differences are signed relational distances (Z_rel)            |
  |    - Hierarchy arises from iterated Whole-completion                     |
  |    - Coherence follows from preserved connectivity across levels         |
  |                                                                          |
  |  CHANGELOG:                                                              |
  |    v1.3.0 - Added TickReachability: inductive transitive closure         |
  |           - Added reach_advance: reachability iff advance equivalence    |
  |           - Added reach_distance: reachability distance theorem          |
  |           - Added dilation_chain: dilation(A,C)=dilation(A,B)*dil(B,C)  |
  |           - Added proper_time_chain: chained frame transformations       |
  |           - Fixed same_rate_trans/faster_trans with explicit algebra      |
  |           - Added honest documentation for level_coherent limitations    |
  |    v1.2.0 - Integrated RelationalAlgebra (rel_graph, composition)        |
  |           - Integrated UCF_Lia (ucf_lia, ucf_auto tactics)               |
  |           - Integrated UCF_Nia (ucf_nia for nonlinear Z/Q goals)         |
  |           - Added RelationalAlgebraBridge with iterated composition      |
  |           - Added same_rate_trans, faster_trans (completing orders)       |
  |           - Added level_coherent_sym, level_coherent_trans                |
  |           - Added dilation_factor as Q_rel with dilation_refl            |
  |           - Added proper_time as Q_rel with proper_time_self             |
  |    v1.1.0 - Dual nat/N_rel interfaces with conversion lemmas            |
  |    v1.0.0 - Initial hierarchical clock construction                      |
  |                                                                          |
  |  IMPORTS:                                                                |
  |    - Top__Extensions__Prelude (UE, WholeCompletion, Composition)         |
  |    - Top__Numbers__Relational (N_rel)                                    |
  |    - Top__Numbers__RelationalIntegers (Z_rel)                            |
  |    - Top__Numbers__RelationalRationals (Q_rel for dilation_factor)       |
  |    - Top__Numbers__UCF_Lia (ucf_lia, ucf_auto tactics)                   |
  |    - Top__Numbers__UCF_Nia (ucf_nia for nonlinear Z/Q arithmetic)        |
  |    - Top__Relations__RelationalAlgebra (Rel, rel_graph, composition)     |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS | [ok] ZERO ADMITS | [ok] LIBRARY QUALITY     |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Import ListNotations.

(* ========================================================================== *)
(*                                                                            *)
(*                    IMPORTS FROM UCF/GUTT LIBRARY                           *)
(*                                                                            *)
(* ========================================================================== *)

(* Core extension framework *)
Require Import Top__Extensions__Prelude.

(* Relational number systems *)
Require Import Top__Numbers__Relational.
Require Import Top__Numbers__RelationalIntegers.
Require Import Top__Numbers__RelationalRationals.

(* Relational algebra and tactics *)
Require Import Top__Numbers__UCF_Lia.
Require Import Top__Numbers__UCF_Nia.
Require Import Top__Relations__RelationalAlgebra.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    HELPER LEMMAS                                           *)
(*                                                                            *)
(* ========================================================================== *)

(** Non-zero N_rel values have positive to_nat. 
    Used for rate denominators in ClockRates and dilation_factor. *)
Lemma neq_zero_to_nat_pos : forall n : N_rel, n <> Zero_rel -> (to_nat n > 0)%nat.
Proof.
  intros [|m] H.
  - exfalso. apply H. reflexivity.
  - simpl. lia.
Qed.

(** Corollary on Z: non-zero N_rel has positive Z embedding. *)
Lemma neq_zero_Z_pos : forall n : N_rel, n <> Zero_rel -> (Z.of_nat (to_nat n) > 0)%Z.
Proof.
  intros n H. apply neq_zero_to_nat_pos in H. lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CLOCK TICK RELATION                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CLOCK TICKS AS RELATIONAL STEPS
  ================================
  
  A clock is fundamentally a relational structure where:
  - Each tick is a relational step
  - The successor relation captures "next tick"
  - Seriality (from Proposition 1) guarantees time always progresses
  
  We use N_rel as the tick counter, inheriting all its relational properties.
  
  DESIGN DECISION: We provide BOTH nat and N_rel interfaces:
  - nat interface: Compatible with lia tactic, list indexing, etc.
  - N_rel interface: Philosophically consistent with relational foundations
  - Conversion lemmas show these are equivalent via the isomorphism
*)

Module ClockTicks.

  (** A clock reading is a relational natural number. *)
  Definition ClockReading : Type := N_rel.
  
  (** The initial reading (corresponds to Whole in relational sense). *)
  Definition initial_reading : ClockReading := Zero_rel.
  
  (** Advance the clock by one tick (successor relation). *)
  Definition tick (c : ClockReading) : ClockReading := Succ_rel c.
  
  (** The tick relation: c1 ticks to c2 if c2 = tick c1. *)
  Definition ticks_to (c1 c2 : ClockReading) : Prop := c2 = tick c1.
  
  (* ------------------------------------------------------------------------ *)
  (*                    nat-based Interface (Tactic-Compatible)               *)
  (* ------------------------------------------------------------------------ *)
  
  (** Multiple ticks: advance by n steps (nat version for lia compatibility). *)
  Fixpoint advance (n : nat) (c : ClockReading) : ClockReading :=
    match n with
    | O => c
    | S m => tick (advance m c)
    end.
  
  (** Convert reading to natural number (for comparison with external time). *)
  Definition reading_value (c : ClockReading) : nat := to_nat c.
  
  (* ------------------------------------------------------------------------ *)
  (*                    N_rel-based Interface (Relationally Pure)             *)
  (* ------------------------------------------------------------------------ *)
  
  (**
    RELATIONAL ADVANCE: Advance using N_rel step count.
    This is the philosophically pure version that stays entirely within
    the relational number system.
  *)
  Fixpoint advance_rel (n : N_rel) (c : ClockReading) : ClockReading :=
    match n with
    | Zero_rel => c
    | Succ_rel m => tick (advance_rel m c)
    end.
  
  (** Convert reading to relational natural (stays in N_rel). *)
  Definition reading_value_rel (c : ClockReading) : N_rel := c.
  
  (* ------------------------------------------------------------------------ *)
  (*                    Equivalence Between Interfaces                        *)
  (* ------------------------------------------------------------------------ *)
  
  (** The two advance functions are equivalent via the isomorphism. *)
  Theorem advance_advance_rel_equiv : forall n c,
    advance n c = advance_rel (from_nat n) c.
  Proof.
    induction n as [|m IH]; intro c.
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.
  
  (** The converse: advance_rel can be computed via advance. *)
  Theorem advance_rel_advance_equiv : forall n c,
    advance_rel n c = advance (to_nat n) c.
  Proof.
    induction n as [|m IH]; intro c.
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.
  
  (** Reading value equivalence. *)
  Theorem reading_value_rel_equiv : forall c,
    reading_value c = to_nat (reading_value_rel c).
  Proof.
    intro c. reflexivity.
  Qed.
  
  (* ------------------------------------------------------------------------ *)
  (*                    Core Theorems                                         *)
  (* ------------------------------------------------------------------------ *)
  
  (** SERIALITY OF TICKS: Every clock reading has a next tick.
      This is the UCF/GUTT guarantee of temporal progression. *)
  Theorem tick_serial : forall c : ClockReading, exists c', ticks_to c c'.
  Proof.
    intro c. exists (tick c). reflexivity.
  Qed.
  
  (** The tick relation is functional (deterministic time). *)
  Theorem tick_functional : forall c c1 c2,
    ticks_to c c1 -> ticks_to c c2 -> c1 = c2.
  Proof.
    intros c c1 c2 H1 H2.
    unfold ticks_to in *. rewrite H1, H2. reflexivity.
  Qed.
  
  (** Advancing from initial gives expected value (nat version). *)
  Theorem advance_from_initial : forall n,
    reading_value (advance n initial_reading) = n.
  Proof.
    induction n as [|m IH].
    - reflexivity.
    - simpl. unfold reading_value, tick in *. 
      rewrite IH. reflexivity.
  Qed.
  
  (** Advancing from initial gives expected value (N_rel version). *)
  Theorem advance_rel_from_initial : forall n,
    reading_value_rel (advance_rel n initial_reading) = n.
  Proof.
    induction n as [|m IH].
    - reflexivity.
    - simpl. unfold reading_value_rel, tick in *.
      rewrite IH. reflexivity.
  Qed.
  
  (** Advance is additive (nat version). *)
  Theorem advance_add : forall m n c,
    advance m (advance n c) = advance (m + n) c.
  Proof.
    induction m as [|m' IH]; intros n c.
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.
  
  (** Advance is additive (N_rel version). *)
  Theorem advance_rel_add : forall m n c,
    advance_rel m (advance_rel n c) = advance_rel (m +r n) c.
  Proof.
    induction m as [|m' IH]; intros n c.
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.
  
  (** advance_rel respects the isomorphism. *)
  Theorem advance_rel_to_nat : forall n c,
    to_nat (advance_rel n c) = to_nat n + to_nat c.
  Proof.
    induction n as [|m IH]; intro c.
    - simpl. lia.
    - simpl. unfold tick. simpl. rewrite IH. lia.
  Qed.
  
  (** advance_rel with addition corresponds to nat addition. *)
  Theorem advance_rel_add_correct : forall m n c,
    to_nat (advance_rel (m +r n) c) = to_nat m + to_nat n + to_nat c.
  Proof.
    intros m n c.
    rewrite advance_rel_to_nat.
    rewrite add_rel_correct.
    lia.
  Qed.

End ClockTicks.

(* ========================================================================== *)
(*                                                                            *)
(*           SECTION 1A: RELATIONAL ALGEBRA BRIDGE                            *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CLOCK TICK AS REL_GRAPH
  =======================
  
  The tick function is a total, deterministic function on ClockReading.
  In relational algebra terms, its graph is a serial, functional relation.
  This section connects ClockTicks to the RelationalAlgebra vocabulary,
  enabling composition, converse, and lattice reasoning on clock relations.
*)

Module RelationalAlgebraBridge.

  Import ClockTicks.

  (** The tick relation expressed as a relational graph.
      rel_graph tick c1 c2  <->  c2 = tick c1  <->  ticks_to c1 c2 *)
  Definition tick_graph : Rel ClockReading ClockReading :=
    rel_graph tick.

  (** tick_graph coincides with ticks_to. *)
  Theorem tick_graph_is_ticks_to : forall c1 c2,
    tick_graph c1 c2 <-> ticks_to c1 c2.
  Proof.
    intros c1 c2. unfold tick_graph, rel_graph, ticks_to. split; auto.
  Qed.

  (** tick_graph is serial (every reading has a successor).
      This follows from rel_graph_total since tick is a total function. *)
  Theorem tick_graph_serial : forall c : ClockReading,
    exists c', tick_graph c c'.
  Proof.
    intro c. unfold tick_graph.
    apply rel_graph_total.
  Qed.

  (** tick_graph is functional (deterministic). *)
  Theorem tick_graph_functional : forall c c1 c2,
    tick_graph c c1 -> tick_graph c c2 -> c1 = c2.
  Proof.
    intros c c1 c2 H1 H2.
    unfold tick_graph, rel_graph in *.
    subst. reflexivity.
  Qed.

  (** n-fold composition of tick_graph via advance.
      advance n is itself a function, so its graph captures n ticks. *)
  Definition advance_graph (n : nat) : Rel ClockReading ClockReading :=
    rel_graph (advance n).

  (** advance_graph 0 is the identity relation. *)
  Theorem advance_graph_0 : rel_equiv (advance_graph 0) (@rel_id ClockReading).
  Proof.
    intros a b. split; intro H;
      unfold advance_graph, rel_graph, rel_id in *; simpl in *; auto.
  Qed.

  (** advance_graph (S n) factors as tick_graph composed with advance_graph n. *)
  Theorem advance_graph_step : forall n,
    rel_equiv (advance_graph (S n))
              (rel_comp (advance_graph n) tick_graph).
  Proof.
    intro n. intros a b. split.
    - intro H. unfold advance_graph, rel_graph in H. simpl in H.
      unfold rel_comp. exists (advance n a). split.
      + unfold rel_graph. reflexivity.
      + unfold tick_graph, rel_graph. exact H.
    - intros [z [Hz Ht]].
      unfold advance_graph, rel_graph in *. simpl.
      unfold tick_graph, rel_graph in Ht. subst z. exact Ht.
  Qed.

  (* ---- Iterated relational composition ---- *)

  (** n-fold relational composition of R with itself. *)
  Fixpoint rel_comp_iter {A : Type} (n : nat) (R : Rel A A) : Rel A A :=
    match n with
    | O => @rel_id A
    | S m => rel_comp (rel_comp_iter m R) R
    end.

  (** advance_graph n equals the n-fold composition of tick_graph.
      This connects the functional and relational views of multi-step advance. *)
  Theorem advance_graph_is_iter : forall n,
    rel_equiv (advance_graph n) (rel_comp_iter n tick_graph).
  Proof.
    induction n as [|m IH].
    - (* n = 0 *) exact advance_graph_0.
    - (* n = S m *)
      intros a b. split.
      + intro H.
        apply advance_graph_step in H.
        destruct H as [z [Hz Ht]].
        simpl. exists z. split.
        * apply IH. exact Hz.
        * exact Ht.
      + intro H.
        apply advance_graph_step.
        simpl in H. destruct H as [z [Hz Ht]].
        exists z. split.
        * apply IH. exact Hz.
        * exact Ht.
  Qed.

  (** The converse of tick_graph: "was ticked from". *)
  Definition tick_prev : Rel ClockReading ClockReading :=
    rel_conv tick_graph.

  (** tick_prev relates c2 to c1 iff c1 ticks to c2. *)
  Theorem tick_prev_spec : forall c1 c2,
    tick_prev c2 c1 <-> ticks_to c1 c2.
  Proof.
    intros c1 c2. unfold tick_prev, rel_conv.
    apply tick_graph_is_ticks_to.
  Qed.

  (** tick_graph lifted through UE is serial.
      This connects clock seriality to the general seriality mechanism:
      Whole-completion guarantees every element relates to Whole. *)
  Theorem tick_graph_ue_serial :
    forall x : UE.Carrier ClockReading,
      exists y, UE.lift ticks_to x y.
  Proof.
    intro x. exists UE.Whole. apply UE.serial.
  Qed.

End RelationalAlgebraBridge.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: TIME DIFFERENCES (SIGNED)                    *)
(*                                                                            *)
(* ========================================================================== *)

(**
  TIME DIFFERENCES AS RELATIONAL INTEGERS
  ========================================
  
  Comparing two clock readings requires SIGNED arithmetic:
  - t2 - t1 can be positive (t2 after t1) or negative (t2 before t1)
  - Z_rel provides this through pairs of N_rel
  
  This is an INTRA-SET operation in the UCF/GUTT classification:
  works WITHIN the time domain to capture "how many ticks between readings".
  
  NOTE: Proofs reduce Z_rel goals to stdlib Z via to_Z_* lemmas, then
  discharge with lia. The UCF_Lia import makes ucf_lia/ucf_auto available
  for downstream files that build on this module.
*)

Module TimeDifference.

  Import ClockTicks.
  
  (** Convert a clock reading to a relational integer. *)
  Definition reading_to_Z (c : ClockReading) : Z_rel :=
    embed_N c.
  
  (** Signed time difference between two readings. *)
  Definition time_diff (c1 c2 : ClockReading) : Z_rel :=
    Z_sub (reading_to_Z c2) (reading_to_Z c1).
  
  (** Time difference is zero iff readings are equal. *)
  Theorem time_diff_zero_iff_eq : forall c1 c2 : ClockReading,
    Z_equiv (time_diff c1 c2) Z_zero <-> c1 = c2.
  Proof.
    intros c1 c2. split.
    - intro H.
      unfold time_diff, reading_to_Z in H.
      apply to_Z_respects_equiv in H.
      rewrite to_Z_sub in H.
      repeat rewrite embed_N_to_Z in H.
      rewrite to_Z_zero in H.
      apply to_nat_injective.
      lia.
    - intro Heq. subst c2.
      unfold time_diff, reading_to_Z.
      apply to_Z_faithful.
      rewrite to_Z_sub.
      rewrite to_Z_zero.
      repeat rewrite embed_N_to_Z.
      lia.
  Qed.
  
  (** Time difference is anti-symmetric. *)
  Theorem time_diff_antisym : forall c1 c2,
    Z_equiv (time_diff c2 c1) (Z_neg (time_diff c1 c2)).
  Proof.
    intros c1 c2.
    unfold time_diff.
    apply to_Z_faithful.
    repeat rewrite to_Z_sub.
    rewrite to_Z_neg.
    rewrite to_Z_sub.
    lia.
  Qed.
  
  (** Triangle inequality for time differences. *)
  Theorem time_diff_triangle : forall c1 c2 c3,
    Z_equiv (Z_add (time_diff c1 c2) (time_diff c2 c3)) (time_diff c1 c3).
  Proof.
    intros c1 c2 c3.
    unfold time_diff.
    apply to_Z_faithful.
    rewrite to_Z_add.
    repeat rewrite to_Z_sub.
    lia.
  Qed.
  
  (** Helper: advance adds to the reading value. *)
  Lemma advance_to_nat : forall n c, to_nat (advance n c) = n + to_nat c.
  Proof.
    induction n as [|m IH]; intro c.
    - simpl. lia.
    - simpl. unfold tick. simpl. rewrite IH. lia.
  Qed.

  (** Time difference after advancing (nat version). *)
  Theorem time_diff_advance : forall c n,
    to_Z (time_diff c (advance n c)) = Z.of_nat n.
  Proof.
    intros c n.
    unfold time_diff, reading_to_Z.
    rewrite to_Z_sub.
    repeat rewrite embed_N_to_Z.
    rewrite advance_to_nat.
    lia.
  Qed.
  
  (** Time difference after advancing (N_rel version). *)
  Theorem time_diff_advance_rel : forall c n,
    to_Z (time_diff c (advance_rel n c)) = Z.of_nat (to_nat n).
  Proof.
    intros c n.
    unfold time_diff, reading_to_Z.
    rewrite to_Z_sub.
    repeat rewrite embed_N_to_Z.
    rewrite advance_rel_to_nat.
    lia.
  Qed.
  
  (** Positive difference means c2 is after c1. *)
  Definition is_after (c1 c2 : ClockReading) : Prop :=
    Z_lt Z_zero (time_diff c1 c2).
  
  (** Negative difference means c2 is before c1. *)
  Definition is_before (c1 c2 : ClockReading) : Prop :=
    Z_lt (time_diff c1 c2) Z_zero.
  
  (** After and before are mutually exclusive. *)
  Theorem after_before_exclusive : forall c1 c2,
    ~ (is_after c1 c2 /\ is_before c1 c2).
  Proof.
    intros c1 c2 [Hafter Hbefore].
    unfold is_after, is_before, Z_lt in *.
    lia.
  Qed.

End TimeDifference.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: CLOCK RATES (INTER-SET)                      *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CLOCK RATES AS INTER-SET OPERATIONS
  ====================================
  
  Comparing RATES of different clocks is an INTER-SET operation:
  - Relates different temporal domains
  - Uses multiplication/division (not addition/subtraction)
  
  This corresponds to:
  - Frequency ratios between clocks
  - Relativistic time dilation factors
  - Quantum vs classical tick rates
  
  NOTE: Nonlinear goals (cross-multiplication, positivity cancellation)
  are discharged via explicit Z algebra (Z.mul_reg_r, Z.mul_lt_mono_pos_r),
  ensuring full auditability of the nonlinear arithmetic steps.
*)

Module ClockRates.

  Import ClockTicks.
  
  (** A clock rate expressed as ticks per unit external time.
      We use N_rel throughout for relational consistency. *)
  Record ClockRate := mkRate {
    rate_ticks : N_rel;      (* number of ticks *)
    rate_interval : N_rel;   (* per this many external units *)
    rate_nonzero : rate_interval <> Zero_rel
  }.
  
  (** Rate ratio: how many times faster is clock1 than clock2?
      This is an INTER-SET operation using Z_rel multiplication/division. *)
  Definition rate_ratio_num (r1 r2 : ClockRate) : Z_rel :=
    Z_mul (embed_N (rate_ticks r1)) (embed_N (rate_interval r2)).
  
  Definition rate_ratio_denom (r1 r2 : ClockRate) : Z_rel :=
    Z_mul (embed_N (rate_interval r1)) (embed_N (rate_ticks r2)).
  
  (** Two clocks have the same rate. *)
  Definition same_rate (r1 r2 : ClockRate) : Prop :=
    Z_equiv (rate_ratio_num r1 r2) (rate_ratio_denom r1 r2).
  
  (** Same rate is reflexive. *)
  Theorem same_rate_refl : forall r, same_rate r r.
  Proof.
    intro r. unfold same_rate, rate_ratio_num, rate_ratio_denom.
    apply to_Z_faithful.
    repeat rewrite to_Z_mul.
    repeat rewrite embed_N_to_Z.
    lia.
  Qed.
  
  (** Same rate is symmetric. *)
  Theorem same_rate_sym : forall r1 r2,
    same_rate r1 r2 -> same_rate r2 r1.
  Proof.
    intros r1 r2 H.
    unfold same_rate, rate_ratio_num, rate_ratio_denom in *.
    apply to_Z_faithful.
    apply to_Z_respects_equiv in H.
    repeat rewrite to_Z_mul in *.
    repeat rewrite embed_N_to_Z in *.
    lia.
  Qed.
  
  (** Same rate is transitive.
      Proof strategy: reduce to Z, then use Z.mul_reg_r to cancel i2 > 0.
      From H12: t1*i2 = i1*t2 and H23: t2*i3 = i2*t3,
      derive t1*i3*i2 = t1*i2*i3 = i1*t2*i3 = i1*(i2*t3) = i1*t3*i2,
      then cancel the common factor i2 > 0. *)
  Theorem same_rate_trans : forall r1 r2 r3,
    same_rate r1 r2 -> same_rate r2 r3 -> same_rate r1 r3.
  Proof.
    intros r1 r2 r3 H12 H23.
    unfold same_rate, rate_ratio_num, rate_ratio_denom in *.
    apply to_Z_faithful.
    apply to_Z_respects_equiv in H12.
    apply to_Z_respects_equiv in H23.
    repeat rewrite to_Z_mul in *.
    repeat rewrite embed_N_to_Z in *.
    (* H12: t1 * i2 = i1 * t2
       H23: t2 * i3 = i2 * t3
       Goal: t1 * i3 = i1 * t3 *)
    set (t1 := Z.of_nat (to_nat (rate_ticks r1))) in *.
    set (i1 := Z.of_nat (to_nat (rate_interval r1))) in *.
    set (t2 := Z.of_nat (to_nat (rate_ticks r2))) in *.
    set (i2 := Z.of_nat (to_nat (rate_interval r2))) in *.
    set (t3 := Z.of_nat (to_nat (rate_ticks r3))) in *.
    set (i3 := Z.of_nat (to_nat (rate_interval r3))) in *.
    assert (Hi2 : (i2 > 0)%Z)
      by (subst i2; apply neq_zero_Z_pos; exact (rate_nonzero r2)).
    assert (Step : ((t1 * i3) * i2 = (i1 * t3) * i2)%Z).
    { replace ((t1 * i3) * i2)%Z with ((t1 * i2) * i3)%Z by ring.
      rewrite H12.
      replace ((i1 * t2) * i3)%Z with (i1 * (t2 * i3))%Z by ring.
      rewrite H23. ring. }
    apply Z.mul_cancel_r in Step; [exact Step | lia].
  Qed.
  
  (** Clock rate is faster if it has more ticks per interval. *)
  Definition is_faster (r1 r2 : ClockRate) : Prop :=
    Z_lt (rate_ratio_denom r1 r2) (rate_ratio_num r1 r2).
  
  (** Faster is anti-symmetric. *)
  Theorem faster_antisym : forall r1 r2,
    is_faster r1 r2 -> ~ is_faster r2 r1.
  Proof.
    intros r1 r2 H12 H21.
    unfold is_faster, Z_lt in *.
    unfold rate_ratio_num, rate_ratio_denom in *.
    repeat rewrite to_Z_mul in *.
    repeat rewrite embed_N_to_Z in *.
    lia.
  Qed.

  (** Faster is transitive.
      Proof: chain i1*i2*t3 < i1*t2*i3 < t1*i2*i3 using positivity
      of i1 and i3, then cancel i2 > 0 from both sides. *)
  Theorem faster_trans : forall r1 r2 r3,
    is_faster r1 r2 -> is_faster r2 r3 -> is_faster r1 r3.
  Proof.
    intros r1 r2 r3 H12 H23.
    unfold is_faster, Z_lt in *.
    unfold rate_ratio_num, rate_ratio_denom in *.
    repeat rewrite to_Z_mul in *.
    repeat rewrite embed_N_to_Z in *.
    set (t1 := Z.of_nat (to_nat (rate_ticks r1))) in *.
    set (i1 := Z.of_nat (to_nat (rate_interval r1))) in *.
    set (t2 := Z.of_nat (to_nat (rate_ticks r2))) in *.
    set (i2 := Z.of_nat (to_nat (rate_interval r2))) in *.
    set (t3 := Z.of_nat (to_nat (rate_ticks r3))) in *.
    set (i3 := Z.of_nat (to_nat (rate_interval r3))) in *.
    (* H12: i1*t2 < t1*i2
       H23: i2*t3 < t2*i3
       Goal: i1*t3 < t1*i3 *)
    assert (Hi1 : (i1 > 0)%Z) by (subst i1; apply neq_zero_Z_pos; exact (rate_nonzero r1)).
    assert (Hi2 : (i2 > 0)%Z) by (subst i2; apply neq_zero_Z_pos; exact (rate_nonzero r2)).
    assert (Hi3 : (i3 > 0)%Z) by (subst i3; apply neq_zero_Z_pos; exact (rate_nonzero r3)).
    (* Multiply H12 by i3 > 0: i1*t2*i3 < t1*i2*i3 *)
    assert (S1 : (i1 * t2 * i3 < t1 * i2 * i3)%Z).
    { apply Z.mul_lt_mono_pos_r; lia. }
    (* Multiply H23 by i1 > 0: i1*(i2*t3) < i1*(t2*i3) *)
    assert (S2 : (i1 * (i2 * t3) < i1 * (t2 * i3))%Z).
    { apply Z.mul_lt_mono_pos_l; lia. }
    (* Rewrite S2: i1*i2*t3 < i1*t2*i3 *)
    replace (i1 * (i2 * t3))%Z with (i1 * i2 * t3)%Z in S2 by ring.
    replace (i1 * (t2 * i3))%Z with (i1 * t2 * i3)%Z in S2 by ring.
    (* Chain: i1*i2*t3 < i1*t2*i3 < t1*i2*i3, so i1*i2*t3 < t1*i2*i3 *)
    assert (Chain : (i1 * i2 * t3 < t1 * i2 * i3)%Z) by lia.
    (* Rewrite as (i1*t3)*i2 < (t1*i3)*i2, then cancel i2 > 0 *)
    replace (i1 * i2 * t3)%Z with ((i1 * t3) * i2)%Z in Chain by ring.
    replace (t1 * i2 * i3)%Z with ((t1 * i3) * i2)%Z in Chain by ring.
    apply Zmult_lt_reg_r in Chain; [exact Chain | lia].
  Qed.

End ClockRates.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: HIERARCHICAL CLOCKS                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  HIERARCHICAL CLOCKS VIA SERIAL COMPOSITION
  ===========================================
  
  Real physical systems have HIERARCHICAL temporal structure:
  - Atomic clocks (quantum level)
  - Electronic oscillators (mesoscopic level)  
  - Mechanical clocks (macroscopic level)
  - Astronomical cycles (cosmic level)
  
  We model this using SerialComposition's iterated Whole-completion:
  - Each level has its own "Whole" (terminal reference point)
  - Elements at each level relate to all higher-level Wholes
  - This is the fractal connectivity theorem in action
  
  NOTE: We use nat for hierarchy levels since this is used for
  type-level iteration (iter_carrier, iter_inject, etc.) which
  requires nat for Coq's type system.
*)

Module HierarchicalClocks.

  Import ClockTicks.
  
  (** A hierarchical clock system with n levels.
      Level 0 = finest (quantum), Level n-1 = coarsest (cosmic). *)
  Definition HierarchicalClock (n : nat) : Type :=
    SerialComposition.iter_carrier n ClockReading.
  
  (** Embed a base clock reading at depth n. *)
  Definition embed_reading (n : nat) (c : ClockReading) : HierarchicalClock n :=
    SerialComposition.iter_inject n ClockReading c.
  
  (** The Whole at the outermost level (universal time reference). *)
  Definition universal_reference (n : nat) : HierarchicalClock (S n) :=
    SerialComposition.iter_point n ClockReading.
  
  (** Lift the tick relation through the hierarchy. *)
  Definition hierarchical_tick (n : nat) : 
    HierarchicalClock n -> HierarchicalClock n -> Prop :=
    SerialComposition.iter_lift n ClockReading ticks_to.
  
  (** COHERENCE THEOREM 1: Every clock reading relates to the universal reference.
      This is the fundamental coherence condition - all clocks are synchronized
      to the universal time reference at the top of the hierarchy. *)
  Theorem universal_coherence : forall n (c : ClockReading),
    hierarchical_tick (S n) (embed_reading (S n) c) (universal_reference n).
  Proof.
    intros n c.
    unfold hierarchical_tick, embed_reading, universal_reference.
    apply SerialComposition.iter_serial.
  Qed.
  
  (** COHERENCE THEOREM 2: The hierarchy is conservative.
      Base clock relations are preserved when embedded in the hierarchy. *)
  Theorem hierarchy_conservative : forall n (c1 c2 : ClockReading),
    hierarchical_tick n (embed_reading n c1) (embed_reading n c2) <->
    ticks_to c1 c2.
  Proof.
    intros n c1 c2.
    unfold hierarchical_tick, embed_reading.
    apply SerialComposition.iter_lift_conservative.
  Qed.
  
  (** Embedding is injective (distinct readings remain distinct). *)
  Theorem embed_injective : forall n (c1 c2 : ClockReading),
    embed_reading n c1 = embed_reading n c2 -> c1 = c2.
  Proof.
    intros n c1 c2 H.
    unfold embed_reading in H.
    apply SerialComposition.iter_inject_injective in H.
    exact H.
  Qed.
  
  (** The universal reference is fresh (not a clock reading). *)
  Theorem universal_fresh : forall n (c : ClockReading),
    embed_reading (S n) c <> universal_reference n.
  Proof.
    intros n c.
    unfold embed_reading, universal_reference.
    apply SerialComposition.iter_point_fresh.
  Qed.

End HierarchicalClocks.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: MULTI-LEVEL COHERENCE                        *)
(*                                                                            *)
(* ========================================================================== *)

(**
  MULTI-LEVEL COHERENCE THEOREMS
  ===============================
  
  When we have multiple levels of hierarchy, coherence propagates:
  - Level k connects to all levels > k
  - This is the "fractal connectivity" of UCF/GUTT
*)

Module MultiLevelCoherence.

  Import ClockTicks.
  Import HierarchicalClocks.
  
  (** 
    INTERMEDIATE REFERENCE: Get the Whole at an intermediate level.
    Given a hierarchy of depth n, we can access the reference point
    at any level 0 <= k < n.
  *)
  
  (** Two hierarchies at the same level are coherent if they both
      connect to the universal reference (Whole) when embedded one level up.
      
      HONESTY NOTE: This definition is VACUOUS in its current form.
      The underlying relation is (fun _ _ => True), so lift_rel
      trivially holds for any pair â€” every x satisfies lift_rel R x None
      by WholeCompletion.serial. The refl/sym/trans proofs below are
      therefore trivial. The real coherence content is:
        (a) universal_coherence (Section 4): embedded readings always
            connect to Whole via the ACTUAL ticks_to relation.
        (b) hierarchy_conservative (Section 4): ticks_to is preserved
            under embedding.
        (c) TickReachability (Section 5A): constructive reachability
            through finite chains of actual ticks.
      
      A future v1.4+ should replace this with a substantive definition
      using hierarchical_tick or tick_reachable. *)
  Definition level_coherent (n : nat) (h1 h2 : HierarchicalClock n) : Prop :=
    let R := SerialComposition.iter_lift 1 (HierarchicalClock n) 
               (fun _ _ => True) in
    R (Some h1) None /\ R (Some h2) None.
  
  (** Every element is coherent with itself. *)
  Theorem level_coherent_refl : forall n (h : HierarchicalClock n),
    level_coherent n h h.
  Proof.
    intros n h.
    unfold level_coherent.
    split; exact I.
  Qed.

  (** Coherence is symmetric. *)
  Theorem level_coherent_sym : forall n (h1 h2 : HierarchicalClock n),
    level_coherent n h1 h2 -> level_coherent n h2 h1.
  Proof.
    intros n h1 h2 [H1 H2]. split; assumption.
  Qed.

  (** Coherence is transitive. *)
  Theorem level_coherent_trans : forall n (h1 h2 h3 : HierarchicalClock n),
    level_coherent n h1 h2 -> level_coherent n h2 h3 -> level_coherent n h1 h3.
  Proof.
    intros n h1 h2 h3 [H1 _] [_ H3]. split; assumption.
  Qed.

End MultiLevelCoherence.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5A: TICK REACHABILITY                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  TICK REACHABILITY: TRANSITIVE CLOSURE OF CLOCK TICKS
  =====================================================
  
  Unlike level_coherent (which is vacuous), tick reachability provides
  SUBSTANTIVE connectivity: two readings are reachable iff one can
  reach the other through a finite chain of actual tick steps.
  
  This is the reflexive-transitive closure of ticks_to, and it
  coincides exactly with the N_rel ordering (le_rel).
  
  KEY RESULTS:
    - reach_refl, reach_step, reach_trans: closure properties
    - reach_iff_le: reachability â†” le_rel
    - reach_advance: c is reachable from d iff c = advance n d
    - reach_distance: the unique n such that advance n d = c
    - hierarchical_reach_conservative: reachability preserved under embed
*)

Module TickReachability.

  Import ClockTicks.
  Import TimeDifference.
  Import HierarchicalClocks.

  (** Reflexive-transitive closure of ticks_to.
      tick_reachable c d means "d is reachable from c via â‰¥ 0 ticks". *)
  Inductive tick_reachable : ClockReading -> ClockReading -> Prop :=
    | reach_refl : forall c, tick_reachable c c
    | reach_step : forall c d, tick_reachable c d -> 
                               tick_reachable c (tick d).

  (** Transitivity of reachability. *)
  Theorem reach_trans : forall c d e,
    tick_reachable c d -> tick_reachable d e -> tick_reachable c e.
  Proof.
    intros c d e Hcd Hde.
    induction Hde as [| d' e' Hde' IH].
    - exact Hcd.
    - apply reach_step. exact (IH Hcd).
  Qed.

  (** Advancing by n ticks produces a reachable state. *)
  Lemma advance_reachable : forall n c,
    tick_reachable c (advance n c).
  Proof.
    induction n as [|n IH]; intro c; simpl.
    - apply reach_refl.
    - apply reach_step. apply IH.
  Qed.

  (** Reachability implies the le_rel ordering.
      If d is reachable from c, then c <=r d. *)
  Theorem reach_implies_le : forall c d,
    tick_reachable c d -> c <=r d.
  Proof.
    intros c d H. induction H as [| c' d' _ IH].
    - unfold le_rel. lia.
    - unfold le_rel in *. unfold tick. simpl. lia.
  Qed.

  (** The le_rel ordering implies reachability.
      If c <=r d, then d is reachable from c in (to_nat d - to_nat c) steps. *)
  Theorem le_implies_reach : forall c d,
    c <=r d -> tick_reachable c d.
  Proof.
    intros c d Hle.
    unfold le_rel in Hle.
    (* The distance is to_nat d - to_nat c *)
    assert (Hdist : to_nat d = to_nat c + (to_nat d - to_nat c)) by lia.
    set (n := to_nat d - to_nat c) in *.
    (* Prove by showing d = advance n c *)
    assert (Hadv : to_nat (advance n c) = to_nat c + n).
    { rewrite advance_to_nat. lia. }
    assert (Heq : to_nat d = to_nat (advance n c)) by lia.
    apply to_nat_injective in Heq.
    rewrite Heq.
    apply advance_reachable.
  Qed.

  (** MAIN EQUIVALENCE: Reachability â†” le_rel ordering.
      This is the key theorem: tick_reachable is exactly the 
      natural ordering on N_rel. *)
  Theorem reach_iff_le : forall c d,
    tick_reachable c d <-> c <=r d.
  Proof.
    split.
    - apply reach_implies_le.
    - apply le_implies_reach.
  Qed.

  (** DISTANCE THEOREM: For any two reachable readings, the unique
      number of steps from c to d equals (to_nat d - to_nat c). *)
  Theorem reach_distance : forall c d,
    tick_reachable c d ->
    advance (to_nat d - to_nat c) c = d.
  Proof.
    intros c d H.
    apply reach_implies_le in H.
    unfold le_rel in H.
    apply to_nat_injective.
    rewrite advance_to_nat. lia.
  Qed.

  (** Advance characterization: d is reachable from c iff d = advance n c
      for some n. *)
  Theorem reach_advance : forall c d,
    tick_reachable c d <-> exists n, advance n c = d.
  Proof.
    split.
    - intro H. exists (to_nat d - to_nat c). apply reach_distance. exact H.
    - intros [n Hn]. rewrite <- Hn. apply advance_reachable.
  Qed.

  (** Reachability is decidable (since le_rel is decidable). *)
  Theorem reach_dec : forall c d,
    tick_reachable c d \/ ~ tick_reachable c d.
  Proof.
    intros c d.
    destruct (Nat.le_decidable (to_nat c) (to_nat d)) as [Hle | Hgt].
    - left. apply le_implies_reach. unfold le_rel. exact Hle.
    - right. intro Habs. apply reach_implies_le in Habs.
      unfold le_rel in Habs. lia.
  Qed.

  (** Reachability is antisymmetric (mutual reachability implies equality). *)
  Theorem reach_antisym : forall c d,
    tick_reachable c d -> tick_reachable d c -> c = d.
  Proof.
    intros c d Hcd Hdc.
    apply reach_implies_le in Hcd.
    apply reach_implies_le in Hdc.
    unfold le_rel in *.
    apply to_nat_injective. lia.
  Qed.

End TickReachability.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: QUANTUM CLOCK MODEL                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUANTUM CLOCKS AS RELATIONAL STRUCTURES
  ========================================
  
  A quantum clock is characterized by:
  - Discrete tick events (quantized time)
  - Seriality (always has a next state)
  - Uncertainty in precise timing (modeled via relations)
  
  This section shows how quantum clocks emerge naturally from N_rel.
*)

Module QuantumClock.

  Import ClockTicks.
  
  (** A quantum clock state is just a relational natural.
      The discreteness is built into N_rel's inductive structure. *)
  Definition QuantumState := ClockReading.
  
  (** Quantum transition: exactly one tick forward (unitary-like). *)
  Definition quantum_tick := tick.
  
  (** Quantum seriality: every state has exactly one successor.
      This is stronger than classical seriality - it's deterministic. *)
  Theorem quantum_determinism : forall s : QuantumState,
    exists! s', quantum_tick s = s'.
  Proof.
    intro s.
    exists (quantum_tick s).
    split.
    - reflexivity.
    - intros s' H. exact H.
  Qed.
  
  (** Quantum states form a chain (total order). *)
  Theorem quantum_chain : forall s1 s2 : QuantumState,
    s1 <=r s2 \/ s2 <=r s1.
  Proof.
    apply le_rel_total.
  Qed.
  
  (** No state is its own successor (irreflexivity). *)
  Theorem quantum_irrefl : forall s : QuantumState,
    quantum_tick s <> s.
  Proof.
    intro s. unfold quantum_tick, tick.
    (* Goal: Succ_rel s <> s (displayed as s +r1 <> s) *)
    intro H.
    (* H : Succ_rel s = s, but succ_irrefl expects s = Succ_rel s *)
    symmetry in H.
    (* Now H : s = Succ_rel s *)
    apply succ_irrefl in H.
    exact H.
  Qed.
  
  (** Quantum advance using N_rel (fully relational). *)
  Definition quantum_advance := advance_rel.
  
  (** Quantum advance preserves the chain property. *)
  Theorem quantum_advance_monotone : forall n s,
    s <=r quantum_advance n s.
  Proof.
    intros n s.
    unfold le_rel.
    rewrite advance_rel_to_nat.
    lia.
  Qed.

End QuantumClock.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: RELATIVISTIC TIME DILATION                   *)
(*                                                                            *)
(* ========================================================================== *)

(**
  RELATIVISTIC TIME AS INTER-SET OPERATION
  =========================================
  
  Time dilation in relativity is fundamentally a RATE comparison:
  - Observer A's clock ticks at rate r_A
  - Observer B's clock ticks at rate r_B (in A's frame)
  - The ratio r_A / r_B is the Lorentz factor
  
  This is an INTER-SET operation because it relates different frames.
*)

Module RelativisticTime.

  Import ClockTicks.
  Import ClockRates.
  Import TimeDifference.
  
  (** A reference frame has its own clock rate. *)
  Record Frame := mkFrame {
    frame_rate : ClockRate;
    frame_origin : ClockReading  (* when the frame's clock started *)
  }.
  
  (** Time dilation factor between two frames (as Z_rel ratio). *)
  Definition dilation_num (A B : Frame) : Z_rel :=
    rate_ratio_num (frame_rate A) (frame_rate B).
  
  Definition dilation_denom (A B : Frame) : Z_rel :=
    rate_ratio_denom (frame_rate A) (frame_rate B).
  
  (** Positivity of dilation denominator when rate_ticks B is nonzero.
      Factored out so that dilation_factor reduces cleanly in proofs. *)
  Lemma dilation_denom_pos (A B : Frame)
      (HtB : rate_ticks (frame_rate B) <> Zero_rel) :
    (Z.of_nat (to_nat (rate_interval (frame_rate A))) *
     Z.of_nat (to_nat (rate_ticks (frame_rate B))) > 0)%Z.
  Proof.
    apply Z.lt_gt. apply Z.mul_pos_pos; apply Z.gt_lt; apply neq_zero_Z_pos.
    - exact (rate_nonzero (frame_rate A)).
    - exact HtB.
  Qed.

  (** Time dilation factor as a proper Q_rel rational.
      Requires the denominator clock (B) to have nonzero rate_ticks,
      since we divide by rate_ticks(B) * rate_interval(A).
      
      dilation_factor A B = (ticks_A * interval_B) / (interval_A * ticks_B) *)
  Definition dilation_factor (A B : Frame)
      (HtB : rate_ticks (frame_rate B) <> Zero_rel) : Q_rel :=
    mkQ (Z.of_nat (to_nat (rate_ticks (frame_rate A))) *
         Z.of_nat (to_nat (rate_interval (frame_rate B))))
        (Z.of_nat (to_nat (rate_interval (frame_rate A))) *
         Z.of_nat (to_nat (rate_ticks (frame_rate B))))
        (dilation_denom_pos A B HtB).

  (** Local proof tactic: unfold Q_rel equation, reduce projections, solve. *)
  Local Ltac solve_qeq :=
    unfold qeq; unfold dilation_factor; unfold Q_one; unfold qmul;
    simpl qnum; simpl qden; ring.
  
  (** Dilation factor from a frame to itself is 1. *)
  Theorem dilation_refl : forall A (Ht : rate_ticks (frame_rate A) <> Zero_rel),
    dilation_factor A A Ht =Q= Q_one.
  Proof. intros A Ht. solve_qeq. Qed.

  (** Dilation factor product is symmetric: 
      dilation(A,B) * dilation(B,A) =Q= 1 when both are well-defined. *)
  Theorem dilation_product_one : forall A B
      (HtA : rate_ticks (frame_rate A) <> Zero_rel)
      (HtB : rate_ticks (frame_rate B) <> Zero_rel),
    (dilation_factor A B HtB *Q dilation_factor B A HtA) =Q= Q_one.
  Proof. intros A B HtA HtB. solve_qeq. Qed.
  
  (** Proper time in frame A corresponding to coordinate time in B (Z_rel version).
      Multiplies by the numerator only Ã¢â‚¬â€ a scaled representation
      where the denominator is implicit. *)
  Definition proper_time_Z (A B : Frame) (coord_t : ClockReading) : Z_rel :=
    Z_mul (embed_N coord_t) (dilation_num A B).

  (** Proper time as a proper Q_rel rational.
      proper_time = coord_t * dilation_factor(A, B). *)
  Definition proper_time (A B : Frame) 
      (HtB : rate_ticks (frame_rate B) <> Zero_rel) 
      (coord_t : ClockReading) : Q_rel :=
    qmul (Z_to_Q (Z.of_nat (to_nat coord_t))) (dilation_factor A B HtB).

  (** Proper time in one's own frame equals coordinate time. *)
  Theorem proper_time_self : forall A 
      (Ht : rate_ticks (frame_rate A) <> Zero_rel) 
      (t : ClockReading),
    proper_time A A Ht t =Q= Z_to_Q (Z.of_nat (to_nat t)).
  Proof.
    intros A Ht t.
    unfold proper_time.
    assert (Hd : dilation_factor A A Ht =Q= Q_one) by apply dilation_refl.
    (* t * dilation(A,A) =Q= t * 1 =Q= t *)
    apply (qeq_trans _ (qmul (Z_to_Q (Z.of_nat (to_nat t))) Q_one)).
    - apply qmul_respects_qeq. apply qeq_refl. exact Hd.
    - apply qmul_1_r.
  Qed.

  (** Backward compatibility: the old symmetric product theorem on Z_rel. *)
  Theorem dilation_symmetric_product : forall A B,
    Z_equiv 
      (Z_mul (dilation_num A B) (dilation_num B A))
      (Z_mul (dilation_denom A B) (dilation_denom B A)).
  Proof.
    intros A B.
    unfold dilation_num, dilation_denom, rate_ratio_num, rate_ratio_denom.
    apply to_Z_faithful.
    repeat rewrite to_Z_mul.
    repeat rewrite embed_N_to_Z.
    lia.
  Qed.

  (** DILATION CHAIN RULE: dilation factors compose multiplicatively.
      dilation(A,C) =Q= dilation(A,B) * dilation(B,C)
      
      This is the fundamental composition law for reference frame 
      transformations. The proof reduces to Z ring arithmetic:
      both sides have the same numerator and denominator up to
      commutativity of multiplication. *)
  Theorem dilation_chain : forall A B C
      (HtB : rate_ticks (frame_rate B) <> Zero_rel)
      (HtC : rate_ticks (frame_rate C) <> Zero_rel),
    dilation_factor A C HtC =Q=
    (dilation_factor A B HtB *Q dilation_factor B C HtC).
  Proof.
    intros A B C HtB HtC.
    unfold qeq, dilation_factor, qmul. simpl qnum. simpl qden.
    ring.
  Qed.

  (** PROPER TIME CHAIN: transforming through an intermediate frame
      is equivalent to direct transformation.
      proper_time(A, C, t) =Q= proper_time(A, B, coord_tBC) 
      where coord_tBC appropriately accounts for B's frame.
      
      More precisely: t * dilation(A,C) =Q= t * dilation(A,B) * dilation(B,C).
      This follows directly from the dilation chain rule. *)
  Theorem proper_time_chain : forall A B C
      (HtB : rate_ticks (frame_rate B) <> Zero_rel)
      (HtC : rate_ticks (frame_rate C) <> Zero_rel)
      (t : ClockReading),
    proper_time A C HtC t =Q=
    qmul (proper_time A B HtB t) (dilation_factor B C HtC).
  Proof.
    intros A B C HtB HtC t.
    unfold proper_time.
    (* Goal: t * dilation(A,C) =Q= (t * dilation(A,B)) * dilation(B,C) *)
    set (tv := Z_to_Q (Z.of_nat (to_nat t))).
    (* Step 1: use dilation_chain to rewrite LHS *)
    assert (Hchain : dilation_factor A C HtC =Q=
                     (dilation_factor A B HtB *Q dilation_factor B C HtC))
      by apply dilation_chain.
    (* Step 2: tv * dilation(A,C) =Q= tv * (dilation(A,B) * dilation(B,C)) *)
    apply (qeq_trans _ (qmul tv (dilation_factor A B HtB *Q dilation_factor B C HtC))).
    - apply qmul_respects_qeq. apply qeq_refl. exact Hchain.
    - (* tv * (d_AB * d_BC) =Q= (tv * d_AB) * d_BC by associativity *)
      apply qeq_sym. apply qmul_assoc.
  Qed.

End RelativisticTime.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: PUBLIC API MODULE                            *)
(*                                                                            *)
(* ========================================================================== *)

(**
  CHC: The canonical public API for Clock Hierarchy Coherence.
  
  This module provides stable, memorable names for downstream use.
*)

Module CHC.

  (* Types *)
  Definition ClockReading := ClockTicks.ClockReading.
  Definition ClockRate := ClockRates.ClockRate.
  Definition HierarchicalClock := HierarchicalClocks.HierarchicalClock.
  Definition QuantumState := QuantumClock.QuantumState.
  Definition Frame := RelativisticTime.Frame.
  
  (* Constructors *)
  Definition initial := ClockTicks.initial_reading.
  Definition tick := ClockTicks.tick.
  Definition mkRate := ClockRates.mkRate.
  Definition mkFrame := RelativisticTime.mkFrame.
  
  (* Operations - nat interface *)
  Definition advance := ClockTicks.advance.
  Definition value := ClockTicks.reading_value.
  
  (* Operations - N_rel interface (preferred) *)
  Definition advance_rel := ClockTicks.advance_rel.
  Definition value_rel := ClockTicks.reading_value_rel.
  
  (* Time differences *)
  Definition time_diff := TimeDifference.time_diff.
  Definition is_after := TimeDifference.is_after.
  Definition is_before := TimeDifference.is_before.
  
  (* Clock rates *)
  Definition same_rate := ClockRates.same_rate.
  Definition is_faster := ClockRates.is_faster.
  
  (* Hierarchy *)
  Definition embed := HierarchicalClocks.embed_reading.
  Definition universal_ref := HierarchicalClocks.universal_reference.
  Definition hierarchical_tick := HierarchicalClocks.hierarchical_tick.
  Definition level_coherent := MultiLevelCoherence.level_coherent.
  
  (* Quantum *)
  Definition quantum_tick := QuantumClock.quantum_tick.
  Definition quantum_advance := QuantumClock.quantum_advance.
  
  (* Relativistic *)
  Definition dilation_factor := RelativisticTime.dilation_factor.
  Definition proper_time := RelativisticTime.proper_time.
  Definition proper_time_Z := RelativisticTime.proper_time_Z.
  
  (* Key theorems - clock ticks *)
  Definition tick_serial := ClockTicks.tick_serial.
  Definition advance_equiv := ClockTicks.advance_advance_rel_equiv.
  
  (* Key theorems - rates *)
  Definition same_rate_refl := ClockRates.same_rate_refl.
  Definition same_rate_sym := ClockRates.same_rate_sym.
  Definition same_rate_trans := ClockRates.same_rate_trans.
  Definition faster_antisym := ClockRates.faster_antisym.
  Definition faster_trans := ClockRates.faster_trans.
  
  (* Key theorems - hierarchy *)
  Definition universal_coherence := HierarchicalClocks.universal_coherence.
  Definition hierarchy_conservative := HierarchicalClocks.hierarchy_conservative.
  Definition level_coherent_refl := MultiLevelCoherence.level_coherent_refl.
  Definition level_coherent_sym := MultiLevelCoherence.level_coherent_sym.
  Definition level_coherent_trans := MultiLevelCoherence.level_coherent_trans.
  
  (* Key theorems - quantum *)
  Definition quantum_determinism := QuantumClock.quantum_determinism.

  (* Key theorems - relativistic *)
  Definition dilation_refl := RelativisticTime.dilation_refl.
  Definition dilation_product_one := RelativisticTime.dilation_product_one.
  Definition dilation_chain := RelativisticTime.dilation_chain.
  Definition proper_time_self := RelativisticTime.proper_time_self.
  Definition proper_time_chain := RelativisticTime.proper_time_chain.

  (* Tick reachability *)
  Definition tick_reachable := TickReachability.tick_reachable.
  Definition reach_iff_le := TickReachability.reach_iff_le.
  Definition reach_advance := TickReachability.reach_advance.
  Definition reach_distance := TickReachability.reach_distance.
  Definition reach_dec := TickReachability.reach_dec.
  Definition reach_antisym := TickReachability.reach_antisym.

  (* Relational algebra bridge *)
  Definition tick_graph := RelationalAlgebraBridge.tick_graph.
  Definition tick_graph_serial := RelationalAlgebraBridge.tick_graph_serial.
  Definition tick_graph_functional := RelationalAlgebraBridge.tick_graph_functional.
  Definition advance_graph := RelationalAlgebraBridge.advance_graph.
  Definition advance_graph_is_iter := RelationalAlgebraBridge.advance_graph_is_iter.
  Definition rel_comp_iter := @RelationalAlgebraBridge.rel_comp_iter.

End CHC.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: HINT DATABASES & TACTICS                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Hint database for clock hierarchy proofs. *)
Create HintDb chc discriminated.

#[export] Hint Resolve ClockTicks.tick_serial : chc.
#[export] Hint Resolve ClockTicks.advance_from_initial : chc.
#[export] Hint Resolve ClockTicks.advance_rel_from_initial : chc.
#[export] Hint Resolve ClockRates.same_rate_refl : chc.
#[export] Hint Resolve ClockRates.same_rate_sym : chc.
#[export] Hint Resolve ClockRates.same_rate_trans : chc.
#[export] Hint Resolve ClockRates.faster_antisym : chc.
#[export] Hint Resolve HierarchicalClocks.universal_coherence : chc.
#[export] Hint Resolve HierarchicalClocks.embed_injective : chc.
#[export] Hint Resolve MultiLevelCoherence.level_coherent_refl : chc.
#[export] Hint Resolve MultiLevelCoherence.level_coherent_sym : chc.
#[export] Hint Resolve QuantumClock.quantum_determinism : chc.
#[export] Hint Resolve QuantumClock.quantum_chain : chc.
#[export] Hint Resolve RelationalAlgebraBridge.tick_graph_serial : chc.
#[export] Hint Resolve RelationalAlgebraBridge.tick_graph_functional : chc.
#[export] Hint Resolve RelativisticTime.dilation_refl : chc.
#[export] Hint Resolve RelativisticTime.dilation_chain : chc.
#[export] Hint Resolve TickReachability.reach_refl : chc.
#[export] Hint Resolve TickReachability.advance_reachable : chc.

(** Simplification tactic for clock expressions. *)
Ltac chc_simpl :=
  unfold CHC.advance, CHC.advance_rel, CHC.value, CHC.value_rel,
         CHC.time_diff, CHC.tick, CHC.initial,
         ClockTicks.advance, ClockTicks.advance_rel,
         ClockTicks.reading_value, ClockTicks.reading_value_rel,
         ClockTicks.tick, ClockTicks.initial_reading,
         TimeDifference.time_diff, TimeDifference.reading_to_Z in *;
  simpl in *.

(** Combined tactic for clock hierarchy proofs. *)
Ltac chc_auto := chc_simpl; auto with chc nrel.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: EXAMPLES & TESTS                            *)
(*                                                                            *)
(* ========================================================================== *)

Module ClockExamples.

  Import ClockTicks.
  Import TimeDifference.
  
  (** Basic clock operations. *)
  Example ex_tick : tick initial_reading = one_rel.
  Proof. reflexivity. Qed.
  
  Example ex_advance_3 : advance 3 initial_reading = three_rel.
  Proof. reflexivity. Qed.
  
  Example ex_advance_rel_3 : advance_rel 3r initial_reading = three_rel.
  Proof. reflexivity. Qed.
  
  (** Equivalence of interfaces. *)
  Example ex_interface_equiv : 
    advance 5 initial_reading = advance_rel 5r initial_reading.
  Proof.
    rewrite advance_advance_rel_equiv. reflexivity.
  Qed.
  
  (** Time difference. *)
  Example ex_time_diff : 
    to_Z (time_diff initial_reading (advance 3 initial_reading)) = 3%Z.
  Proof.
    rewrite time_diff_advance. reflexivity.
  Qed.
  
  (** Seriality. *)
  Example ex_serial : exists c', ticks_to two_rel c'.
  Proof. apply tick_serial. Qed.

End ClockExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)
  
  Definition test_tick : ClockTicks.tick Zero_rel = one_rel.
  Proof. reflexivity. Qed.
  
  Definition test_advance : ClockTicks.advance 2 Zero_rel = two_rel.
  Proof. reflexivity. Qed.
  
  Definition test_advance_rel : ClockTicks.advance_rel 2r Zero_rel = two_rel.
  Proof. reflexivity. Qed.
  
  Definition test_equiv : 
    ClockTicks.advance 3 Zero_rel = ClockTicks.advance_rel 3r Zero_rel.
  Proof. reflexivity. Qed.
  
  Definition test_value : ClockTicks.reading_value three_rel = 3.
  Proof. reflexivity. Qed.
  
  Definition test_value_rel : ClockTicks.reading_value_rel three_rel = 3r.
  Proof. reflexivity. Qed.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (CHC):
    CHC.ClockReading      = N_rel
    CHC.initial           = Zero_rel
    CHC.tick              = Succ_rel
    CHC.advance n c       = advance by n ticks (nat version)
    CHC.advance_rel n c   = advance by n ticks (N_rel version, preferred)
    CHC.value c           = to_nat c (nat result)
    CHC.value_rel c       = c (N_rel result)
    CHC.time_diff c1 c2   = signed difference as Z_rel
    CHC.same_rate r1 r2   = rate equivalence (equiv. relation)
    CHC.is_faster r1 r2   = strict rate ordering (strict partial order)
    CHC.dilation_factor   = rate ratio as Q_rel
    CHC.dilation_chain    = dilation(A,C) =Q= dilation(A,B) * dilation(B,C)
    CHC.proper_time       = coord time * dilation factor (Q_rel)
    CHC.proper_time_chain = t*dil(A,C) =Q= (t*dil(A,B))*dil(B,C)
    CHC.tick_graph         = rel_graph tick (relational algebra form)
    CHC.advance_graph n    = rel_graph (advance n) (n-step graph)
    CHC.rel_comp_iter n R  = n-fold relational composition
    CHC.tick_reachable     = reflexive-transitive closure of tick
    CHC.reach_iff_le       = reachability <-> le_rel ordering
    CHC.reach_advance      = reachable <-> exists n, advance n c = d
    CHC.reach_distance     = unique n steps from c to d
    CHC.reach_dec          = reachability is decidable
    CHC.reach_antisym      = mutual reachability -> equality
  
  DUAL INTERFACES:
    nat version: Compatible with lia, list indexing, stdlib
    N_rel version: Consistent with UCF/GUTT relational foundations
    Conversion: advance n c = advance_rel (from_nat n) c
  
  RELATIONAL ALGEBRA BRIDGE:
    tick_graph             = rel_graph tick
    tick_graph_serial/functional : serial + functional
    advance_graph_is_iter  : advance_graph n == rel_comp_iter n tick_graph
    tick_prev              = rel_conv tick_graph
    tick_graph_ue_serial   : UE.lift ticks_to is serial
  
  ALGEBRAIC PROPERTIES:
    same_rate: refl, sym, trans (equivalence relation)
    is_faster: antisym, trans (strict partial order)
    level_coherent: refl, sym, trans (VACUOUS -- see honest note in Section 5)
    dilation_factor: refl (=Q= 1), product (A->B * B->A =Q= 1), chain
    proper_time_self: proper_time(A,A,t) =Q= t
    proper_time_chain: t*dil(A,C) =Q= (t*dil(A,B))*dil(B,C)
    tick_reachable: refl, trans, antisym, decidable
    reach_iff_le: reachability <-> N_rel ordering (THE KEY EQUIVALENCE)
  
  HINT DATABASE: chc
  TACTICS: chc_simpl, chc_auto, ucf_lia, ucf_nia (from UCF_Lia/UCF_Nia)
  
  AXIOM STATUS: ZERO additional axioms beyond Coq's standard library.
*)
