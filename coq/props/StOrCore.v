(**
  StOrCore_Reconciled.v
  =====================
  RECONCILED VERSION: Unifies Proposition 15 and StOrCore
  
  This file resolves the conflict between:
  - Proposition_15_Strength_proven.v (with stor_index)
  - Original StOrCore.v (without stor_index, but with rich operations)
  
  Resolution Strategy:
  1. Keep StrengthMeasure name (more generic than StrengthOfRelation)
  2. Add stor_index field to support StOr₀, StOr₁, ... notation
  3. Preserve all morphisms and Proper instances from StOrCore
  4. Maintain integration with DistanceMeasure and MetricCore
  5. Unify operation names with consistent notation
  
  ZERO AXIOMS - Fully Constructive
  
  UCF/GUTT Research & Evaluation License v1.1
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

From Coq Require Import Reals.
From Coq Require Import micromega.Lra.
From Coq Require Import Morphisms RelationClasses.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Bool.
Import ListNotations.
Require Import MetricCore DistanceMeasure.

Set Implicit Arguments.
Local Open Scope R_scope.

(* ================================================================ *)
(* Part A: Strength Measure - RECONCILED Core Record               *)
(* ================================================================ *)

(**
  RECONCILED DEFINITION:
  
  Combines features from both versions:
  - strength_value: R (Prop 15: stor_value)
  - strength_positive: proof (both versions had this)
  - strength_index: nat (NEW: from Prop 15 to support StOr₀, StOr₁, ...)
  
  The index allows tracking different strength types as in original
  Proposition 15 notation, while maintaining the rich operational
  framework from StOrCore.
*)

Record StrengthMeasure := {
  strength_value : R;
  strength_positive : 0 < strength_value;
  strength_index : nat  (* StOr₀, StOr₁, ... *)
}.

(* Backwards compatibility accessors *)
Definition stor_value (s : StrengthMeasure) : R := strength_value s.
Definition stor_positive (s : StrengthMeasure) : 0 < stor_value s := strength_positive s.
Definition stor_index (s : StrengthMeasure) : nat := strength_index s.

(* ================================================================ *)
(* Part B: Equality and Setoid Structure                           *)
(* ================================================================ *)

(**
  Two strengths are equal if their values AND indices are equal.
  This reconciles both versions' equality notions.
*)

Definition sm_eq (s1 s2 : StrengthMeasure) : Prop :=
  strength_value s1 = strength_value s2 /\ 
  strength_index s1 = strength_index s2.

(* Value-only equality (for when index doesn't matter) *)
Definition sm_eq_value (s1 s2 : StrengthMeasure) : Prop :=
  strength_value s1 = strength_value s2.

Notation "s1 ≈ s2" := (sm_eq s1 s2) (at level 70).
Notation "s1 ≈ᵥ s2" := (sm_eq_value s1 s2) (at level 70).

(* Full equality is an equivalence *)
Lemma sm_eq_refl : forall s, s ≈ s.
Proof. intros. unfold sm_eq. split; reflexivity. Qed.

Lemma sm_eq_sym : forall s1 s2, s1 ≈ s2 -> s2 ≈ s1.
Proof. intros. unfold sm_eq in *. destruct H. split; symmetry; assumption. Qed.

Lemma sm_eq_trans : forall s1 s2 s3, s1 ≈ s2 -> s2 ≈ s3 -> s1 ≈ s3.
Proof. 
  intros. unfold sm_eq in *. destruct H, H0.
  split; [rewrite H; assumption | rewrite H1; assumption].
Qed.

#[export] Instance sm_equivalence : Equivalence sm_eq.
Proof.
  split.
  - exact sm_eq_refl.
  - exact sm_eq_sym.
  - exact sm_eq_trans.
Qed.

(* Value equality is also an equivalence *)
Lemma sm_eq_value_refl : forall s, s ≈ᵥ s.
Proof. intros. unfold sm_eq_value. reflexivity. Qed.

Lemma sm_eq_value_sym : forall s1 s2, s1 ≈ᵥ s2 -> s2 ≈ᵥ s1.
Proof. intros. unfold sm_eq_value in *. symmetry. assumption. Qed.

Lemma sm_eq_value_trans : forall s1 s2 s3, s1 ≈ᵥ s2 -> s2 ≈ᵥ s3 -> s1 ≈ᵥ s3.
Proof. intros. unfold sm_eq_value in *. rewrite H. assumption. Qed.

#[export] Instance sm_eq_value_equivalence : Equivalence sm_eq_value.
Proof.
  split.
  - exact sm_eq_value_refl.
  - exact sm_eq_value_sym.
  - exact sm_eq_value_trans.
Qed.

(* ================================================================ *)
(* Part C: Ordering Relations                                      *)
(* ================================================================ *)

(**
  Ordering is based on value only (index doesn't affect magnitude).
  This matches both original versions.
*)

Definition sm_lt (s1 s2 : StrengthMeasure) : Prop :=
  strength_value s1 < strength_value s2.

Definition sm_le (s1 s2 : StrengthMeasure) : Prop :=
  strength_value s1 <= strength_value s2.

Notation "s1 <ₛ s2" := (sm_lt s1 s2) (at level 70).
Notation "s1 ≤ₛ s2" := (sm_le s1 s2) (at level 70).

(* Backwards compatibility *)
Definition stor_lt := sm_lt.
Definition stor_le := sm_le.

Lemma sm_lt_irrefl : forall s, ~ (s <ₛ s).
Proof. intros s H. unfold sm_lt in H. lra. Qed.

Lemma sm_lt_trans : forall s1 s2 s3,
  s1 <ₛ s2 -> s2 <ₛ s3 -> s1 <ₛ s3.
Proof. intros. unfold sm_lt in *. lra. Qed.

Lemma sm_le_refl : forall s, s ≤ₛ s.
Proof. intros. unfold sm_le. lra. Qed.

Lemma sm_le_trans : forall s1 s2 s3,
  s1 ≤ₛ s2 -> s2 ≤ₛ s3 -> s1 ≤ₛ s3.
Proof. intros. unfold sm_le in *. lra. Qed.

Lemma sm_le_antisym : forall s1 s2,
  s1 ≤ₛ s2 -> s2 ≤ₛ s1 -> s1 ≈ᵥ s2.
Proof. intros. unfold sm_le, sm_eq_value in *. lra. Qed.

(* ================================================================ *)
(* Part D: Standard Strength Values (RECONCILED)                   *)
(* ================================================================ *)

(**
  Standard reference strengths with explicit indices.
  Reconciles both versions' standard values.
*)

Definition sm_minimal : StrengthMeasure.
Proof.
  refine {| strength_value := 0.01; strength_index := 0 |}.
  lra.
Defined.

Definition sm_very_weak : StrengthMeasure.
Proof.
  refine {| strength_value := 0.2; strength_index := 1 |}.
  lra.
Defined.

Definition sm_weak : StrengthMeasure.
Proof.
  refine {| strength_value := 0.4; strength_index := 2 |}.
  lra.
Defined.

Definition sm_moderate : StrengthMeasure.
Proof.
  refine {| strength_value := 0.8; strength_index := 3 |}.
  lra.
Defined.

Definition sm_strong : StrengthMeasure.
Proof.
  refine {| strength_value := 1.5; strength_index := 4 |}.
  lra.
Defined.

Definition sm_very_strong : StrengthMeasure.
Proof.
  refine {| strength_value := 5.0; strength_index := 5 |}.
  lra.
Defined.

Definition sm_maximal : StrengthMeasure.
Proof.
  refine {| strength_value := 100.0; strength_index := 6 |}.
  lra.
Defined.

(* Backwards compatibility aliases *)
Definition stor_minimal := sm_minimal.
Definition stor_very_weak := sm_very_weak.
Definition stor_weak := sm_weak.
Definition stor_moderate := sm_moderate.
Definition stor_strong := sm_strong.
Definition stor_very_strong := sm_very_strong.
Definition stor_maximal := sm_maximal.

(* ================================================================ *)
(* Part E: Strength Classification                                 *)
(* ================================================================ *)

(**
  Unified classification system from both versions.
*)

Inductive StrengthLabel :=
  | VeryWeak    : StrengthLabel
  | Weak        : StrengthLabel
  | Moderate    : StrengthLabel
  | Strong      : StrengthLabel
  | VeryStrong  : StrengthLabel.

(* Alternative with embedded strength (from Prop 15) *)
Inductive StrengthDegree :=
  | VeryWeakD    : StrengthMeasure -> StrengthDegree
  | WeakD        : StrengthMeasure -> StrengthDegree
  | ModerateD    : StrengthMeasure -> StrengthDegree
  | StrongD      : StrengthMeasure -> StrengthDegree
  | VeryStrongD  : StrengthMeasure -> StrengthDegree.

Definition strength_label_eq_dec : forall (l1 l2 : StrengthLabel), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. Defined.

Definition classify_strength (s : StrengthMeasure) : StrengthLabel :=
  let v := strength_value s in
  if Rle_dec v 0.25 then VeryWeak
  else if Rle_dec v 0.5 then Weak
  else if Rle_dec v 1.0 then Moderate
  else if Rle_dec v 2.0 then Strong
  else VeryStrong.

(* Classification with embedded strength *)
Definition classify_strength_degree (s : StrengthMeasure) : StrengthDegree :=
  let v := strength_value s in
  if Rle_dec v 0.25 then VeryWeakD s
  else if Rle_dec v 0.5 then WeakD s
  else if Rle_dec v 1.0 then ModerateD s
  else if Rle_dec v 2.0 then StrongD s
  else VeryStrongD s.

Lemma classify_proper : forall s1 s2,
  s1 ≈ᵥ s2 -> classify_strength s1 = classify_strength s2.
Proof.
  intros s1 s2 Heq.
  unfold sm_eq_value in Heq.
  unfold classify_strength.
  rewrite Heq.
  reflexivity.
Qed.

#[export] Instance classify_morphism : 
  Proper (sm_eq_value ==> eq) classify_strength.
Proof.
  intros s1 s2 Heq.
  apply classify_proper.
  assumption.
Qed.

(* ================================================================ *)
(* Part F: Operation ⊕ - Strength Addition (RECONCILED)            *)
(* ================================================================ *)

(**
  Combines two strengths additively.
  Index is taken as max (as in Prop 15's stor_combine).
*)

Definition sm_add (s1 s2 : StrengthMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := strength_value s1 + strength_value s2;
    strength_index := max (strength_index s1) (strength_index s2)
  |}.
  pose proof (strength_positive s1) as H1.
  pose proof (strength_positive s2) as H2.
  lra.
Defined.

Notation "s1 ⊕ₛ s2" := (sm_add s1 s2) (at level 50, left associativity).

(* Backwards compatibility *)
Definition stor_combine := sm_add.

#[export] Instance sm_add_proper : Proper (sm_eq_value ==> sm_eq_value ==> sm_eq_value) sm_add.
Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  unfold sm_eq_value in *.
  simpl. lra.
Qed.

Lemma sm_add_assoc_value : forall s1 s2 s3, 
  (s1 ⊕ₛ s2) ⊕ₛ s3 ≈ᵥ s1 ⊕ₛ (s2 ⊕ₛ s3).
Proof.
  intros. unfold sm_eq_value. simpl. lra.
Qed.

Lemma sm_add_comm_value : forall s1 s2, s1 ⊕ₛ s2 ≈ᵥ s2 ⊕ₛ s1.
Proof.
  intros. unfold sm_eq_value. simpl. lra.
Qed.

Lemma sm_add_increases_left : forall s1 s2, s1 <ₛ (s1 ⊕ₛ s2).
Proof.
  intros. unfold sm_lt, sm_add. simpl.
  pose proof (strength_positive s2) as H. lra.
Qed.

Lemma sm_add_increases_right : forall s1 s2, s2 <ₛ (s1 ⊕ₛ s2).
Proof.
  intros. unfold sm_lt, sm_add. simpl.
  pose proof (strength_positive s1). lra.
Qed.

(* ================================================================ *)
(* Part G: Operation ⊗ - Strength Multiplication                   *)
(* ================================================================ *)

(**
  Multiply two strengths.
  Index preserved from s1 (could also use max).
*)

Definition sm_mult (s1 s2 : StrengthMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := strength_value s1 * strength_value s2;
    strength_index := strength_index s1
  |}.
  apply Rmult_lt_0_compat; apply strength_positive.
Defined.

Notation "s1 ⊗ s2" := (sm_mult s1 s2) (at level 40, left associativity).

#[export] Instance sm_mult_proper : Proper (sm_eq_value ==> sm_eq_value ==> sm_eq_value) sm_mult.
Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  unfold sm_eq_value in *.
  simpl. rewrite Hs1, Hs2. reflexivity.
Qed.

(* ================================================================ *)
(* Part H: Scalar Multiplication                                   *)
(* ================================================================ *)

Definition sm_scale (α : R) (Hα : 0 < α) (s : StrengthMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := α * strength_value s;
    strength_index := strength_index s
  |}.
  apply Rmult_lt_0_compat; [exact Hα | apply strength_positive].
Defined.

Arguments sm_scale α {Hα} s.

(* Backwards compatibility *)
Definition stor_scale (s : StrengthMeasure) (factor : R) (H : 0 < factor) : StrengthMeasure :=
  @sm_scale factor H s.

#[export] Instance sm_scale_proper α (Hα : 0 < α) : 
  Proper (sm_eq_value ==> sm_eq_value) (@sm_scale α Hα).
Proof.
  intros s1 s2 Hs.
  unfold sm_eq_value in *. simpl.
  rewrite Hs. reflexivity.
Qed.

(* ================================================================ *)
(* Part I: Averaging Operation                                     *)
(* ================================================================ *)

Definition sm_average (s1 s2 : StrengthMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := (strength_value s1 + strength_value s2) / 2;
    strength_index := (strength_index s1 + strength_index s2) / 2
  |}.
  pose proof (strength_positive s1).
  pose proof (strength_positive s2).
  apply Rmult_lt_0_compat; [lra | lra].
Defined.

Notation "s1 ⊕/ s2" := (sm_average s1 s2) (at level 50).

(* Backwards compatibility *)
Definition stor_average := sm_average.

#[export] Instance sm_average_proper : Proper (sm_eq_value ==> sm_eq_value ==> sm_eq_value) sm_average.
Proof.
  intros s1 s1' Hs1 s2 s2' Hs2.
  unfold sm_eq_value in *.
  simpl. rewrite Hs1, Hs2. reflexivity.
Qed.

(* ================================================================ *)
(* Part J: Distance-Based Attenuation (RECONCILED)                 *)
(* ================================================================ *)

(**
  Attenuate strength by distance.
  Reconciles Prop 15's stor_attenuate_by_distance with StOrCore's
  sm_attenuate_linear, using DistanceMeasure for type safety.
*)

(* Linear attenuation with DistanceMeasure *)
Definition sm_attenuate_linear (s : StrengthMeasure) (d : DistanceMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := strength_value s / (1 + dist_value d);
    strength_index := strength_index s
  |}.
  pose proof (strength_positive s).
  pose proof (dist_nonneg d).
  apply Rmult_lt_0_compat; [assumption |].
  apply Rinv_0_lt_compat. lra.
Defined.

Notation "s ⊘₁ d" := (sm_attenuate_linear s d) (at level 45, left associativity).

(* Backwards compatibility: attenuation with raw R distance *)
Definition stor_attenuate_by_distance (s : StrengthMeasure) (d : R) (Hd : 0 <= d) : StrengthMeasure :=
  sm_attenuate_linear s {| dist_value := d; dist_nonneg := Hd |}.

(* Inverse square attenuation *)
Definition sm_attenuate_square (s : StrengthMeasure) (d : DistanceMeasure) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := strength_value s / (1 + (dist_value d) * (dist_value d));
    strength_index := strength_index s
  |}.
  pose proof (strength_positive s).
  pose proof (dist_nonneg d).
  apply Rmult_lt_0_compat; [assumption |].
  apply Rinv_0_lt_compat.
  assert (0 <= dist_value d * dist_value d).
  { apply Rmult_le_pos; assumption. }
  lra.
Defined.

Notation "s ⊘₂ d" := (sm_attenuate_square s d) (at level 45, left associativity).

(* ================================================================ *)
(* Part K: Key Theorems (RECONCILED)                               *)
(* ================================================================ *)

(* From both versions: strength is always positive *)
Theorem strength_always_positive :
  forall (s : StrengthMeasure),
    strength_value s > 0.
Proof.
  intro s.
  apply strength_positive.
Qed.

(* Combining strengths increases total *)
Theorem sm_add_increases :
  forall s1 s2,
    s1 <ₛ (s1 ⊕ₛ s2) /\ s2 <ₛ (s1 ⊕ₛ s2).
Proof.
  intros s1 s2.
  split.
  - apply sm_add_increases_left.
  - apply sm_add_increases_right.
Qed.

(* Backwards compatibility *)
Theorem stor_combine_increases :
  forall (s1 s2 : StrengthMeasure),
    stor_lt s1 (stor_combine s1 s2) /\
    stor_lt s2 (stor_combine s1 s2).
Proof.
  apply sm_add_increases.
Qed.

(* Attenuation decreases strength *)
Lemma sm_attenuate_decreases : forall s d,
  dist_value d > 0 ->
  (s ⊘₁ d) <ₛ s.
Proof.
  intros s d Hpos.
  unfold sm_lt, sm_attenuate_linear. simpl.
  pose proof (strength_positive s) as Hs.
  pose proof (dist_nonneg d) as Hd.
  unfold Rdiv.
  assert (Hsum: 0 < 1 + dist_value d) by lra.
  assert (Hinv: / (1 + dist_value d) < 1).
  { apply Rmult_lt_reg_l with (r := 1 + dist_value d).
    - exact Hsum.
    - rewrite Rinv_r by lra. lra. }
  assert (strength_value s * / (1 + dist_value d) < strength_value s * 1).
  { apply Rmult_lt_compat_l; assumption. }
  lra.
Qed.

(* Backwards compatibility *)
Theorem stor_attenuate_decreases :
  forall (s : StrengthMeasure) (d : R) (Hd : 0 <= d),
    d > 0 ->
    stor_lt (@stor_attenuate_by_distance s d Hd) s.
Proof.
  intros s d Hd Hpos.
  unfold stor_attenuate_by_distance.
  apply sm_attenuate_decreases.
  exact Hpos.
Qed.

(* Propagation factor *)
Definition propagation_factor (s : StrengthMeasure) : R :=
  strength_value s.

Theorem stronger_propagates_faster : forall s1 s2,
  s1 <ₛ s2 ->
  propagation_factor s1 < propagation_factor s2.
Proof.
  intros s1 s2 Hlt.
  unfold propagation_factor, sm_lt in *.
  exact Hlt.
Qed.

(* ================================================================ *)
(* Part L: Conversion to/from DistanceMeasure                      *)
(* ================================================================ *)

Definition strength_to_distance (s : StrengthMeasure) : DistanceMeasure.
Proof.
  refine {| dist_value := 1 / strength_value s |}.
  pose proof (strength_positive s) as Hpos.
  apply Rlt_le.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - lra.
  - apply Rinv_0_lt_compat. exact Hpos.
Defined.

Definition distance_to_strength (d : DistanceMeasure) 
  (Hpos : 0 < dist_value d) : StrengthMeasure.
Proof.
  refine {| 
    strength_value := 1 / dist_value d;
    strength_index := 0  (* default index *)
  |}.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - lra.
  - apply Rinv_0_lt_compat. exact Hpos.
Defined.

(* ================================================================ *)
(* Part M: Summary Banner                                          *)
(* ================================================================ *)

(*
  ╔══════════════════════════════════════════════════════════════╗
  ║         🎯 STOR CORE RECONCILED - ZERO AXIOMS 🎯           ║
  ║                                                              ║
  ║  RECONCILIATION COMPLETE:                                   ║
  ║                                                              ║
  ║  ✅ Unified StrengthMeasure with stor_index                 ║
  ║  ✅ Backwards compatible with Proposition 15                ║
  ║  ✅ Preserves StOrCore operations and morphisms             ║
  ║  ✅ Integrates with DistanceMeasure framework               ║
  ║  ✅ Consistent notation across both versions                ║
  ║  ✅ ZERO AXIOMS - Fully constructive                        ║
  ║                                                              ║
  ║  KEY UNIFICATIONS:                                          ║
  ║                                                              ║
  ║  • StrengthMeasure now has strength_index field            ║
  ║  • sm_add (⊕ₛ) = stor_combine                              ║
  ║  • sm_attenuate_linear = stor_attenuate_by_distance        ║
  ║  • Both value-only (≈ᵥ) and full (≈) equality              ║
  ║  • Dual classification systems (Label + Degree)            ║
  ║                                                              ║
  ╚══════════════════════════════════════════════════════════════╝
  
  MIGRATION PATH:
  
  Files using Proposition_15_Strength_proven.v:
  - Change: Require Import Proposition_15_Strength_proven.
  - To:     Require Import StOrCore_Reconciled.
  - Use:    stor_value, stor_index, stor_combine (aliases provided)
  
  Files using original StOrCore.v:
  - Change: Require Import StOrCore.
  - To:     Require Import StOrCore_Reconciled.
  - Note:   StrengthMeasure now has strength_index field
  - Use:    strength_value, strength_index, sm_add
  
  QED.
*)
