(**
  DistanceMeasure.v
  =================
  Operations on distance measures with morphism proofs (ZERO axioms).
  
  Contents:
  - DistanceMeasure record with nonnegativity witness
  - Algebraic operations: ⊕ (addition), • (scalar multiplication)
  - Proper instances proving operations respect equality
  - Monoid structure for ⊕ with identity element
  - Compatibility with MetricCore pseudometric framework
  
  Dependencies: Reals, Lra, Morphisms, RelationClasses, MetricCore
  Part of: UCF/GUTT Proposition 18 - Distance of Relation
*
    © 2023–2025 Michael Fillippini. All Rights Reserved.)

From Coq Require Import Reals.
From Coq Require Import micromega.Lra.
From Coq Require Import Morphisms RelationClasses.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import MetricCore.

Set Implicit Arguments.
Local Open Scope R_scope.

(* ================================================================ *)
(* Distance Measure - Record with Nonnegativity Witness            *)
(* ================================================================ *)

(**
  A DistanceMeasure is a real value with a proof it's non-negative.
  This is the computational representation of distances.
*)

Record DistanceMeasure := {
  dist_value : R;
  dist_nonneg : 0 <= dist_value
}.

(* ================================================================ *)
(* Equality and Setoid Structure                                    *)
(* ================================================================ *)

(**
  Two distances are equal if their values are equal.
  The nonnegativity proofs are in Prop, so proof-irrelevant.
*)

Definition dm_eq (d1 d2 : DistanceMeasure) : Prop :=
  dist_value d1 = dist_value d2.

Notation "d1 ≡ d2" := (dm_eq d1 d2) (at level 70).

Lemma dm_eq_refl : forall d, d ≡ d.
Proof. intros. unfold dm_eq. reflexivity. Qed.

Lemma dm_eq_sym : forall d1 d2, d1 ≡ d2 -> d2 ≡ d1.
Proof. intros. unfold dm_eq in *. symmetry. assumption. Qed.

Lemma dm_eq_trans : forall d1 d2 d3, d1 ≡ d2 -> d2 ≡ d3 -> d1 ≡ d3.
Proof. intros. unfold dm_eq in *. rewrite H. assumption. Qed.

#[export] Instance dm_equivalence : Equivalence dm_eq.
Proof.
  split.
  - exact dm_eq_refl.
  - exact dm_eq_sym.
  - exact dm_eq_trans.
Qed.

(* ================================================================ *)
(* Zero Distance (Identity Element)                                 *)
(* ================================================================ *)

Definition dm_zero : DistanceMeasure.
Proof.
  refine {| dist_value := 0 |}.
  lra.
Defined.

Notation "𝟘" := dm_zero.

(* ================================================================ *)
(* Operation ⊕: Distance Addition                                   *)
(* ================================================================ *)

(**
  Adding two distances: combines separation measures.
  Result is non-negative since both inputs are non-negative.
*)

Definition dm_add (d1 d2 : DistanceMeasure) : DistanceMeasure.
Proof.
  refine {| dist_value := dist_value d1 + dist_value d2 |}.
  pose proof (dist_nonneg d1).
  pose proof (dist_nonneg d2).
  lra.
Defined.

Notation "d1 ⊕ d2" := (dm_add d1 d2) (at level 50, left associativity).

(* ---------------------------------------------------------------- *)
(* Proper Instance for ⊕                                            *)
(* ---------------------------------------------------------------- *)

#[export] Instance dm_add_proper : Proper (dm_eq ==> dm_eq ==> dm_eq) dm_add.
Proof.
  intros d1 d1' Hd1 d2 d2' Hd2.
  unfold dm_eq in *.
  simpl. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* Algebraic Properties of ⊕                                        *)
(* ---------------------------------------------------------------- *)

Lemma dm_add_assoc : forall d1 d2 d3, (d1 ⊕ d2) ⊕ d3 ≡ d1 ⊕ (d2 ⊕ d3).
Proof.
  intros. unfold dm_eq. simpl. lra.
Qed.

Lemma dm_add_comm : forall d1 d2, d1 ⊕ d2 ≡ d2 ⊕ d1.
Proof.
  intros. unfold dm_eq. simpl. lra.
Qed.

Lemma dm_add_zero_l : forall d, 𝟘 ⊕ d ≡ d.
Proof.
  intros. unfold dm_eq. simpl. lra.
Qed.

Lemma dm_add_zero_r : forall d, d ⊕ 𝟘 ≡ d.
Proof.
  intros. unfold dm_eq. simpl. lra.
Qed.

(* ================================================================ *)
(* Operation •: Scalar Multiplication                               *)
(* ================================================================ *)

(* ================================================================ *)
(* Operation •: Scalar Multiplication                               *)
(* ================================================================ *)

(**
  Scaling a distance by a non-negative scalar.
  Useful for weighted combinations and normalization.
*)

Definition dm_scale (α : R) (Hα : 0 <= α) (d : DistanceMeasure) : DistanceMeasure.
Proof.
  refine {| dist_value := α * dist_value d |}.
  apply Rmult_le_pos; [exact Hα | apply dist_nonneg].
Defined.

(* Make the nonnegativity proof implicit *)
Arguments dm_scale α {Hα} d.

(* -------------------------------------------------------------- *)
(* Proper Instance for •                                          *)
(* -------------------------------------------------------------- *)

#[export] Instance dm_scale_proper α (Hα : 0 <= α) : 
  Proper (dm_eq ==> dm_eq) (@dm_scale α Hα).
Proof.
  intros d1 d2 Hd.
  unfold dm_eq in *. simpl. 
  rewrite Hd. reflexivity.
Qed.

(* -------------------------------------------------------------- *)
(* Interaction with ⊕                                             *)
(* -------------------------------------------------------------- *)

Lemma dm_scale_add α (Hα : 0 <= α) : forall d1 d2, 
  @dm_scale α Hα (d1 ⊕ d2) ≡ @dm_scale α Hα d1 ⊕ @dm_scale α Hα d2.
Proof.
  intros. unfold dm_eq. simpl. lra.
Qed.

Lemma dm_scale_zero α (Hα : 0 <= α) : 
  @dm_scale α Hα 𝟘 ≡ 𝟘.
Proof.
  unfold dm_eq. simpl. lra.
Qed.

(* ================================================================ *)
(* Connection to MetricCore: Lift d to DistanceMeasure             *)
(* ================================================================ *)

(**
  Given a pseudometric space, we can lift the distance function
  to produce DistanceMeasure values with their nonnegativity proofs.
*)

Section LiftMetric.
  Context {U : Type} `{PseudoMetricSpace U}.

  Definition lift_d (x y : U) : DistanceMeasure.
  Proof.
    refine {| dist_value := d x y |}.
    apply d_nonneg.
  Defined.

  (* Lifted distance respects metric properties *)
  Lemma lift_d_sym : forall x y, lift_d x y ≡ lift_d y x.
  Proof.
    intros. unfold dm_eq, lift_d. simpl.
    apply d_sym.
  Qed.

  Lemma lift_d_triangle : forall x y z,
    lift_d x z ⊕ 𝟘 ≡ 𝟘 ⊕ lift_d x z ->
    dist_value (lift_d x z) <= dist_value (lift_d x y) + dist_value (lift_d y z).
  Proof.
    intros. unfold lift_d. simpl.
    apply d_triangle.
  Qed.

  (* More direct triangle inequality *)
  Lemma lift_d_triangle_direct : forall x y z,
    dist_value (lift_d x z) <= dist_value (lift_d x y) + dist_value (lift_d y z).
  Proof.
    intros. unfold lift_d. simpl.
    apply d_triangle.
  Qed.

End LiftMetric.

(* ================================================================ *)
(* Maximum Distance (Join Operation)                                *)
(* ================================================================ *)

(**
  Taking the maximum of two distances.
  Useful for combining parallel distance constraints.
*)

Definition dm_max (d1 d2 : DistanceMeasure) : DistanceMeasure.
Proof.
  refine {| dist_value := Rmax (dist_value d1) (dist_value d2) |}.
  apply Rmax_case_strong; intros; apply dist_nonneg.
Defined.

Notation "d1 ⊔ d2" := (dm_max d1 d2) (at level 50, left associativity).

#[export] Instance dm_max_proper : Proper (dm_eq ==> dm_eq ==> dm_eq) dm_max.
Proof.
  intros d1 d1' Hd1 d2 d2' Hd2.
  unfold dm_eq in *. simpl.
  rewrite Hd1, Hd2. reflexivity.
Qed.

Lemma dm_max_comm : forall d1 d2, d1 ⊔ d2 ≡ d2 ⊔ d1.
Proof.
  intros. unfold dm_eq. simpl.
  apply Rmax_comm.
Qed.

Lemma dm_max_assoc : forall d1 d2 d3, (d1 ⊔ d2) ⊔ d3 ≡ d1 ⊔ (d2 ⊔ d3).
Proof.
  intros. unfold dm_eq. simpl.
  unfold Rmax.
  destruct (Rle_dec (dist_value d1) (dist_value d2));
  destruct (Rle_dec (dist_value d2) (dist_value d3));
  destruct (Rle_dec (dist_value d1) (dist_value d3));
  destruct (Rle_dec (dist_value d2) (dist_value d3));
  destruct (Rle_dec (dist_value d1) (dist_value d2));
  try lra; try reflexivity.
Qed.

(* ================================================================ *)
(* Minimum Distance (Meet Operation)                                *)
(* ================================================================ *)

Definition dm_min (d1 d2 : DistanceMeasure) : DistanceMeasure.
Proof.
  refine {| dist_value := Rmin (dist_value d1) (dist_value d2) |}.
  apply Rmin_case_strong; intros; apply dist_nonneg.
Defined.

Notation "d1 ⊓ d2" := (dm_min d1 d2) (at level 50, left associativity).

#[export] Instance dm_min_proper : Proper (dm_eq ==> dm_eq ==> dm_eq) dm_min.
Proof.
  intros d1 d1' Hd1 d2 d2' Hd2.
  unfold dm_eq in *. simpl.
  rewrite Hd1, Hd2. reflexivity.
Qed.

(* ================================================================ *)
(* Distance from Discrete Metric                                    *)
(* ================================================================ *)

(**
  Given a type with decidable equality, construct DistanceMeasure
  values from the discrete metric.
*)

Section DiscreteDistance.
  Context {U : Type} {E : EqDec U}.

  Definition dm_discrete (x y : U) : DistanceMeasure.
  Proof.
    refine {| dist_value := if eq_dec x y then 0 else 1 |}.
    destruct (eq_dec x y); lra.
  Defined.

  Lemma dm_discrete_zero : forall x, dm_discrete x x ≡ 𝟘.
  Proof.
    intros. unfold dm_eq, dm_discrete, dm_zero. simpl.
    destruct (eq_dec x x); [reflexivity | congruence].
  Qed.

  Lemma dm_discrete_pos : forall x y, x <> y ->
    dist_value (dm_discrete x y) = 1.
  Proof.
    intros. unfold dm_discrete. simpl.
    destruct (eq_dec x y); [congruence | reflexivity].
  Qed.

End DiscreteDistance.

(* ================================================================ *)
(* Weighted Sum Constructor                                         *)
(* ================================================================ *)

(**
  Construct weighted combinations of distances.
  Foundation for multi-attribute distance measures.
*)

Section WeightedSum.
  Variable n : nat.
  Variable weights : list R.
  Variable distances : list DistanceMeasure.
  
  Hypothesis weights_nonneg : forall w, In w weights -> 0 <= w.
  Hypothesis same_length : length weights = length distances.

  Fixpoint weighted_sum_aux (ws : list R) (ds : list DistanceMeasure) : R :=
    match ws, ds with
    | [], [] => 0
    | w::ws', d::ds' => w * dist_value d + weighted_sum_aux ws' ds'
    | _, _ => 0  (* impossible given same_length *)
    end.

  Definition weighted_sum : DistanceMeasure.
  Proof.
    refine {| dist_value := weighted_sum_aux weights distances |}.
    (* Proof that weighted sum is non-negative *)
    revert distances same_length.
    induction weights as [|w ws IH]; intros [|d ds] Hlen.
    - simpl. lra.
    - simpl in Hlen. discriminate.
    - simpl in Hlen. discriminate.
    - simpl. 
      apply Rplus_le_le_0_compat.
      + apply Rmult_le_pos.
        * apply weights_nonneg. simpl. left. reflexivity.
        * apply dist_nonneg.
      + apply (IH (fun w' Hin => weights_nonneg w' (or_intror Hin)) ds).
        simpl in Hlen. injection Hlen as Hlen. exact Hlen.
  Defined.

End WeightedSum.

(* ================================================================ *)
(* Hint Database                                                    *)
(* ================================================================ *)

#[export] Hint Resolve 
  dm_eq_refl dm_eq_sym dm_eq_trans
  dm_add_assoc dm_add_comm dm_add_zero_l dm_add_zero_r
  dm_max_comm dm_max_assoc
  : distmeasure.

#[export] Hint Resolve dist_nonneg : distmeasure.
