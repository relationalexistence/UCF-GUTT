(**
  DistanceLabels.v
  ================
  Configurable classification thresholds for distance measures (ZERO axioms).
  
  Contents:
  - Label types (Close, Medium, Far, Infinite)
  - Threshold configuration with nonnegativity proofs
  - Classification functions with decidability
  - Proper instances for label equality
  - Multi-threshold hierarchical classification
  - Integration with DistanceMeasure operations
  
  Dependencies: Reals, Lra, Morphisms, DistanceMeasure
  Part of: UCF/GUTT Proposition 18 - Distance of Relation
*
    © 2023–2025 Michael Fillippini. All Rights Reserved.)

From Coq Require Import Reals.
From Coq Require Import micromega.Lra.
From Coq Require Import Morphisms RelationClasses.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import MetricCore DistanceMeasure.

Set Implicit Arguments.
Local Open Scope R_scope.

(* ================================================================ *)
(* Distance Labels - Classification Categories                      *)
(* ================================================================ *)

(**
  Labels represent qualitative distance categories.
  These can be customized per domain application.
*)

Inductive DistanceLabel :=
  | Close       : DistanceLabel
  | Medium      : DistanceLabel
  | Far         : DistanceLabel
  | VeryFar     : DistanceLabel
  | Infinite    : DistanceLabel.

(* Decidable equality for labels *)
Definition label_eq_dec : forall (l1 l2 : DistanceLabel), {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
Defined.

(* Label ordering (for threshold comparisons) *)
Definition label_le (l1 l2 : DistanceLabel) : Prop :=
  match l1, l2 with
  | Close, _ => True
  | Medium, Close => False
  | Medium, _ => True
  | Far, Close | Far, Medium => False
  | Far, _ => True
  | VeryFar, (Close | Medium | Far) => False
  | VeryFar, _ => True
  | Infinite, Infinite => True
  | Infinite, _ => False
  end.

Notation "l1 ≤ᴸ l2" := (label_le l1 l2) (at level 70).

Lemma label_le_refl : forall l, l ≤ᴸ l.
Proof.
  intros []; simpl; exact I.
Qed.

Lemma label_le_trans : forall l1 l2 l3, 
  l1 ≤ᴸ l2 -> l2 ≤ᴸ l3 -> l1 ≤ᴸ l3.
Proof.
  intros [] [] []; simpl; intros; auto; contradiction.
Qed.

(* ================================================================ *)
(* Threshold Configuration                                          *)
(* ================================================================ *)

(**
  A threshold configuration maps labels to distance thresholds.
  All thresholds must be non-negative and properly ordered.
*)

Record ThresholdConfig := {
  threshold_close : R;
  threshold_medium : R;
  threshold_far : R;
  threshold_veryfar : R;
  
  (* Nonnegativity requirements *)
  close_nonneg : 0 <= threshold_close;
  medium_nonneg : 0 <= threshold_medium;
  far_nonneg : 0 <= threshold_far;
  veryfar_nonneg : 0 <= threshold_veryfar;
  
  (* Ordering requirements *)
  close_le_medium : threshold_close <= threshold_medium;
  medium_le_far : threshold_medium <= threshold_far;
  far_le_veryfar : threshold_far <= threshold_veryfar
}.

(* Extract threshold for a given label *)
Definition get_threshold (cfg : ThresholdConfig) (l : DistanceLabel) : R :=
  match l with
  | Close => threshold_close cfg
  | Medium => threshold_medium cfg
  | Far => threshold_far cfg
  | VeryFar => threshold_veryfar cfg
  | Infinite => threshold_veryfar cfg + 1  (* Above all finite thresholds *)
  end.

Lemma get_threshold_ordered : forall cfg l1 l2,
  l1 ≤ᴸ l2 -> get_threshold cfg l1 <= get_threshold cfg l2.
Proof.
  intros cfg [] []; simpl; intros H; try contradiction; try lra;
  try (apply close_le_medium);
  try (apply medium_le_far);
  try (apply far_le_veryfar);
  try (pose proof (close_le_medium cfg); 
       pose proof (medium_le_far cfg); lra);
  try (pose proof (close_le_medium cfg);
       pose proof (medium_le_far cfg);
       pose proof (far_le_veryfar cfg); lra);
  try (pose proof (medium_le_far cfg);
       pose proof (far_le_veryfar cfg); lra);
  try (pose proof (far_le_veryfar cfg); lra).
Qed.

(* ================================================================ *)
(* Default Configuration Examples                                   *)
(* ================================================================ *)

(* Physical distances (meters) *)
Definition physical_thresholds : ThresholdConfig.
Proof.
  refine {|
    threshold_close := 1;
    threshold_medium := 10;
    threshold_far := 100;
    threshold_veryfar := 1000
  |}.
  all: lra.
Defined.

(* Abstract/normalized distances (0-1 scale) *)
Definition normalized_thresholds : ThresholdConfig.
Proof.
  refine {|
    threshold_close := 0.1;
    threshold_medium := 0.3;
    threshold_far := 0.6;
    threshold_veryfar := 0.9
  |}.
  all: lra.
Defined.

(* Information-theoretic distances (bits) *)
Definition information_thresholds : ThresholdConfig.
Proof.
  refine {|
    threshold_close := 0.5;
    threshold_medium := 2;
    threshold_far := 8;
    threshold_veryfar := 32
  |}.
  all: lra.
Defined.

(* ================================================================ *)
(* Classification Function                                          *)
(* ================================================================ *)

(**
  Classify a distance measure according to threshold configuration.
  Uses strict inequalities for clear boundaries.
*)

Definition classify (cfg : ThresholdConfig) (d : DistanceMeasure) : DistanceLabel :=
  let v := dist_value d in
  if Rle_dec v (threshold_close cfg) then Close
  else if Rle_dec v (threshold_medium cfg) then Medium
  else if Rle_dec v (threshold_far cfg) then Far
  else if Rle_dec v (threshold_veryfar cfg) then VeryFar
  else Infinite.

(* Classification is decidable *)
Lemma classify_dec : forall cfg d l,
  {classify cfg d = l} + {classify cfg d <> l}.
Proof.
  intros. apply label_eq_dec.
Qed.

(* ---------------------------------------------------------------- *)
(* Classification Respects Equivalence                             *)
(* ---------------------------------------------------------------- *)

Lemma classify_proper : forall cfg d1 d2,
  d1 ≡ d2 -> classify cfg d1 = classify cfg d2.
Proof.
  intros cfg d1 d2 Heq.
  unfold dm_eq in Heq.
  unfold classify.
  rewrite Heq.
  reflexivity.
Qed.

(* Make this a Proper instance *)
#[export] Instance classify_morphism cfg : 
  Proper (dm_eq ==> eq) (classify cfg).
Proof.
  intros d1 d2 Heq.
  apply classify_proper.
  assumption.
Qed.

(* ================================================================ *)
(* Classification Properties                                        *)
(* ================================================================ *)

Lemma classify_monotone : forall cfg d1 d2,
  dist_value d1 <= dist_value d2 ->
  classify cfg d1 ≤ᴸ classify cfg d2.
Proof.
  intros cfg d1 d2 Hle.
  unfold classify.
  destruct (Rle_dec (dist_value d1) (threshold_close cfg));
  destruct (Rle_dec (dist_value d2) (threshold_close cfg));
  destruct (Rle_dec (dist_value d1) (threshold_medium cfg));
  destruct (Rle_dec (dist_value d2) (threshold_medium cfg));
  destruct (Rle_dec (dist_value d1) (threshold_far cfg));
  destruct (Rle_dec (dist_value d2) (threshold_far cfg));
  destruct (Rle_dec (dist_value d1) (threshold_veryfar cfg));
  destruct (Rle_dec (dist_value d2) (threshold_veryfar cfg));
  simpl; auto; try lra.
Qed.

Lemma classify_zero : forall cfg,
  classify cfg 𝟘 = Close.
Proof.
  intros cfg.
  unfold classify, dm_zero. simpl.
  destruct (Rle_dec 0 (threshold_close cfg)).
  - reflexivity.
  - pose proof (close_nonneg cfg). lra.
Qed.

Lemma classify_bound : forall cfg d l,
  classify cfg d = l ->
  l <> Infinite ->
  dist_value d <= get_threshold cfg l.
Proof.
  intros cfg d l Hclass Hninf.
  unfold classify in Hclass.
  destruct l; try contradiction;
  destruct (Rle_dec (dist_value d) (threshold_close cfg));
  destruct (Rle_dec (dist_value d) (threshold_medium cfg));
  destruct (Rle_dec (dist_value d) (threshold_far cfg));
  destruct (Rle_dec (dist_value d) (threshold_veryfar cfg));
  simpl; try discriminate; auto.
Qed.

(* ================================================================ *)
(* Boolean Classification (for computation)                         *)
(* ================================================================ *)

Definition is_close (cfg : ThresholdConfig) (d : DistanceMeasure) : bool :=
  if Rle_dec (dist_value d) (threshold_close cfg) then true else false.

Definition is_within (cfg : ThresholdConfig) (l : DistanceLabel) (d : DistanceMeasure) : bool :=
  if Rle_dec (dist_value d) (get_threshold cfg l) then true else false.

Lemma is_close_correct : forall cfg d,
  is_close cfg d = true <-> classify cfg d = Close.
Proof.
  intros cfg d. split; intro H.
  - (* -> direction *)
    unfold is_close in H.
    destruct (Rle_dec (dist_value d) (threshold_close cfg)) as [Hle | Hnle]; 
      try discriminate.
    unfold classify.
    destruct (Rle_dec (dist_value d) (threshold_close cfg)) as [_ | Hnle']; 
      try contradiction.
    reflexivity.
  - (* <- direction *)
    unfold is_close.
    destruct (Rle_dec (dist_value d) (threshold_close cfg)) as [Hle | Hnle].
    + reflexivity.
    + unfold classify in H.
      destruct (Rle_dec (dist_value d) (threshold_close cfg)) as [Hle | _]; 
        try contradiction.
      (* H : Close = Close \/ ... = Close, but first case gives Close *)
      destruct (Rle_dec (dist_value d) (threshold_medium cfg));
      destruct (Rle_dec (dist_value d) (threshold_far cfg));
      destruct (Rle_dec (dist_value d) (threshold_veryfar cfg));
      discriminate H.
Qed.

(* ================================================================ *)
(* Multi-Threshold Operations                                       *)
(* ================================================================ *)

(**
  Check if a distance is within a given label's threshold.
  Useful for boundary analysis.
  For Infinite label, this is always True (no finite bound).
*)

Definition within_label (cfg : ThresholdConfig) (l : DistanceLabel) 
  (d : DistanceMeasure) : Prop :=
  match l with
  | Infinite => True
  | _ => dist_value d <= get_threshold cfg l
  end.

Lemma within_label_dec : forall cfg l d,
  {within_label cfg l d} + {~ within_label cfg l d}.
Proof.
  intros cfg [|  |  |  |] d; unfold within_label.
  - apply Rle_dec.
  - apply Rle_dec.
  - apply Rle_dec.
  - apply Rle_dec.
  - left. exact I.
Qed.

(* Relation between classification and within_label *)
Lemma classify_within : forall cfg d,
  within_label cfg (classify cfg d) d.
Proof.
  intros cfg d.
  unfold classify.
  destruct (Rle_dec (dist_value d) (threshold_close cfg)) as [Hc | Hnc].
  - (* Case: Close *) simpl. exact Hc.
  - destruct (Rle_dec (dist_value d) (threshold_medium cfg)) as [Hm | Hnm].
    + (* Case: Medium *) simpl. exact Hm.
    + destruct (Rle_dec (dist_value d) (threshold_far cfg)) as [Hf | Hnf].
      * (* Case: Far *) simpl. exact Hf.
      * destruct (Rle_dec (dist_value d) (threshold_veryfar cfg)) as [Hv | Hnv].
        -- (* Case: VeryFar *) simpl. exact Hv.
        -- (* Case: Infinite *) simpl. exact I.
Qed.

(* ================================================================ *)
(* Combined Distance Classification                                 *)
(* ================================================================ *)

(**
  Classify the combination of two distances.
  Useful for analyzing composite separation measures.
*)

Definition classify_sum (cfg : ThresholdConfig) 
  (d1 d2 : DistanceMeasure) : DistanceLabel :=
  classify cfg (d1 ⊕ d2).

(* ================================================================ *)
(* Scaled Distance Classification                                   *)
(* ================================================================ *)

(**
  Classify a scaled distance.
  Scaling factor affects which threshold is crossed.
*)

Definition classify_scaled (cfg : ThresholdConfig) (α : R) (Hα : 0 <= α)
  (d : DistanceMeasure) : DistanceLabel :=
  classify cfg (@dm_scale α Hα d).

Arguments classify_scaled cfg α {Hα} d.

Lemma classify_scaled_zero : forall (cfg : ThresholdConfig) (α : R) (Hα : 0 <= α) (d : DistanceMeasure),
  α = 0 -> @classify_scaled cfg α Hα d = Close.
Proof.
  intros cfg α Hα d Hzero.
  unfold classify_scaled.
  subst α.
  (* After substitution, we have dm_scale 0 d *)
  (* We know dm_scale 0 d has value 0 *)
  assert (Heq : dist_value (@dm_scale 0 Hα d) = 0).
  { simpl. lra. }
  unfold classify.
  rewrite Heq.
  destruct (Rle_dec 0 (threshold_close cfg)).
  - reflexivity.
  - pose proof (close_nonneg cfg). lra.
Qed.

(* ================================================================ *)
(* Hierarchical Multi-Scale Classification                          *)
(* ================================================================ *)

(**
  Multiple threshold configurations for different scales.
  Allows multi-resolution distance analysis.
*)

Record MultiScaleConfig := {
  local_config : ThresholdConfig;
  regional_config : ThresholdConfig;
  global_config : ThresholdConfig
}.

Definition classify_local (msc : MultiScaleConfig) (d : DistanceMeasure) : DistanceLabel :=
  classify (local_config msc) d.

Definition classify_regional (msc : MultiScaleConfig) (d : DistanceMeasure) : DistanceLabel :=
  classify (regional_config msc) d.

Definition classify_global (msc : MultiScaleConfig) (d : DistanceMeasure) : DistanceLabel :=
  classify (global_config msc) d.

(* Multi-scale analysis returns all three classifications *)
Record MultiScaleLabel := {
  local_label : DistanceLabel;
  regional_label : DistanceLabel;
  global_label : DistanceLabel
}.

Definition classify_multiscale (msc : MultiScaleConfig) 
  (d : DistanceMeasure) : MultiScaleLabel :=
  {|
    local_label := classify_local msc d;
    regional_label := classify_regional msc d;
    global_label := classify_global msc d
  |}.

(* ================================================================ *)
(* Integration with Lifted Metrics                                  *)
(* ================================================================ *)

Section ClassifyMetric.
  Context {U : Type} `{PseudoMetricSpace U}.
  Variable cfg : ThresholdConfig.

  Definition classify_points (x y : U) : DistanceLabel :=
    classify cfg (lift_d x y).

  Lemma classify_points_sym : forall x y,
    classify_points x y = classify_points y x.
  Proof.
    intros x y.
    unfold classify_points.
    apply classify_proper.
    apply lift_d_sym.
  Qed.

  (* Points are close if their distance is within close threshold *)
  Definition points_close (x y : U) : Prop :=
    classify_points x y = Close.

  Lemma points_close_refl : forall x,
    d x x = 0 -> points_close x x.
  Proof.
    intros x Hd.
    unfold points_close, classify_points.
    assert (lift_d x x ≡ 𝟘).
    { unfold dm_eq, lift_d, dm_zero. simpl. exact Hd. }
    rewrite H0.
    apply classify_zero.
  Qed.

End ClassifyMetric.

(* ================================================================ *)
(* Discrete Metric Classification                                   *)
(* ================================================================ *)

Section DiscreteClassify.
  Context {U : Type} {E : EqDec U}.
  Variable cfg : ThresholdConfig.

  Definition classify_discrete (x y : U) : DistanceLabel :=
    classify cfg (dm_discrete x y).

  Lemma classify_discrete_eq : forall x y,
    x = y -> classify_discrete x y = Close.
  Proof.
    intros x y Heq.
    unfold classify_discrete.
    assert (Hdm: dm_discrete x y ≡ 𝟘).
    { subst y. apply dm_discrete_zero. }
    rewrite Hdm.
    apply classify_zero.
  Qed.

  Lemma classify_discrete_neq : forall x y,
    x <> y ->
    1 <= threshold_close cfg ->
    classify_discrete x y = Close.
  Proof.
    intros x y Hneq Hthresh.
    unfold classify_discrete, classify.
    assert (Hval: dist_value (dm_discrete x y) = 1).
    { apply dm_discrete_pos. exact Hneq. }
    rewrite Hval.
    destruct (Rle_dec 1 (threshold_close cfg)); try contradiction.
    reflexivity.
  Qed.

End DiscreteClassify.

(* ================================================================ *)
(* Hint Database                                                    *)
(* ================================================================ *)

#[export] Hint Resolve 
  label_le_refl label_le_trans
  classify_zero classify_proper
  classify_points_sym
  : distlabel.

#[export] Hint Resolve 
  close_nonneg medium_nonneg far_nonneg veryfar_nonneg
  close_le_medium medium_le_far far_le_veryfar
  : distlabel.
