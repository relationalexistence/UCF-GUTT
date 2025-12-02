(*
  UCF/GUTT Research & Evaluation License v1.1
  © 2023–2025 Michael Fillippini. All Rights Reserved.

  Proposition_13_PointOfRelation_proven.v
  =======================================
  
  PROPOSITION 13: The "Point of Relation" (POR₀, POR₁, ...) marks the moment 
  or context in which an entity, through its Sensory Mechanism (SM), 
  successfully perceives a relational change within its sphere of influence 
  and resonant frequency range.
  
  Definition: Within the Relational System (RS), the "Point of Relation" (POR) 
  is not a fixed point in space or time, but dynamically determined by:
  
  1. Entity's Sensory Mechanism: Resonant frequency tuning and sensitivity to 
     relational changes across different distances.
  2. Properties of the Relational Change: The frequency spectrum and inherent 
     strength of the relational change influence whether it registers above 
     the entity's perception threshold.
  3. Propagation Delays: Due to delays introduced by Strength of Relation, 
     Distance of Relation, and intervening entities, there's a lag between 
     the relational change occurring and being detected.
  
  STATUS: FULLY PROVEN - MINIMAL AXIOMS
  
  Building on:
  - Proposition_10_Direction_proven.v (Direction of relation)
  - Proposition_11_Origin_proven.v (Origin of relations)
  - Proposition_12_SensoryMechanism_proven.v (Sensory Mechanism)
  - Proposition_14_TimeOfRelation_proven.v (Temporal aspects)
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope R_scope.

(* ============================================================ *)
(* Part A: Basic Types                                          *)
(* ============================================================ *)

Definition EntityId : Type := nat.
Definition Frequency : Type := R.
Definition Distance : Type := R.
Definition Strength : Type := R.  (* Relation strength: [0, 1] *)
Definition Time : Type := R.      (* Time as real number *)

(* ============================================================ *)
(* Part B: Indexed Structures (from Prop 12)                    *)
(* ============================================================ *)

(* Indexed Sensory Mechanisms *)
Inductive SensoryMechanism : Type :=
| SM (id : nat) : SensoryMechanism.

(* Indexed Points of Relation *)
Inductive PointOfRelation : Type :=
| POR (id : nat) : PointOfRelation.

(* Equality decidability *)
Definition SM_eq_dec : forall (sm1 sm2 : SensoryMechanism), {sm1 = sm2} + {sm1 <> sm2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. rewrite e. reflexivity.
  - right. intro H. inversion H. contradiction.
Defined.

Definition POR_eq_dec : forall (p1 p2 : PointOfRelation), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. rewrite e. reflexivity.
  - right. intro H. inversion H. contradiction.
Defined.

(* ============================================================ *)
(* Part C: Frequency Range (from Prop 12)                       *)
(* ============================================================ *)

Record FrequencyRange : Type := {
  f_min : Frequency;
  f_max : Frequency;
  f_valid : f_min <= f_max
}.

Definition in_frequency_range (fr : FrequencyRange) (f : Frequency) : Prop :=
  f_min fr <= f <= f_max fr.

(* ============================================================ *)
(* Part D: Sensory Mechanism Configuration                      *)
(* ============================================================ *)

Record SM_Config : Type := {
  sm : SensoryMechanism;
  por : PointOfRelation;           (* Each SM corresponds to a POR *)
  resonant_range : FrequencyRange;  (* Frequency sensitivity *)
  sphere_radius : Distance;         (* Spatial extent *)
  perception_threshold : Strength;  (* Minimum strength to perceive *)
  sphere_positive : 0 < sphere_radius;
  threshold_valid : 0 <= perception_threshold <= 1
}.

(* ============================================================ *)
(* Part E: Relational Change Event                              *)
(* ============================================================ *)

(*
  A relational change is an event that can be perceived.
  It has:
  - Source and target PORs
  - Frequency spectrum
  - Inherent strength
  - Distance from perceiver
  - Time of occurrence
*)

Record RelationalChange : Type := {
  rc_source : PointOfRelation;
  rc_target : PointOfRelation;
  rc_frequency : Frequency;
  rc_strength : Strength;
  rc_distance : Distance;
  rc_time_emitted : Time;
  rc_strength_valid : 0 <= rc_strength <= 1;
  rc_distance_nonneg : 0 <= rc_distance
}.

(* ============================================================ *)
(* Part F: Propagation Delay Model                              *)
(* ============================================================ *)

(*
  CORE INSIGHT: Relations don't propagate instantaneously.
  Delay depends on:
  1. Distance of relation
  2. Strength of relation (stronger = faster)
  3. Intervening entities (add friction)
*)

(* Base propagation speed (normalized to 1) *)
Definition base_speed : R := 1.

(* Speed factor based on strength: stronger relations propagate faster *)
(* Range: [0.5, 1.5] based on strength [0, 1] *)
Definition strength_speed_factor (s : Strength) : R :=
  0.5 + s.  (* At s=0: 0.5x speed, at s=1: 1.5x speed *)

(* Friction factor from intervening entities *)
(* More entities = slower propagation *)
Definition friction_factor (n_intervening : nat) : R :=
  1 / (1 + INR n_intervening).

(* Combined propagation speed *)
Definition effective_speed (s : Strength) (n_intervening : nat) : R :=
  base_speed * strength_speed_factor s * friction_factor n_intervening.

(* Propagation delay = distance / speed *)
Definition propagation_delay (rc : RelationalChange) (n_intervening : nat) : Time :=
  rc_distance rc / effective_speed (rc_strength rc) n_intervening.

(* Time of arrival at perceiver *)
Definition arrival_time (rc : RelationalChange) (n_intervening : nat) : Time :=
  rc_time_emitted rc + propagation_delay rc n_intervening.

(* ============================================================ *)
(* Part G: Perception Conditions                                *)
(* ============================================================ *)

(*
  For an entity to perceive a relational change at a Point of Relation,
  ALL of the following must hold:
  1. Frequency match: Change frequency within entity's resonant range
  2. Spatial reach: Change distance within entity's sphere of influence
  3. Strength threshold: Change strength above perception threshold
*)

Definition frequency_matches (cfg : SM_Config) (rc : RelationalChange) : Prop :=
  in_frequency_range (resonant_range cfg) (rc_frequency rc).

Definition within_sphere (cfg : SM_Config) (rc : RelationalChange) : Prop :=
  rc_distance rc <= sphere_radius cfg.

Definition above_threshold (cfg : SM_Config) (rc : RelationalChange) : Prop :=
  rc_strength rc >= perception_threshold cfg.

(* Combined perception predicate *)
Definition can_perceive (cfg : SM_Config) (rc : RelationalChange) : Prop :=
  frequency_matches cfg rc /\
  within_sphere cfg rc /\
  above_threshold cfg rc.

(* ============================================================ *)
(* Part H: Point of Relation Definition                         *)
(* ============================================================ *)

(*
  CORE DEFINITION: The Point of Relation Event
  
  This is the moment/context where successful perception occurs.
  It captures:
  - Which entity perceives (via SM)
  - What relational change is perceived
  - When perception occurs (accounting for delay)
  - The context (propagation parameters)
*)

Record POR_Event : Type := {
  perceiver : SM_Config;
  change : RelationalChange;
  n_intervening_entities : nat;
  (* The POR is valid if perception conditions are met *)
  perception_valid : can_perceive perceiver change
}.

(* The time at which the POR occurs *)
Definition POR_time (event : POR_Event) : Time :=
  arrival_time (change event) (n_intervening_entities event).

(* The location (POR) where perception happens *)
Definition POR_location (event : POR_Event) : PointOfRelation :=
  por (perceiver event).

(* ============================================================ *)
(* Part I: Core Theorems                                        *)
(* ============================================================ *)

(* THEOREM 1: POR is dynamically determined by multiple factors *)
Theorem POR_dynamically_determined :
  forall (event : POR_Event),
    (* POR time depends on: *)
    POR_time event = 
      rc_time_emitted (change event) + 
      propagation_delay (change event) (n_intervening_entities event).
Proof.
  intros event.
  unfold POR_time, arrival_time.
  reflexivity.
Qed.

(* Helper: 0 < 1 + INR n *)
Lemma one_plus_INR_pos : forall n : nat, 0 < 1 + INR n.
Proof.
  intros n.
  assert (H: 0 <= INR n) by apply pos_INR.
  lra.
Qed.

(* THEOREM 2: Propagation delay is always non-negative *)
Theorem propagation_delay_nonneg :
  forall (rc : RelationalChange) (n : nat),
    0 <= rc_strength rc <= 1 ->
    0 <= rc_distance rc ->
    0 <= propagation_delay rc n.
Proof.
  intros rc n Hstr Hdist.
  unfold propagation_delay, effective_speed.
  unfold strength_speed_factor, friction_factor, base_speed.
  apply Rmult_le_pos.
  - exact Hdist.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat.
      * lra.
      * destruct Hstr as [Hlo Hhi]. lra.
    + apply Rmult_lt_0_compat.
      * lra.
      * apply Rinv_0_lt_compat.
        apply one_plus_INR_pos.
Qed.

(* THEOREM 3: Arrival time is always after emission time *)
Theorem arrival_after_emission :
  forall (rc : RelationalChange) (n : nat),
    0 <= rc_strength rc <= 1 ->
    0 <= rc_distance rc ->
    rc_time_emitted rc <= arrival_time rc n.
Proof.
  intros rc n Hstr Hdist.
  unfold arrival_time.
  assert (H: 0 <= propagation_delay rc n).
  { apply propagation_delay_nonneg; assumption. }
  lra.
Qed.

(* THEOREM 4: Greater distance means greater delay *)
Theorem distance_increases_delay :
  forall (rc1 rc2 : RelationalChange) (n : nat),
    rc_strength rc1 = rc_strength rc2 ->
    0 <= rc_strength rc1 <= 1 ->
    0 <= rc_distance rc1 ->
    0 <= rc_distance rc2 ->
    rc_distance rc1 <= rc_distance rc2 ->
    propagation_delay rc1 n <= propagation_delay rc2 n.
Proof.
  intros rc1 rc2 n Hstr_eq Hstr Hd1 Hd2 Hdist_le.
  unfold propagation_delay.
  rewrite Hstr_eq.
  apply Rmult_le_compat_r.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    unfold effective_speed, strength_speed_factor, friction_factor, base_speed.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat.
      * lra.
      * destruct Hstr as [Hlo Hhi]. lra.
    + apply Rmult_lt_0_compat.
      * lra.
      * apply Rinv_0_lt_compat.
        apply one_plus_INR_pos.
  - exact Hdist_le.
Qed.

(* THEOREM 5: Stronger relations propagate faster (shorter delay) *)
(* This is a structural theorem - higher strength gives higher speed factor *)
Theorem stronger_means_faster_speed :
  forall (s1 s2 : Strength) (n : nat),
    s1 < s2 ->
    strength_speed_factor s1 < strength_speed_factor s2.
Proof.
  intros s1 s2 n Hlt.
  unfold strength_speed_factor.
  lra.
Qed.

(* Corollary: Higher speed means lower delay for same distance *)
Theorem higher_speed_lower_delay :
  forall (d : Distance) (speed1 speed2 : R),
    0 < d ->
    0 < speed1 ->
    0 < speed2 ->
    speed1 < speed2 ->
    d / speed2 < d / speed1.
Proof.
  intros d speed1 speed2 Hd Hs1 Hs2 Hlt.
  apply Rmult_lt_compat_l.
  - exact Hd.
  - apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; assumption.
    + exact Hlt.
Qed.

(* Helper lemma: effective speed is positive *)
Lemma effective_speed_pos :
  forall (s : Strength) (n : nat),
    0 <= s <= 1 ->
    0 < effective_speed s n.
Proof.
  intros s n [Hlo Hhi].
  unfold effective_speed, strength_speed_factor, friction_factor, base_speed.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + lra.
    + lra.
  - apply Rmult_lt_0_compat.
    + lra.
    + apply Rinv_0_lt_compat.
      apply one_plus_INR_pos.
Qed.

(* Helper: More intervening entities means slower speed *)
Lemma more_entities_slower :
  forall (s : Strength) (n1 n2 : nat),
    0 <= s <= 1 ->
    (n1 < n2)%nat ->
    effective_speed s n2 < effective_speed s n1.
Proof.
  intros s n1 n2 Hstr Hn.
  unfold effective_speed, strength_speed_factor, friction_factor, base_speed.
  destruct Hstr as [Hlo Hhi].
  apply Rmult_lt_compat_l.
  - apply Rmult_lt_0_compat; lra.
  - apply Rmult_lt_compat_l.
    + lra.
    + apply Rinv_lt_contravar.
      * apply Rmult_lt_0_compat; apply one_plus_INR_pos.
      * apply Rplus_lt_compat_l.
        apply lt_INR.
        exact Hn.
Qed.

(* THEOREM 6: More intervening entities means more delay *)
Theorem more_entities_more_delay :
  forall (rc : RelationalChange) (n1 n2 : nat),
    0 <= rc_strength rc <= 1 ->
    0 < rc_distance rc ->
    (n1 < n2)%nat ->
    propagation_delay rc n1 < propagation_delay rc n2.
Proof.
  intros rc n1 n2 Hstr Hdist Hn.
  unfold propagation_delay.
  apply Rmult_lt_compat_l.
  - exact Hdist.
  - apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat.
      * apply effective_speed_pos. exact Hstr.
      * apply effective_speed_pos. exact Hstr.
    + apply more_entities_slower.
      * exact Hstr.
      * exact Hn.
Qed.

(* ============================================================ *)
(* Part J: Perception Success Theorems                          *)
(* ============================================================ *)

(* THEOREM 7: Perception requires all three conditions *)
Theorem perception_requires_all :
  forall (cfg : SM_Config) (rc : RelationalChange),
    can_perceive cfg rc <->
    (frequency_matches cfg rc /\ within_sphere cfg rc /\ above_threshold cfg rc).
Proof.
  intros cfg rc.
  unfold can_perceive.
  reflexivity.
Qed.

(* THEOREM 8: Failure outside sphere *)
Theorem no_perception_outside_sphere :
  forall (cfg : SM_Config) (rc : RelationalChange),
    sphere_radius cfg < rc_distance rc ->
    ~ within_sphere cfg rc.
Proof.
  intros cfg rc Hout.
  unfold within_sphere.
  lra.
Qed.

(* THEOREM 9: Failure below threshold *)
Theorem no_perception_below_threshold :
  forall (cfg : SM_Config) (rc : RelationalChange),
    rc_strength rc < perception_threshold cfg ->
    ~ above_threshold cfg rc.
Proof.
  intros cfg rc Hbelow.
  unfold above_threshold.
  lra.
Qed.

(* THEOREM 10: Failure outside frequency range *)
Theorem no_perception_wrong_frequency :
  forall (cfg : SM_Config) (rc : RelationalChange),
    rc_frequency rc < f_min (resonant_range cfg) \/
    rc_frequency rc > f_max (resonant_range cfg) ->
    ~ frequency_matches cfg rc.
Proof.
  intros cfg rc Hout.
  unfold frequency_matches, in_frequency_range.
  destruct Hout as [Hlow | Hhigh]; lra.
Qed.

(* ============================================================ *)
(* Part K: POR as Dynamic Context                               *)
(* ============================================================ *)

(*
  THEOREM 11: Different propagation contexts yield different arrival times.
  This demonstrates that POR is context-dependent.
*)

(* First, we show that different n values give different speeds (when valid) *)
Lemma different_n_different_speed :
  forall (s : Strength) (n1 n2 : nat),
    0 <= s <= 1 ->
    n1 <> n2 ->
    effective_speed s n1 <> effective_speed s n2.
Proof.
  intros s n1 n2 Hstr Hneq.
  unfold effective_speed, friction_factor.
  intro Heq.
  destruct Hstr as [Hlo Hhi].
  assert (Hinv_eq: / (1 + INR n1) = / (1 + INR n2)).
  { unfold strength_speed_factor, base_speed in Heq.
    assert (Hpos: 0 < 1 * (0.5 + s)) by lra.
    apply Rmult_eq_reg_l in Heq.
    - apply Rmult_eq_reg_l in Heq.
      + exact Heq.
      + lra.
    - lra. }
  apply Rinv_eq_reg in Hinv_eq.
  apply Rplus_eq_reg_l in Hinv_eq.
  apply INR_eq in Hinv_eq.
  contradiction.
Qed.

(* Main theorem: Different contexts give different POR times (when distance > 0) *)
Theorem POR_context_dependent :
  forall (rc : RelationalChange) (n1 n2 : nat),
    0 <= rc_strength rc <= 1 ->
    0 < rc_distance rc ->
    n1 <> n2 ->
    arrival_time rc n1 <> arrival_time rc n2.
Proof.
  intros rc n1 n2 Hstr Hdist Hneq.
  unfold arrival_time, propagation_delay.
  intro Heq.
  assert (Hdiv_eq: rc_distance rc / effective_speed (rc_strength rc) n1 =
                   rc_distance rc / effective_speed (rc_strength rc) n2).
  { lra. }
  unfold Rdiv in Hdiv_eq.
  apply Rmult_eq_reg_l in Hdiv_eq.
  - apply Rinv_eq_reg in Hdiv_eq.
    apply different_n_different_speed in Hdiv_eq.
    + exact Hdiv_eq.
    + exact Hstr.
    + exact Hneq.
  - lra.
Qed.

(* Corollary: Same relational change can create different POR events *)
Corollary POR_perceiver_dependent :
  forall (rc : RelationalChange) 
         (cfg1 cfg2 : SM_Config) 
         (n1 n2 : nat)
         (H1 : can_perceive cfg1 rc)
         (H2 : can_perceive cfg2 rc),
    0 < rc_distance rc ->
    n1 <> n2 ->
    let event1 := {| perceiver := cfg1; change := rc; 
                     n_intervening_entities := n1; perception_valid := H1 |} in
    let event2 := {| perceiver := cfg2; change := rc; 
                     n_intervening_entities := n2; perception_valid := H2 |} in
    POR_time event1 <> POR_time event2.
Proof.
  intros rc cfg1 cfg2 n1 n2 H1 H2 Hdist Hneq.
  simpl.
  apply POR_context_dependent.
  - exact (rc_strength_valid rc).
  - exact Hdist.
  - exact Hneq.
Qed.

(* ============================================================ *)
(* Part L: Main Proposition 13 Theorem                          *)
(* ============================================================ *)

(*
  PROPOSITION 13: Complete Characterization of Point of Relation
  
  The POR marks the moment where successful perception occurs,
  determined by the interplay of:
  1. Sensory Mechanism (frequency range, sphere, threshold)
  2. Relational Change properties (frequency, strength, distance)
  3. Propagation context (intervening entities, delays)
*)

Theorem proposition_13_point_of_relation :
  (* Part 1: POR exists iff perception conditions are met *)
  (forall (cfg : SM_Config) (rc : RelationalChange),
     can_perceive cfg rc <->
     exists event : POR_Event,
       perceiver event = cfg /\ change event = rc) /\
  
  (* Part 2: POR time is dynamically determined by propagation *)
  (forall (event : POR_Event),
     POR_time event = rc_time_emitted (change event) + 
                      propagation_delay (change event) (n_intervening_entities event)) /\
  
  (* Part 3: POR occurs after emission (causality) *)
  (forall (event : POR_Event),
     rc_time_emitted (change event) <= POR_time event) /\
  
  (* Part 4: Distance increases delay *)
  (forall (rc1 rc2 : RelationalChange) (n : nat),
     rc_strength rc1 = rc_strength rc2 ->
     0 <= rc_strength rc1 <= 1 ->
     0 <= rc_distance rc1 ->
     0 <= rc_distance rc2 ->
     rc_distance rc1 <= rc_distance rc2 ->
     propagation_delay rc1 n <= propagation_delay rc2 n) /\
  
  (* Part 5: More intervening entities increase delay *)
  (forall (rc : RelationalChange) (n1 n2 : nat),
     0 <= rc_strength rc <= 1 ->
     0 < rc_distance rc ->
     (n1 < n2)%nat ->
     propagation_delay rc n1 < propagation_delay rc n2).
Proof.
  split; [| split; [| split; [| split]]].
  
  - (* Part 1: Existence *)
    intros cfg rc.
    split.
    + (* can_perceive -> exists event *)
      intro Hcan.
      exists {| perceiver := cfg; 
                change := rc; 
                n_intervening_entities := 0;
                perception_valid := Hcan |}.
      simpl. auto.
    + (* exists event -> can_perceive *)
      intros [event [Hcfg Hrc]].
      rewrite <- Hcfg, <- Hrc.
      exact (perception_valid event).
  
  - (* Part 2: Dynamic determination *)
    exact POR_dynamically_determined.
  
  - (* Part 3: Causality *)
    intros event.
    apply arrival_after_emission.
    + exact (rc_strength_valid (change event)).
    + exact (rc_distance_nonneg (change event)).
  
  - (* Part 4: Distance increases delay *)
    exact distance_increases_delay.
  
  - (* Part 5: Intervening entities increase delay *)
    exact more_entities_more_delay.
Qed.

(* ============================================================ *)
(* Part M: Additional Properties                                *)
(* ============================================================ *)

(* Every POR has a unique location (the perceiver's POR) *)
Theorem POR_has_unique_location :
  forall (event : POR_Event),
    exists! p : PointOfRelation, p = POR_location event.
Proof.
  intros event.
  exists (POR_location event).
  split.
  - reflexivity.
  - intros p' Hp'. symmetry. exact Hp'.
Qed.

(* POR time is well-defined (single value) *)
Theorem POR_time_well_defined :
  forall (event : POR_Event),
    exists! t : Time, t = POR_time event.
Proof.
  intros event.
  exists (POR_time event).
  split.
  - reflexivity.
  - intros t' Ht'. symmetry. exact Ht'.
Qed.

(* Perception is decidable given all parameters *)
Definition perception_decidable (cfg : SM_Config) (rc : RelationalChange) : 
  {can_perceive cfg rc} + {~ can_perceive cfg rc}.
Proof.
  unfold can_perceive, frequency_matches, within_sphere, above_threshold.
  unfold in_frequency_range.
  destruct (Rle_dec (f_min (resonant_range cfg)) (rc_frequency rc)) as [Hf1|Hf1].
  - destruct (Rle_dec (rc_frequency rc) (f_max (resonant_range cfg))) as [Hf2|Hf2].
    + destruct (Rle_dec (rc_distance rc) (sphere_radius cfg)) as [Hd|Hd].
      * destruct (Rge_dec (rc_strength rc) (perception_threshold cfg)) as [Hs|Hs].
        -- left. repeat split; assumption.
        -- right. intros [_ [_ Habs]]. lra.
      * right. intros [_ [Habs _]]. lra.
    + right. intros [[_ Habs] _]. lra.
  - right. intros [[Habs _] _]. lra.
Defined.

(* ============================================================ *)
(* Part N: Summary and Exports                                  *)
(* ============================================================ *)

(*
  PROPOSITION 13 SUMMARY:
  
  The Point of Relation (POR) is the moment/context where an entity
  successfully perceives a relational change. Key properties proven:
  
  1. DYNAMIC DETERMINATION:
     - POR is NOT fixed in space/time
     - Depends on perceiver's SM configuration
     - Depends on relational change properties
     - Depends on propagation context
  
  2. SENSORY MECHANISM ROLE:
     - Frequency range filters which changes can be perceived
     - Sphere of influence limits spatial extent
     - Perception threshold filters weak signals
  
  3. PROPAGATION DELAYS:
     - Distance increases delay
     - Stronger relations propagate faster
     - Intervening entities add friction/delay
  
  4. CAUSALITY:
     - POR always occurs AFTER emission
     - Delay is always non-negative
  
  This completes the bridge between:
  - Prop 11 (Origin): Where relations start
  - Prop 12 (Sensory Mechanism): How entities perceive
  - Prop 14 (Time of Relation): When relations occur
  - Prop 13 (Point of Relation): The perception event itself
*)

Definition UCF_GUTT_PointOfRelation := PointOfRelation.
Definition UCF_GUTT_POR_Event := POR_Event.
Definition UCF_GUTT_Proposition13 := proposition_13_point_of_relation.

(* Verification checks *)
Check proposition_13_point_of_relation.
Check POR_dynamically_determined.
Check propagation_delay_nonneg.
Check arrival_after_emission.
Check distance_increases_delay.
Check stronger_means_faster_speed.
Check more_entities_more_delay.
Check perception_requires_all.
Check POR_perceiver_dependent.
Check perception_decidable.

(* End of Proposition 13 *)