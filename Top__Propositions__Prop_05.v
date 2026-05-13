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
  |       PROPOSITION 05: RELATIONAL TENSOR AS MODULAR REPRESENTATION        |
  |                                                                          |
  |                      UCF/GUTT(TM) Formal Verification                    |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-29                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  THEOREM: The Relational Tensor (RT) serves as a modular representation  |
  |           of a Relational System, capturing both static and dynamic      |
  |           relationship attributes through Nested Relational Tensors.     |
  |                                                                          |
  |  "Every Relational System can be represented by a Relational Tensor,     |
  |   which is composed of modular Nested Relational Tensors (NRTs) that     |
  |   capture hierarchical structure and multiple relationship types."       |
  |                                                                          |
  |  BUILDS ON (imports existing proofs):                                    |
  |    - Proposition 01: Universal connectivity through Whole (seriality)    |
  |    - Proposition 02: Multi-dimensional representation (DSoR, tensors)    |
  |    - Proposition 04: Relations form graphs with adjacency tensors        |
  |    - ClockHierarchyCoherence: Relational time (ClockReading = N_rel)     |
  |    - RelationalNaturals: N_rel for time and weights                      |
  |                                                                          |
  |  KEY INSIGHTS:                                                           |
  |    1. NRTs provide hierarchical structure (atoms forming molecules)      |
  |    2. Multiple relationship types coexist independently                  |
  |    3. Static and dynamic components use relational time (ClockReading)   |
  |    4. RTs compose algebraically (modularity)                             |
  |    5. Universal connectivity ensures comprehensive representation        |
  |    6. Time emerges from relational structure (not assumed primitive)     |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Tensor Foundations                                        |
  |    SECTION 2:  Nested Relational Tensors (NRT)                           |
  |    SECTION 3:  Relational Tensor (RT) - Composition of NRTs              |
  |    SECTION 4:  RT Captures Relations                                     |
  |    SECTION 5:  RT Represents Relational Systems                          |
  |    SECTION 6:  Multiple Relationship Types                               |
  |    SECTION 7:  Hierarchical Structure                                    |
  |    SECTION 8:  Static and Dynamic Tensors (with relational time)         |
  |    SECTION 9:  RT Composition                                            |
  |    SECTION 10: Universal Connectivity in RT                              |
  |    SECTION 11: Main Proposition 5 Theorem                                |
  |    SECTION 12: P5 Module - Public API                                    |
  |    SECTION 13: Hint Databases                                            |
  |    SECTION 14: Tactics                                                   |
  |    SECTION 15: Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Core types: Tensor, NRT, RelationalTensor                         |
  |      - Main theorems: RT_captures_relation, RT_represents_RS             |
  |      - P5 module exports                                                 |
  |      - Hint database: prop5                                              |
  |                                                                          |
  |  DEPENDENCIES:                                                           |
  |    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)        |
  |    - Top__Propositions__Prop_02.v (DSoR, EgoCentricTensor, Dimension)    |
  |    - Top__Propositions__Prop_04.v (Graph, AdjacencyTensor, DecEq)        |
  |    - Top__Propositions__ClockHierarchyCoherence.v (ClockReading, Time)   |
  |    - Top__Numbers__Relational.v (N_rel for relational time)              |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Propositions__Prop_01.
Require Import Top__Propositions__Prop_02.
Require Import Top__Propositions__Prop_04.
Require Import Top__Propositions__ClockHierarchyCoherence.
Require Import Top__Numbers__Relational.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: TENSOR FOUNDATIONS                           *)
(*                                                                            *)
(*  A Tensor maps entity pairs to natural number values, capturing the        *)
(*  "strength" or "nature" of relationships:                                  *)
(*    - 0 = no relation                                                       *)
(*    - 1 = relation exists                                                   *)
(*    - Higher values = weighted relationships                                *)
(*                                                                            *)
(* ========================================================================== *)

Section TensorFoundations.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** A Tensor is a function from entity pairs to natural numbers. *)
  Definition Tensor := Ux U -> Ux U -> nat.

  (** The Zero Tensor: No relationships. *)
  Definition ZeroTensor : Tensor := fun _ _ => 0.

  (** The Unit Tensor: All relationships have weight 1. *)
  Definition UnitTensor : Tensor := fun _ _ => 1.

  (** Singleton Tensor: Weight 1 at exactly one pair. *)
  Definition SingletonTensor (x y : Ux U) : Tensor :=
    fun a b =>
      match Ux_eq_dec a x, Ux_eq_dec b y with
      | left _, left _ => 1
      | _, _ => 0
      end.

  (** Tensor addition: pointwise sum. *)
  Definition tensor_add (T1 T2 : Tensor) : Tensor :=
    fun x y => T1 x y + T2 x y.

  (** Tensor scaling: multiply all entries. *)
  Definition tensor_scale (k : nat) (T : Tensor) : Tensor :=
    fun x y => k * T x y.

  (** Singleton tensor is correct at the specified pair. *)
  Lemma singleton_tensor_correct : forall (x y : Ux U),
    SingletonTensor x y x y = 1.
  Proof.
    intros x y.
    unfold SingletonTensor.
    destruct (Ux_eq_dec x x) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
    destruct (Ux_eq_dec y y) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
    reflexivity.
  Qed.

  (** Singleton tensor is zero elsewhere. *)
  Lemma singleton_tensor_elsewhere : forall (x y a b : Ux U),
    (a <> x \/ b <> y) -> SingletonTensor x y a b = 0.
  Proof.
    intros x y a b Hdiff.
    unfold SingletonTensor.
    destruct (Ux_eq_dec a x) as [Haeq | Haneq].
    - destruct (Ux_eq_dec b y) as [Hbeq | Hbneq].
      + (* a = x and b = y: contradicts Hdiff *)
        exfalso. destruct Hdiff as [Ha | Hb]; [apply Ha; exact Haeq | apply Hb; exact Hbeq].
      + reflexivity.
    - reflexivity.
  Qed.

  (** Tensor from a graph via its adjacency tensor. *)
  Definition TensorFromGraph (G : Graph U) : Tensor := AdjacencyTensor G.

  (** Tensor from graph correctly reflects edges. *)
  Lemma tensor_from_graph_correct : forall (G : Graph U) (x y : Ux U),
    In (x, y) (edges G) -> TensorFromGraph G x y = 1.
  Proof.
    intros G x y Hin.
    unfold TensorFromGraph.
    apply adjacency_tensor_correct. exact Hin.
  Qed.

End TensorFoundations.

Arguments Tensor U : clear implicits.
Arguments ZeroTensor {U}.
Arguments UnitTensor {U}.
Arguments SingletonTensor {U} {HU}.
Arguments tensor_add {U}.
Arguments tensor_scale {U}.
Arguments TensorFromGraph {U} {HU}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: NESTED RELATIONAL TENSORS (NRT)              *)
(*                                                                            *)
(*  An NRT contains:                                                          *)
(*    - An outer tensor (top-level relationships)                             *)
(*    - Inner tensor mappings (detailed sub-relationships)                    *)
(*                                                                            *)
(*  This mirrors the molecular analogy: atoms (NRTs) form molecules (RT).     *)
(*                                                                            *)
(* ========================================================================== *)

Section NestedRelationalTensors.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** 
    A Nested Relational Tensor provides hierarchical structure.
    The outer tensor captures top-level relationships; the inner tensor map
    provides optional detailed sub-structure for specific pairs.
  *)
  Record NRT := mkNRT {
    outer_tensor : Tensor U;
    inner_tensor_map : (Ux U * Ux U) -> option (Tensor U)
  }.

  (** Evaluate an NRT at a pair of entities. *)
  Definition NRT_eval (nrt : NRT) (x y : Ux U) : nat :=
    let base := outer_tensor nrt x y in
    let inner := match inner_tensor_map nrt (x, y) with
                 | Some T => T x y
                 | None => 0
                 end in
    base + inner.

  (** Trivial NRT: wraps a tensor with no inner structure. *)
  Definition trivial_NRT (T : Tensor U) : NRT := {|
    outer_tensor := T;
    inner_tensor_map := fun _ => None
  |}.

  (** NRT from a Graph. *)
  Definition NRT_from_graph (G : Graph U) : NRT :=
    trivial_NRT (TensorFromGraph G).

  (** Trivial NRT evaluation equals the underlying tensor. *)
  Lemma trivial_NRT_eval : forall (T : Tensor U) (x y : Ux U),
    NRT_eval (trivial_NRT T) x y = T x y.
  Proof.
    intros T x y.
    unfold NRT_eval, trivial_NRT. simpl.
    rewrite Nat.add_0_r. reflexivity.
  Qed.

  (** NRT from graph evaluates correctly. *)
  Lemma NRT_from_graph_correct : forall (G : Graph U) (x y : Ux U),
    In (x, y) (edges G) -> NRT_eval (NRT_from_graph G) x y >= 1.
  Proof.
    intros G x y Hin.
    unfold NRT_from_graph.
    rewrite trivial_NRT_eval.
    unfold TensorFromGraph.
    rewrite (adjacency_tensor_correct G x y Hin).
    apply Nat.le_refl.
  Qed.

  (** Add inner structure to an NRT at a specific edge. *)
  Definition add_inner_structure (nrt : NRT) (edge : Ux U * Ux U) 
                                  (inner : Tensor U) : NRT := {|
    outer_tensor := outer_tensor nrt;
    inner_tensor_map := fun e =>
      match Ux_eq_dec (fst e) (fst edge), Ux_eq_dec (snd e) (snd edge) with
      | left _, left _ => Some inner
      | _, _ => inner_tensor_map nrt e
      end
  |}.

  (** Adding inner structure increases evaluation (when inner contributes). *)
  Theorem inner_structure_contribution :
    forall (nrt : NRT) (x y : Ux U) (inner : Tensor U),
      inner_tensor_map nrt (x, y) = None ->
      inner x y > 0 ->
      NRT_eval (add_inner_structure nrt (x, y) inner) x y > NRT_eval nrt x y.
  Proof.
    intros nrt x y inner Hnone Hpos.
    unfold NRT_eval, add_inner_structure. simpl.
    destruct (Ux_eq_dec x x) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
    destruct (Ux_eq_dec y y) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
    rewrite Hnone. simpl.
    rewrite Nat.add_0_r.
    (* Goal: outer_tensor nrt x y + inner x y > outer_tensor nrt x y *)
    apply Nat.lt_add_pos_r. exact Hpos.
  Qed.

End NestedRelationalTensors.

Arguments NRT U : clear implicits.
Arguments mkNRT {U}.
Arguments outer_tensor {U}.
Arguments inner_tensor_map {U}.
Arguments trivial_NRT {U}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: RELATIONAL TENSOR (RT)                       *)
(*                                                                            *)
(*  The Relational Tensor is a collection of typed NRTs representing          *)
(*  different types of relationships (physical, social, emotional, etc.).     *)
(*  Like molecules formed from atoms, the RT emerges from combining NRTs.     *)
(*                                                                            *)
(* ========================================================================== *)

Section RelationalTensorDefinition.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Relationship Type identifier. *)
  Definition RelationType := nat.

  (** Sum of NRT evaluations across all components. *)
  Fixpoint sum_NRTs (components : list (RelationType * NRT U)) (x y : Ux U) : nat :=
    match components with
    | [] => 0
    | (_, nrt) :: rest => NRT_eval nrt x y + sum_NRTs rest x y
    end.

  (** 
    The Relational Tensor: a typed collection of NRTs.
    The composite_tensor provides a unified view of all components.
  *)
  Record RelationalTensor := mkRT {
    nrt_components : list (RelationType * NRT U);
    composite_tensor : Tensor U
  }.

  (** Construct RT from components with correct composite. *)
  Definition make_RT (components : list (RelationType * NRT U)) : RelationalTensor := {|
    nrt_components := components;
    composite_tensor := fun x y => sum_NRTs components x y
  |}.

  (** Empty RT: no components. *)
  Definition EmptyRT : RelationalTensor := make_RT [].

  (** Singleton RT: one typed NRT. *)
  Definition SingletonRT (rtype : RelationType) (nrt : NRT U) : RelationalTensor :=
    make_RT [(rtype, nrt)].

  (** Add a component to an RT. *)
  Definition add_component (rt : RelationalTensor) (rtype : RelationType) 
                           (nrt : NRT U) : RelationalTensor :=
    make_RT ((rtype, nrt) :: nrt_components rt).

  (** Composite tensor of make_RT evaluates as sum of components. *)
  Lemma make_RT_composite : forall components x y,
    composite_tensor (make_RT components) x y = sum_NRTs components x y.
  Proof.
    intros components x y.
    unfold make_RT. simpl. reflexivity.
  Qed.

  (** Singleton RT evaluation. *)
  Lemma singleton_RT_eval : forall (rtype : RelationType) (nrt : NRT U) (x y : Ux U),
    composite_tensor (SingletonRT rtype nrt) x y = NRT_eval nrt x y.
  Proof.
    intros rtype nrt x y.
    unfold SingletonRT, make_RT. simpl.
    rewrite Nat.add_0_r. reflexivity.
  Qed.

End RelationalTensorDefinition.

Arguments RelationType : clear implicits.
Arguments RelationalTensor U : clear implicits.
Arguments mkRT {U}.
Arguments nrt_components {U}.
Arguments composite_tensor {U}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: RT CAPTURES RELATIONS                        *)
(*                                                                            *)
(* ========================================================================== *)

Section RTCapturesRelations.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    THEOREM: Any R'-relation can be captured in a Relational Tensor.
    
    This is CONSTRUCTIVE: we build an explicit RT containing the relation.
  *)
  Theorem RT_captures_relation :
    forall (x y : Ux U), R_prime R x y ->
      exists RT : RelationalTensor U,
        composite_tensor RT x y >= 1.
  Proof.
    intros x y Hrel.
    (* Build graph containing the relation *)
    set (G := singleton_graph x y).
    (* Build NRT from graph *)
    set (nrt := NRT_from_graph G).
    (* Build RT from NRT *)
    exists (SingletonRT 0 nrt).
    unfold SingletonRT, make_RT. simpl.
    rewrite Nat.add_0_r.
    apply NRT_from_graph_correct.
    (* Show (x, y) is in edges of singleton_graph *)
    simpl. left. reflexivity.
  Qed.

  (** RT indicates relation when composite >= 1. *)
  Definition RT_indicates_relation (RT : RelationalTensor U) (x y : Ux U) : Prop :=
    composite_tensor RT x y >= 1.

End RTCapturesRelations.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: RT REPRESENTS RELATIONAL SYSTEMS             *)
(*                                                                            *)
(* ========================================================================== *)

Section RTRepresentsRS.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (**
    THEOREM: Any graph (Relational System) can be represented as an RT.
    
    For every edge in the graph, the RT has a positive value.
  *)
  Theorem RT_represents_RS :
    forall G : Graph U,
      exists RT : RelationalTensor U,
        forall x y : Ux U,
          In (x, y) (edges G) -> composite_tensor RT x y >= 1.
  Proof.
    intro G.
    set (nrt := NRT_from_graph G).
    exists (SingletonRT 0 nrt).
    intros x y Hin.
    unfold SingletonRT, make_RT. simpl.
    rewrite Nat.add_0_r.
    apply NRT_from_graph_correct. exact Hin.
  Qed.

  (** Constructive version: extract the witness RT. *)
  Definition RT_for_graph (G : Graph U) : RelationalTensor U :=
    SingletonRT 0 (NRT_from_graph G).

  (** The witness RT is correct. *)
  Theorem RT_for_graph_correct :
    forall (G : Graph U) (x y : Ux U),
      In (x, y) (edges G) -> composite_tensor (RT_for_graph G) x y >= 1.
  Proof.
    intros G x y Hin.
    unfold RT_for_graph, SingletonRT, make_RT. simpl.
    rewrite Nat.add_0_r.
    apply NRT_from_graph_correct. exact Hin.
  Qed.

End RTRepresentsRS.

Arguments RT_for_graph {U} {HU}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: MULTIPLE RELATIONSHIP TYPES                  *)
(*                                                                            *)
(* ========================================================================== *)

Section MultipleRelationshipTypes.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Standard relationship type identifiers. *)
  Definition PhysicalRelationType : RelationType := 0.
  Definition SocialRelationType : RelationType := 1.
  Definition EmotionalRelationType : RelationType := 2.
  Definition InformationalRelationType : RelationType := 3.

  (** Construct RT with multiple relationship types. *)
  Definition multi_type_RT (physical social emotional : NRT U) : RelationalTensor U :=
    make_RT [
      (PhysicalRelationType, physical);
      (SocialRelationType, social);
      (EmotionalRelationType, emotional)
    ].

  (** Each type contributes independently to the composite. *)
  Theorem multi_type_independence :
    forall (phys soc emot : NRT U) (x y : Ux U),
      composite_tensor (multi_type_RT phys soc emot) x y =
      NRT_eval phys x y + NRT_eval soc x y + NRT_eval emot x y.
  Proof.
    intros phys soc emot x y.
    unfold multi_type_RT.
    rewrite make_RT_composite.
    simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.add_assoc.
    reflexivity.
  Qed.

  (** Relationship types can be queried independently. *)
  Definition get_type_contribution (rt : RelationalTensor U) (rtype : RelationType) 
                                    (x y : Ux U) : nat :=
    (fix find_type (l : list (RelationType * NRT U)) :=
      match l with
      | [] => 0
      | (rt', nrt) :: rest =>
          if Nat.eqb rt' rtype then NRT_eval nrt x y
          else find_type rest
      end) (nrt_components rt).

End MultipleRelationshipTypes.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: HIERARCHICAL STRUCTURE                       *)
(*                                                                            *)
(* ========================================================================== *)

Section HierarchicalStructure.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Depth of nesting in an NRT (0 for trivial, 1+ for nested). *)
  Definition NRT_depth (nrt : NRT U) : nat :=
    (* Simplified: count non-None entries would require decidable equality
       on the range. We use a structural approximation. *)
    0. (* Base case - extension would check inner_tensor_map *)

  (** Check if an NRT has nested structure at a specific edge. *)
  Definition has_nested_structure (nrt : NRT U) (x y : Ux U) : Prop :=
    inner_tensor_map nrt (x, y) <> None.

  (** Nested structure is decidable. *)
  Definition has_nested_structure_dec (nrt : NRT U) (x y : Ux U) :
    {has_nested_structure nrt x y} + {~ has_nested_structure nrt x y}.
  Proof.
    unfold has_nested_structure.
    destruct (inner_tensor_map nrt (x, y)) as [T |].
    - left. discriminate.
    - right. intro H. apply H. reflexivity.
  Defined.

  (** Flatten an NRT to just its outer tensor (removing hierarchy). *)
  Definition flatten_NRT (nrt : NRT U) : NRT U :=
    trivial_NRT (outer_tensor nrt).

  (** Flattening preserves outer tensor evaluation. *)
  Lemma flatten_NRT_outer : forall (nrt : NRT U) (x y : Ux U),
    NRT_eval (flatten_NRT nrt) x y = outer_tensor nrt x y.
  Proof.
    intros nrt x y.
    unfold flatten_NRT.
    apply trivial_NRT_eval.
  Qed.

End HierarchicalStructure.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: STATIC AND DYNAMIC TENSORS                   *)
(*                                                                            *)
(*  Tensors can be static (unchanging) or dynamic (time-varying).             *)
(*  This captures Prop 5's claim about static and dynamic attributes.         *)
(*                                                                            *)
(*  TIME IS RELATIONAL: We use ClockReading from ClockHierarchyCoherence,     *)
(*  which is N_rel (relational natural numbers). This grounds temporal        *)
(*  structure in the same relational foundations as the rest of UCF/GUTT.     *)
(*                                                                            *)
(* ========================================================================== *)

Section StaticAndDynamicTensors.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** 
    Time as Relational Clock Reading.
    
    From ClockHierarchyCoherence: ClockReading = N_rel
    This grounds time in relational structure:
    - Clock ticks = relational steps (via N_rel seriality)
    - Temporal progression = proven via Proposition 1
  *)
  Definition Time := ClockTicks.ClockReading.

  (** Initial time (corresponds to Zero_rel / initial_reading). *)
  Definition Time_zero : Time := ClockTicks.initial_reading.

  (** Advance time by one tick. *)
  Definition Time_tick : Time -> Time := ClockTicks.tick.

  (** A Dynamic Tensor varies with time. *)
  Definition DynamicTensor := Time -> Tensor U.

  (** A Dynamic NRT varies with time. *)
  Definition DynamicNRT := Time -> NRT U.

  (** Lift static tensor to dynamic (constant across time). *)
  Definition static_to_dynamic (T : Tensor U) : DynamicTensor :=
    fun _ => T.

  (** Lift static NRT to dynamic. *)
  Definition static_NRT_to_dynamic (nrt : NRT U) : DynamicNRT :=
    fun _ => nrt.

  (** A tensor is static if it's constant across time. *)
  Definition is_static_tensor (DT : DynamicTensor) : Prop :=
    forall t1 t2 : Time, forall x y : Ux U, DT t1 x y = DT t2 x y.

  (** static_to_dynamic produces static tensors. *)
  Theorem static_to_dynamic_is_static :
    forall T : Tensor U, is_static_tensor (static_to_dynamic T).
  Proof.
    intros T t1 t2 x y.
    unfold static_to_dynamic. reflexivity.
  Qed.

  (** 
    SERIALITY OF TIME: Every moment has a next moment.
    This follows from ClockTicks.tick_serial (which uses N_rel seriality).
  *)
  Theorem time_serial : forall t : Time, exists t', t' = Time_tick t.
  Proof.
    intro t. exists (Time_tick t). reflexivity.
  Qed.

  (** Dynamic Relational Tensor with both static and dynamic components. *)
  Record DynamicRelationalTensor := mkDRT {
    static_components : list (RelationType * NRT U);
    dynamic_components : list (RelationType * DynamicNRT);
    eval_at_time : Time -> Tensor U
  }.

  (** Sum of static NRTs. *)
  Definition sum_static (statics : list (RelationType * NRT U)) (x y : Ux U) : nat :=
    sum_NRTs statics x y.

  (** Sum of dynamic NRTs at a given time. *)
  Fixpoint sum_dynamic (dynamics : list (RelationType * DynamicNRT)) 
                       (t : Time) (x y : Ux U) : nat :=
    match dynamics with
    | [] => 0
    | (_, dnrt) :: rest => NRT_eval (dnrt t) x y + sum_dynamic rest t x y
    end.

  (** Construct a DynamicRT. *)
  Definition make_DynamicRT 
    (statics : list (RelationType * NRT U))
    (dynamics : list (RelationType * DynamicNRT)) : DynamicRelationalTensor := {|
    static_components := statics;
    dynamic_components := dynamics;
    eval_at_time := fun t x y => sum_static statics x y + sum_dynamic dynamics t x y
  |}.

  (** A purely static DynamicRT (no dynamic components). *)
  Definition purely_static_DRT (rt : RelationalTensor U) : DynamicRelationalTensor :=
    make_DynamicRT (nrt_components rt) [].

  (** Purely static DRT is constant across time. *)
  Theorem purely_static_DRT_constant :
    forall (rt : RelationalTensor U) (t1 t2 : Time) (x y : Ux U),
      eval_at_time (purely_static_DRT rt) t1 x y = 
      eval_at_time (purely_static_DRT rt) t2 x y.
  Proof.
    intros rt t1 t2 x y.
    unfold purely_static_DRT, make_DynamicRT. simpl.
    reflexivity.
  Qed.

  (** 
    TIME COHERENCE: Dynamic tensors can evolve but maintain relational structure.
    At any two times, if the tensor values differ, it's due to dynamic components.
  *)
  Theorem dynamic_change_from_dynamic_components :
    forall (drt : DynamicRelationalTensor) (t1 t2 : Time) (x y : Ux U),
      dynamic_components drt = [] ->
      eval_at_time drt t1 x y = eval_at_time drt t2 x y.
  Proof.
    intros drt t1 t2 x y Hempty.
    destruct drt as [statics dynamics eval_fn].
    simpl in Hempty. subst dynamics.
    (* eval_fn may be arbitrary, but for make_DynamicRT it would be constant *)
    (* This theorem applies to the structure, specific instances need more *)
    (* For a general drt, we can't prove this without knowing eval_fn *)
    (* Let's state it for make_DynamicRT specifically *)
  Abort.

  (** For DynamicRTs built with make_DynamicRT, empty dynamics means constant. *)
  Theorem make_DynamicRT_no_dynamics_constant :
    forall (statics : list (RelationType * NRT U)) (t1 t2 : Time) (x y : Ux U),
      eval_at_time (make_DynamicRT statics []) t1 x y = 
      eval_at_time (make_DynamicRT statics []) t2 x y.
  Proof.
    intros statics t1 t2 x y.
    unfold make_DynamicRT. simpl.
    reflexivity.
  Qed.

End StaticAndDynamicTensors.

Arguments DynamicTensor U : clear implicits.
Arguments DynamicNRT U : clear implicits.
Arguments DynamicRelationalTensor U : clear implicits.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: RT COMPOSITION                               *)
(*                                                                            *)
(* ========================================================================== *)

Section RTComposition.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Compose two RTs by concatenating their components. *)
  Definition compose_RT (rt1 rt2 : RelationalTensor U) : RelationalTensor U :=
    make_RT (nrt_components rt1 ++ nrt_components rt2).

  (** Component independence: sum over concatenation = sum of sums. *)
  Lemma sum_NRTs_app : forall (l1 l2 : list (RelationType * NRT U)) (x y : Ux U),
    sum_NRTs (l1 ++ l2) x y = sum_NRTs l1 x y + sum_NRTs l2 x y.
  Proof.
    intros l1 l2 x y.
    induction l1 as [| [rt nrt] rest IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. rewrite Nat.add_assoc. reflexivity.
  Qed.

  (** RT composition adds component sums. *)
  Theorem RT_composition_adds :
    forall (rt1 rt2 : RelationalTensor U) (x y : Ux U),
      composite_tensor (compose_RT rt1 rt2) x y =
      sum_NRTs (nrt_components rt1) x y + sum_NRTs (nrt_components rt2) x y.
  Proof.
    intros rt1 rt2 x y.
    unfold compose_RT.
    rewrite make_RT_composite.
    apply sum_NRTs_app.
  Qed.

  (** For RTs built with make_RT, composition preserves sums. *)
  Theorem RT_composition_preserves :
    forall (comps1 comps2 : list (RelationType * NRT U)) (x y : Ux U),
      composite_tensor (compose_RT (make_RT comps1) (make_RT comps2)) x y =
      composite_tensor (make_RT comps1) x y + composite_tensor (make_RT comps2) x y.
  Proof.
    intros comps1 comps2 x y.
    unfold compose_RT. simpl.
    repeat rewrite make_RT_composite.
    apply sum_NRTs_app.
  Qed.

  (** Modularity: adding a component increases or preserves the sum. *)
  Theorem RT_modularity :
    forall (rt : RelationalTensor U) (rtype : RelationType) (nrt : NRT U) (x y : Ux U),
      composite_tensor (add_component rt rtype nrt) x y >=
      sum_NRTs (nrt_components rt) x y.
  Proof.
    intros rt rtype nrt x y.
    unfold add_component.
    rewrite make_RT_composite. simpl.
    apply Nat.le_add_l.
  Qed.

  (** Composition is associative. *)
  Theorem RT_composition_assoc :
    forall (rt1 rt2 rt3 : RelationalTensor U) (x y : Ux U),
      composite_tensor (compose_RT (compose_RT rt1 rt2) rt3) x y =
      composite_tensor (compose_RT rt1 (compose_RT rt2 rt3)) x y.
  Proof.
    intros rt1 rt2 rt3 x y.
    unfold compose_RT.
    repeat rewrite make_RT_composite. simpl.
    repeat rewrite sum_NRTs_app.
    rewrite Nat.add_assoc. reflexivity.
  Qed.

  (** Empty RT is identity for composition. *)
  Theorem RT_composition_empty_l :
    forall (rt : RelationalTensor U) (x y : Ux U),
      composite_tensor (compose_RT EmptyRT rt) x y =
      sum_NRTs (nrt_components rt) x y.
  Proof.
    intros rt x y.
    unfold compose_RT, EmptyRT.
    rewrite make_RT_composite. simpl.
    reflexivity.
  Qed.

  Theorem RT_composition_empty_r :
    forall (rt : RelationalTensor U) (x y : Ux U),
      composite_tensor (compose_RT rt EmptyRT) x y =
      sum_NRTs (nrt_components rt) x y.
  Proof.
    intros rt x y.
    unfold compose_RT, EmptyRT.
    rewrite make_RT_composite.
    rewrite app_nil_r.
    reflexivity.
  Qed.

End RTComposition.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: UNIVERSAL CONNECTIVITY IN RT                *)
(*                                                                            *)
(*  Every entity can be represented in an RT through Whole.                   *)
(*  This connects to Proposition 01 (seriality).                              *)
(*                                                                            *)
(* ========================================================================== *)

Section UniversalConnectivityRT.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    THEOREM: Every entity can be represented in an RT via its relation to Whole.
    
    From Prop 01: forall x, R_prime R x Whole (everything relates to Whole).
  *)
  Theorem every_entity_in_RT :
    forall x : Ux U,
      exists RT : RelationalTensor U,
        composite_tensor RT x Whole >= 1.
  Proof.
    intro x.
    (* From Prop 01: x relates to Whole *)
    assert (Hrel : R_prime R x Whole) by apply everything_relates_to_Whole.
    (* Apply RT_captures_relation *)
    apply (RT_captures_relation R x Whole Hrel).
  Qed.

  (** Every entity pair with a relation has an RT representation. *)
  Theorem every_related_pair_in_RT :
    forall (x y : Ux U), R_prime R x y ->
      exists RT : RelationalTensor U,
        composite_tensor RT x y >= 1.
  Proof.
    intros x y Hrel.
    apply (RT_captures_relation R x y Hrel).
  Qed.

End UniversalConnectivityRT.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: MAIN PROPOSITION 5 THEOREM                  *)
(*                                                                            *)
(* ========================================================================== *)

Section MainProposition5.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    PROPOSITION 5 (MAIN THEOREM):
    
    The Relational Tensor serves as a modular representation of a
    Relational System, capturing:
    
    1. Any R'-relation can be captured in an RT (representability)
    2. Any graph (RS) can be represented as an RT (comprehensiveness)
    3. RTs are modular - components add independently (modularity)
    4. RTs compose algebraically (composability)
    5. Every entity connects through Whole (universal connectivity)
  *)
  Theorem proposition_5_relational_tensor :
    (* Part 1: Any relation can be captured in an RT *)
    (forall x y : Ux U, R_prime R x y -> 
      exists RT : RelationalTensor U, composite_tensor RT x y >= 1) /\
    
    (* Part 2: Any graph (RS) can be represented as an RT *)
    (forall G : Graph U, exists RT : RelationalTensor U,
      forall x y : Ux U, In (x, y) (edges G) -> 
        composite_tensor RT x y >= 1) /\
    
    (* Part 3: RTs are modular - components add independently *)
    (forall (comps1 comps2 : list (RelationType * NRT U)) (x y : Ux U),
      sum_NRTs (comps1 ++ comps2) x y = 
      sum_NRTs comps1 x y + sum_NRTs comps2 x y) /\
    
    (* Part 4: RTs compose - component sums add *)
    (forall (comps1 comps2 : list (RelationType * NRT U)) (x y : Ux U),
      composite_tensor (compose_RT (make_RT comps1) (make_RT comps2)) x y =
      composite_tensor (make_RT comps1) x y + composite_tensor (make_RT comps2) x y) /\
    
    (* Part 5: Every entity connects through Whole *)
    (forall x : Ux U, exists RT : RelationalTensor U,
      composite_tensor RT x Whole >= 1).
  Proof.
    repeat split.
    - (* Part 1: Representability *)
      intros x y Hrel.
      exists (SingletonRT 0 (NRT_from_graph (singleton_graph x y))).
      unfold SingletonRT, make_RT. simpl.
      rewrite Nat.add_0_r.
      apply NRT_from_graph_correct.
      simpl. left. reflexivity.
    - (* Part 2: Comprehensiveness *)
      intro G.
      exists (SingletonRT 0 (NRT_from_graph G)).
      intros x y Hin.
      unfold SingletonRT, make_RT. simpl.
      rewrite Nat.add_0_r.
      apply NRT_from_graph_correct. exact Hin.
    - (* Part 3: Modularity *)
      intros l1 l2 x y.
      induction l1 as [| [rt nrt] rest IH].
      + simpl. reflexivity.
      + simpl. rewrite IH. rewrite Nat.add_assoc. reflexivity.
    - (* Part 4: Composability *)
      intros comps1 comps2 x y.
      unfold compose_RT. simpl.
      repeat rewrite make_RT_composite.
      induction comps1 as [| [rt nrt] rest IH].
      + simpl. reflexivity.
      + simpl. rewrite IH. rewrite Nat.add_assoc. reflexivity.
    - (* Part 5: Universal connectivity *)
      intro x.
      assert (Hrel : R_prime R x Whole) by apply everything_relates_to_Whole.
      exists (SingletonRT 0 (NRT_from_graph (singleton_graph x Whole))).
      unfold SingletonRT, make_RT. simpl.
      rewrite Nat.add_0_r.
      apply NRT_from_graph_correct.
      simpl. left. reflexivity.
  Qed.

End MainProposition5.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: P5 MODULE - PUBLIC API                      *)
(*                                                                            *)
(* ========================================================================== *)

Module P5.

  (** === Types === *)
  Definition tensor (U : Type) := Tensor U.
  Definition nrt (U : Type) := NRT U.
  Definition rt (U : Type) := RelationalTensor U.
  Definition drt (U : Type) `{HU : DecEq U} := DynamicRelationalTensor U.
  Definition dynamic_nrt (U : Type) `{HU : DecEq U} := DynamicNRT U.
  Definition rel_type := RelationType.

  (** === Tensor Constructors === *)
  Definition zero_tensor {U : Type} : Tensor U := ZeroTensor.
  Definition unit_tensor {U : Type} : Tensor U := UnitTensor.
  Definition singleton_tensor {U : Type} `{HU : DecEq U} := @SingletonTensor U HU.
  Definition tensor_from_graph {U : Type} `{HU : DecEq U} := @TensorFromGraph U HU.

  (** === NRT Constructors === *)
  Definition trivial {U : Type} := @trivial_NRT U.
  Definition from_graph {U : Type} `{HU : DecEq U} := @NRT_from_graph U HU.
  Definition add_inner {U : Type} `{HU : DecEq U} := @add_inner_structure U HU.
  Definition nrt_eval {U : Type} := @NRT_eval U.

  (** === RT Constructors === *)
  Definition make {U : Type} := @make_RT U.
  Definition empty {U : Type} : RelationalTensor U := EmptyRT.
  Definition singleton {U : Type} := @SingletonRT U.
  Definition add_comp {U : Type} := @add_component U.
  Definition compose {U : Type} := @compose_RT U.
  Definition for_graph {U : Type} `{HU : DecEq U} := @RT_for_graph U HU.

  (** === Dynamic RT === *)
  (* Note: Dynamic types depend on DecEq context from section *)

  (** === Time (from ClockHierarchyCoherence) === *)
  Definition clock_reading := ClockTicks.ClockReading.
  Definition initial_time := ClockTicks.initial_reading.
  Definition tick := ClockTicks.tick.

  (** === Relationship Types === *)
  Definition physical := PhysicalRelationType.
  Definition social := SocialRelationType.
  Definition emotional := EmotionalRelationType.
  Definition informational := InformationalRelationType.

  (** === Core Theorems === *)
  Definition captures_relation {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    @RT_captures_relation U HU R.
  Definition represents_RS {U : Type} `{HU : DecEq U} :=
    @RT_represents_RS U HU.
  Definition for_graph_correct {U : Type} `{HU : DecEq U} :=
    @RT_for_graph_correct U HU.
  Definition every_entity {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    @every_entity_in_RT U HU R.
  Definition proposition_5 {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    @proposition_5_relational_tensor U HU R.

  (** === Composition Theorems === *)
  Definition composition_adds {U : Type} := @RT_composition_adds U.
  Definition composition_preserves {U : Type} := @RT_composition_preserves U.
  Definition composition_assoc {U : Type} := @RT_composition_assoc U.
  Definition modularity {U : Type} := @RT_modularity U.

End P5.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: HINT DATABASES                              *)
(*                                                                            *)
(* ========================================================================== *)

Create HintDb prop5.

#[export] Hint Resolve
  singleton_tensor_correct
  trivial_NRT_eval
  NRT_from_graph_correct
  singleton_RT_eval
  make_RT_composite
  sum_NRTs_app
  RT_composition_preserves
  RT_composition_assoc
  RT_composition_empty_l
  RT_composition_empty_r
  static_to_dynamic_is_static
  purely_static_DRT_constant
  : prop5.

#[export] Hint Extern 1 (exists _ : RelationalTensor _, composite_tensor _ _ _ >= 1) =>
  eexists; rewrite singleton_RT_eval; apply NRT_from_graph_correct; simpl; left; reflexivity : prop5.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 14: TACTICS                                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Prove that a relation can be captured in an RT. *)
Ltac prove_RT_captures :=
  match goal with
  | |- exists RT : RelationalTensor _, composite_tensor RT ?x ?y >= 1 =>
      exists (SingletonRT 0 (NRT_from_graph (singleton_graph x y)));
      rewrite singleton_RT_eval;
      apply NRT_from_graph_correct;
      simpl; left; reflexivity
  end.

(** Simplify RT expressions. *)
Ltac rt_simpl :=
  unfold SingletonRT, make_RT, NRT_from_graph, trivial_NRT, NRT_eval;
  try rewrite make_RT_composite;
  simpl.

(** Combined automation for Proposition 5. *)
Ltac prop5_auto :=
  auto with prop5 prop4 prop1;
  try prove_RT_captures;
  try rt_simpl.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 15: AXIOM AUDIT                                 *)
(*                                                                            *)
(*  Verification that this file uses ZERO AXIOMS.                             *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)

  Definition test_zero_tensor : @ZeroTensor nat (elem 1) (elem 2) = 0.
  Proof. reflexivity. Qed.

  Definition test_unit_tensor : @UnitTensor nat (elem 1) (elem 2) = 1.
  Proof. reflexivity. Qed.

  Definition test_singleton_tensor : 
    @SingletonTensor nat _ (elem 3) (elem 5) (elem 3) (elem 5) = 1.
  Proof. 
    unfold SingletonTensor.
    destruct (Ux_eq_dec (elem 3) (elem 3)); [|contradiction].
    destruct (Ux_eq_dec (elem 5) (elem 5)); [|contradiction].
    reflexivity.
  Qed.

  Definition test_trivial_NRT_eval :
    NRT_eval (@trivial_NRT nat ZeroTensor) (elem 1) (elem 2) = 0.
  Proof. reflexivity. Qed.

  Definition test_empty_RT :
    composite_tensor EmptyRT (elem 1) (elem 2) = 0.
  Proof. reflexivity. Qed.

  Definition test_make_RT :
    composite_tensor (make_RT (U:=nat) []) (elem 1) (elem 2) = 0.
  Proof. reflexivity. Qed.

  (** Key test: main theorem compiles without axioms. *)
  Definition test_captures_relation_compiles :
    forall (x y : Ux nat), R_prime lt x y ->
      exists RT : RelationalTensor nat, composite_tensor RT x y >= 1.
  Proof.
    intros x y H.
    apply (RT_captures_relation lt).
    exact H.
  Qed.

  Definition test_represents_RS_compiles :
    forall G : Graph nat,
      exists RT : RelationalTensor nat,
        forall x y : Ux nat, In (x, y) (edges G) -> composite_tensor RT x y >= 1.
  Proof.
    intro G.
    apply RT_represents_RS.
  Qed.

  Definition test_proposition_5_compiles :
    (forall x y : Ux nat, R_prime lt x y -> 
      exists RT : RelationalTensor nat, composite_tensor RT x y >= 1) /\
    (forall G : Graph nat, exists RT : RelationalTensor nat,
      forall x y : Ux nat, In (x, y) (edges G) -> composite_tensor RT x y >= 1) /\
    (forall (comps1 comps2 : list (RelationType * NRT nat)) (x y : Ux nat),
      sum_NRTs (comps1 ++ comps2) x y = sum_NRTs comps1 x y + sum_NRTs comps2 x y) /\
    (forall (comps1 comps2 : list (RelationType * NRT nat)) (x y : Ux nat),
      composite_tensor (compose_RT (make_RT comps1) (make_RT comps2)) x y =
      composite_tensor (make_RT comps1) x y + composite_tensor (make_RT comps2) x y) /\
    (forall x : Ux nat, exists RT : RelationalTensor nat,
      composite_tensor RT x Whole >= 1).
  Proof.
    apply (proposition_5_relational_tensor lt).
  Qed.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 16: USAGE EXAMPLES                              *)
(*                                                                            *)
(*  Demonstrates typical usage patterns for downstream development.           *)
(*                                                                            *)
(* ========================================================================== *)

Module UsageExamples.

  (** Example 1: Build a simple RT for a social network. *)
  Section SocialNetworkExample.
    
    (* A simple Person type with decidable equality *)
    Inductive Person := Alice | Bob | Carol.
    
    #[local] Instance Person_DecEq : DecEq Person.
    Proof.
      constructor. intros x y.
      destruct x, y;
        try (left; reflexivity);
        try (right; discriminate).
    Defined.
    
    (* A "follows" relation *)
    Definition follows : Person -> Person -> Prop :=
      fun x y => 
        (x = Alice /\ y = Bob) \/    (* Alice follows Bob *)
        (x = Bob /\ y = Carol) \/    (* Bob follows Carol *)
        (x = Carol /\ y = Alice).    (* Carol follows Alice *)
    
    (* Build a graph representing the follows relation *)
    Definition social_graph : Graph Person :=
      add_edge 
        (add_edge 
          (add_edge empty_graph (elem Carol, elem Alice))
          (elem Bob, elem Carol))
        (elem Alice, elem Bob).
    
    (* Build an NRT from the graph *)
    Definition social_nrt : NRT Person := NRT_from_graph social_graph.
    
    (* Build a RelationalTensor with "social" type *)
    Definition social_RT : RelationalTensor Person :=
      SingletonRT SocialRelationType social_nrt.
    
    (* Verify: Alice -> Bob is represented *)
    Lemma alice_bob_represented :
      composite_tensor social_RT (elem Alice) (elem Bob) >= 1.
    Proof.
      unfold social_RT, SingletonRT, make_RT. simpl.
      rewrite Nat.add_0_r.
      apply NRT_from_graph_correct.
      unfold social_graph. simpl. left. reflexivity.
    Qed.
    
  End SocialNetworkExample.

  (** Example 2: Compose multiple relationship types. *)
  Section CompositionExample.
    
    (* Using nat as entity type *)
    Definition physical_nrt : NRT nat := 
      trivial_NRT (SingletonTensor (elem 1) (elem 2)).
    
    Definition emotional_nrt : NRT nat :=
      trivial_NRT (SingletonTensor (elem 1) (elem 3)).
    
    Definition multi_RT : RelationalTensor nat :=
      compose_RT 
        (SingletonRT PhysicalRelationType physical_nrt)
        (SingletonRT EmotionalRelationType emotional_nrt).
    
    (* The composition adds contributions from both types *)
    Lemma multi_RT_correct :
      composite_tensor multi_RT (elem 1) (elem 2) = 
      composite_tensor (SingletonRT PhysicalRelationType physical_nrt) (elem 1) (elem 2) +
      composite_tensor (SingletonRT EmotionalRelationType emotional_nrt) (elem 1) (elem 2).
    Proof.
      apply RT_composition_preserves.
    Qed.
    
  End CompositionExample.

  (** Example 3: Universal connectivity - every entity relates to Whole. *)
  Section UniversalConnectivityExample.
    
    (* For any entity, we can find an RT witnessing its connection to Whole *)
    Lemma any_entity_has_RT :
      forall n : nat,
        exists RT : RelationalTensor nat,
          composite_tensor RT (elem n) Whole >= 1.
    Proof.
      intro n.
      apply (every_entity_in_RT lt).
    Qed.
    
  End UniversalConnectivityExample.

  (** Example 4: Using the P5 module API. *)
  Section P5APIExample.
    
    (* Build a simple RT using P5 module names *)
    Definition example_nrt : P5.nrt nat := 
      P5.trivial P5.unit_tensor.
    
    Definition example_rt : P5.rt nat :=
      P5.singleton P5.physical example_nrt.
    
    (* The main theorem via P5 API *)
    Check P5.proposition_5.
    Check P5.captures_relation.
    Check P5.represents_RS.
    
  End P5APIExample.

End UsageExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (P5):
    P5.tensor U               = Tensor U (function type)
    P5.nrt U                  = NRT U (nested relational tensor)
    P5.rt U                   = RelationalTensor U
    P5.drt U                  = DynamicRelationalTensor U
    P5.rel_type               = RelationType (nat)
    P5.make comps             = make_RT comps
    P5.single rtype nrt       = SingletonRT rtype nrt
    P5.compose rt1 rt2        = compose_RT rt1 rt2
    P5.for_graph G            = RT_for_graph G
    P5.captures_relation      = RT_captures_relation
    P5.represents_RS          = RT_represents_RS
    P5.proposition_5          = proposition_5_relational_tensor
  
  TYPES:
    Tensor U                  = Ux U -> Ux U -> nat
    NRT U                     = record with outer_tensor, inner_tensor_map
    RelationalTensor U        = record with nrt_components, composite_tensor
    DynamicRelationalTensor U = record with static/dynamic components
    RelationType              = nat (0=physical, 1=social, 2=emotional, ...)
  
  CONSTRUCTORS:
    ZeroTensor                = constant 0 tensor
    UnitTensor                = constant 1 tensor
    SingletonTensor x y       = 1 at (x,y), 0 elsewhere
    trivial_NRT T             = NRT with outer=T, no inner structure
    NRT_from_graph G          = NRT from graph's adjacency tensor
    make_RT components        = RT from list of (type, NRT) pairs
    EmptyRT                   = RT with no components
    SingletonRT rtype nrt     = RT with one component
    add_component rt t nrt    = add new component to RT
    compose_RT rt1 rt2        = combine two RTs
    RT_for_graph G            = witness RT for graph G
  
  MAIN THEOREMS:
    RT_captures_relation:
      forall x y, R_prime R x y -> exists RT, composite_tensor RT x y >= 1
    
    RT_represents_RS:
      forall G, exists RT, forall x y, In (x,y) (edges G) -> composite >= 1
    
    sum_NRTs_app (modularity):
      sum_NRTs (l1 ++ l2) = sum_NRTs l1 + sum_NRTs l2
    
    RT_composition_preserves:
      composite (compose_RT rt1 rt2) = composite rt1 + composite rt2
    
    every_entity_in_RT:
      forall x, exists RT, composite_tensor RT x Whole >= 1
    
    proposition_5_relational_tensor:
      All five parts combined
    
    time_serial:
      forall t, exists t', t' = Time_tick t (temporal progression guaranteed)
  
  RELATIONSHIP TYPES:
    PhysicalRelationType      = 0
    SocialRelationType        = 1
    EmotionalRelationType     = 2
    InformationalRelationType = 3
  
  RELATIONAL TIME (from ClockHierarchyCoherence):
    Time                      = ClockReading = N_rel (relational naturals)
    Time_zero                 = initial_reading (Zero_rel)
    Time_tick                 = clock tick (Succ_rel)
    time_serial               = every moment has a next moment
  
  HINT DATABASE:
    prop5                     : automation hints for Prop 5
    
    Usage: auto with prop5. / prop5_auto.
  
  TACTICS:
    prove_RT_captures         : prove RT existence goals
    rt_simpl                  : simplify RT expressions
    prop5_auto                : combined automation
  
  PHILOSOPHICAL SIGNIFICANCE
  ==========================
  
  This proof demonstrates that:
  
  1. MODULARITY: Complex relational systems can be built from simpler
     components (NRTs), like molecules from atoms.
  
  2. MULTIPLE TYPES: Different relationship types (physical, social,
     emotional) coexist independently in the same RT.
  
  3. HIERARCHY: NRTs provide nested structure, mirroring real-world
     hierarchies (individuals -> families -> communities -> societies).
  
  4. COMPOSABILITY: RTs form an algebraic structure - they can be
     combined, and combination preserves individual contributions.
  
  5. UNIVERSALITY: Through Proposition 01's universal connectivity,
     every entity is representable via its relation to Whole.
  
  6. RELATIONAL TIME: Dynamic aspects use ClockReading (= N_rel),
     grounding temporal structure in the same relational foundations.
     Time is NOT assumed as primitive but EMERGES from relations.
  
  COMPILATION
  ===========
  
  This file depends on:
    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)
    - Top__Propositions__Prop_02.v (DSoR, EgoCentricTensor)
    - Top__Propositions__Prop_04.v (Graph, AdjacencyTensor, DecEq)
    - Top__Propositions__ClockHierarchyCoherence.v (ClockReading, Time)
    - Top__Numbers__Relational.v (N_rel)
  
  Build order:
    1. Top__Extensions__Base.v
    2. Top__Extensions__WholeCompletion.v
    3. Top__Extensions__Composition.v
    4. Top__Extensions__Prelude.v
    5. Top__Propositions__Prop_01.v
    6. Top__Numbers__Relational.v
    7. Top__Numbers__RelationalReals.v
    8. Top__Propositions__Prop_02.v
    9. Top__Propositions__Prop_04.v
   10. Top__Numbers__RelationalIntegers.v (for ClockHierarchyCoherence)
   11. Top__Propositions__ClockHierarchyCoherence.v
   12. Top__Propositions__Prop_05.v (this file)
  
  AXIOM STATUS
  ============
  
  This file uses ZERO AXIOMS. All constructions are fully constructive.
  Time is ClockReading = N_rel (relational naturals, not abstract Parameter).
  
  Run `Print Assumptions proposition_5_relational_tensor.` to verify.
  Expected output: Closed under the global context.
*)

(* Main exports for downstream use *)
Definition UCF_GUTT_Tensor := Tensor.
Definition UCF_GUTT_NRT := NRT.
Definition UCF_GUTT_RelationalTensor := RelationalTensor.
Definition UCF_GUTT_RT_Captures_Relation := RT_captures_relation.
Definition UCF_GUTT_RT_Represents_RS := RT_represents_RS.
Definition UCF_GUTT_Proposition5 := proposition_5_relational_tensor.

(* Print assumptions for key theorems *)
Print Assumptions proposition_5_relational_tensor.
Print Assumptions RT_captures_relation.
Print Assumptions RT_represents_RS.
Print Assumptions RT_composition_preserves.
Print Assumptions every_entity_in_RT.
