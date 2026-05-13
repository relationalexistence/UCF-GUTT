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
  |       PROPOSITION 10: DIRECTION OF RELATION AS OPTIONAL ATTRIBUTE        |
  |                                                                          |
  |                      UCF/GUTT(TM) Formal Verification                    |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-12                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  THEOREM: Direction of Relation (DOR) is an optional attribute that      |
  |           does not determine relation existence.                         |
  |                                                                          |
  |  DEFINITION: In the Relational System (RS), the term "Direction of       |
  |  Relation" (DOR) is an attribute that describes the orientation or       |
  |  flow of the relationship between entities. DOR_0, DOR_1, ... represent    |
  |  various directional flows: to self, to other, system internal, or       |
  |  to external entities/systems. This includes:                            |
  |    - Unidirectional relations (source -> target)                         |
  |    - Bidirectional relations (source <-> target)                         |
  |    - Multi-directional relations (complex multi-entity flow)             |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Core Definitions (Direction, CoreRelation)                |
  |    SECTION 2:  Relation Constructors (Undirected, Uni, Bi, Multi)        |
  |    SECTION 3:  Existence Theorems                                        |
  |    SECTION 4:  Direction Independence                                    |
  |    SECTION 5:  Direction Types (Self, Other, Internal)                   |
  |    SECTION 6:  Direction Manipulation                                    |
  |    SECTION 7:  Bidirectionality Properties                               |
  |    SECTION 8:  Multi-Directionality Properties                           |
  |    SECTION 9:  Origin and Flow                                           |
  |    SECTION 10: Connection to Proposition 1                               |
  |    SECTION 11: P10 Module - Public API                                   |
  |    SECTION 12: Hint Databases & Tactics                                  |
  |    SECTION 13: Examples                                                  |
  |    SECTION 14: Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Types: Direction, CoreRelation, RelationWithDirection             |
  |      - Constructors: Unidirectional, Bidirectional, MultiDirectional     |
  |      - Functions: UndirectedRelation, DirectedRelation_*                 |
  |      - P10 module exports                                                |
  |      - Hint database: prop10                                             |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - Types: UpperCamelCase (Direction, CoreRelation)                     |
  |    - Constructors: UpperCamelCase (Unidirectional, Bidirectional)        |
  |    - Functions: snake_case with context (DirectedRelation_Uni)           |
  |    - Theorems: snake_case descriptive (direction_independent_of_...)     |
  |                                                                          |
  |  KEY RESULTS:                                                            |
  |    - Relations exist with or without direction (direction is optional)   |
  |    - Direction does not determine relation existence                     |
  |    - Same core can have different directions (diversity)                 |
  |    - All direction types connect to Prop 1's universal connectivity      |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                            |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Import the UCF/GUTT extension framework *)
Require Import Top__Extensions__Prelude.

(* Import Proposition 1 for universal connectivity *)
Require Import Top__Propositions__Prop_01.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE DEFINITIONS                             *)
(*                                                                            *)
(* ========================================================================== *)

(**
  PHILOSOPHICAL GROUNDING
  =======================
  
  Direction is an ATTRIBUTE of relation, not its essence. A relation exists
  by virtue of connecting entities; direction describes HOW it flows.
  
  This is analogous to:
  - A road exists between cities; direction describes one-way vs two-way
  - A message exists between sender/receiver; direction describes the flow
  - A dependency exists between modules; direction describes import order
  
  The key insight: EXISTENCE is determined by source and target (the core).
  DIRECTION is metadata about flow, which can be:
  - Absent (undirected relation)
  - Unidirectional (one-way flow)
  - Bidirectional (mutual flow)
  - Multi-directional (complex flow patterns)
*)

Section DirectionTheory.

  (** Base universe - parametric, not an axiom. *)
  Variable U : Type.
  
  (** Extended universe from Proposition 1. *)
  Definition Ux : Type := P1.Carrier U.
  
  (** The Whole element (terminal sink). *)
  Definition Whole : Ux := P1.whole.
  
  (** Embed an element of U into Ux. *)
  Definition elem (u : U) : Ux := P1.embed u.
  
  (** Entity type for relations (elements of extended universe). *)
  Definition Entity : Type := Ux.

  (* ------------------------------------------------------------------------ *)
  (*                         Direction Type                                   *)
  (* ------------------------------------------------------------------------ *)
  
  (**
    Direction captures the orientation or flow of a relationship.
    
    - Unidirectional: one-way flow from source to target
    - Bidirectional: mutual flow between source and target
    - MultiDirectional: complex flow involving multiple entities
  *)
  Inductive Direction : Type :=
    | Unidirectional : Entity -> Entity -> Direction
    | Bidirectional : Entity -> Entity -> Direction
    | MultiDirectional : list Entity -> Direction.

  (* ------------------------------------------------------------------------ *)
  (*                         Core Relation                                    *)
  (* ------------------------------------------------------------------------ *)
  
  (**
    CoreRelation captures the ESSENTIAL structure of a relation:
    source and target. This is what determines existence.
  *)
  Record CoreRelation := mkCoreRelation {
    source : Entity;
    target : Entity
  }.

  (**
    RelationWithDirection extends CoreRelation with an OPTIONAL
    direction attribute. The key word is OPTIONAL (option type).
  *)
  Record RelationWithDirection := mkRelationWithDirection {
    core : CoreRelation;
    direction : option Direction
  }.

  (**
    Relation existence is determined SOLELY by the core.
    Direction plays no role in existence.
  *)
  Definition RelationExists (r : RelationWithDirection) : Prop :=
    exists (src tgt : Entity), 
      core r = mkCoreRelation src tgt.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: RELATION CONSTRUCTORS                        *)
(*                                                                            *)
(* ========================================================================== *)

  (** Construct a relation WITHOUT direction. *)
  Definition UndirectedRelation (src tgt : Entity) : RelationWithDirection :=
    mkRelationWithDirection 
      (mkCoreRelation src tgt) 
      None.

  (** Construct a relation WITH unidirectional flow. *)
  Definition DirectedRelation_Uni (src tgt : Entity) : RelationWithDirection :=
    mkRelationWithDirection 
      (mkCoreRelation src tgt) 
      (Some (Unidirectional src tgt)).

  (** Construct a relation WITH bidirectional flow. *)
  Definition DirectedRelation_Bi (src tgt : Entity) : RelationWithDirection :=
    mkRelationWithDirection 
      (mkCoreRelation src tgt) 
      (Some (Bidirectional src tgt)).

  (** Construct a relation WITH multi-directional flow. *)
  Definition DirectedRelation_Multi (entities : list Entity) (src tgt : Entity) 
    : RelationWithDirection :=
    mkRelationWithDirection 
      (mkCoreRelation src tgt) 
      (Some (MultiDirectional entities)).

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: EXISTENCE THEOREMS                           *)
(*                                                                            *)
(* ========================================================================== *)

  (** THEOREM: Relations exist without direction. *)
  Theorem relation_exists_without_direction :
    forall (x y : Entity), RelationExists (UndirectedRelation x y).
  Proof.
    intros x y.
    unfold RelationExists, UndirectedRelation.
    exists x, y. reflexivity.
  Qed.

  (** THEOREM: Relations exist with unidirectional direction. *)
  Theorem relation_exists_with_unidirectional :
    forall (x y : Entity), RelationExists (DirectedRelation_Uni x y).
  Proof.
    intros x y.
    unfold RelationExists, DirectedRelation_Uni.
    exists x, y. reflexivity.
  Qed.

  (** THEOREM: Relations exist with bidirectional direction. *)
  Theorem relation_exists_with_bidirectional :
    forall (x y : Entity), RelationExists (DirectedRelation_Bi x y).
  Proof.
    intros x y.
    unfold RelationExists, DirectedRelation_Bi.
    exists x, y. reflexivity.
  Qed.

  (** THEOREM: Relations exist with multi-directional direction. *)
  Theorem relation_exists_with_multidirectional :
    forall (entities : list Entity) (x y : Entity), 
      RelationExists (DirectedRelation_Multi entities x y).
  Proof.
    intros entities x y.
    unfold RelationExists, DirectedRelation_Multi.
    exists x, y. reflexivity.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: DIRECTION INDEPENDENCE                       *)
(*                                                                            *)
(* ========================================================================== *)

  (** 
    THEOREM: Direction does not determine existence.
    Two relations with the same core exist equivalently,
    regardless of their directions.
  *)
  Theorem direction_independent_of_existence :
    forall (src tgt : Entity) (r1 r2 : RelationWithDirection),
      core r1 = mkCoreRelation src tgt ->
      core r2 = mkCoreRelation src tgt ->
      RelationExists r1 <-> RelationExists r2.
  Proof.
    intros src tgt r1 r2 H1 H2.
    unfold RelationExists.
    split; intro H.
    - exists src, tgt. exact H2.
    - exists src, tgt. exact H1.
  Qed.

  (**
    THEOREM: Same core, different directions.
    Demonstrates that direction is truly independent metadata.
  *)
  Theorem same_core_different_directions :
    forall (src tgt : Entity),
      exists (r1 r2 r3 r4 : RelationWithDirection),
        core r1 = core r2 /\
        core r2 = core r3 /\
        core r3 = core r4 /\
        direction r1 <> direction r2 /\
        direction r2 <> direction r3 /\
        direction r3 <> direction r4.
  Proof.
    intros src tgt.
    set (r1 := UndirectedRelation src tgt).
    set (r2 := DirectedRelation_Uni src tgt).
    set (r3 := DirectedRelation_Bi src tgt).
    set (r4 := DirectedRelation_Multi [src; tgt] src tgt).
    exists r1, r2, r3, r4.
    split. { reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    split. { unfold r1, r2. discriminate. }
    split. { unfold r2, r3. discriminate. }
    { unfold r3, r4. discriminate. }
  Qed.

  (** THEOREM: Direction creates relation diversity. *)
  Theorem direction_creates_diversity :
    forall (src tgt : Entity),
      exists (r1 r2 : RelationWithDirection),
        core r1 = core r2 /\
        direction r1 <> direction r2 /\
        RelationExists r1 /\
        RelationExists r2.
  Proof.
    intros src tgt.
    exists (UndirectedRelation src tgt), (DirectedRelation_Uni src tgt).
    split. { reflexivity. }
    split. { discriminate. }
    split.
    - apply relation_exists_without_direction.
    - apply relation_exists_with_unidirectional.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: DIRECTION TYPES                              *)
(*                                                                            *)
(* ========================================================================== *)

  (** Self-relation: entity relates to itself. *)
  Definition SelfRelation (x : Entity) : RelationWithDirection :=
    DirectedRelation_Uni x x.

  (** Other-relation: entity relates to a different entity. *)
  Definition OtherRelation (x y : Entity) : RelationWithDirection :=
    DirectedRelation_Uni x y.

  (** Internal relation: relation within a system of entities. *)
  Definition InternalRelation (system : list Entity) (x y : Entity) 
    : RelationWithDirection :=
    DirectedRelation_Multi system x y.

  (** THEOREM: Self-relations exist. *)
  Theorem self_relation_exists :
    forall (x : Entity), RelationExists (SelfRelation x).
  Proof.
    intro x. unfold SelfRelation. apply relation_exists_with_unidirectional.
  Qed.

  (** THEOREM: Other-relations exist. *)
  Theorem other_relation_exists :
    forall (x y : Entity), RelationExists (OtherRelation x y).
  Proof.
    intros x y. unfold OtherRelation. apply relation_exists_with_unidirectional.
  Qed.

  (** THEOREM: Internal relations exist. *)
  Theorem internal_relation_exists :
    forall (system : list Entity) (x y : Entity),
      RelationExists (InternalRelation system x y).
  Proof.
    intros system x y. unfold InternalRelation. 
    apply relation_exists_with_multidirectional.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: DIRECTION MANIPULATION                       *)
(*                                                                            *)
(* ========================================================================== *)

  (** Extract direction from a relation. *)
  Definition get_direction (r : RelationWithDirection) : option Direction :=
    direction r.

  (** Add direction to a relation. *)
  Definition add_direction (r : RelationWithDirection) (d : Direction) 
    : RelationWithDirection :=
    mkRelationWithDirection (core r) (Some d).

  (** Change direction of a relation. *)
  Definition change_direction (r : RelationWithDirection) (d : Direction) 
    : RelationWithDirection :=
    mkRelationWithDirection (core r) (Some d).

  (** Remove direction from a relation. *)
  Definition remove_direction (r : RelationWithDirection) : RelationWithDirection :=
    mkRelationWithDirection (core r) None.

  (** THEOREM: Adding direction preserves existence. *)
  Theorem add_direction_preserves_existence :
    forall (r : RelationWithDirection) (d : Direction),
      RelationExists r -> RelationExists (add_direction r d).
  Proof.
    intros r d [src [tgt Hcore]].
    unfold RelationExists, add_direction.
    exists src, tgt. simpl. exact Hcore.
  Qed.

  (** THEOREM: Changing direction preserves core. *)
  Theorem change_direction_preserves_core :
    forall (r : RelationWithDirection) (d : Direction),
      core (change_direction r d) = core r.
  Proof.
    intros r d. reflexivity.
  Qed.

  (** THEOREM: Removing direction preserves existence. *)
  Theorem remove_direction_preserves_existence :
    forall (r : RelationWithDirection),
      RelationExists r -> RelationExists (remove_direction r).
  Proof.
    intros r [src [tgt Hcore]].
    unfold RelationExists, remove_direction.
    exists src, tgt. simpl. exact Hcore.
  Qed.

  (** THEOREM: Direction is independent of entities. *)
  Theorem direction_independent_of_entities :
    forall (r : RelationWithDirection),
      RelationExists r ->
      exists (src tgt : Entity) (dir : option Direction),
        core r = mkCoreRelation src tgt /\
        direction r = dir.
  Proof.
    intros r [src [tgt Hcore]].
    exists src, tgt, (direction r).
    split; [exact Hcore | reflexivity].
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: BIDIRECTIONALITY PROPERTIES                  *)
(*                                                                            *)
(* ========================================================================== *)

  (** Two separate unidirectional relations (for comparison). *)
  Definition TwoUnidirectionalRelations (x y : Entity) 
    : RelationWithDirection * RelationWithDirection :=
    (DirectedRelation_Uni x y, DirectedRelation_Uni y x).

  (** One bidirectional relation (for comparison). *)
  Definition OneBidirectionalRelation (x y : Entity) : RelationWithDirection :=
    DirectedRelation_Bi x y.

  (** THEOREM: Bidirectional is distinct from two unidirectional. *)
  Theorem bidirectional_distinct_from_two_uni :
    forall (x y : Entity),
      let (r1, r2) := TwoUnidirectionalRelations x y in
      let r3 := OneBidirectionalRelation x y in
      direction r1 <> direction r3 /\
      direction r2 <> direction r3.
  Proof.
    intros x y.
    unfold TwoUnidirectionalRelations, OneBidirectionalRelation.
    unfold DirectedRelation_Uni, DirectedRelation_Bi.
    simpl. split; discriminate.
  Qed.

  (** THEOREM: Bidirectional relations are symmetric in representation. *)
  Theorem bidirectional_symmetric_representation :
    forall (x y : Entity),
      exists (r : RelationWithDirection),
        direction r = Some (Bidirectional x y) \/
        direction r = Some (Bidirectional y x).
  Proof.
    intros x y.
    exists (DirectedRelation_Bi x y).
    left. reflexivity.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: MULTI-DIRECTIONALITY PROPERTIES              *)
(*                                                                            *)
(* ========================================================================== *)

  (** Multi-directional with specific entity list. *)
  Definition MultiEntityFlow (entities : list Entity) (src tgt : Entity) 
    : RelationWithDirection :=
    DirectedRelation_Multi entities src tgt.

  (** THEOREM: Multi-directional supports arbitrary entity counts. *)
  Theorem multidirectional_arbitrary_entities :
    forall (entities : list Entity) (x y : Entity),
      RelationExists (MultiEntityFlow entities x y).
  Proof.
    intros entities x y.
    unfold MultiEntityFlow. apply relation_exists_with_multidirectional.
  Qed.

  (** THEOREM: Multi-directional with empty list still exists. *)
  Theorem multidirectional_empty_list :
    forall (x y : Entity),
      RelationExists (DirectedRelation_Multi [] x y).
  Proof.
    intros x y. apply relation_exists_with_multidirectional.
  Qed.

  (** THEOREM: Multi-directional distinct from bidirectional. *)
  Theorem multidirectional_distinct_from_bidirectional :
    forall (x y : Entity) (entities : list Entity),
      direction (DirectedRelation_Multi entities x y) <>
      direction (DirectedRelation_Bi x y).
  Proof.
    intros x y entities. simpl. discriminate.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: ORIGIN AND FLOW                              *)
(*                                                                            *)
(* ========================================================================== *)

  (** Extract source as origin. *)
  Definition origin_of_relation (r : RelationWithDirection) : Entity :=
    source (core r).

  (** Extract target as destination. *)
  Definition destination_of_relation (r : RelationWithDirection) : Entity :=
    target (core r).

  (** THEOREM: Self-directed relations have same source and target. *)
  Theorem self_directed_same_endpoints :
    forall (x : Entity),
      origin_of_relation (SelfRelation x) = x /\
      destination_of_relation (SelfRelation x) = x.
  Proof.
    intro x.
    unfold origin_of_relation, destination_of_relation, SelfRelation.
    unfold DirectedRelation_Uni. simpl.
    split; reflexivity.
  Qed.

  (** THEOREM: Other-directed relations have defined endpoints. *)
  Theorem other_directed_has_endpoints :
    forall (x y : Entity),
      exists (src tgt : Entity),
        origin_of_relation (OtherRelation x y) = src /\
        destination_of_relation (OtherRelation x y) = tgt.
  Proof.
    intros x y.
    exists x, y.
    unfold origin_of_relation, destination_of_relation, OtherRelation.
    unfold DirectedRelation_Uni. simpl.
    split; reflexivity.
  Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: CONNECTION TO PROPOSITION 1                 *)
(*                                                                            *)
(* ========================================================================== *)

  (**
    CONNECTION TO UNIVERSAL CONNECTIVITY
    ====================================
    
    Proposition 1 guarantees that every entity in Ux relates to Whole.
    This means every entity can form a directed relation to Whole,
    ensuring no entity is relationally isolated.
  *)

  (** Base relation parameter for connectivity. *)
  Variable R : U -> U -> Prop.

  (** The extended relation from Proposition 1. *)
  Definition R' : Ux -> Ux -> Prop := P1.lift R.

  (** THEOREM: All entities can form directed relations to Whole. *)
  Theorem all_entities_relate_to_Whole :
    forall (x : Ux), R' x Whole.
  Proof.
    intro x. unfold R', Whole. apply P1.to_whole.
  Qed.

  (** THEOREM: Direction can be added to any connectivity relation. *)
  Theorem connectivity_supports_direction :
    forall (x : Ux),
      R' x Whole ->
      RelationExists (DirectedRelation_Uni x Whole).
  Proof.
    intros x _. apply relation_exists_with_unidirectional.
  Qed.

  (** THEOREM: Universal connectivity with direction. *)
  Theorem universal_connectivity_directed :
    forall (x : Ux),
      exists (r : RelationWithDirection),
        origin_of_relation r = x /\
        destination_of_relation r = Whole /\
        direction r = Some (Unidirectional x Whole) /\
        RelationExists r.
  Proof.
    intro x.
    exists (DirectedRelation_Uni x Whole).
    repeat split.
    apply relation_exists_with_unidirectional.
  Qed.

End DirectionTheory.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: P10 MODULE - PUBLIC API                     *)
(*                                                                            *)
(* ========================================================================== *)

(**
  P10: The canonical public API for Proposition 10.
  
  This module provides stable, memorable names for downstream use.
*)

Module P10.

  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)
  
  (** Direction type (parametric over U). *)
  Definition Dir (U : Type) := Direction U.
  
  (** Core relation type. *)
  Definition Core (U : Type) := CoreRelation U.
  
  (** Relation with direction type. *)
  Definition Rel (U : Type) := RelationWithDirection U.
  
  (** Entity type. *)
  Definition Ent (U : Type) := Entity U.
  
  (* ====================================================================== *)
  (*                         Constructors                                   *)
  (* ====================================================================== *)
  
  Definition undirected {U : Type} := @UndirectedRelation U.
  Definition uni {U : Type} := @DirectedRelation_Uni U.
  Definition bi {U : Type} := @DirectedRelation_Bi U.
  Definition multi {U : Type} := @DirectedRelation_Multi U.
  
  Definition self {U : Type} := @SelfRelation U.
  Definition other {U : Type} := @OtherRelation U.
  Definition internal {U : Type} := @InternalRelation U.
  
  (* ====================================================================== *)
  (*                         Accessors                                      *)
  (* ====================================================================== *)
  
  Definition get_dir {U : Type} := @get_direction U.
  Definition origin {U : Type} := @origin_of_relation U.
  Definition dest {U : Type} := @destination_of_relation U.
  
  (* ====================================================================== *)
  (*                         Manipulation                                   *)
  (* ====================================================================== *)
  
  Definition add_dir {U : Type} := @add_direction U.
  Definition change_dir {U : Type} := @change_direction U.
  Definition remove_dir {U : Type} := @remove_direction U.
  
  (* ====================================================================== *)
  (*                        Key Theorems                                    *)
  (* ====================================================================== *)
  
  Definition exists_without_dir {U : Type} := @relation_exists_without_direction U.
  Definition exists_uni {U : Type} := @relation_exists_with_unidirectional U.
  Definition exists_bi {U : Type} := @relation_exists_with_bidirectional U.
  Definition exists_multi {U : Type} := @relation_exists_with_multidirectional U.
  
  Definition dir_independent {U : Type} := @direction_independent_of_existence U.
  Definition dir_diversity {U : Type} := @direction_creates_diversity U.
  
  Definition add_preserves {U : Type} := @add_direction_preserves_existence U.
  Definition remove_preserves {U : Type} := @remove_direction_preserves_existence U.
  
  Definition self_exists {U : Type} := @self_relation_exists U.
  Definition other_exists {U : Type} := @other_relation_exists U.
  Definition internal_exists {U : Type} := @internal_relation_exists U.

End P10.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: HINT DATABASES & TACTICS                    *)
(*                                                                            *)
(* ========================================================================== *)

(** Hints for Proposition 10. *)

#[export] Hint Resolve
  relation_exists_without_direction
  relation_exists_with_unidirectional
  relation_exists_with_bidirectional
  relation_exists_with_multidirectional
  self_relation_exists
  other_relation_exists
  internal_relation_exists
  add_direction_preserves_existence
  remove_direction_preserves_existence
  multidirectional_empty_list
  multidirectional_arbitrary_entities
  : prop10.

#[export] Hint Rewrite
  @change_direction_preserves_core
  : prop10.

(** Tactic to prove relation existence. *)
Ltac prove_rel_exists :=
  match goal with
  | |- RelationExists (UndirectedRelation _ _ _) => 
      apply relation_exists_without_direction
  | |- RelationExists (DirectedRelation_Uni _ _ _) => 
      apply relation_exists_with_unidirectional
  | |- RelationExists (DirectedRelation_Bi _ _ _) => 
      apply relation_exists_with_bidirectional
  | |- RelationExists (DirectedRelation_Multi _ _ _ _) => 
      apply relation_exists_with_multidirectional
  | |- RelationExists (SelfRelation _ _) => 
      apply self_relation_exists
  | |- RelationExists (OtherRelation _ _ _) => 
      apply other_relation_exists
  | |- RelationExists (InternalRelation _ _ _ _) => 
      apply internal_relation_exists
  | |- RelationExists _ => 
      unfold RelationExists; eexists; eexists; reflexivity
  end.

(** Tactic for Proposition 10 automation. *)
Ltac prop10_auto :=
  auto with prop10;
  try prove_rel_exists.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: EXAMPLES                                    *)
(*                                                                            *)
(* ========================================================================== *)

Module DirectionExamples.

  (** Example with nat as base universe. *)
  Section NatExamples.
    
    Let U := nat.
    Let Ux := Entity U.
    Let W := @Whole U.
    Let e := @elem U.
    
    Example undirected_nat_relation :
      RelationExists U (UndirectedRelation U (e 1) (e 2)).
    Proof. prop10_auto. Qed.
    
    Example directed_nat_relation :
      RelationExists U (DirectedRelation_Uni U (e 3) W).
    Proof. prop10_auto. Qed.
    
    Example self_nat_relation :
      RelationExists U (SelfRelation U (e 5)).
    Proof. prop10_auto. Qed.
    
    Example direction_diversity_nat :
      exists r1 r2 : RelationWithDirection U,
        core U r1 = core U r2 /\
        direction U r1 <> direction U r2.
    Proof.
      exists (UndirectedRelation U (e 1) (e 2)).
      exists (DirectedRelation_Uni U (e 1) (e 2)).
      split; [reflexivity | discriminate].
    Qed.
    
    Example all_four_direction_types :
      exists r1 r2 r3 r4 : RelationWithDirection U,
        direction U r1 = None /\
        (exists x y, direction U r2 = Some (Unidirectional U x y)) /\
        (exists x y, direction U r3 = Some (Bidirectional U x y)) /\
        (exists es, direction U r4 = Some (MultiDirectional U es)).
    Proof.
      exists (UndirectedRelation U (e 1) (e 2)).
      exists (DirectedRelation_Uni U (e 1) (e 2)).
      exists (DirectedRelation_Bi U (e 1) (e 2)).
      exists (DirectedRelation_Multi U [e 1; e 2; e 3] (e 1) (e 2)).
      repeat split; try reflexivity.
      - exists (e 1), (e 2). reflexivity.
      - exists (e 1), (e 2). reflexivity.
      - exists [e 1; e 2; e 3]. reflexivity.
    Qed.

  End NatExamples.

End DirectionExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 14: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)
  
  Definition test_undirected : 
    direction nat (UndirectedRelation nat (Some 1) (Some 2)) = None.
  Proof. reflexivity. Qed.
  
  Definition test_unidirectional :
    exists d, direction nat (DirectedRelation_Uni nat (Some 1) (Some 2)) = Some d.
  Proof. eexists. reflexivity. Qed.
  
  Definition test_bidirectional :
    exists d, direction nat (DirectedRelation_Bi nat (Some 1) (Some 2)) = Some d.
  Proof. eexists. reflexivity. Qed.
  
  Definition test_core_preserved :
    core nat (change_direction nat (UndirectedRelation nat (Some 1) (Some 2)) 
                                   (Unidirectional nat (Some 1) (Some 2))) =
    core nat (UndirectedRelation nat (Some 1) (Some 2)).
  Proof. reflexivity. Qed.
  
  Definition test_origin :
    origin_of_relation nat (DirectedRelation_Uni nat (Some 1) (Some 2)) = Some 1.
  Proof. reflexivity. Qed.
  
  Definition test_destination :
    destination_of_relation nat (DirectedRelation_Uni nat (Some 1) (Some 2)) = Some 2.
  Proof. reflexivity. Qed.

End AxiomAudit.

(** Print Assumptions for key theorems. *)
Print Assumptions relation_exists_without_direction.
Print Assumptions relation_exists_with_unidirectional.
Print Assumptions direction_independent_of_existence.
Print Assumptions direction_creates_diversity.
Print Assumptions self_relation_exists.
Print Assumptions add_direction_preserves_existence.
Print Assumptions all_entities_relate_to_Whole.
Print Assumptions universal_connectivity_directed.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (P10):
    P10.Dir U               = Direction U (direction type)
    P10.Core U              = CoreRelation U
    P10.Rel U               = RelationWithDirection U
    P10.Ent U               = Entity U
    
    P10.undirected          = UndirectedRelation
    P10.uni                 = DirectedRelation_Uni
    P10.bi                  = DirectedRelation_Bi
    P10.multi               = DirectedRelation_Multi
    
    P10.self                = SelfRelation
    P10.other               = OtherRelation
    P10.internal            = InternalRelation
    
    P10.get_dir             = get_direction
    P10.origin              = origin_of_relation
    P10.dest                = destination_of_relation
    
    P10.add_dir             = add_direction
    P10.change_dir          = change_direction
    P10.remove_dir          = remove_direction
  
  TYPES:
    Direction U             = Unidirectional | Bidirectional | MultiDirectional
    CoreRelation U          = { source, target : Entity U }
    RelationWithDirection U = { core : CoreRelation; direction : option Direction }
  
  KEY THEOREMS:
    relation_exists_without_direction     : relations exist without direction
    relation_exists_with_unidirectional   : relations exist with uni direction
    direction_independent_of_existence    : direction doesn't affect existence
    direction_creates_diversity           : same core, different directions
    add_direction_preserves_existence     : adding direction preserves existence
    all_entities_relate_to_Whole          : connection to Prop 1
  
  HINT DATABASE:
    prop10      : core lemmas for Proposition 10
    
    Usage: auto with prop10.
  
  TACTICS:
    prove_rel_exists        : prove RelationExists goals
    prop10_auto             : combined automation
  
  CONNECTION TO PROP 1:
    all_entities_relate_to_Whole          : forall x, R' x Whole
    connectivity_supports_direction       : R' x Whole -> exists directed relation
    universal_connectivity_directed       : every entity has directed path to Whole
  
  AXIOM STATUS
  ============
  
  This file uses ZERO AXIOMS beyond Coq's standard library.
  All theorems verify as "Closed under the global context".
  
  COMPILATION
  ===========
  
  Requires: Top__Extensions__Prelude.v, Top__Propositions__Prop_01.v
  
    coqc Top__Extensions__Base.v
    coqc Top__Extensions__WholeCompletion.v
    coqc Top__Extensions__Composition.v
    coqc Top__Extensions__Prelude.v
    coqc Top__Propositions__Prop_01.v
    coqc Top__Propositions__Prop_10.v
*)
