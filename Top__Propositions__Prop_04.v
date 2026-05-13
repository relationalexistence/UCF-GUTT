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
  |          PROPOSITION 04: RELATIONS FORM A RELATIONAL SYSTEM              |
  |                                                                          |
  |                      UCF/GUTT(TM) Formal Verification                    |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-26                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  THEOREM: Relations can be represented as graphs with adjacency tensors  |
  |                                                                          |
  |  "Every relation R(x,y) in the extended universe can be represented      |
  |   as an edge in a graph structure, and this edge corresponds to a        |
  |   non-zero entry in the graph's adjacency tensor."                       |
  |                                                                          |
  |  This builds on Proposition 01 (seriality) to show that:                 |
  |    1. Relations naturally induce graph structures                        |
  |    2. Adjacency tensors correctly encode edge membership                 |
  |    3. Graph dynamics preserve relational structure                       |
  |    4. Relational systems are never empty (via universal connectivity)    |
  |                                                                          |
  |  KEY INSIGHT: Graph representation is CONSTRUCTIVE - we provide explicit |
  |  witness graphs containing any given relation as an edge.                |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Decidable Equality Infrastructure                         |
  |    SECTION 2:  Graph Structure Definition                                |
  |    SECTION 3:  Adjacency Tensor Definition & Correctness                 |
  |    SECTION 4:  Main Theorems (relation_in_graph, representation)         |
  |    SECTION 5:  Graph Dynamics                                            |
  |    SECTION 6:  Universal Connectivity Properties                         |
  |    SECTION 7:  Additional Graph Properties                               |
  |    SECTION 8:  P4 Module - Public API                                    |
  |    SECTION 9:  Hint Databases                                            |
  |    SECTION 10: Tactics                                                   |
  |    SECTION 11: Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Core types: Graph, Vertex, Edge                                   |
  |      - Main theorems: relation_in_graph, relational_system_representation|
  |      - P4 module exports                                                 |
  |      - Hint database: prop4                                              |
  |                                                                          |
  |  DEPENDENCIES:                                                           |
  |    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)        |
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
Require Import List.
Require Import Bool.
Import ListNotations.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: DECIDABLE EQUALITY INFRASTRUCTURE            *)
(*                                                                            *)
(*  The [Class DecEq], its instances ([DecEq_option], [DecEq_nat],            *)
(*  [DecEq_bool], [DecEq_unit]), and [Lemma Ux_eq_dec] (type-class form) are  *)
(*  all inherited from Top__Propositions__Prop_01 (imported above).  They     *)
(*  were previously duplicated in this file; the duplicates were removed to   *)
(*  keep a single canonical definition site for shared utilities.             *)
(*                                                                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: GRAPH STRUCTURE DEFINITION                   *)
(*                                                                            *)
(*  A Graph is a concrete representation of a relational system.              *)
(*  Vertices are elements of the carrier type, edges are pairs.               *)
(*                                                                            *)
(* ========================================================================== *)

Section GraphDefinitions.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** The carrier type for graph vertices. *)
  Definition Vertex := Ux U.

  (** An edge is a directed pair of vertices. *)
  Definition Edge := (Vertex * Vertex)%type.

  (** A Graph consists of a vertex set and an edge set. *)
  Record Graph := mkGraph {
    vertices : list Vertex;
    edges    : list Edge
  }.

  (** Empty graph constructor. *)
  Definition empty_graph : Graph := mkGraph [] [].

  (** Singleton edge graph constructor. *)
  Definition singleton_graph (x y : Vertex) : Graph :=
    mkGraph [x; y] [(x, y)].

  (** Add a vertex to a graph. *)
  Definition add_vertex (G : Graph) (v : Vertex) : Graph :=
    mkGraph (v :: vertices G) (edges G).

  (** Add an edge to a graph. *)
  Definition add_edge (G : Graph) (e : Edge) : Graph :=
    mkGraph (vertices G) (e :: edges G).

  (** Check if a vertex is in the graph. *)
  Definition has_vertex (G : Graph) (v : Vertex) : Prop :=
    In v (vertices G).

  (** Check if an edge is in the graph. *)
  Definition has_edge (G : Graph) (e : Edge) : Prop :=
    In e (edges G).

  (** Vertex count. *)
  Definition vertex_count (G : Graph) : nat := length (vertices G).

  (** Edge count. *)
  Definition edge_count (G : Graph) : nat := length (edges G).

End GraphDefinitions.

Arguments Vertex U : clear implicits.
Arguments Edge U : clear implicits.
Arguments Graph U : clear implicits.
Arguments mkGraph {U}.
Arguments vertices {U}.
Arguments edges {U}.
Arguments empty_graph {U}.
Arguments singleton_graph {U}.
Arguments add_vertex {U}.
Arguments add_edge {U}.
Arguments has_vertex {U}.
Arguments has_edge {U}.
Arguments vertex_count {U}.
Arguments edge_count {U}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: ADJACENCY TENSOR DEFINITION & CORRECTNESS    *)
(*                                                                            *)
(*  The adjacency tensor maps vertex pairs to {0, 1}, encoding edge presence. *)
(*  This is CONSTRUCTIVE: we can compute the tensor for any concrete graph.   *)
(*                                                                            *)
(* ========================================================================== *)

Section AdjacencyTensor.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Boolean edge membership check. *)
  Definition edge_memberb (G : Graph U) (x y : Ux U) : bool :=
    existsb (fun p : Edge U =>
      match p with
      | (x', y') =>
          andb (if Ux_eq_dec x x' then true else false)
               (if Ux_eq_dec y y' then true else false)
      end) (edges G).

  (** The adjacency tensor: 1 if (x,y) is an edge, 0 otherwise. *)
  Definition AdjacencyTensor (G : Graph U) (x y : Ux U) : nat :=
    if edge_memberb G x y then 1 else 0.

  (** Core lemma: existsb reflects actual membership. *)
  Lemma existsb_edge_correct : forall (G : Graph U) (x y : Ux U),
    In (x, y) (edges G) ->
    edge_memberb G x y = true.
  Proof.
    intros G x y Hin.
    unfold edge_memberb.
    induction (edges G) as [| [x' y'] es IH].
    - (* Empty list case *)
      inversion Hin.
    - (* Cons case *)
      simpl in Hin.
      destruct Hin as [Heq | Hin'].
      + (* First element: (x', y') = (x, y) *)
        simpl.
        injection Heq as Hx Hy. subst x' y'.
        destruct (Ux_eq_dec x x) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
        destruct (Ux_eq_dec y y) as [_ | Hneq]; [| exfalso; apply Hneq; reflexivity].
        simpl. reflexivity.
      + (* Later in list *)
        simpl.
        destruct (Ux_eq_dec x x'); destruct (Ux_eq_dec y y'); simpl.
        * (* Both equal: left side of || is true *)
          reflexivity.
        * (* x equal, y not equal: use IH *)
          apply IH. exact Hin'.
        * (* x not equal: use IH *)
          apply IH. exact Hin'.
        * (* Neither equal: use IH *)
          apply IH. exact Hin'.
  Qed.

  (** The adjacency tensor correctly reflects edge membership. *)
  Theorem adjacency_tensor_correct : forall (G : Graph U) (x y : Ux U),
    In (x, y) (edges G) -> AdjacencyTensor G x y = 1.
  Proof.
    intros G x y Hin.
    unfold AdjacencyTensor.
    rewrite (existsb_edge_correct G x y Hin).
    reflexivity.
  Qed.

  (** Non-edges have tensor value 0. *)
  Theorem adjacency_tensor_non_edge : forall (G : Graph U) (x y : Ux U),
    ~ In (x, y) (edges G) -> AdjacencyTensor G x y = 0.
  Proof.
    intros G x y Hnot.
    unfold AdjacencyTensor.
    (* If existsb returns true, we get a contradiction *)
    destruct (edge_memberb G x y) eqn:Hmem.
    - (* Contradiction case: edge_memberb true but edge not in list *)
      exfalso.
      unfold edge_memberb in Hmem.
      apply existsb_exists in Hmem.
      destruct Hmem as [[x' y'] [Hin Hcheck]].
      destruct (Ux_eq_dec x x') as [Hxeq | Hxneq]; [| discriminate].
      destruct (Ux_eq_dec y y') as [Hyeq | Hyneq]; [| discriminate].
      subst x' y'.
      apply Hnot. exact Hin.
    - reflexivity.
  Qed.

  (** Tensor reflects membership: iff characterization. *)
  Theorem adjacency_tensor_iff : forall (G : Graph U) (x y : Ux U),
    AdjacencyTensor G x y = 1 <-> In (x, y) (edges G).
  Proof.
    intros G x y. split.
    - intro Htensor.
      unfold AdjacencyTensor in Htensor.
      destruct (edge_memberb G x y) eqn:Hmem.
      + (* edge_memberb is true *)
        unfold edge_memberb in Hmem.
        apply existsb_exists in Hmem.
        destruct Hmem as [[x' y'] [Hin Hcheck]].
        destruct (Ux_eq_dec x x') as [Hxeq | Hxneq]; [| discriminate].
        destruct (Ux_eq_dec y y') as [Hyeq | Hyneq]; [| discriminate].
        subst x' y'. exact Hin.
      + (* edge_memberb is false: contradiction *)
        discriminate.
    - apply adjacency_tensor_correct.
  Qed.

End AdjacencyTensor.

Arguments edge_memberb {U} {HU}.
Arguments AdjacencyTensor {U} {HU}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: MAIN THEOREMS                                *)
(*                                                                            *)
(*  Core results showing relations form relational systems.                   *)
(*                                                                            *)
(* ========================================================================== *)

Section MainTheorems.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    THEOREM: Every R'-relation can be represented as a graph edge.

    This is CONSTRUCTIVE: we build a minimal witness graph containing
    exactly the related pair as an edge.
  *)
  Theorem relation_in_graph :
    forall (x y : Ux U), R_prime R x y ->
    exists G : Graph U, In (x, y) (edges G).
  Proof.
    intros x y HR.
    (* Construct minimal witness graph *)
    exists (singleton_graph x y).
    simpl. left. reflexivity.
  Qed.

  (**
    MAIN THEOREM: Relational System Representation

    For any R'-related pair (x,y), there exists:
    - A graph G containing (x,y) as an edge
    - The adjacency tensor correctly encodes this edge

    This establishes that relations form representable relational systems.
  *)
  Theorem relational_system_representation :
    forall (x y : Ux U), R_prime R x y ->
    exists G : Graph U,
      In (x, y) (edges G) /\ AdjacencyTensor G x y = 1.
  Proof.
    intros x y HR.
    destruct (relation_in_graph x y HR) as [G Hedge].
    exists G. split.
    - exact Hedge.
    - apply adjacency_tensor_correct. exact Hedge.
  Qed.

End MainTheorems.

(**
  Constructive witness extraction: returns a Graph for any related pair.
  This is defined outside the section since it doesn't depend on R.
*)
Definition witness_graph {U : Type} `{HU : DecEq U} (x y : Ux U) : Graph U :=
  singleton_graph x y.

Section WitnessCorrectness.
  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    The witness graph correctly represents the relation.
  *)
  Theorem witness_graph_correct :
    forall (x y : Ux U), R_prime R x y ->
    In (x, y) (edges (witness_graph x y)) /\ AdjacencyTensor (witness_graph x y) x y = 1.
  Proof.
    intros x y HR. split.
    - simpl. left. reflexivity.
    - apply adjacency_tensor_correct. simpl. left. reflexivity.
  Qed.

  (** Sigma-type version for extraction. *)
  Definition relational_system_representation_sigma :
    forall (x y : Ux U), R_prime R x y ->
    { G : Graph U | In (x, y) (edges G) /\ AdjacencyTensor G x y = 1 }.
  Proof.
    intros x y HR.
    exists (singleton_graph x y). split.
    - simpl. left. reflexivity.
    - apply adjacency_tensor_correct. simpl. left. reflexivity.
  Defined.

End WitnessCorrectness.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: GRAPH DYNAMICS                               *)
(*                                                                            *)
(*  Dynamics are transformations on graphs that preserve structure.           *)
(*  The identity is the simplest edge-preserving transformation.              *)
(*                                                                            *)
(* ========================================================================== *)

Section GraphDynamics.

  Context {U : Type}.

  (** Type of graph dynamics (graph transformations). *)
  Definition Dynamics := Graph U -> Graph U.

  (** The identity dynamics: trivially preserves all structure. *)
  Definition id_dynamics : Dynamics := fun G => G.

  (** A dynamics respects relations if it preserves edges. *)
  Definition respects_relations (f : Dynamics) : Prop :=
    forall G x y, In (x, y) (edges G) -> In (x, y) (edges (f G)).

  (** Identity dynamics respects relations. *)
  Theorem id_dynamics_respects : respects_relations id_dynamics.
  Proof.
    unfold respects_relations, id_dynamics.
    intros G x y H. exact H.
  Qed.

  (** A dynamics preserves vertices if it keeps the vertex set. *)
  Definition preserves_vertices (f : Dynamics) : Prop :=
    forall G, vertices (f G) = vertices G.

  (** Identity dynamics preserves vertices. *)
  Theorem id_dynamics_preserves_vertices : preserves_vertices id_dynamics.
  Proof.
    unfold preserves_vertices, id_dynamics.
    intro G. reflexivity.
  Qed.

  (** Composition of dynamics. *)
  Definition compose_dynamics (f g : Dynamics) : Dynamics :=
    fun G => f (g G).

  (** Composed dynamics preserve relations if both components do. *)
  Theorem compose_respects_relations :
    forall f g, respects_relations f -> respects_relations g ->
    respects_relations (compose_dynamics f g).
  Proof.
    intros f g Hf Hg.
    unfold respects_relations, compose_dynamics.
    intros G x y Hin.
    apply Hf. apply Hg. exact Hin.
  Qed.

End GraphDynamics.

Arguments Dynamics U : clear implicits.
Arguments id_dynamics {U}.
Arguments respects_relations {U}.
Arguments preserves_vertices {U}.
Arguments compose_dynamics {U}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: UNIVERSAL CONNECTIVITY PROPERTIES            *)
(*                                                                            *)
(*  Properties derived from Proposition 01's seriality.                       *)
(*                                                                            *)
(* ========================================================================== *)

Section UniversalConnectivity.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    Universal connectivity: Every entity relates to at least one other.

    This follows directly from Proposition 01 (seriality via Whole-completion).
  *)
  Theorem universal_connectivity :
    forall x : Ux U, exists y : Ux U, R_prime R x y.
  Proof.
    intro x. apply proposition_01.
  Qed.

  (**
    Relational systems are never empty: every entity participates in
    at least one edge of some graph.
  *)
  Theorem relational_system_nonempty :
    forall x : Ux U, exists G : Graph U,
      vertices G <> [] /\ (exists y, In (x, y) (edges G) \/ In (y, x) (edges G)).
  Proof.
    intro x.
    destruct (universal_connectivity x) as [y Hxy].
    exists (singleton_graph x y).
    split.
    - simpl. discriminate.
    - exists y. left. simpl. left. reflexivity.
  Qed.

  (**
    Every entity has a graph representation via Whole.
  *)
  Theorem entity_has_graph_via_Whole :
    forall x : Ux U, exists G : Graph U,
      In (x, Whole) (edges G) /\ AdjacencyTensor G x Whole = 1.
  Proof.
    intro x.
    exists (singleton_graph x Whole). split.
    - simpl. left. reflexivity.
    - apply adjacency_tensor_correct. simpl. left. reflexivity.
  Qed.

  (**
    No isolated entities: there are no vertices with zero edges.
  *)
  Theorem no_isolated_entities :
    ~ exists x : Ux U, forall y : Ux U, ~ R_prime R x y.
  Proof.
    intro Hisolated.
    destruct Hisolated as [x Hno_edges].
    destruct (universal_connectivity x) as [y Hxy].
    apply (Hno_edges y). exact Hxy.
  Qed.

End UniversalConnectivity.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: ADDITIONAL GRAPH PROPERTIES                  *)
(*                                                                            *)
(* ========================================================================== *)

Section AdditionalProperties.

  Context {U : Type}.
  Context `{HU : DecEq U}.

  (** Graph union: combines vertices and edges from two graphs. *)
  Definition graph_union (G1 G2 : Graph U) : Graph U :=
    mkGraph (vertices G1 ++ vertices G2) (edges G1 ++ edges G2).

  (** Union preserves edges from both graphs. *)
  Lemma union_preserves_edges_left :
    forall G1 G2 x y, In (x, y) (edges G1) -> In (x, y) (edges (graph_union G1 G2)).
  Proof.
    intros G1 G2 x y H.
    unfold graph_union. simpl.
    apply in_or_app. left. exact H.
  Qed.

  Lemma union_preserves_edges_right :
    forall G1 G2 x y, In (x, y) (edges G2) -> In (x, y) (edges (graph_union G1 G2)).
  Proof.
    intros G1 G2 x y H.
    unfold graph_union. simpl.
    apply in_or_app. right. exact H.
  Qed.

  (** Subgraph relation. *)
  Definition is_subgraph (G1 G2 : Graph U) : Prop :=
    (forall v, In v (vertices G1) -> In v (vertices G2)) /\
    (forall e, In e (edges G1) -> In e (edges G2)).

  (** Empty graph is a subgraph of any graph. *)
  Lemma empty_subgraph : forall G, is_subgraph empty_graph G.
  Proof.
    intro G. split; intros; inversion H.
  Qed.

  (** Any graph is a subgraph of itself. *)
  Lemma subgraph_refl : forall G, is_subgraph G G.
  Proof.
    intro G. split; intros; exact H.
  Qed.

  (** Subgraph is transitive. *)
  Lemma subgraph_trans : forall G1 G2 G3,
    is_subgraph G1 G2 -> is_subgraph G2 G3 -> is_subgraph G1 G3.
  Proof.
    intros G1 G2 G3 [Hv12 He12] [Hv23 He23]. split.
    - intros v Hv. apply Hv23. apply Hv12. exact Hv.
    - intros e He. apply He23. apply He12. exact He.
  Qed.

End AdditionalProperties.

Arguments graph_union {U}.
Arguments is_subgraph {U}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: P4 MODULE - PUBLIC API                       *)
(*                                                                            *)
(* ========================================================================== *)

Module P4.

  (* Types *)
  Definition vertex (U : Type) := Vertex U.
  Definition edge (U : Type) := Edge U.
  Definition graph (U : Type) := Graph U.
  Definition dynamics (U : Type) := Dynamics U.

  (* Constructors *)
  Definition empty {U : Type} := @empty_graph U.
  Definition singleton {U : Type} := @singleton_graph U.
  Definition witness {U : Type} `{HU : DecEq U} := @witness_graph U HU.

  (* Graph operations *)
  Definition add_v {U : Type} := @add_vertex U.
  Definition add_e {U : Type} := @add_edge U.
  Definition union {U : Type} := @graph_union U.

  (* Adjacency tensor *)
  Definition tensor {U : Type} `{HU : DecEq U} := @AdjacencyTensor U HU.
  Definition tensor_correct {U : Type} `{HU : DecEq U} := @adjacency_tensor_correct U HU.
  Definition tensor_iff {U : Type} `{HU : DecEq U} := @adjacency_tensor_iff U HU.

  (* Core theorems - note: these require a relation R parameter *)
  Definition rel_in_graph {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    relation_in_graph R.
  Definition representation {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    relational_system_representation R.
  Definition connectivity {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    universal_connectivity R.
  Definition nonempty {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    relational_system_nonempty R.
  Definition no_isolated {U : Type} `{HU : DecEq U} (R : U -> U -> Prop) :=
    no_isolated_entities R.

  (* Dynamics *)
  Definition id_dyn {U : Type} := @id_dynamics U.
  Definition id_respects {U : Type} := @id_dynamics_respects U.
  Definition compose_dyn {U : Type} := @compose_dynamics U.

  (* Subgraph *)
  Definition subgraph {U : Type} := @is_subgraph U.
  Definition subgraph_refl {U : Type} := @subgraph_refl U.
  Definition subgraph_trans {U : Type} := @subgraph_trans U.

End P4.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: HINT DATABASES                               *)
(*                                                                            *)
(* ========================================================================== *)

Create HintDb prop4.

#[export] Hint Resolve
  adjacency_tensor_correct
  id_dynamics_respects
  id_dynamics_preserves_vertices
  compose_respects_relations
  subgraph_refl
  empty_subgraph
  union_preserves_edges_left
  union_preserves_edges_right
  : prop4.

#[export] Hint Extern 1 (exists _ : Graph _, In (_, _) (edges _)) =>
  eexists; simpl; left; reflexivity : prop4.

#[export] Hint Extern 1 (In (_, _) (edges (singleton_graph _ _))) =>
  simpl; left; reflexivity : prop4.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: TACTICS                                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Prove that a relation is represented in a graph. *)
Ltac prove_representation :=
  match goal with
  | |- exists G : Graph _, In (?x, ?y) (edges G) /\ AdjacencyTensor G ?x ?y = 1 =>
      exists (singleton_graph x y); split;
      [ simpl; left; reflexivity
      | apply adjacency_tensor_correct; simpl; left; reflexivity ]
  | |- exists G : Graph _, In (?x, ?y) (edges G) =>
      exists (singleton_graph x y); simpl; left; reflexivity
  end.

(** Tactic to handle edge membership proofs. *)
Ltac solve_edge_in :=
  match goal with
  | |- In (?x, ?y) (edges (singleton_graph ?x ?y)) =>
      simpl; left; reflexivity
  | |- In ?e (edges (graph_union _ _)) =>
      apply union_preserves_edges_left + apply union_preserves_edges_right; solve_edge_in
  | |- In ?e (_ :: _) =>
      simpl; (left; reflexivity) + (right; solve_edge_in)
  end.

(** Combined automation. *)
Ltac prop4_auto :=
  auto with prop4 prop1;
  try prove_representation;
  try solve_edge_in.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: AXIOM AUDIT                                 *)
(*                                                                            *)
(*  Verification that this file uses ZERO AXIOMS.                             *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)

  Definition test_empty_graph : @vertices nat empty_graph = [].
  Proof. reflexivity. Qed.

  Definition test_singleton_vertices : @vertices nat (singleton_graph (elem 1) (elem 2)) = [elem 1; elem 2].
  Proof. reflexivity. Qed.

  Definition test_singleton_edges : @edges nat (singleton_graph (elem 1) (elem 2)) = [(elem 1, elem 2)].
  Proof. reflexivity. Qed.

  Definition test_witness_graph : @witness_graph nat _ (elem 3) (elem 5) = singleton_graph (elem 3) (elem 5).
  Proof. reflexivity. Qed.

  Definition test_id_dynamics : @id_dynamics nat (singleton_graph (elem 1) (elem 2)) = singleton_graph (elem 1) (elem 2).
  Proof. reflexivity. Qed.

  (**
    Key test: main theorems compile without axioms.

    relation_in_graph depends only on:
    - Prop_01 (which is axiom-free)
    - Decidable equality (typeclass, not axiom)
  *)
  Definition test_relation_in_graph_compiles :
    forall (x y : Ux nat), R_prime lt x y -> exists G : Graph nat, In (x, y) (edges G).
  Proof.
    intros x y H.
    apply (relation_in_graph lt).
    exact H.
  Qed.

  Definition test_representation_compiles :
    forall (x y : Ux nat), R_prime lt x y ->
    exists G : Graph nat, In (x, y) (edges G) /\ AdjacencyTensor G x y = 1.
  Proof.
    intros x y H.
    apply (relational_system_representation lt).
    exact H.
  Qed.

  Definition test_connectivity_compiles :
    forall x : Ux nat, exists y : Ux nat, R_prime lt x y.
  Proof.
    intro x. apply (universal_connectivity lt).
  Qed.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============

  PUBLIC API MODULE (P4):
    P4.graph U                = Graph U (graph type)
    P4.vertex U               = Vertex U (alias for Ux U)
    P4.edge U                 = Edge U (pair of vertices)
    P4.singleton x y          = singleton_graph x y
    P4.witness R x y          = witness_graph R x y
    P4.tensor G x y           = AdjacencyTensor G x y
    P4.representation R       = relational_system_representation R
    P4.connectivity R         = universal_connectivity R
    P4.id_dyn                 = id_dynamics
    P4.subgraph G1 G2         = is_subgraph G1 G2

  TYPES:
    Vertex U                  = Ux U (extended carrier)
    Edge U                    = (Vertex U * Vertex U)
    Graph U                   = record with vertices and edges
    Dynamics U                = Graph U -> Graph U

  CONSTRUCTORS:
    empty_graph               = graph with no vertices or edges
    singleton_graph x y       = minimal graph with edge (x,y)
    witness_graph R x y       = graph witnessing R'(x,y)
    add_vertex G v            = add vertex v to G
    add_edge G e              = add edge e to G
    graph_union G1 G2         = combine two graphs

  ADJACENCY TENSOR:
    AdjacencyTensor G x y     = 1 if (x,y) in edges, 0 otherwise
    adjacency_tensor_correct  : In (x,y) (edges G) -> tensor = 1
    adjacency_tensor_iff      : tensor = 1 <-> In (x,y) (edges G)

  MAIN THEOREMS:
    relation_in_graph:
      forall x y, R_prime R x y -> exists G, In (x,y) (edges G)

    relational_system_representation:
      forall x y, R_prime R x y -> exists G, In (x,y) (edges G) /\ tensor = 1

    universal_connectivity:
      forall x, exists y, R_prime R x y  (from Prop 01)

    relational_system_nonempty:
      forall x, exists G, vertices G <> [] /\ (exists y, edge involving x)

    no_isolated_entities:
      ~ exists x, forall y, ~ R_prime R x y

  DYNAMICS:
    id_dynamics               = identity transformation
    respects_relations f      = f preserves edges
    preserves_vertices f      = f preserves vertex set
    compose_dynamics f g      = sequential composition
    id_dynamics_respects      : respects_relations id_dynamics
    compose_respects_relations: both respect => composition respects

  SUBGRAPH:
    is_subgraph G1 G2         = G1's vertices/edges are in G2
    subgraph_refl             : G is subgraph of G
    subgraph_trans            : subgraph is transitive
    empty_subgraph            : empty_graph is subgraph of any G

  TYPECLASS:
    DecEq A                   : decidable equality on A
    DecEq_option              : A decidable => option A decidable
    DecEq_nat, DecEq_bool     : standard instances

  HINT DATABASE:
    prop4                     : automation hints for Prop 4

    Usage: auto with prop4. / prop4_auto.

  TACTICS:
    prove_representation      : prove graph representation goals
    solve_edge_in             : prove edge membership
    prop4_auto                : combined automation

  PHILOSOPHICAL SIGNIFICANCE
  ==========================

  This proof demonstrates that:

  1. Relations are REPRESENTABLE: Every relation R(x,y) corresponds to
     concrete graph structure, not just abstract logical propositions.

  2. Representation is CONSTRUCTIVE: We provide explicit witness graphs,
     not just existence proofs. This enables computational applications.

  3. Tensors ENCODE relations: The adjacency tensor provides a numeric
     encoding of relational structure, bridging logic and linear algebra.

  4. Dynamics PRESERVE structure: Graph transformations maintain the
     relational content, modeling how systems evolve while preserving
     their essential connectivity.

  5. Universal CONNECTIVITY holds: By Proposition 01, every entity
     participates in at least one relation (to Whole), so relational
     systems are never empty and have no isolated components.

  COMPILATION
  ===========

  This file depends on:
    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)

  Build order:
    1. Top__Extensions__Base.v
    2. Top__Extensions__WholeCompletion.v
    3. Top__Extensions__Composition.v
    4. Top__Extensions__Prelude.v
    5. Top__Propositions__Prop_01.v
    6. Top__Propositions__Prop_04.v (this file)

  AXIOM STATUS
  ============

  This file uses ZERO AXIOMS. The DecEq typeclass is not an axiom -
  it's a constraint that must be satisfied by concrete instantiation.
  All proofs are fully constructive.

  Run `Print Assumptions relational_system_representation.` to verify.
  Expected output: Closed under the global context.
*)
