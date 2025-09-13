(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
  See LICENSE, NOTICE, and TRADEMARKS in the repo root.

  Notes/overview: notes/prop4_nested_relational_tensors.md
*)

Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Arith.

(* ---------- Proposition 4: Relations Form a Relational System (Nested) ---------- *)

(* Let E be a set of entities, with decidable equality *)
Parameter E : Type.
Parameter eq_dec : forall (x y : E), {x = y} + {x <> y}.

(* A relation on entities *)
Parameter R : E -> E -> Prop.

(* Basic graph: vertices and edges (ordered pairs) *)
Record Graph := {
  vertices : list E;
  edges : list (E * E)
}.

(* Assumption: for any R x y, there exists some Graph containing edge (x,y). *)
Axiom relation_in_graph :
  forall (x y : E), R x y -> exists G : Graph, In (x,y) (edges G).

(* AdjacencyTensor(G)(x,y) = 1 iff (x,y) ∈ edges(G), else 0 *)
Definition AdjacencyTensor (G : Graph) : E -> E -> nat :=
  fun x y =>
    if existsb
         (fun p =>
            match p with
            | (x', y') =>
              andb (if eq_dec x x' then true else false)
                   (if eq_dec y y' then true else false)
            end)
         (edges G)
    then 1 else 0.

(* Helper: existsb is true if (x,y) is actually in the list *)
Lemma existsb_in : forall (l: list (E * E)) (x y: E),
  In (x, y) l ->
  existsb
    (fun p =>
       match p with
       | (x', y') =>
         andb (if eq_dec x x' then true else false)
              (if eq_dec y y' then true else false)
       end) l = true.
Proof.
  induction l as [| p l' IH]; intros.
  - inversion H.
  - simpl in H. simpl.
    destruct H as [H | H].
    + destruct p as [x' y'].
      destruct (if eq_dec x x' then true else false) eqn:Heq1.
      * destruct (if eq_dec y y' then true else false) eqn:Heq2; [reflexivity|].
        exfalso. apply Heq2. destruct (eq_dec x x'); [assumption|contradiction].
      * exfalso. destruct (eq_dec x x'); [congruence|contradiction].
    + apply IH; assumption.
Qed.

Lemma adjacency_tensor_correct : forall (G: Graph) (x y: E),
  In (x,y) (edges G) -> AdjacencyTensor G x y = 1.
Proof.
  intros G x y H.
  unfold AdjacencyTensor.
  apply existsb_in; assumption.
Qed.

(* --- Dynamics placeholder: an update f that preserves existing edges *)
Parameter f : Graph -> Graph.
Axiom dynamic_respects_relations :
  forall (G : Graph) (x y : E),
    In (x,y) (edges G) -> In (x,y) (edges (f G)).

(* ---------- Nested Relational Tensors ---------- *)

(* A NestedGraph has an outer graph and (optionally) an inner graph per edge *)
Record NestedGraph := {
  outer_graph : Graph;
  inner_graph : (E * E) -> option Graph
}.

(* NestedAdjacencyTensor adds the inner contribution if present *)
Definition NestedAdjacencyTensor (NG : NestedGraph) : E -> E -> nat :=
  fun x y =>
    let base := AdjacencyTensor (outer_graph NG) x y in
    base +
    match inner_graph NG (x,y) with
    | Some G_inner => AdjacencyTensor G_inner x y
    | None => 0
    end.

(* A simple existence axiom for nesting: we can always choose None for the inner graph *)
Axiom nested_relation_in_graph :
  forall (x y : E), R x y ->
    exists NG : NestedGraph,
      In (x,y) (edges (outer_graph NG)) /\ inner_graph NG (x,y) = None.

(* The main theorem: nested representation exists and yields tensor value 1 *)
Theorem nested_relational_system_representation :
  forall (x y : E), R x y ->
    exists NG : NestedGraph,
      In (x,y) (edges (outer_graph NG)) /\
      NestedAdjacencyTensor NG x y = 1.
Proof.
  intros x y H.
  destruct (nested_relation_in_graph x y H) as [NG [H_edge H_inner]].
  exists NG; split; [assumption|].
  unfold NestedAdjacencyTensor. rewrite H_inner. simpl.
  rewrite Nat.add_0_r. apply adjacency_tensor_correct; assumption.
Qed.

(* For developer curiosity: show the (large) proof term *)
(* Print nested_relational_system_representation. *)
