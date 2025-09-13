(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

(* ---------- Proposition 4: Relations Form a Relational System ---------- *)

Require Import List.
Import ListNotations.
Require Import Bool.

(* Let E be a set of entities. Assume decidable equality for E. *)
Parameter E : Type.
Parameter eq_dec : forall (x y : E), {x = y} + {x <> y}.

(* A relation on entities. *)
Parameter R : E -> E -> Prop.

(* A Graph represents a relational system. *)
Record Graph := {
  vertices : list E;
  edges    : list (E * E)
}.

(* Assumption: Every relation R x y is represented by an edge (x,y) in some graph. *)
Axiom relation_in_graph :
  forall (x y : E), R x y -> exists G : Graph, In (x,y) (edges G).

(* --- Adjacency Tensor Definition --- *)
(* 1 if (x,y) is an edge of G, else 0. *)
Definition AdjacencyTensor (G : Graph) : E -> E -> nat :=
  fun x y =>
    if existsb (fun p =>
      match p with
      | (x', y') =>
          if andb (if eq_dec x x' then true else false)
                  (if eq_dec y y' then true else false)
          then true else false
      end) (edges G)
    then 1 else 0.

(* --- Lemma: If (x,y) is an edge in G, then AdjacencyTensor G x y = 1 --- *)
Lemma existsb_in : forall (l: list (E * E)) (x y: E),
  In (x, y) l ->
  existsb (fun p =>
    match p with
    | (x', y') =>
        if andb (if eq_dec x x' then true else false)
                (if eq_dec y y' then true else false)
        then true else false
    end) l = true.
Proof.
  induction l as [| p l' IH]; intros.
  - inversion H.
  - simpl in H. simpl.
    destruct H as [H | H].
    + destruct p as [x' y'].
      destruct (if eq_dec x x' then true else false) eqn:Heq1.
      * destruct (if eq_dec y y' then true else false) eqn:Heq2.
        { reflexivity. }
        { exfalso. apply Heq2.
          destruct (eq_dec x x'); [assumption | contradiction]. }
      * exfalso. destruct (eq_dec x x'); [congruence | contradiction].
    + apply IH; assumption.
Qed.

Lemma adjacency_tensor_correct : forall (G: Graph) (x y: E),
  In (x,y) (edges G) -> AdjacencyTensor G x y = 1.
Proof.
  intros G x y H.
  unfold AdjacencyTensor.
  apply existsb_in.
  assumption.
Qed.

(* --- Optional dynamics placeholder --- *)
Parameter f : Graph -> Graph.
Axiom dynamic_respects_relations :
  forall (G : Graph) (x y : E),
    In (x,y) (edges G) -> In (x,y) (edges (f G)).

(* --- Theorem: Relational System Representation --- *)
Theorem relational_system_representation :
  forall (x y : E), R x y ->
  exists G : Graph,
    In (x,y) (edges G) /\ AdjacencyTensor G x y = 1.
Proof.
  intros x y H.
  apply relation_in_graph in H.
  destruct H as [G H_edge].
  exists G; split; [assumption|].
  now apply adjacency_tensor_correct.
Qed.

(* Tip (interactive): Print relational_system_representation. *)
