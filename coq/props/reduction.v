(* proofs/reduction.v
   - Part A: Prop1 (Connectivity) inlined
   - Part B: Free/Forgetful pattern between 0/1 graphs and weighted relations
   Pointwise proofs; no 'extensionality' and no fragile ltb rewrites. *)

(* ---------- Part A: Connectivity (Prop1) inline ---------- *)

(* Basic types and relations for the logical (Prop) layer *)
Parameter E : Type.               (* Elements *)
Parameter R : E -> E -> Prop.     (* Relation over E *)

(* Prop 1: Connectivity - Every element relates to something *)
Definition Connectivity : Prop :=
  forall x : E, exists y : E, R x y.

(* Axiom (may later be replaced by a proof in specific models) *)
Axiom Connectivity_Holds : Connectivity.

(* Export a convenient theorem alias *)
Theorem Connectivity_Exists : forall x : E, exists y : E, R x y.
Proof. apply Connectivity_Holds. Qed.

(* (Optional helper: no isolates) *)
Lemma No_Isolates : forall x:E, ~ (forall y:E, ~ R x y).
Proof.
  intros x Hnone.
  destruct (Connectivity_Exists x) as [y Hy].
  specialize (Hnone y). tauto.
Qed.

(* ---------- Part B: Weighted/Boolean relations (computational layer) ---------- *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Set Implicit Arguments.

Definition RelObj := Type.
Definition WRel (A B:RelObj) := A -> B -> nat.   (* weighted relation *)
Definition BRel (A B:RelObj) := A -> B -> bool.  (* 0/1 graph *)

(* Forgetful U: weighted -> 0/1 (true iff weight > 0) *)
Definition U {A B} (R:WRel A B) : BRel A B :=
  fun x y => Nat.ltb 0 (R x y).

(* Free F: 0/1 -> weighted (true ↦ 1, false ↦ 0) *)
Definition F {A B} (G:BRel A B) : WRel A B :=
  fun x y => if G x y then 1 else 0.

(* 1) U ∘ F = id on 0/1 morphisms (pointwise form) *)
Lemma U_F_id_pt {A B} (G:BRel A B) :
  forall x y, U (F G) x y = G x y.
Proof.
  intros x y. unfold U, F.
  destruct (G x y); simpl.
  - (* true  *) reflexivity.   (* Nat.ltb 0 1 = true by computation *)
  - (* false *) reflexivity.   (* Nat.ltb 0 0 = false by computation *)
Qed.

(* 2) F ∘ U is pointwise ≤ id on weighted morphisms (minimal enrichment) *)
Lemma F_U_le {A B} (R:WRel A B) :
  forall x y, F (U R) x y <= R x y.
Proof.
  intros x y. unfold F, U.
  destruct (Nat.ltb 0 (R x y)) eqn:H.
  - (* true: weight > 0 ⇒ 1 ≤ weight *)
    apply Nat.ltb_lt in H. simpl; lia.
  - (* false: weight = 0 ⇒ 0 ≤ weight *)
    apply Nat.ltb_ge in H. simpl; lia.
Qed.

(* “Adjunction-like” helpers as pointwise statements *)
Definition to_bool  {A B} (f:WRel A B) : BRel A B := U f.
Definition from_bool{A B} (g:BRel A B) : WRel A B := F g.

Lemma to_from_roundtrip_pt {A B} (g:BRel A B) :
  forall x y, to_bool (from_bool g) x y = g x y.
Proof.
  intros x y. unfold to_bool, from_bool. apply U_F_id_pt.
Qed.

Lemma from_to_minimal_pt {A B} (f:WRel A B) :
  forall x y, from_bool (to_bool f) x y <= f x y.
Proof.
  intros x y. unfold to_bool, from_bool. apply F_U_le.
Qed.

(* Triangle-style laws, stated pointwise *)
Lemma triangle_1_pt {A B} (g:BRel A B) :
  forall x y, to_bool (from_bool g) x y = g x y.
Proof. apply to_from_roundtrip_pt. Qed.

Lemma triangle_2_pt {A B} (f:WRel A B) :
  forall x y, from_bool (to_bool f) x y <= f x y.
Proof. apply from_to_minimal_pt. Qed.
