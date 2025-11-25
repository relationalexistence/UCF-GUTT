(*
   UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
  See LICENSE, NOTICE, and TRADEMARKS in the repo root.
  
  reduction_proven.v
  -------------------
  Free/Forgetful pattern between 0/1 graphs and weighted relations
  NOW USING PROVEN PROPOSITION 1 (no axioms!)
  
  Changes from original reduction.v:
  - Imports Prop1_proven
  - Uses Ux (extended universe) instead of Parameter E
  - Replaces Axiom Connectivity_Holds with proven theorem
  - Maintains all original functionality
*)

(* ============================================================ *)
(* Part A: Import Proven Refined Proposition 1                  *)
(* ============================================================ *)

Require Import Prop1_proven.

(* Extract the types and definitions we need *)
Definition E_base : Type := U.      (* Base universe *)
Definition E : Type := Ux.          (* Extended universe U ∪ {Whole} *)
Definition R_base := R.             (* Original relation on U *)
Definition R_ext := R_prime.        (* Extended relation on Ux *)

(* ============================================================ *)
(* Part B: Connectivity - NOW PROVEN, NOT AXIOMATIZED          *)
(* ============================================================ *)

(* Define connectivity property *)
Definition Connectivity : Prop :=
  forall x : E, exists y : E, R_ext x y.

(* BEFORE: Axiom Connectivity_Holds : Connectivity. *)
(* AFTER: Proven theorem! *)
Theorem Connectivity_Holds : Connectivity.
Proof.
  unfold Connectivity.
  exact refined_proposition_1.
Qed.

(* Export convenient theorem alias *)
Theorem Connectivity_Exists : forall x : E, exists y : E, R_ext x y.
Proof. exact Connectivity_Holds. Qed.

(* No isolates - proven, not assumed *)
Lemma No_Isolates : forall x:E, ~ (forall y:E, ~ R_ext x y).
Proof.
  intros x Hnone.
  destruct (Connectivity_Exists x) as [y Hy].
  specialize (Hnone y). 
  contradiction.
Qed.

(* Additional lemmas about the extension *)
Lemma Whole_is_connected : exists y : E, R_ext Whole y.
Proof. apply Connectivity_Exists. Qed.

Lemma elem_connected : forall (e : U), exists y : E, R_ext (elem e) y.
Proof. intro e. apply Connectivity_Exists. Qed.

(* Show how R_ext relates to R_base on U elements *)
Lemma R_ext_on_U_elements :
  forall (a b : U), R_ext (Some a) (Some b) <-> R_base a b.
Proof.
  intros a b.
  apply R_prime_restricts.
Qed.

(* ============================================================ *)
(* Part C: Weighted/Boolean Relations (computational layer)     *)
(* ============================================================ *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Set Implicit Arguments.

Definition RelObj := Type.
Definition WRel (A B:RelObj) := A -> B -> nat.   (* weighted relation *)
Definition BRel (A B:RelObj) := A -> B -> bool.  (* 0/1 graph *)

(* Forgetful U: weighted -> 0/1 (true iff weight > 0) *)
Definition U_functor {A B} (R:WRel A B) : BRel A B :=
  fun x y => Nat.ltb 0 (R x y).

(* Free F: 0/1 -> weighted (true ↦ 1, false ↦ 0) *)
Definition F_functor {A B} (G:BRel A B) : WRel A B :=
  fun x y => if G x y then 1 else 0.

(* Preorder on relations (pointwise) *)
Definition brel_le {A B} (r1 r2 : BRel A B) : Prop :=
  forall x y, (r1 x y = true -> r2 x y = true).

Definition wrel_le {A B} (s1 s2 : WRel A B) : Prop :=
  forall x y, s1 x y <= s2 x y.

(* Reflexivity and transitivity for brel_le *)
Lemma brel_le_refl {A B} (r : BRel A B) : brel_le r r.
Proof. intros x y H; exact H. Qed.

Lemma brel_le_trans {A B} (r1 r2 r3 : BRel A B) :
  brel_le r1 r2 -> brel_le r2 r3 -> brel_le r1 r3.
Proof. intros H12 H23 x y Hr1; apply H23, H12, Hr1. Qed.

(* Reflexivity and transitivity for wrel_le *)
Lemma wrel_le_refl {A B} (s : WRel A B) : wrel_le s s.
Proof. intros x y; lia. Qed.

Lemma wrel_le_trans {A B} (s1 s2 s3 : WRel A B) :
  wrel_le s1 s2 -> wrel_le s2 s3 -> wrel_le s1 s3.
Proof. intros H12 H23 x y; etransitivity; [apply H12 | apply H23]. Qed.

(* ============================================================ *)
(* Part D: Adjunction-like Properties                           *)
(* ============================================================ *)

(* 1) U ∘ F = id on 0/1 morphisms (pointwise form) *)
Lemma U_F_id_pt {A B} (G:BRel A B) :
  forall x y, U_functor (F_functor G) x y = G x y.
Proof.
  intros x y. unfold U_functor, F_functor.
  destruct (G x y); simpl.
  - (* true  *) reflexivity.
  - (* false *) reflexivity.
Qed.

(* 2) F ∘ U is pointwise ≤ id on weighted morphisms (minimal enrichment) *)
Lemma F_U_le {A B} (R:WRel A B) :
  forall x y, F_functor (U_functor R) x y <= R x y.
Proof.
  intros x y. unfold F_functor, U_functor.
  destruct (Nat.ltb 0 (R x y)) eqn:H.
  - (* true: weight > 0 ⇒ 1 ≤ weight *)
    apply Nat.ltb_lt in H. simpl; lia.
  - (* false: weight = 0 ⇒ 0 ≤ weight *)
    apply Nat.ltb_ge in H. simpl; lia.
Qed.

(* "Adjunction-like" helpers as pointwise statements *)
Definition to_bool  {A B} (f:WRel A B) : BRel A B := U_functor f.
Definition from_bool{A B} (g:BRel A B) : WRel A B := F_functor g.

Lemma to_from_roundtrip_pt {A B} (g:BRel A B) :
  forall x y, to_bool (from_bool g) x y = g x y.
Proof.
  intros x y. unfold to_bool, from_bool. 
  apply U_F_id_pt.
Qed.

Lemma from_to_minimal_pt {A B} (f:WRel A B) :
  forall x y, from_bool (to_bool f) x y <= f x y.
Proof.
  intros x y. unfold to_bool, from_bool. 
  apply F_U_le.
Qed.

(* ============================================================ *)
(* Part E: Connection to Relational Foundation                  *)
(* ============================================================ *)

(*
  PHILOSOPHICAL NOTE:
  
  This proof now rests on the proven foundation that existence
  implies relation (Refined Proposition 1). The Free/Forgetful
  adjunction between weighted and boolean relations reflects
  the deeper truth that:
  
  - Relations are fundamental (Prop 1)
  - They can be viewed at different levels of abstraction
    (weighted vs boolean)
  - The structure-preserving maps (F and U) maintain relational
    coherence across these levels
  
  The fact that we can PROVE connectivity (rather than assume it)
  means this computational structure is grounded in proven
  ontological necessity, not convenient assumption.
*)

(* Example: Boolean relation over extended universe *)
Definition example_brel : BRel E E :=
  fun x y => match x, y with
             | Some _, None => true  (* Elements relate to Whole *)
             | None, None => true    (* Whole relates to itself *)
             | _, _ => false
             end.

(* Verify our example respects proven connectivity *)
Lemma example_respects_connectivity :
  forall x : E, exists y : E, example_brel x y = true.
Proof.
  intro x.
  exists None.
  unfold example_brel.
  destruct x; reflexivity.
Qed.

(* ============================================================ *)
(* Part F: Export Summary                                       *)
(* ============================================================ *)

(*
  SUMMARY OF CHANGES FROM reduction.v:
  
  1. ✓ Eliminated Axiom Connectivity_Holds
  2. ✓ Replaced with proven Theorem using proven proposition1
  3. ✓ Extended to work over Ux (with Whole)
  4. ✓ Added lemmas showing how extension relates to base
  5. ✓ Maintained all original Free/Forgetful functionality
  6. ✓ Added philosophical commentary on grounding
  
  WHAT THIS ACHIEVES:
  
  - Removes axiomatic dependency
  - Grounds computational structure in proven ontology
  - Maintains backward compatibility (all original lemmas present)
  - Adds stronger guarantees (no isolated elements possible)
  - Exemplifies how to migrate other proofs
  
  COMPILATION:
  
  Requires: Prop1_proven.v to be compiled first
  Tested: Coq 8.12+
*)
