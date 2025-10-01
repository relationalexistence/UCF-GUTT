Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Set Implicit Arguments.
(* ---------- Part A: Connectivity (Prop1) inline ---------- *)
(* Basic types and relations for the logical (Prop) layer *)
Parameter E : Type. (* Elements *)
Parameter R : E -> E -> Prop. (* Relation over E *)
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
Definition WRel (A B:RelObj) := A -> B -> nat. (* weighted relation *)
Definition BRel (A B:RelObj) := A -> B -> bool. (* 0/1 graph *)
(* Forgetful U: weighted -> 0/1 (true iff weight > 0) *)
Definition U {A B} (R:WRel A B) : BRel A B :=
  fun x y => Nat.ltb 0 (R x y).
(* Free F: 0/1 -> weighted (true ↦ 1, false ↦ 0) *)
Definition F {A B} (G:BRel A B) : WRel A B :=
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
(* 1) U ∘ F = id on 0/1 morphisms (pointwise form) *)
Lemma U_F_id_pt {A B} (G:BRel A B) :
  forall x y, U (F G) x y = G x y.
Proof.
  intros x y. unfold U, F.
  destruct (G x y); simpl.
  - (* true *) reflexivity. (* Nat.ltb 0 1 = true by computation *)
  - (* false *) reflexivity. (* Nat.ltb 0 0 = false by computation *)
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
Definition to_bool {A B} (f:WRel A B) : BRel A B := U f.
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
Lemma galois_connection {A B} (r : BRel A B) (s : WRel A B) :
  wrel_le (F r) s <-> brel_le r (U s).
Proof.
  split.
  - (* F r ≤ s ⇒ r ≤ U s *)
    intros H x y Hr_true.
    unfold U. (* Goal is Nat.ltb 0 (s x y) = true *)
    apply Nat.ltb_lt. (* Goal is 0 < s x y *)
    specialize (H x y).
    unfold F in H.
    rewrite Hr_true in H. (* H is now 1 <= s x y *)
    lia.
  - (* r ≤ U s ⇒ F r ≤ s *)
    intros H x y.
    destruct (r x y) eqn:Eq_r.
    + (* Case: r x y = true *)
      (* First, let's see our goal. `F r x y` becomes 1. *)
      unfold F. rewrite Eq_r. simpl. (* Goal: 1 <= s x y *)
      (* Now, let's use H. Since r x y = true, H tells us U s x y = true. *)
      assert (H_U : U s x y = true). {
        apply H. exact Eq_r.
      }
      (* `U s x y = true` means `0 < s x y` *)
      unfold U in H_U.
      apply Nat.ltb_lt in H_U. (* H_U is now: 0 < s x y *)
      (* For natural numbers, 0 < n is the same as 1 <= n. `lia` solves this. *)
      lia.
    + (* Case: r x y = false *)
      (* Here, `F r x y` is 0. The goal `0 <= s x y` is always true for nats. *)
      unfold F. rewrite Eq_r. lia.
Qed.

Section Composition.
  (* 1. Declare all variables first *)
  Variable sum_y : forall (B : RelObj), (B -> nat) -> nat.
  Variable default_seq : forall (B:RelObj), list B.
  (* 2. State all axioms about the variables *)
  Axiom sum_nonneg : forall (D:RelObj) (f : D -> nat),
    (@sum_y D f) >= 0.
  Axiom sum_ge_term : forall (D:RelObj) (f : D -> nat) (yy : D),
    In yy (@default_seq D) -> (@sum_y D f) >= f yy.
  (* 3. Make definitions using the variables *)
  Definition wrel_comp {A B C} (r1 : WRel A B) (r2 : WRel B C) : WRel A C :=
    fun x z => @sum_y B (fun y => r1 x y * r2 y z).
  Definition brel_comp {A B C} (r1 : BRel A B) (r2 : BRel B C) : BRel A C :=
    fun x z => existsb (fun y => andb (r1 x y) (r2 y z)) (@default_seq B).
  (* 4. Prove lemmas about the definitions *)
  Require Import Coq.Bool.Bool.
  Require Import Coq.Lists.List.
  Import ListNotations.
  Lemma F_preserves_comp {A B C} (g1 : BRel A B) (g2 : BRel B C) :
    wrel_le (F (brel_comp g1 g2)) (wrel_comp (F g1) (F g2)).
  Proof.
    unfold wrel_le; intros x z.
    unfold F, brel_comp, wrel_comp.
    set (f := fun yy : B => (if g1 x yy then 1 else 0) * (if g2 yy z then 1 else 0)).
    destruct (existsb (fun y => andb (g1 x y) (g2 y z)) (@default_seq B)) eqn:Hpath.
    - (* boolean path exists: LHS = 1 ≤ sum *)
      apply existsb_exists in Hpath.
      destruct Hpath as [y0 [H_in H_and]].
      assert (Hge : (@sum_y B f) >= f y0).
      { apply (@sum_ge_term B f y0); exact H_in. }
      apply andb_true_iff in H_and; destruct H_and as [Hg1 Hg2].
      assert (Hf_y0 : f y0 = 1).
      { unfold f; rewrite Hg1, Hg2; simpl; reflexivity. }
      rewrite Hf_y0 in Hge; lia.
    - (* no path: LHS = 0 ≤ sum, and sum ≥ 0 by axiom *)
      apply (@sum_nonneg B f).
  Qed.
  Lemma U_preserves_comp_le {A B C} (s1 : WRel A B) (s2 : WRel B C) :
    brel_le (brel_comp (U s1) (U s2)) (U (wrel_comp s1 s2)).
  Proof.
    unfold brel_le; intros x z Hcomp.
    unfold brel_comp in Hcomp.
    apply existsb_exists in Hcomp.
    destruct Hcomp as [y0 [H_in H_and]].
    apply andb_true_iff in H_and; destruct H_and as [HU1 HU2].
    unfold U in HU1, HU2.
    apply Nat.ltb_lt in HU1. (* 0 < s1 x y0 *)
    apply Nat.ltb_lt in HU2. (* 0 < s2 y0 z *)
    unfold U, wrel_comp.
    set (f := fun yy : B => s1 x yy * s2 yy z).
    assert (Hge : (@sum_y B f) >= f y0).
    { apply (@sum_ge_term B f y0); exact H_in. }
    assert (Hpos : 1 <= f y0) by (unfold f; simpl; lia).
    apply Nat.ltb_lt; lia.
  Qed.
End Composition.

(* Minimality of from_bool: the least WRel lifting true↦≥1, false↦0 w.r.t. wrel_le *)
Lemma from_bool_minimal {A B} (g : BRel A B) (R : WRel A B) :
  (forall x y, g x y = true -> R x y >= 1) ->
  (forall x y, g x y = false -> R x y = 0) ->
  wrel_le (F g) R.
Proof.
  intros Htrue Hfalse x y.
  destruct (g x y) eqn:Hg.
  - (* true: 1 <= R *)
    specialize (Htrue x y Hg).
    unfold F; rewrite Hg; lia.
  - (* false: 0 <= R, but Hfalse says R=0 *)
    specialize (Hfalse x y Hg).
    unfold F; rewrite Hg.
    subst; lia.
Qed.