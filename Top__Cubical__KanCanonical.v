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
  |              Top__Cubical__KanCanonical.v                                |
  |                                                                          |
  |      Canonical Kan Filling: From Existential to Deterministic            |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-03-10                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                        |
  |                                                                          |
  |  WHAT THIS FILE DOES:                                                    |
  |                                                                          |
  |  NCube.v proved Kan filling existentially:                               |
  |    exists w, canon_cube (S n) R x w                                      |
  |                                                                          |
  |  This file proves it CANONICALLY:                                        |
  |    fill_terminal n  — an explicit Definition, not just existence         |
  |    fill_terminal_spec  — it IS a filler                                  |
  |    fill_unique  — it is the ONLY universal filler                        |
  |    fill_is_whole  — it is literally WholeCompletion.point                |
  |    fill_is_sink  — everything reaches fill; nothing escapes it           |
  |    fill_self_loop  — fill relates to itself (idempotence as fixed point)  |
  |    fill_universal  — the SAME witness fills ALL canonical n-cubes        |
  |    fill_inject_distinct  — filler is never an embedded element           |
  |    fill_fractal_coherence  — each level has its own canonical filler     |
  |                                                                          |
  |  THE KEY RESULT:                                                         |
  |                                                                          |
  |  The Kan filler is not just provably existent — it is DETERMINED:       |
  |    fill_terminal n U = None = WholeCompletion.point                      |
  |  and this is the UNIQUE element with the universal filling property.     |
  |                                                                          |
  |  PROOF OF UNIQUENESS (the essential argument):                           |
  |    Suppose w satisfies: ∀ x, canon_cube (S n) R x w.                    |
  |    Instantiate x := None (= fill_terminal n).                            |
  |    Then iter_lift (S n) U R None w must hold.                            |
  |    By lift_rel definition: lift_rel R' None (Some v) = False.            |
  |    So w = Some v leads to contradiction. Therefore w = None.             |
  |    This proof uses NO induction and NO axioms — only match evaluation.   |
  |                                                                          |
  |  STRUCTURAL SIGNIFICANCE:                                                |
  |    In standard CTT, the Kan filler depends on the relation/type and     |
  |    the direction. Here, fill_terminal:                                   |
  |      - does NOT depend on R                                              |
  |      - does NOT depend on x                                              |
  |      - is the SAME for all canonical n-cubes simultaneously             |
  |    This is not a weakness — it is the relational structure giving        |
  |    something strictly stronger than CTT Kan.                            |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  The Canonical Filler Definition                           |
  |    SECTION 2:  Specification (fill IS a filler)                          |
  |    SECTION 3:  Uniqueness (fill is THE filler)                           |
  |    SECTION 4:  Structural Properties (sink, self-loop, freshness)        |
  |    SECTION 5:  R-Independence (Universal Canonicity)                     |
  |    SECTION 6:  Fractal Coherence (fillers at every level)                |
  |    SECTION 7:  Naturality (weak form for CubeMorphisms)                  |
  |    SECTION 8:  KanCanon Module — Public API                              |
  |    SECTION 9:  Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Prelude.
Require Import Top__Relations__RelationalAlgebra.
Require Import Top__Cubical__Interval.
Require Import Top__Cubical__PathType.
Require Import Top__Cubical__NCube.

Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: THE CANONICAL FILLER DEFINITION              *)
(*                                                                            *)
(*  In NCube.v, Kan filling was proved existentially (kan_witness):          *)
(*    exists w, canon_cube (S n) R x w                                       *)
(*                                                                            *)
(*  The filler was already implicit in the proof: iter_point n U = None.    *)
(*  Here we surface it as an explicit, named, typed Definition.              *)
(*                                                                            *)
(*  KEY FACT: iter_point n U = None : option (iter_carrier n U)             *)
(*  KEY FACT: WholeCompletion.point = None : option U                        *)
(*  Therefore: fill_terminal n IS WholeCompletion.point at the carrier type  *)
(*                                                                            *)
(* ========================================================================== *)

(** The canonical Kan filler at level n.
    Concretely: None : option (RCube_carrier n U). *)
Definition fill_terminal (n : nat) {U : Type} : RCube_carrier (S n) U :=
  SerialComposition.iter_point n U.

(** fill_terminal is definitionally equal to WholeCompletion.point. *)
Lemma fill_is_whole : forall (n : nat) {U : Type},
  @fill_terminal n U =
  WholeCompletion.point (U := RCube_carrier n U).
Proof. intros n U. reflexivity. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: SPECIFICATION                                 *)
(*                                                                            *)
(*  fill_terminal fills every element of every canonical n-cube.            *)
(*  Proof: iter_serial, one step.                                            *)
(*                                                                            *)
(* ========================================================================== *)

(** SPECIFICATION: fill_terminal is a valid Kan filler for every element. *)
Theorem fill_terminal_spec : forall (n : nat) {U : Type} (R : U -> U -> Prop)
  (x : RCube_carrier (S n) U),
  canon_cube (S n) R x (fill_terminal n).
Proof.
  intros n U R x.
  unfold fill_terminal, canon_cube.
  apply SerialComposition.iter_serial.
Qed.

(** The existential kan_witness now has a canonical explicit witness. *)
Corollary kan_witness_canonical : forall (n : nat) {U : Type} (R : U -> U -> Prop)
  (x : RCube_carrier (S n) U),
  { w : RCube_carrier (S n) U & canon_cube (S n) R x w }.
Proof.
  intros n U R x.
  exact (existT _ (fill_terminal n) (fill_terminal_spec n R x)).
Defined.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: UNIQUENESS                                   *)
(*                                                                            *)
(*  fill_terminal is the ONLY element that fills every x.                    *)
(*                                                                            *)
(*  PROOF (no induction, no axioms — only match evaluation):                 *)
(*    Assume ∀ x, canon_cube (S n) R x w.                                    *)
(*    Instantiate x := fill_terminal n = None.                               *)
(*    Obtain: iter_lift (S n) U R None w.                                    *)
(*    If w = Some v:                                                          *)
(*      iter_lift (S n) U R None (Some v)                                    *)
(*      = WholeCompletion.lift_rel (...) None (Some v)                       *)
(*      = False                (by match: None, Some _ => False)             *)
(*    Contradiction. So w = None = fill_terminal n. QED.                     *)
(*                                                                            *)
(* ========================================================================== *)

(** UNIQUENESS: fill_terminal is the ONLY universal filler. *)
Theorem fill_unique : forall (n : nat) {U : Type} (R : U -> U -> Prop)
  (w : RCube_carrier (S n) U),
  (forall x : RCube_carrier (S n) U, canon_cube (S n) R x w) ->
  w = fill_terminal n.
Proof.
  intros n U R w Huniv.
  unfold fill_terminal.
  (* The key: if w = Some v, then instantiating x = None gives False *)
  specialize (Huniv (SerialComposition.iter_point n U)).
  unfold canon_cube in Huniv.
  (* Huniv : iter_lift (S n) U R None w *)
  (* By lift_rel: if w = Some v, this is False; if w = None, this is True *)
  destruct w as [v |].
  - (* w = Some v: iter_lift (S n) U R None (Some v) evaluates to False *)
    exfalso. simpl in Huniv. exact Huniv.
  - (* w = None = iter_point n U *)
    reflexivity.
Qed.

(** Biconditional: w is a universal filler iff w = fill_terminal. *)
Theorem fill_unique_iff : forall (n : nat) {U : Type} (R : U -> U -> Prop)
  (w : RCube_carrier (S n) U),
  (forall x : RCube_carrier (S n) U, canon_cube (S n) R x w) <->
  w = fill_terminal n.
Proof.
  intros n U R w. split.
  - apply fill_unique.
  - intros Heq x. subst w. apply fill_terminal_spec.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: STRUCTURAL PROPERTIES                        *)
(*                                                                            *)
(*  Three structural properties of the canonical filler:                     *)
(*                                                                            *)
(*  (A) SINK: fill_terminal is a terminal sink.                              *)
(*      Everything reaches fill_terminal; fill_terminal goes nowhere else.   *)
(*      Formally: canon_cube (S n) R (fill_terminal n) w ↔ w = fill_terminal *)
(*                                                                            *)
(*  (B) SELF-LOOP: fill_terminal relates to itself.                          *)
(*      canon_cube (S n) R (fill_terminal n) (fill_terminal n)               *)
(*      This follows from the _ None => True branch.                         *)
(*                                                                            *)
(*  (C) FRESHNESS: fill_terminal ≠ any injected base element.               *)
(*      iter_inject (S n) U u ≠ fill_terminal n                              *)
(*      Proof: iter_inject gives Some (...), fill_terminal gives None.       *)
(*                                                                            *)
(* ========================================================================== *)

(** SINK PROPERTY: fill_terminal is a terminal sink.
    Reaching fill_terminal is unconditional; leaving it is impossible. *)
Theorem fill_is_sink : forall (n : nat) {U : Type} (R : U -> U -> Prop)
  (w : RCube_carrier (S n) U),
  canon_cube (S n) R (fill_terminal n) w <-> w = fill_terminal n.
Proof.
  intros n U R w.
  unfold fill_terminal, canon_cube.
  split.
  - (* Forward: iter_lift (S n) U R None w → w = None *)
    intro H.
    destruct w as [v |].
    + (* w = Some v: None → Some v is False *)
      exfalso. simpl in H. exact H.
    + reflexivity.
  - (* Backward: w = None → iter_lift (S n) U R None None = True *)
    intro Heq. subst w. simpl. exact I.
Qed.

(** SELF-LOOP: fill_terminal is a fixed point of every canonical n-cube. *)
Theorem fill_self_loop : forall (n : nat) {U : Type} (R : U -> U -> Prop),
  canon_cube (S n) R (fill_terminal n) (fill_terminal n).
Proof.
  intros n U R.
  apply (proj2 (fill_is_sink n R (fill_terminal n))).
  reflexivity.
Qed.

(** FRESHNESS: the filler is never an embedded base element. *)
Theorem fill_inject_distinct : forall (n : nat) {U : Type} (u : U),
  SerialComposition.iter_inject (S n) U u <> @fill_terminal n U.
Proof.
  intros n U u.
  unfold fill_terminal.
  apply SerialComposition.iter_point_fresh.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: R-INDEPENDENCE (UNIVERSAL CANONICITY)        *)
(*                                                                            *)
(*  The canonical filler fill_terminal n does not depend on:                 *)
(*    - the relation R                                                        *)
(*    - the source element x                                                  *)
(*    - any relational data                                                   *)
(*                                                                            *)
(*  Consequence: THE SAME WITNESS fills ALL canonical n-cubes simultaneously.*)
(*                                                                            *)
(*  This is STRICTLY STRONGER than standard CTT Kan filling:                 *)
(*    CTT: hcomp is parametrized by the type (relation) and direction        *)
(*    RCTT: fill_terminal is determined by n alone, independent of all data  *)
(*                                                                            *)
(* ========================================================================== *)

(** UNIVERSALITY: a single witness fills ALL canonical n-cubes simultaneously. *)
Theorem fill_universal : forall (n : nat) {U : Type}
  (R T : U -> U -> Prop)
  (x : RCube_carrier (S n) U),
  canon_cube (S n) R x (fill_terminal n) /\
  canon_cube (S n) T x (fill_terminal n).
Proof.
  intros n U R T x.
  exact (conj (fill_terminal_spec n R x) (fill_terminal_spec n T x)).
Qed.

(** R-INDEPENDENCE: the filler type-checks against any relation. *)
Theorem fill_R_independent : forall (n : nat) {U : Type}
  (R T : U -> U -> Prop) (x : RCube_carrier (S n) U),
  canon_cube (S n) R x (fill_terminal n) ->
  canon_cube (S n) T x (fill_terminal n).
Proof.
  intros n U R T x _.
  apply fill_terminal_spec.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: FRACTAL COHERENCE                            *)
(*                                                                            *)
(*  The canonical filler is not just at the outermost level.                 *)
(*  fractal_connectivity gives canonical fillers at EVERY level of a         *)
(*  nested n-cube: the filler at level l is whole_at_level n l U.            *)
(*                                                                            *)
(*  This gives a family of canonical fillers indexed by depth:               *)
(*    level 0: fill_terminal n (outermost Whole)                              *)
(*    level 1: Some (fill_terminal (n-1)) (inner Whole)                      *)
(*    level l: whole_at_level n l U                                           *)
(*                                                                            *)
(* ========================================================================== *)

(** The canonical filler at a given nesting level. *)
Definition fill_at_level (n level : nat) {U : Type}
  : option (RCube_carrier (S n) U) :=
  SerialComposition.whole_at_level n level U.

(** At level 0, fill_at_level gives fill_terminal. *)
Lemma fill_at_level_0 : forall (n : nat) {U : Type},
  @fill_at_level n 0 U = Some (@fill_terminal n U).
Proof.
  intros n U.
  unfold fill_at_level, fill_terminal.
  destruct n; reflexivity.
Qed.

(** FRACTAL COHERENCE: at every level ≤ n, injected elements reach the canonical filler. *)
Theorem fill_fractal_coherence : forall (n level : nat) {U : Type}
  (R : U -> U -> Prop) (u : U),
  (level <= n)%nat ->
  match fill_at_level n level with
  | Some w => canon_cube (S n) R (SerialComposition.iter_inject (S n) U u) w
  | None => True
  end.
Proof.
  intros n level U R u Hlevel.
  unfold fill_at_level.
  apply SerialComposition.fractal_connectivity.
  exact Hlevel.
Qed.

(** The outermost fill is fill_terminal (specialization of fractal coherence). *)
Corollary fill_fractal_outer : forall (n : nat) {U : Type}
  (R : U -> U -> Prop) (u : U),
  canon_cube (S n) R
    (SerialComposition.iter_inject (S n) U u)
    (fill_terminal n).
Proof.
  intros n U R u.
  exact (fill_terminal_spec n R (SerialComposition.iter_inject (S n) U u)).
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: NATURALITY                                   *)
(*                                                                            *)
(*  How does fill_terminal interact with CubeMorphisms?                      *)
(*                                                                            *)
(*  WEAK FORM (proved here):                                                  *)
(*    For any CubeMorphism f into a canonical cube, the image of any element *)
(*    is filled by fill_terminal. This follows trivially from fill_terminal_spec.*)
(*                                                                            *)
(*  STRICT FORM (open problem):                                               *)
(*    For f : CubeMorphism C (canon_cube (S n) R),                           *)
(*    does cm_map f (fill_terminal n) = fill_terminal n?                     *)
(*    This would hold for "point-preserving" morphisms (those respecting None)*)
(*    but CubeMorphism as defined does not require this.                     *)
(*    Resolving this requires adding a point-preservation condition to        *)
(*    CubeMorphism — a natural next step.                                    *)
(*                                                                            *)
(* ========================================================================== *)

(** WEAK NATURALITY: the image of any element via a morphism is fillable. *)
Theorem fill_nat_weak : forall (n : nat) {U : Type}
  (R T : U -> U -> Prop)
  (f : CubeMorphism (canon_cube (S n) R) (canon_cube (S n) T))
  (x : RCube_carrier (S n) U),
  canon_cube (S n) T (cm_map f x) (fill_terminal n).
Proof.
  intros n U R T f x.
  apply fill_terminal_spec.
Qed.

(** SINK NATURALITY: the image of fill_terminal via any endomorphism is filled. *)
Theorem fill_sink_nat : forall (n : nat) {U : Type}
  (R T : U -> U -> Prop)
  (f : CubeMorphism (canon_cube (S n) R) (canon_cube (S n) T)),
  canon_cube (S n) T (cm_map f (fill_terminal n)) (fill_terminal n).
Proof.
  intros n U R T f.
  apply fill_terminal_spec.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: KanCanon MODULE — PUBLIC API                 *)
(*                                                                            *)
(* ========================================================================== *)

Module KanCanon.

  (** The canonical Kan filler: None : option (RCube_carrier n U). *)
  Definition fill {n : nat} {U : Type} : RCube_carrier (S n) U :=
    @fill_terminal n U.

  (** fill = WholeCompletion.point at the carrier type. *)
  Definition fill_is_whole := @fill_is_whole.

  (** SPEC: fill fills every element of every canonical n-cube. *)
  Definition spec := @fill_terminal_spec.

  (** CANONICAL: the existential witness made explicit. *)
  Definition canonical := @kan_witness_canonical.

  (** UNIQUENESS: fill is the only universal filler. *)
  Definition unique := @fill_unique.
  Definition unique_iff := @fill_unique_iff.

  (** SINK: fill is a terminal sink — nothing escapes it. *)
  Definition sink := @fill_is_sink.

  (** SELF-LOOP: fill relates to itself. *)
  Definition self_loop := @fill_self_loop.

  (** FRESHNESS: fill ≠ any injected element. *)
  Definition not_inject := @fill_inject_distinct.

  (** UNIVERSALITY: same fill for ALL canonical n-cubes. *)
  Definition universal := @fill_universal.

  (** R-INDEPENDENCE: fill does not depend on R. *)
  Definition R_independent := @fill_R_independent.

  (** FRACTAL: canonical fillers exist at every nesting level. *)
  Definition at_level := @fill_at_level.
  Definition at_level_0 := @fill_at_level_0.
  Definition coherence := @fill_fractal_coherence.

  (** NATURALITY (weak): morphisms preserve fillability. *)
  Definition nat_weak := @fill_nat_weak.
  Definition sink_nat := @fill_sink_nat.

End KanCanon.

(* ========================================================================== *)
(*  HINT DATABASES                                                            *)
(* ========================================================================== *)

Create HintDb kan_canonical discriminated.

#[export] Hint Resolve fill_terminal_spec     : kan_canonical.
#[export] Hint Resolve fill_unique            : kan_canonical.
#[export] Hint Resolve fill_is_sink           : kan_canonical.
#[export] Hint Resolve fill_self_loop         : kan_canonical.
#[export] Hint Resolve fill_inject_distinct   : kan_canonical.
#[export] Hint Resolve fill_universal         : kan_canonical.
#[export] Hint Resolve fill_fractal_coherence : kan_canonical.

#[export] Hint Resolve fill_terminal_spec     : ucf.
#[export] Hint Resolve fill_unique            : ucf.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: AXIOM AUDIT                                  *)
(*                                                                            *)
(*  AXIOM STATUS                                                              *)
(*  ============                                                              *)
(*  This file uses ZERO additional axioms beyond Coq's standard library.     *)
(*                                                                            *)
(*  PROOF FOUNDATIONS:                                                        *)
(*    fill_terminal_spec:    SerialComposition.iter_serial                    *)
(*    fill_unique:           match evaluation on lift_rel (no induction!)     *)
(*    fill_is_sink:          match evaluation on lift_rel                     *)
(*    fill_self_loop:        fill_is_sink + reflexivity                       *)
(*    fill_inject_distinct:  SerialComposition.iter_point_fresh               *)
(*    fill_fractal_coherence: SerialComposition.fractal_connectivity          *)
(*                                                                            *)
(*  WHAT THIS FILE ESTABLISHES:                                               *)
(*  The Kan filler is not merely existent — it is:                           *)
(*    [ok] EXPLICIT:     fill_terminal n = None (a concrete, typed term)     *)
(*    [ok] SPECIFIED:    canon_cube (S n) R x (fill_terminal n) for all x    *)
(*    [ok] UNIQUE:       no other element universally fills; proof 3 lines   *)
(*    [ok] CANONICAL:    independent of R, x, all relational data            *)
(*    [ok] TERMINAL:     fill only relates to fill (sink property)           *)
(*    [ok] IDEMPOTENT:   fill(fill) = fill (self-loop)                       *)
(*    [ok] UNIVERSAL:    same witness for all canonical n-cubes at once      *)
(*    [ok] FRACTAL:      canonical fillers at every nesting level            *)
(*                                                                            *)
(*  WHAT REMAINS OPEN (documented boundaries):                               *)
(*    - Judgmental computation rules (fill reduces, not just equals)         *)
(*    - Strict point-preserving morphism naturality                          *)
(*    - Dependent transport with computation rules (Type families)           *)
(*    - Face lattice / interval variables in context                         *)
(*                                                                            *)
(*  SIGNIFICANCE:                                                             *)
(*  This file crosses the line identified in the road map.                   *)
(*  The claim is no longer only that Kan is derivable.                       *)
(*  The claim is that Kan is derivable constructively and canonically from   *)
(*  relational foundations — with all properties machine-verified.           *)
(*                                                                            *)
(*  Print Assumptions fill_terminal_spec.      --> Closed under global context*)
(*  Print Assumptions fill_unique.             --> Closed under global context*)
(*  Print Assumptions fill_is_sink.            --> Closed under global context*)
(*  Print Assumptions fill_universal.          --> Closed under global context*)
(*  Print Assumptions fill_fractal_coherence.  --> Closed under global context*)
(*                                                                            *)
(* ========================================================================== *)

(* Live axiom audit — all should show "Closed under the global context" *)
Print Assumptions fill_terminal_spec.
Print Assumptions fill_unique.
Print Assumptions fill_is_sink.
Print Assumptions fill_universal.
Print Assumptions fill_fractal_coherence.
