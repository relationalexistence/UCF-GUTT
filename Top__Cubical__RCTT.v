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
  |                    Top__Cubical__RCTT.v                                  |
  |                                                                          |
  |         Relational Cubical Type Theory (RCTT): Main Assembly            |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.1.0                                                          |
  |  DATE:    2026-03-10                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                        |
  |                                                                          |
  |  PURPOSE: Assemble and summarize the Relational Cubical Type Theory      |
  |  derived from the UCF/GUTT foundations.  This file presents the         |
  |  complete RCTT structure and its key theorems in one place.              |
  |                                                                          |
  |  WHAT RCTT IS:                                                           |
  |  Relational Cubical Type Theory is a cubical type theory whose:          |
  |    - INTERVAL is derived (option unit = WholeCompletion of unit)         |
  |    - PATHS are relational chains (RChain, VDPath)                        |
  |    - KAN FILLING is a theorem (fractal_connectivity)                     |
  |    - KAN FILLING is CANONICAL (fill_terminal, unique, sink, universal)  |
  |    - UNIVALENCE is a theorem (relational_univalence)                     |
  |    - CUBES generalize to variable-dimension NRT structures (VDRel)       |
  |                                                                          |
  |  WHAT RCTT IS NOT:                                                       |
  |    - It does NOT claim full dependent type theory (CIC-level)            |
  |    - The J-rule for Prop paths IS proved (relational_J_full, JRule.v)   |
  |    - funext is NOT an axiom here: rel_funext is a THEOREM (JRule.v)     |
  |    - Full arithmetic on arbitrary R_cauchy is ongoing                    |
  |    - HITs (circles, suspensions) are an open extension                   |
  |                                                                          |
  |  THREE KEY INVERSIONS from standard CTT:                                 |
  |    1. The interval I is not a PRIMITIVE — it is a THEOREM                 |
  |    2. Kan filling is not a POSTULATE — it is a THEOREM, and the filler   |
  |       is CANONICAL, UNIQUE, and R-INDEPENDENT (KanCanonical.v)           |
  |    3. Univalence is not an AXIOM — it is a THEOREM (for relational eq)   |
  |                                                                          |
  |  BEYOND CUBES: VDRel generalizes n-cubes to trees of relations where    |
  |    each edge carries its own dimensional sub-structure.                  |
  |    This extends NRT from Prop_05 to arbitrary depth.                     |
  |    It models: linguistic structures (GUTT-L), molecular graphs,          |
  |    organizational networks, and nested semantic hierarchies.             |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  RCTT Summary Theorems                                     |
  |    SECTION 2:  Comparison Table: RCTT vs Standard CTT                    |
  |    SECTION 3:  The RCTT Module (unified public API)                      |
  |    SECTION 4:  Dependency Chain                                          |
  |    SECTION 5:  Application: GUTT-L Linguistic Paths                      |
  |    SECTION 6:  Complete Axiom Audit                                      |
  |                                                                          |
  |  NEW IN v1.1.0:                                                          |
  |    - Requires Top__Cubical__KanCanonical                                 |
  |    - RCTT_kan_is_theorem upgraded: canonical witness exposed             |
  |    - RCTT_kan_canonical: fill_terminal, unique, sink, universal proved   |
  |    - RCTT Module: KanCanon API integrated                                |
  |    - Comparison table updated: Kan row reflects canonical status         |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (entire RCTT stack)                           |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Export Top__Cubical__Interval.
Require Export Top__Cubical__PathType.
Require Export Top__Cubical__NCube.
Require Export Top__Cubical__Univalence.
Require Export Top__Cubical__JRule.
Require Export Top__Cubical__KanCanonical.
Require Import Top__Extensions__Prelude.
Require Import Top__Relations__RelationalAlgebra.
Require Import Top__Propositions__Prop_01.
Require Import Top__Propositions__Prop_04.
Require Import Top__Propositions__Prop_05.

Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: RCTT SUMMARY THEOREMS                        *)
(*                                                                            *)
(*  These are the FOUR FOUNDATIONAL THEOREMS of RCTT.                        *)
(*  Each is PROVED from existing UCF/GUTT infrastructure.                    *)
(*  None requires a new axiom.                                               *)
(*                                                                            *)
(* ========================================================================== *)

(**
  THEOREM 1 — THE INTERVAL IS DERIVED:
  
  The relational interval I_R is NOT a primitive type.  It is the
  WholeCompletion of unit, derived from the foundational Proposition 01.
  Its two endpoints are computationally distinct.
*)
Theorem RCTT_interval_derived :
  I_R = WholeCompletion.carrier unit /\
  i0 = WholeCompletion.inject tt /\
  i1 = WholeCompletion.point (U := unit) /\
  i0 <> i1.
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact i0_neq_i1.
Qed.

(**
  THEOREM 2 — KAN FILLING IS A THEOREM (CANONICAL FORM):
  
  In standard CTT, Kan filling is a postulated operation (or computational rule).
  In RCTT, it is PROVED canonically:
    fill_terminal n = None : option (RCube_carrier n U)
  is THE unique element such that ∀ x, canon_cube (S n) R x (fill_terminal n).
  The filler does not depend on R or x — it is determined by n alone.
  
  KanCanonical.v upgrades this from existential to:
    [ok] EXPLICIT witness (fill_terminal n = a concrete Definition)
    [ok] UNIQUE (the only universal filler, proved by 3-line match eval)
    [ok] CANONICAL (R-independent, x-independent)
    [ok] SINK (nothing escapes fill_terminal)
    [ok] UNIVERSAL (same witness fills all canonical n-cubes simultaneously)
*)
Theorem RCTT_kan_is_theorem : forall (n : nat) (U : Type) (R : U -> U -> Prop),
  forall (x : RCube_carrier (S n) U),
  { w : RCube_carrier (S n) U & canon_cube (S n) R x w }.
Proof.
  intros n U R x.
  exact (kan_witness_canonical n R x).
Qed.

(**
  THEOREM 2b — THE KAN FILLER IS CANONICAL AND UNIQUE:
  
  The specific filler is fill_terminal n = None, and it is the ONLY
  element that universally fills every x at level n.
*)
Theorem RCTT_kan_canonical : forall (n : nat) (U : Type) (R : U -> U -> Prop),
  (* fill_terminal fills everything *)
  (forall (x : RCube_carrier (S n) U),
    canon_cube (S n) R x (fill_terminal n)) /\
  (* fill_terminal is the ONLY such element *)
  (forall (w : RCube_carrier (S n) U),
    (forall x, canon_cube (S n) R x w) -> w = fill_terminal n) /\
  (* fill_terminal is a terminal sink *)
  (forall (w : RCube_carrier (S n) U),
    canon_cube (S n) R (fill_terminal n) w <-> w = fill_terminal n) /\
  (* fill_terminal does not depend on R *)
  (forall (T : U -> U -> Prop) (x : RCube_carrier (S n) U),
    canon_cube (S n) T x (fill_terminal n)).
Proof.
  intros n U R.
  refine (conj _ (conj _ (conj _ _))).
  - intro x. apply fill_terminal_spec.
  - intros w Hw. exact (fill_unique n R w Hw).
  - intro w. apply fill_is_sink.
  - intros T x. apply fill_terminal_spec.
Qed.

(**
  THEOREM 3 — RELATIONAL UNIVALENCE IS A THEOREM:
  
  In HoTT, Univalence is an axiom: (A ≃ B) → (A = B).
  In RCTT, the relational version is PROVED:
  Isomorphic extensions are relationally indistinguishable.
  No additional axiom is required.
*)
Theorem RCTT_univalence_is_theorem :
  forall (U : Type) (E1 E2 : UniverseExtension U),
  UE_Iso E1 E2 ->
  forall (R : U -> U -> Prop) (a b : U),
    ue_lift E1 R (ue_inject E1 a) (ue_inject E1 b) <->
    ue_lift E2 R (ue_inject E2 a) (ue_inject E2 b).
Proof.
  intros U E1 E2 iso R a b.
  exact (relational_univalence E1 E2 iso R a b).
Qed.

(**
  THEOREM 4 — NRTs EXTEND TO VARIABLE-DIMENSION STRUCTURES BEYOND CUBES:
  
  Standard CTT cubes are uniform: dimension n is the same for every edge.
  VDRel structures allow each edge to carry its own sub-dimension.
  Every NRT from Prop_05 embeds into a VDRel at depth 1.
  VDRel at depth d provides d levels of dimensional nesting per edge.
*)
Theorem RCTT_beyond_cubes :
  forall (U : Type) `{HU : DecEq U} (nrt : NRT U),
  (* Every NRT embeds into a VDRel at depth 1 *)
  exists (v : VDRel U 1),
    forall (a b : Ux U),
      (NRT_eval nrt a b > 0) <->
      vdr_outer v a b.
Proof.
  intros U HU nrt.
  exists (NRT_to_VDRel nrt).
  intros a b.
  apply NRT_to_VDRel_outer.
Qed.

(**
  THEOREM 5 — SERIALITY IMPLIES CONNECTIVITY AT ALL DIMENSIONS:
  
  The fundamental UCF/GUTT principle "everything relates to the Whole"
  lifts to all n-dimensional cubes: at every level and every nesting depth,
  an element is always connected to its local Whole.
*)
Theorem RCTT_fractal_connectivity : forall (n level : nat) (U : Type) (R : U -> U -> Prop) (u : U),
  (level <= n)%nat ->
  match SerialComposition.whole_at_level n level U with
  | Some w => canon_cube (S n) R
                (SerialComposition.iter_inject (S n) U u) w
  | None => True
  end.
Proof.
  intros n level U R u Hlevel.
  apply kan_fill_fractal. exact Hlevel.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*  SECTION 2: COMPARISON TABLE (as Coq comments)                            *)
(*                                                                            *)
(*  ╔══════════════════════════════╦═════════════════════╦═══════════════════╗*)
(*  ║ Component                    ║ Standard CTT        ║ RCTT (UCF/GUTT)  ║*)
(*  ╠══════════════════════════════╬═════════════════════╬═══════════════════╣*)
(*  ║ Interval I                   ║ Primitive (axiom)   ║ option unit       ║*)
(*  ║ Endpoints i0, i1             ║ Primitive           ║ Some tt, None     ║*)
(*  ║ i0 ≠ i1                      ║ Assumed             ║ discriminate      ║*)
(*  ║ Path A a b                   ║ I → A               ║ RChain R a b      ║*)
(*  ║ Path refl                    ║ λi.a                ║ rchain_refl       ║*)
(*  ║ Kan filling                  ║ Postulate/rule      ║ fill_terminal (canon)║*)
(*  ║ Kan uniqueness               ║ N/A                 ║ fill_unique (proved) ║*)
(*  ║ Kan as terminal sink         ║ N/A                 ║ fill_is_sink (proved)║*)(*  ║ Connection ∧, ∨              ║ Assumed             ║ I_meet, I_join    ║*)
(*  ║ De Morgan laws               ║ Assumed             ║ I_de_morgan_*     ║*)
(*  ║ Univalence                   ║ Axiom               ║ relational_univ.  ║*)
(*  ║ J-rule (full prop paths)     ║ Derived             ║ relational_J_full ║*)
(*  ║ funext                       ║ Axiom in HoTT       ║ rel_funext THOREM ║*)
(*  ║ Type families P:A→Type       ║ Coq function        ║ VDRel / RelFamily ║*)
(*  ║ n-cube                       ║ I^n → A             ║ iter_lift n R     ║*)
(*  ║ Beyond cubes                 ║ N/A                 ║ VDRel (depth d)   ║*)
(*  ║ NRT embedding                ║ N/A                 ║ NRT_to_VDRel      ║*)
(*  ║ Transport                    ║ via J               ║ transport_elem    ║*)
(*  ║ Groupoid laws                ║ Derived             ║ RId_trans_assoc   ║*)
(*  ╚══════════════════════════════╩═════════════════════╩═══════════════════╝*)
(*                                                                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: THE RCTT MODULE (UNIFIED PUBLIC API)         *)
(*                                                                            *)
(* ========================================================================== *)

Module RCTT.

  (* -------------------------------------------------------------------- *)
  (*                        The Interval                                  *)
  (* -------------------------------------------------------------------- *)

  (** The derived interval type. *)
  Definition Interval := I_R.
  Definition src      := i0.
  Definition tgt      := i1.
  Definition distinct := i0_neq_i1.

  (** Connection operations. *)
  Definition meet   := I_meet.
  Definition join   := I_join.
  Definition neg    := I_neg.

  (** n-dimensional interval. *)
  Definition Interval_n := I_R_n.

  (* -------------------------------------------------------------------- *)
  (*                        Path Types                                    *)
  (* -------------------------------------------------------------------- *)

  (** Path type: relational chain. *)
  Definition Path {U : Type} (R : U -> U -> Prop) := RChain R.

  (** Path constructors. *)
  Definition refl  {U : Type} {R : U -> U -> Prop} := @rchain_refl U R.
  Definition step  {U : Type} {R : U -> U -> Prop} := @rchain_single U R.
  Definition trans {U : Type} {R : U -> U -> Prop} := @rchain_trans U R.
  Definition sym   {U : Type} {R : U -> U -> Prop}
    (Hsym : Symmetric R) := @rchain_sym U R Hsym.

  (** n-dimensional path. *)
  Definition Path_n := @RPath_n.

  (** Path homotopy (2-path). *)
  Definition Homotopy {U : Type} {R : U -> U -> Prop} {a b : U}
    := @RHomotopy U R a b.

  (* -------------------------------------------------------------------- *)
  (*                        n-Cubes                                       *)
  (* -------------------------------------------------------------------- *)

  (** n-cube carrier. *)
  Definition Carrier := RCube_carrier.

  (** n-cube type. *)
  Definition Cube := RCube.

  (** Canonical n-cube from base relation. *)
  Definition canon := @canon_cube.

  (** Conservative embedding. *)
  Definition conservative := @canon_cube_conservative.

  (** Kan filling (canonical). *)
  Definition kan_term      := @kan_fill_terminal.
  Definition kan_frac      := @kan_fill_fractal.
  Definition kan_fill      := @fill_terminal.
  Definition kan_spec      := @fill_terminal_spec.
  Definition kan_unique    := @fill_unique.
  Definition kan_unique_iff:= @fill_unique_iff.
  Definition kan_sink      := @fill_is_sink.
  Definition kan_self_loop := @fill_self_loop.
  Definition kan_universal := @fill_universal.
  Definition kan_R_indep   := @fill_R_independent.
  Definition kan_coherence := @fill_fractal_coherence.

  (** Face and degeneracy. *)
  Definition face_lo := @lower_face.
  Definition face_hi := @upper_face.
  Definition degen   := @degen_cube.

  (* -------------------------------------------------------------------- *)
  (*                        Beyond Cubes: VDRel                           *)
  (* -------------------------------------------------------------------- *)

  (** Variable-dimension relational structure. *)
  Definition VarDim := VDRel.
  Definition vd_base := @vdr_base.
  Definition vd_node := @vdr_node.
  Definition vd_eval := @vdr_eval.
  Definition vd_path := @VDPath.
  Definition vd_refl := @vdpath_refl.
  Definition vd_trans := @vdpath_trans.

  (** NRT embedding into VarDim. *)
  Definition nrt_to_vd := @NRT_to_VDRel.

  (* -------------------------------------------------------------------- *)
  (*                        Relational Univalence                         *)
  (* -------------------------------------------------------------------- *)

  (** Relational equality. *)
  Definition RelEq := @rel_ext_eq.

  (** Relational identity type. *)
  Definition RId := @RId.

  (** MAIN UNIVALENCE THEOREM. *)
  Definition univalence := @relational_univalence.

  (** Transport along relational identity. *)
  Definition transport     := @transport_elem.
  Definition transport_inj := @transport_inject.

  (* -------------------------------------------------------------------- *)
  (*                        Summary Theorems                              *)
  (* -------------------------------------------------------------------- *)

  Definition interval_derived    := RCTT_interval_derived.
  Definition kan_theorem         := RCTT_kan_is_theorem.
  Definition kan_canonical_thm   := RCTT_kan_canonical.
  Definition univalence_theorem  := RCTT_univalence_is_theorem.
  Definition beyond_cubes        := RCTT_beyond_cubes.
  Definition fractal             := RCTT_fractal_connectivity.

End RCTT.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: DEPENDENCY CHAIN                             *)
(*                                                                            *)
(*  The full RCTT dependency chain:                                           *)
(*                                                                            *)
(*  Top__Extensions__Base.v          (relation properties, morphisms)        *)
(*    └── Top__Extensions__WholeCompletion.v  (interval I_R derived here)    *)
(*          └── Top__Extensions__Composition.v  (fractal_connectivity)       *)
(*                └── Top__Propositions__Prop_01.v  (Seriality)              *)
(*                      └── Top__Propositions__Prop_05.v  (NRT, tensors)     *)
(*                                                                            *)
(*  Top__Cubical__Interval.v         (derives I_R, face maps, connections)   *)
(*  Top__Cubical__PathType.v         (RChain, UE_Iso paths, homotopy)        *)
(*  Top__Cubical__NCube.v            (n-cubes, Kan, VDRel beyond cubes)      *)
(*  Top__Cubical__Univalence.v       (relational_univalence theorem)         *)
(*  Top__Cubical__JRule.v            (relational_J_full, rel_funext)         *)
(*  Top__Cubical__KanCanonical.v     (fill_terminal canonical+unique+sink)   *)
(*  Top__Cubical__RCTT.v             (this file: assembly)                   *)
(*                                                                            *)
(* ========================================================================== *)

(** The dependency chain is correct. *)
Lemma rctt_dependency_ok :
  (* Interval derives from WholeCompletion *)
  I_R = WholeCompletion.carrier unit /\
  (* Kan filling uses fractal_connectivity *)
  (forall n (U : Type) (R : U -> U -> Prop)
     (x : RCube_carrier (S n) U),
     canon_cube (S n) R x (SerialComposition.iter_point n U)) /\
  (* Univalence uses hom structure *)
  (forall (U : Type) (E1 E2 : UniverseExtension U),
     UE_Iso E1 E2 -> rel_ext_eq E1 E2).
Proof.
  refine (conj _ (conj _ _)).
  - reflexivity.
  - intros n U R x. apply kan_fill_terminal.
  - intros U E1 E2 iso. apply relational_univalence. exact iso.
Qed.

(** Paths are relational — stated separately since RChain : Type. *)
Lemma rctt_paths_relational : forall (U : Type) (R : U -> U -> Prop) (a : U),
  RChain R a a.
Proof. intros U R a. apply rchain_refl. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: APPLICATION — GUTT-L LINGUISTIC PATHS        *)
(*                                                                            *)
(*  GUTT-L (Grand Unified Tensor Theory applied to Linguistics) uses the     *)
(*  same relational infrastructure for linguistic analysis.                  *)
(*                                                                            *)
(*  In RCTT terms:                                                            *)
(*    - Words are elements of U                                              *)
(*    - Semantic relations R : U → U → Prop are relational edges             *)
(*    - A "sentence" is an RChain R w₁ wₙ (path through semantic space)     *)
(*    - Paraphrase equivalence is RHomotopy (2-paths between sentences)      *)
(*    - Compositional meaning is VDRel: words have inner sub-structure       *)
(*    - Cross-lingual transfer is transport along ExtIso                     *)
(*                                                                            *)
(*  The VDRel structure naturally captures:                                  *)
(*    - VDRel 0 U: basic semantic relation (word → word)                    *)
(*    - VDRel 1 U: outer (syntax) + inner (sub-lexical) per relation         *)
(*    - VDRel d U: d-deep compositional hierarchy                            *)
(*                                                                            *)
(* ========================================================================== *)

Section GUTT_L_Application.

  (** Words as a type with decidable equality. *)
  Variable WordType : Type.
  Variable WordDecEq : DecEq WordType.
  Existing Instance WordDecEq.

  (** A semantic relation on words. *)
  Variable SemRel : Ux WordType -> Ux WordType -> Prop.

  (** A sentence is an RChain in the semantic relation.
      Note: RChain is a Type (not Prop) to allow path induction. *)
  Definition Sentence (w1 w2 : Ux WordType) : Type :=
    RChain SemRel w1 w2.

  (** Every word has a trivial path to itself. *)
  Lemma word_self_path : forall (w : Ux WordType), Sentence w w.
  Proof.
    intro w. apply rchain_refl.
  Qed.

  (** Sentences compose (sequential meaning assembly). *)
  Lemma sentence_compose : forall (w1 w2 w3 : Ux WordType),
    Sentence w1 w2 -> Sentence w2 w3 -> Sentence w1 w3.
  Proof.
    intros w1 w2 w3 H12 H23.
    apply rchain_trans with w2. exact H12. exact H23.
  Qed.

  (** A compositional word meaning: VDRel capturing sub-lexical structure. *)
  Definition CompositionalMeaning (depth : nat) : Type :=
    VDRel WordType depth.

  (** The flat semantic relation as a VDRel at depth 0. *)
  Definition flat_meaning : CompositionalMeaning 0 :=
    vdr_base SemRel.

  (** Adding sub-lexical structure to a word relation. *)
  Definition add_sublexical
    (base : CompositionalMeaning 1)
    (w1 w2 : Ux WordType)
    (sub : CompositionalMeaning 0)
    : CompositionalMeaning 1 :=
    vdr_add_inner (HU := WordDecEq) base w1 w2 sub.

  (** Cross-lingual transfer: transport meaning across a language isomorphism. *)
  Variable LangExt1 LangExt2 : UniverseExtension WordType.
  Variable lang_iso : UE_Iso LangExt1 LangExt2.

  (** Transfer a word from language 1 to language 2. *)
  Definition cross_lingual_transfer (w : ue_carrier LangExt1) : ue_carrier LangExt2 :=
    transport_elem lang_iso w.

  (** Transfer preserves injection (source words map to target words). *)
  Lemma cross_lingual_transfer_preserves_words (w : WordType) :
    cross_lingual_transfer (ue_inject LangExt1 w) = ue_inject LangExt2 w.
  Proof.
    apply transport_inject.
  Qed.

  (** Relational univalence for language transfer:
      Language-invariant semantic predicates are preserved. *)
  Lemma cross_lingual_semantic_invariance :
    forall (R : WordType -> WordType -> Prop) (w1 w2 : WordType),
      ue_lift LangExt1 R (ue_inject LangExt1 w1) (ue_inject LangExt1 w2) <->
      ue_lift LangExt2 R (ue_inject LangExt2 w1) (ue_inject LangExt2 w2).
  Proof.
    intros R w1 w2.
    exact (relational_univalence LangExt1 LangExt2 lang_iso R w1 w2).
  Qed.

End GUTT_L_Application.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: COMPLETE AXIOM AUDIT                         *)
(*                                                                            *)
(*  AXIOM STATUS FOR ENTIRE RCTT STACK                                        *)
(*  =====================================                                     *)
(*  Zero additional axioms beyond Coq's CIC type theory.                     *)
(*  Zero admits at any point in any file.                                    *)
(*                                                                            *)
(*  KEY THEOREMS AND THEIR STATUS:                                            *)
(*    RCTT_interval_derived          --> Closed under global context          *)
(*    RCTT_kan_is_theorem            --> Closed under global context          *)
(*    RCTT_kan_canonical             --> Closed under global context          *)
(*    RCTT_univalence_is_theorem     --> Closed under global context          *)
(*    RCTT_beyond_cubes              --> Closed under global context          *)
(*    RCTT_fractal_connectivity      --> Closed under global context          *)
(*    fill_terminal_spec             --> Closed under global context          *)
(*    fill_unique                    --> Closed under global context          *)
(*    fill_is_sink                   --> Closed under global context          *)
(*    fill_self_loop                 --> Closed under global context          *)
(*    fill_inject_distinct           --> Closed under global context          *)
(*    fill_universal                 --> Closed under global context          *)
(*    fill_fractal_coherence         --> Closed under global context          *)
(*    relational_univalence          --> Closed under global context          *)
(*    kan_fill_fractal               --> Closed under global context          *)
(*    i0_neq_i1                      --> Closed under global context          *)
(*    I_de_morgan_meet               --> Closed under global context          *)
(*    vdpath_trans                   --> Closed under global context          *)
(*    transport_inject               --> Closed under global context          *)
(*                                                                            *)
(*  HONEST BOUNDARIES (what RCTT does NOT yet do):                           *)
(*    1. Full dependent type theory: CIC-level Π-types over RCTT paths.      *)
(*       Adding this would require working inside Coq's universe hierarchy.  *)
(*    2. Full J-rule for TYPE FAMILIES (P : A → Type): relational_J_full     *)
(*       proves the J-rule for Prop-valued predicates (P : path → Prop).     *)
(*       Substitution into general Type families is a separate matter and    *)
(*       IS orthogonal to the relational framework (VDRel handles families). *)
(*    3. Judgmental computation for Kan (fill_terminal reduces):             *)
(*       fill_terminal is now CANONICAL and UNIQUE (KanCanonical.v), but     *)
(*       it does not yet have judgmental reduction rules (hcomp-like terms). *)
(*       Propositional equations are proved; definitional reduction is open. *)
(*    4. funext for bare Coq functions: rel_funext proves function equality  *)
(*       at the RELATIONAL level (graph equality). Coq propositional         *)
(*       function equality f = g is not our goal — we work with rel_graph.  *)
(*    5. Higher inductive types: circles, suspensions, truncations.          *)
(*       VDRel provides tree-like structures beyond cubes, but HITs require  *)
(*       additional computational rules.                                     *)
(*    6. Full arithmetic on R_cauchy: dimensions in Prop_02 use R_cauchy,    *)
(*       but full arithmetic closure is an ongoing completion task.          *)
(*                                                                            *)
(*  These boundaries are documented to maintain scientific credibility.      *)
(*                                                                            *)
(* ========================================================================== *)

(** Live axiom audit — each must print "Closed under the global context." *)
Print Assumptions RCTT_univalence_is_theorem.
Print Assumptions RCTT_kan_is_theorem.
Print Assumptions rctt_paths_relational.
Print Assumptions rctt_dependency_ok.
