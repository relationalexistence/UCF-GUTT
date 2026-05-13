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
  |                    Top__Extensions__Prelude.v                            |
  |                                                                          |
  |                    Public API Surface for Extensions                     |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-12                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Single import point for extension infrastructure.              |
  |  This re-exports the essential definitions under stable names.           |
  |                                                                          |
  |  USAGE:                                                                  |
  |    Require Import Top__Extensions__Prelude.                              |
  |    (* Now you have: UE.Ux, UE.Whole, UE.elem, UE.R_prime, etc. *)        |
  |                                                                          |
  |  This file does NOT import Extras.v (closures, decidability, examples).  |
  |  Import those separately if needed.                                      |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - All exports in the UE module                                      |
  |      - Top-level notations: Ux, Whole, elem, R_prime                     |
  |      - Tactics: ue_simpl, ue_auto                                        |
  |      - Unified hint databases: ucf, ucf_all                              |
  |    Names outside the UE module may change between versions.              |
  |                                                                          |
  |  HINT DATABASES:                                                         |
  |    ucf              - Unified database for common UCF/GUTT usage         |
  |    ucf_all          - Maximum automation (includes all hints)            |
  |    whole_completion - WholeCompletion-specific hints                     |
  |    composition      - Composition-specific hints                         |
  |    serial_composition - SerialComposition hints                          |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - UE module uses short memorable names (elem, Whole, lift)            |
  |    - Tactics use prefix: ue_*, ucf_*                                     |
  |    - Hint databases: lowercase (ucf, whole_completion)                   |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Export Top__Extensions__Base.
Require Export Top__Extensions__WholeCompletion.
Require Export Top__Extensions__Composition.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    UE MODULE - CANONICAL PUBLIC API                        *)
(*                                                                            *)
(* ========================================================================== *)

(**
  UE: The canonical public API for universe extensions.
  
  This module provides stable, memorable names for downstream propositions.
  Prefer importing this over using raw record names.
  
  NAMING CONVENTIONS:
    - Types start with uppercase: Carrier, Ux, Hom, Iso
    - Constructors/values use lowercase: elem, Whole, lift
    - Lemmas use snake_case: lift_preserves, point_fresh
    - Module-qualified names: UE.extension, UE.serial
*)

Module UE.
  
  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)
  
  (** The extended carrier type: U + {Whole}. *)
  Definition Carrier (U : Type) := WholeCompletion.carrier U.
  
  (** Alias for Carrier with cleaner notation. *)
  Definition Ux := WholeCompletion.carrier.
  
  (** The base extension record type. *)
  Definition Extension := UniverseExtension.
  
  (** Pointed extension record type. *)
  Definition PointedExt := PointedUniverseExtension.
  
  (** Fresh pointed extension record type. *)
  Definition FreshPointedExt := FreshPointedUniverseExtension.
  
  (** Serial extension record type. *)
  Definition SerialExt := PointedSerialExtension.
  
  (* ====================================================================== *)
  (*                           Constructors                                 *)
  (* ====================================================================== *)
  
  (** The distinguished "Whole" element (terminal sink). *)
  Definition Whole {U : Type} : Carrier U := WholeCompletion.point.
  
  (** Embed an element of U into the extended carrier. *)
  Definition elem {U : Type} (u : U) : Carrier U := WholeCompletion.inject u.
  
  (** Alternative name for elem. *)
  Definition inject {U : Type} := @elem U.
  
  (* ====================================================================== *)
  (*                         Relation Lifting                               *)
  (* ====================================================================== *)
  
  (** Lift a relation on U to the extended carrier. *)
  Definition lift {U : Type} (R : U -> U -> Prop) := WholeCompletion.lift_rel R.
  
  (** Traditional notation: R' is the lifted relation. *)
  Definition R_prime {U : Type} := @lift U.
  
  (* ====================================================================== *)
  (*                        Extension Records                               *)
  (* ====================================================================== *)
  
  (** The canonical universe extension via option type. *)
  Definition extension (U : Type) := WholeCompletion.as_extension U.
  
  (** The canonical pointed extension. *)
  Definition pointed (U : Type) := WholeCompletion.as_pointed U.
  
  (** The canonical fresh pointed extension. *)
  Definition fresh_pointed (U : Type) := WholeCompletion.as_fresh_pointed U.
  
  (** The canonical pointed-serial extension. *)
  Definition pointed_serial (U : Type) := WholeCompletion.as_pointed_serial U.
  
  (* ====================================================================== *)
  (*                          Core Lemmas                                   *)
  (* ====================================================================== *)
  
  (** Every element relates to Whole (pointed seriality). *)
  Definition serial {U : Type} (R : U -> U -> Prop) := 
    WholeCompletion.serial U R.
  
  (** Weak seriality: every element has a successor. *)
  Definition weak_serial {U : Type} (R : U -> U -> Prop) := 
    WholeCompletion.weak_serial U R.
  
  (** Conservativity: lifted relation agrees with base on U. *)
  Definition conservative {U : Type} := 
    WholeCompletion.lift_conservative U.
  
  (** No dead-ends in the completion. *)
  Definition no_dead_ends {U : Type} := 
    WholeCompletion.no_dead_ends_in_completion U.
  
  (** Whole is not in the image of elem. *)
  Definition point_fresh {U : Type} := 
    WholeCompletion.point_fresh U.
  
  (** Cannot reach an element from Whole. *)
  Definition point_terminal {U : Type} := 
    WholeCompletion.point_terminal U.
  
  (** Lifting preserves the base relation. *)
  Definition lift_preserves {U : Type} := 
    WholeCompletion.lift_preserves U.
  
  (** Whole has a self-loop for any relation. *)
  Definition point_self_loop {U : Type} (R : U -> U -> Prop) :=
    WholeCompletion.point_self_loop U R.
  
  (** elem is injective. *)
  Definition elem_injective {U : Type} := 
    WholeCompletion.inject_injective U.
  
  (* ====================================================================== *)
  (*                        Inversion Principles                            *)
  (* ====================================================================== *)
  
  (** Case analysis on carrier elements. *)
  Definition carrier_case {U : Type} := 
    @WholeCompletion.carrier_case U.
  
  (** Inversion for lift when target is an element. *)
  Definition lift_to_elem_inv {U : Type} := 
    WholeCompletion.lift_rel_to_elem_inv U.
  
  (** Inversion for lift when source is Whole. *)
  Definition lift_from_whole_inv {U : Type} := 
    WholeCompletion.lift_rel_from_point_inv U.
  
  (* ====================================================================== *)
  (*                        Relation Properties                             *)
  (* ====================================================================== *)
  
  (** Seriality property. *)
  Definition Serial := @Top__Extensions__Base.Serial.
  
  (** Totality property. *)
  Definition Total := @Top__Extensions__Base.Total.
  
  (** Reflexivity property. *)
  Definition Reflexive := @Top__Extensions__Base.Reflexive.
  
  (** Symmetry property. *)
  Definition Symmetric := @Top__Extensions__Base.Symmetric.
  
  (** Transitivity property. *)
  Definition Transitive := @Top__Extensions__Base.Transitive.
  
  (** Equivalence (refl + sym + trans). *)
  Definition Equivalence := @Top__Extensions__Base.Equivalence.
  
  (* ====================================================================== *)
  (*                        Extension Records                               *)
  (* ====================================================================== *)
  
  Definition PointedSerialExtension := Top__Extensions__Base.PointedSerialExtension.
  
  (** SerialExtension: Alias for PointedSerialExtension.
      In UCF/GUTT, seriality is achieved via Whole-completion, so serial
      extensions are inherently pointed. This alias provides a shorter name
      when the "pointed" aspect is implicit from context. *)
  Definition SerialExtension := Top__Extensions__Base.PointedSerialExtension.
  
  (* ====================================================================== *)
  (*                           Morphisms                                    *)
  (* ====================================================================== *)
  
  (** Homomorphism between extensions. *)
  Definition Hom := @UE_Hom.
  
  (** Isomorphism between extensions. *)
  Definition Iso := @UE_Iso.
  
  (** Identity homomorphism. *)
  Definition Hom_id := @UE_Hom_id.
  
  (** Composition of homomorphisms. *)
  Definition Hom_compose := @UE_Hom_compose.
  
  (** Identity isomorphism. *)
  Definition Iso_refl := @UE_Iso_refl.
  
  (** Symmetry of isomorphism. *)
  Definition Iso_sym := @UE_Iso_sym.
  
  (** Transitivity of isomorphism. *)
  Definition Iso_trans := @UE_Iso_trans.
  
  (* ====================================================================== *)
  (*                          Composition                                   *)
  (* ====================================================================== *)
  
  (** Compose two extensions. *)
  Definition compose := @Composition.compose.
  
  (** Identity extension. *)
  Definition id_extension := Identity.id_extension.
  
  (** Left unit isomorphism: id >> E ~= E. *)
  Definition compose_id_left_iso := Composition.compose_id_left_iso.
  
  (** Right unit isomorphism: E >> id ~= E. *)
  Definition compose_id_right_iso := Composition.compose_id_right_iso.
  
  (** Associativity isomorphism. *)
  Definition compose_assoc_iso := Composition.compose_assoc_iso.
  
  (* ====================================================================== *)
  (*                      Universal Properties                              *)
  (* ====================================================================== *)
  
  (** Lift and restrict roundtrip. *)
  Definition lift_restrict := UniversalProperties.lift_restrict_roundtrip.
  
  (** Lifting is monotone. *)
  Definition lift_monotone := UniversalProperties.lift_monotone.
  
  (** Lifted empty relation is empty on U. *)
  Definition lift_empty := UniversalProperties.lift_empty_on_U.
  
  (** Lifted full relation is full on U. *)
  Definition lift_full := UniversalProperties.lift_full_on_U.
  
  (* ====================================================================== *)
  (*                       Pointed Serial API                               *)
  (* ====================================================================== *)
  
  (** Access the carrier of a serial extension. *)
  Definition pse_carrier {U : Type} := @pse_carrier U.
  
  (** Access the inject of a serial extension. *)
  Definition pse_inject {U : Type} := @pse_inject U.
  
  (** Access the lift of a serial extension. *)
  Definition pse_lift {U : Type} := @pse_lift U.
  
  (** Access the point of a serial extension. *)
  Definition pse_point {U : Type} := @pse_point U.
  
  (** Pointed serial implies weak serial. *)
  Definition pointed_serial_implies_serial {U : Type} := 
    @pointed_serial_implies_serial U.

End UE.

(* ========================================================================== *)
(*                                                                            *)
(*                    TOP-LEVEL CONVENIENCE EXPORTS                           *)
(*                                                                            *)
(* ========================================================================== *)

(** These are re-exported at top level for maximum convenience.
    Use UE.* for namespaced access if you prefer. *)

Notation Ux := UE.Ux.
Notation Whole := UE.Whole.
Notation elem := UE.elem.
Notation R_prime := UE.R_prime.

(* ========================================================================== *)
(*                                                                            *)
(*                    TACTICS                                                 *)
(*                                                                            *)
(* ========================================================================== *)

(** Tactic to simplify whole-completion goals. *)
Ltac ue_simpl := 
  unfold UE.lift, UE.elem, UE.Whole, UE.Carrier;
  unfold WholeCompletion.lift_rel, WholeCompletion.inject, WholeCompletion.point;
  simpl.

(** Tactic to solve trivial whole-completion goals. *)
Ltac ue_auto :=
  auto with ucf;
  try (ue_simpl; auto; tauto).

(* ========================================================================== *)
(*                                                                            *)
(*                    UNIFIED HINT DATABASE                                   *)
(*                                                                            *)
(* ========================================================================== *)

(**
  The 'ucf' hint database unifies the most commonly needed hints from all
  extension modules. Use this as the default for UCF/GUTT developments.
  
  Includes hints from:
    - whole_completion (seriality, conservativity, point properties)
    - composition (identity, associativity, inject/lift equations)
    - serial_composition (iteration, fractal connectivity)
*)

(* Re-export core hints into unified database *)
#[export] Hint Resolve
  (* WholeCompletion core *)
  WholeCompletion.serial
  WholeCompletion.weak_serial
  WholeCompletion.point_self_loop
  WholeCompletion.point_terminal
  WholeCompletion.point_fresh
  WholeCompletion.inject_injective
  WholeCompletion.lift_preserves
  WholeCompletion.lift_conservative_bwd
  WholeCompletion.no_dead_ends_in_completion
  WholeCompletion.lift_preserves_reflexive
  (* Identity extension *)
  Identity.id_preserves_reflexive
  Identity.id_preserves_symmetric
  Identity.id_preserves_transitive
  Identity.id_preserves_serial
  (* Composition *)
  Composition.compose_conservative
  (* Serial composition *)
  SerialComposition.iter_inject_injective
  SerialComposition.iter_point_fresh
  SerialComposition.iter_serial
  SerialComposition.iter_weak_serial
  : ucf.

#[export] Hint Rewrite
  WholeCompletion.lift_conservative
  SerialComposition.iter_lift_conservative
  : ucf.

#[export] Hint Extern 1 (exists _, WholeCompletion.lift_rel _ _ _) =>
  exists WholeCompletion.point; apply WholeCompletion.serial : ucf.

#[export] Hint Extern 1 (WholeCompletion.lift_rel _ _ WholeCompletion.point) =>
  apply WholeCompletion.serial : ucf.

#[export] Hint Extern 1 (~ WholeCompletion.lift_rel _ WholeCompletion.point (WholeCompletion.inject _)) =>
  apply WholeCompletion.point_terminal : ucf.

(** Combined automation tactic using unified database. *)
Ltac ucf_auto :=
  auto with ucf;
  try (ue_simpl; auto; tauto).

(* ========================================================================== *)
(*                                                                            *)
(*                    MAXIMUM AUTOMATION HINT DATABASE                        *)
(*                                                                            *)
(* ========================================================================== *)

(**
  The 'ucf_all' hint database provides MAXIMUM automation by combining
  ALL available hints. Use when you want the most aggressive automation.
  
  WARNING: May be slower than 'ucf' for large goals. Use 'ucf' for
  routine automation and 'ucf_all' when you need everything.
*)

(* Note: Some lemmas like lift_conservative_fwd cannot be Hint Resolve
   because their conclusion is R a b where R is a variable. These need
   Hint Extern instead. The hints below are the ones with fixed head symbols. *)

#[export] Hint Resolve
  (* WholeCompletion lemmas with fixed conclusion types *)
  WholeCompletion.serial
  WholeCompletion.weak_serial
  WholeCompletion.point_self_loop
  WholeCompletion.point_terminal
  WholeCompletion.point_fresh
  WholeCompletion.point_fresh_sym
  WholeCompletion.inject_injective
  WholeCompletion.lift_preserves
  WholeCompletion.lift_conservative_bwd
  WholeCompletion.no_dead_ends_in_completion
  WholeCompletion.lift_preserves_reflexive
  (* All Identity lemmas *)
  Identity.id_preserves_reflexive
  Identity.id_preserves_symmetric
  Identity.id_preserves_transitive
  Identity.id_preserves_serial
  (* All Composition lemmas *)
  Composition.compose_conservative
  (* All SerialComposition lemmas *)
  SerialComposition.iter_inject_injective
  SerialComposition.iter_point_fresh
  SerialComposition.iter_serial
  SerialComposition.iter_weak_serial
  SerialComposition.inner_outer_distinct
  SerialComposition.inner_fresh
  SerialComposition.elem_to_inner_whole
  SerialComposition.elem_to_outer_whole
  SerialComposition.inner_to_outer
  SerialComposition.compose_is_serial
  (* Additional theorems *)
  completion_minimality
  inject_reflects
  carrier_disjoint_union
  universal_relation_to_point
  point_only_reaches_point
  : ucf_all.

#[export] Hint Rewrite
  WholeCompletion.lift_conservative
  SerialComposition.iter_lift_conservative
  SerialComposition.double_carrier
  SerialComposition.double_point
  SerialComposition.double_inject
  CompositionHints.compose_id_left_inject
  CompositionHints.compose_id_right_inject
  CompositionHints.id_lift_id
  : ucf_all.

#[export] Hint Extern 1 (exists _, WholeCompletion.lift_rel _ _ _) =>
  exists WholeCompletion.point; apply WholeCompletion.serial : ucf_all.

#[export] Hint Extern 1 (WholeCompletion.lift_rel _ _ WholeCompletion.point) =>
  apply WholeCompletion.serial : ucf_all.

#[export] Hint Extern 1 (~ WholeCompletion.lift_rel _ WholeCompletion.point (WholeCompletion.inject _)) =>
  apply WholeCompletion.point_terminal : ucf_all.

#[export] Hint Extern 2 (exists _, SerialComposition.iter_lift _ _ _ _ _) =>
  eexists; apply SerialComposition.iter_serial : ucf_all.

(** Maximum automation tactic using all hints. *)
Ltac ucf_all_auto :=
  auto with ucf_all;
  try (ue_simpl; auto with ucf_all; tauto).

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  Types:
    UE.Carrier U    = option U (the extended universe)
    UE.Ux U         = option U (alias)
  
  Constructors:
    UE.Whole        = None (the terminal element)
    UE.elem u       = Some u (embedding)
  
  Lifting:
    UE.lift R       = the extended relation R'
    UE.R_prime R    = alias for UE.lift R
  
  Key Properties:
    UE.serial R x           : UE.lift R x UE.Whole  (always true)
    UE.conservative R a b   : UE.lift R (elem a) (elem b) <-> R a b
    UE.point_fresh u        : elem u <> Whole
    UE.point_terminal R u   : ~ UE.lift R Whole (elem u)
  
  Extension Records:
    UE.extension U          : UniverseExtension U
    UE.pointed_serial U     : PointedSerialExtension U
  
  Morphisms:
    UE.Hom E1 E2            : type of homomorphisms
    UE.Iso E1 E2            : type of isomorphisms
    UE.Hom_id E             : identity morphism
    UE.Hom_compose f g      : composition
    UE.Iso_trans iso1 iso2  : transitivity of isos
  
  Composition:
    UE.compose E1 E2        : compose extensions
    UE.id_extension U       : identity extension
  
  HINT DATABASES
  ==============
  
    ucf               : Unified database (RECOMMENDED for most uses)
                        Combines essential hints from all modules.
    ucf_all           : Maximum automation (ALL hints, may be slower)
                        Use when ucf doesn't solve it automatically.
    whole_completion  : WholeCompletion-specific hints
    composition       : Composition-specific hints  
    serial_composition: SerialComposition hints
  
  TACTICS
  =======
  
    ue_simpl          : Unfold UE definitions and simplify
    ue_auto           : Auto with ucf database + simplification
    ucf_auto          : Alias for ue_auto (unified automation)
    ucf_all_auto      : Maximum automation using all hints
*)

(** Axiom audit note:
    This file is a pure re-export API surface with no proof terms of its own.
    All definitions and lemmas are audited at their source modules:
      - Top__Extensions__Base         (audited via Top__Extensions__AxiomAudit)
      - Top__Extensions__WholeCompletion
      - Top__Extensions__Composition
      - Top__Extensions__Extras
    Downstream files that import Prelude carry zero additional axioms.
    Confirmed by AxiomAudit.v: "Closed under the global context." *)
