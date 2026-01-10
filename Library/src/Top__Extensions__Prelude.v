(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
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
  |    Names in the UE module are considered stable public API.              |
  |    Names outside UE may change between versions.                         |
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
  
  (** Backward compatibility alias. *)
  Definition serial_extension := pointed_serial.
  
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
  Definition SerialExtension := Top__Extensions__Base.SerialExtension.
  
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
  
  (** Left unit isomorphism: id >> E â‰… E. *)
  Definition compose_id_left_iso := Composition.compose_id_left_iso.
  
  (** Right unit isomorphism: E >> id â‰… E. *)
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
  auto with whole_completion;
  try (ue_simpl; auto; tauto).

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
*)
