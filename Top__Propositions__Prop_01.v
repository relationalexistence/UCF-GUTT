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
  |              PROPOSITION 01: SERIALITY VIA WHOLE-COMPLETION              |
  |                                                                          |
  |                      UCF/GUTT(TM) Formal Verification                    |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-12                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  THEOREM: forall x in U_x, exists y in U_x : R'(x,y)                     |
  |                                                                          |
  |  "Every entity in the extended universe has at least one outgoing edge"  |
  |                                                                          |
  |  This is SERIALITY (every node has a successor), achieved by adding      |
  |  the Whole as a terminal sink that every entity relates to.              |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Core Definitions (Ux, Whole, elem, R_prime)               |
  |    SECTION 2:  Main Theorem (proposition_01, seriality)                  |
  |    SECTION 3:  Key Properties (conservativity, terminality)              |
  |    SECTION 4:  Inversion Principles                                      |
  |    SECTION 5:  Relation Property Preservation                            |
  |    SECTION 6:  Extension Infrastructure                                  |
  |    SECTION 7:  Examples                                                  |
  |    SECTION 8:  P1 Module - Public API                                    |
  |    SECTION 9:  Hint Databases (prop1, prop1_ext)                         |
  |    SECTION 10: Tactics (prove_seriality, rprime_simpl, etc.)             |
  |    SECTION 11: Arguments & Implicit Handling                             |
  |    SECTION 12: Notation Scopes (prop1_scope)                             |
  |    SECTION 13: Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Core definitions: Ux, Whole, elem, R_prime                        |
  |      - Main theorems: proposition_01, seriality, pointed_seriality       |
  |      - P1 module exports (P1.serial, P1.conservative, etc.)              |
  |      - Hint databases: prop1, prop1_ext                                  |
  |      - Tactics: prove_seriality, rprime_simpl, prop1_auto                |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - Main theorem: proposition_01 (formal), seriality (semantic alias)   |
  |    - Properties: *_conservative, *_terminal, *_fresh                     |
  |    - Preservation: *_preserves_*, *_on_elems                             |
  |    - Inversion: *_inv, *_case                                            |
  |    - Direction suffixes: _fwd/_bwd for bidirectional lemmas              |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Prelude.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE DEFINITIONS                             *)
(*                                                                            *)
(*  All definitions are polymorphic in U - no axioms required.                *)
(*                                                                            *)
(* ========================================================================== *)

(** The extended carrier type: U + {Whole}. *)
Definition Ux (U : Type) : Type := UE.Carrier U.

(** The distinguished Whole element (terminal sink). *)
Definition Whole {U : Type} : Ux U := UE.Whole.

(** Embed an element of U into the extended carrier. *)
Definition elem {U : Type} (u : U) : Ux U := UE.elem u.

(** Lift a relation on U to the extended carrier. *)
Definition R_prime {U : Type} (R : U -> U -> Prop) : Ux U -> Ux U -> Prop := UE.lift R.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: MAIN THEOREM                                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  PROPOSITION 01 (Seriality via Whole-Completion):

  For any universe U and any relation R on U, the lifted relation R' on
  the extended universe U_x = U + {Whole} is serial: every element has
  at least one outgoing edge.

  The proof is CONSTRUCTIVE: the witness is always the Whole element.
  By the definition of lift_rel, R'(x, Whole) = True for all x.
*)
Theorem proposition_01 :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
    exists y : Ux U, R_prime R x y.
Proof.
  intros U R x.
  exists Whole.
  apply UE.serial.
Qed.

(** Semantic alias. *)
Definition seriality := proposition_01.

(** Constructive witness function: always returns Whole. *)
Definition witness {U : Type} : Ux U -> Ux U := fun _ => Whole.

(** The witness function actually works: R'(x, witness(x)) holds. *)
Theorem proposition_01_constructive :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
    R_prime R x (witness x).
Proof.
  intros U R x. unfold witness. apply UE.serial.
Qed.

(** Pointed seriality: there exists a UNIFORM witness (same for all x). *)
Theorem pointed_seriality :
  forall (U : Type) (R : U -> U -> Prop),
    exists w : Ux U, forall x : Ux U, R_prime R x w.
Proof.
  intros U R. exists Whole.
  intro x. apply UE.serial.
Qed.

(** Extraction-friendly constructive version with sigma type. *)
Definition proposition_01_sigma :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
    { y : Ux U | R_prime R x y }.
Proof.
  intros U R x.
  exists Whole.
  apply UE.serial.
Defined.

(** Weak seriality: the lifted relation is serial. *)
Theorem weak_seriality :
  forall (U : Type) (R : U -> U -> Prop),
    Top__Extensions__Base.Serial (R_prime R).
Proof.
  intros U R. apply UE.weak_serial.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: KEY PROPERTIES                               *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(*                         Conservativity                                     *)
(* -------------------------------------------------------------------------- *)

(** R' is a conservative extension: restricts to R on U x U. *)
Theorem R_prime_conservative :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R_prime R (elem a) (elem b) <-> R a b.
Proof.
  intros U R a b. apply UE.conservative.
Qed.

(** Forward direction of conservativity. *)
Lemma R_prime_conservative_fwd :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R_prime R (elem a) (elem b) -> R a b.
Proof.
  intros U R a b H. apply UE.conservative. exact H.
Qed.

(** Backward direction of conservativity. *)
Lemma R_prime_conservative_bwd :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R a b -> R_prime R (elem a) (elem b).
Proof.
  intros U R a b H. apply UE.conservative. exact H.
Qed.

(** Any edge in R lifts to R'. *)
Lemma R_lift :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R a b -> R_prime R (elem a) (elem b).
Proof.
  intros U R a b H. apply UE.lift_preserves. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Whole Properties                                   *)
(* -------------------------------------------------------------------------- *)

(** Everything relates to Whole. *)
Theorem everything_relates_to_Whole :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
    R_prime R x Whole.
Proof.
  intros U R x. apply UE.serial.
Qed.

(** Whole has a self-loop. *)
Theorem Whole_self_loop :
  forall (U : Type) (R : U -> U -> Prop),
    R_prime R (@Whole U) (@Whole U).
Proof.
  intros U R. apply UE.point_self_loop.
Qed.

(** Whole is terminal sink w.r.t. U (cannot reach any element from Whole). *)
Theorem Whole_terminal :
  forall (U : Type) (R : U -> U -> Prop) (b : U),
    ~ R_prime R Whole (elem b).
Proof.
  intros U R b. apply UE.point_terminal.
Qed.

(** No entity is isolated in the completion. *)
Theorem no_isolated_entities :
  forall (U : Type) (R : U -> U -> Prop),
    ~ exists x : Ux U, forall y : Ux U, ~ R_prime R x y.
Proof.
  intros U R. apply UE.no_dead_ends.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Embedding Properties                               *)
(* -------------------------------------------------------------------------- *)

(** elem is injective. *)
Theorem elem_injective :
  forall (U : Type) (a b : U), elem a = elem b -> a = b.
Proof.
  intros U a b H. apply UE.elem_injective. exact H.
Qed.

(** Whole is fresh (not in the image of elem). *)
Theorem Whole_fresh :
  forall (U : Type) (u : U), elem u <> (@Whole U).
Proof.
  intros U u. apply UE.point_fresh.
Qed.

(** Freshness in symmetric form. *)
Theorem Whole_fresh_sym :
  forall (U : Type) (u : U), (@Whole U) <> elem u.
Proof.
  intros U u H. apply (Whole_fresh U u). symmetry. exact H.
Qed.

(** The lifted relation is never empty (has at least one edge). *)
Theorem relation_nonempty :
  forall (U : Type) (R : U -> U -> Prop),
    exists x y : Ux U, R_prime R x y.
Proof.
  intros U R. exists Whole, Whole. apply UE.point_self_loop.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: INVERSION PRINCIPLES                         *)
(*                                                                            *)
(* ========================================================================== *)

(** Case analysis on Ux elements. *)
Theorem Ux_case : forall (U : Type) (x : Ux U),
  x = Whole \/ exists u : U, x = elem u.
Proof.
  intros U x. apply UE.carrier_case.
Qed.

(** If R'(x, elem b) then x = elem a for some a with R a b. *)
Theorem R_prime_to_elem_inv :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U) (b : U),
    R_prime R x (elem b) -> exists a : U, x = elem a /\ R a b.
Proof.
  intros U R x b H. apply UE.lift_to_elem_inv. exact H.
Qed.

(** If R'(Whole, y) then y = Whole. *)
Theorem R_prime_from_Whole_inv :
  forall (U : Type) (R : U -> U -> Prop) (y : Ux U),
    R_prime R Whole y -> y = Whole.
Proof.
  intros U R y H.
  unfold R_prime, Whole in H.
  apply WholeCompletion.lift_rel_from_point_inv in H. exact H.
Qed.

(** Decidability of carrier equality (given decidable U), explicit-argument form.
    Useful where the discharge proof is constructed locally; the canonical
    typeclass form [Ux_eq_dec] is below. *)
Theorem Ux_eq_dec_explicit :
  forall (U : Type),
    (forall a b : U, {a = b} + {a <> b}) ->
    forall x y : Ux U, {x = y} + {x <> y}.
Proof.
  intros U Udec. apply WholeCompletion.carrier_eq_dec. exact Udec.
Defined.

(** Decidable-equality type class, hosted in Prop_01 so that every downstream
    file inherits it via a single import.  Previously [Class DecEq] was
    duplicated in Prop_02 and Prop_04. *)
Class DecEq (A : Type) := {
  dec_eq : forall x y : A, {x = y} + {x <> y}
}.

(** Standard [DecEq] instances. *)
#[export] Instance DecEq_option {A : Type} `{HA : DecEq A} : DecEq (option A).
Proof.
  constructor. intros x y.
  destruct x as [a|]; destruct y as [b|].
  - destruct (dec_eq a b) as [Heq | Hneq].
    + left. rewrite Heq. reflexivity.
    + right. intro Heq'. apply Hneq. injection Heq' as Hinj. exact Hinj.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

#[export] Instance DecEq_nat : DecEq nat.
Proof.
  constructor. intros x y.
  decide equality.
Defined.

#[export] Instance DecEq_bool : DecEq bool.
Proof.
  constructor. intros x y.
  decide equality.
Defined.

#[export] Instance DecEq_unit : DecEq unit.
Proof.
  constructor. intros x y.
  destruct x, y. left. reflexivity.
Defined.

(** Canonical type-class form of carrier decidability.  This is the form used
    throughout the Propositions and Cubical layers; the explicit-argument form
    above is kept as [Ux_eq_dec_explicit] for direct API access. *)
Lemma Ux_eq_dec {U : Type} `{HU : DecEq U} : forall (x y : Ux U), {x = y} + {x <> y}.
Proof. apply dec_eq. Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: RELATION PROPERTY PRESERVATION               *)
(*                                                                            *)
(* ========================================================================== *)

(** Lifting preserves reflexivity. *)
Theorem R_prime_preserves_reflexive :
  forall (U : Type) (R : U -> U -> Prop),
    Top__Extensions__Base.Reflexive R ->
    Top__Extensions__Base.Reflexive (R_prime R).
Proof.
  intros U R Hrefl. apply WholeCompletion.lift_preserves_reflexive. exact Hrefl.
Qed.

(** Lifting preserves symmetry between elements. *)
Theorem R_prime_symmetric_on_elems :
  forall (U : Type) (R : U -> U -> Prop),
    Top__Extensions__Base.Symmetric R ->
    forall a b : U, R_prime R (elem a) (elem b) -> R_prime R (elem b) (elem a).
Proof.
  intros U R Hsym a b H. apply WholeCompletion.lift_symmetric_on_elems.
  - exact Hsym.
  - exact H.
Qed.

(** Lifting preserves transitivity on element chains. *)
Theorem R_prime_transitive_on_elems :
  forall (U : Type) (R : U -> U -> Prop),
    Top__Extensions__Base.Transitive R ->
    forall a b c : U,
      R_prime R (elem a) (elem b) ->
      R_prime R (elem b) (elem c) ->
      R_prime R (elem a) (elem c).
Proof.
  intros U R Htrans a b c Hab Hbc.
  apply WholeCompletion.lift_transitive_on_elems with (b := b).
  - exact Htrans.
  - exact Hab.
  - exact Hbc.
Qed.

(** Lifting is monotone. *)
Theorem R_prime_monotone :
  forall (U : Type) (R S : U -> U -> Prop),
    (forall a b, R a b -> S a b) ->
    forall x y : Ux U, R_prime R x y -> R_prime S x y.
Proof.
  intros U R S Himpl x y H.
  apply (WholeCompletion.lift_monotone_general U R S Himpl x y H).
Qed.

(** Lifting respects logical equivalence. *)
Theorem R_prime_equiv :
  forall (U : Type) (R S : U -> U -> Prop),
    (forall a b, R a b <-> S a b) ->
    forall x y : Ux U, R_prime R x y <-> R_prime S x y.
Proof.
  intros U R S Hequiv x y.
  apply (WholeCompletion.lift_equiv U R S Hequiv x y).
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: EXTENSION INFRASTRUCTURE                     *)
(*                                                                            *)
(*  For propositions that need the full extension machinery.                  *)
(*                                                                            *)
(* ========================================================================== *)

Module Extension.

  (** Re-export record types. *)
  Definition UniverseExtension := UE.Extension.
  Definition PointedUniverseExtension := UE.PointedExt.
  Definition FreshPointedUniverseExtension := UE.FreshPointedExt.
  Definition SerialExtension := UE.SerialExt.
  Definition PointedSerialExtension := UE.PointedSerialExtension.

  (** Canonical serial extension via Whole-completion. *)
  Definition serial_extension (U : Type) : SerialExtension U := UE.pointed_serial U.

  (** Composition of extensions. *)
  Definition compose {U : Type}
    (E1 : Top__Extensions__Base.UniverseExtension U)
    (E2 : Top__Extensions__Base.UniverseExtension (ue_carrier E1)) :=
    Composition.compose E1 E2.

  (** Identity extension. *)
  Definition id_extension (U : Type) := UE.id_extension U.

  (** Morphisms. *)
  Definition Hom := @UE.Hom.
  Definition Iso := @UE.Iso.

  (** Access to underlying completion. *)
  Definition as_extension (U : Type) := WholeCompletion.as_extension U.
  Definition as_pointed (U : Type) := WholeCompletion.as_pointed U.
  Definition as_fresh_pointed (U : Type) := WholeCompletion.as_fresh_pointed U.
  Definition as_pointed_serial (U : Type) := WholeCompletion.as_pointed_serial U.

End Extension.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: EXAMPLES                                     *)
(*                                                                            *)
(* ========================================================================== *)

Module SerialityExamples.

  (** Example with nat: any relation becomes serial. *)
  Example nat_serial :
    forall (R : nat -> nat -> Prop) (x : Ux nat),
      exists y : Ux nat, R_prime R x y.
  Proof.
    intros R x. exists Whole. apply UE.serial.
  Qed.

  (** Example: 3 < 5 is preserved in the completion. *)
  Example lt_preserved : R_prime lt (elem 3) (elem 5).
  Proof.
    apply R_lift. auto.
  Qed.

  (** Example: the completion has at least two elements for nonempty U. *)
  Example completion_has_two_elements :
    forall (U : Type) (u : U), elem u <> (@Whole U).
  Proof.
    intros U u. apply Whole_fresh.
  Qed.

  (** Example: empty relation becomes serial. *)
  Example empty_becomes_serial :
    forall (x : Ux nat),
      exists y : Ux nat, R_prime (fun _ _ => False) x y.
  Proof.
    intro x. exists Whole. apply UE.serial.
  Qed.

  (** Example: reflexive relation stays reflexive. *)
  Example reflexive_preserved :
    forall (U : Type) (R : U -> U -> Prop),
      Top__Extensions__Base.Reflexive R ->
      forall x : Ux U, R_prime R x x.
  Proof.
    intros U R Hrefl x.
    apply R_prime_preserves_reflexive. exact Hrefl.
  Qed.

  (** Example: conservativity in action. *)
  Example conservativity_example :
    R_prime lt (elem 2) (elem 5) <-> 2 < 5.
  Proof.
    apply R_prime_conservative.
  Qed.

End SerialityExamples.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: P1 MODULE - PUBLIC API                       *)
(*                                                                            *)
(* ========================================================================== *)

(**
  P1: The canonical public API for Proposition 01.

  This module provides stable, memorable names for downstream use.
  Prefer importing this over using raw definitions.

  NAMING CONVENTIONS:
    - Types start with uppercase: Carrier, Ux
    - Constructors/values use lowercase: whole, elem
    - Lemmas use snake_case: serial, conservative
*)

Module P1.

  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)

  (** The extended carrier type. *)
  Definition Carrier (U : Type) := Ux U.

  (* ====================================================================== *)
  (*                           Constructors                                 *)
  (* ====================================================================== *)

  (** The distinguished Whole element. *)
  Definition whole {U : Type} : Carrier U := Whole.

  (** Embed an element of U into the extended carrier. *)
  Definition embed {U : Type} := @elem U.

  (** Lift a relation. *)
  Definition lift {U : Type} := @R_prime U.

  (** Constructive witness. *)
  Definition wit {U : Type} := @witness U.

  (* ====================================================================== *)
  (*                        Main Theorems                                   *)
  (* ====================================================================== *)

  (** The main theorem. *)
  Definition serial := proposition_01.

  (** Pointed seriality. *)
  Definition pointed_serial := pointed_seriality.

  (** Constructive version. *)
  Definition serial_constructive := proposition_01_constructive.

  (** Sigma type version. *)
  Definition serial_sigma := proposition_01_sigma.

  (** Weak seriality. *)
  Definition weak_serial := weak_seriality.

  (* ====================================================================== *)
  (*                        Conservativity                                  *)
  (* ====================================================================== *)

  Definition conservative {U : Type} := @R_prime_conservative U.
  Definition conservative_fwd {U : Type} := @R_prime_conservative_fwd U.
  Definition conservative_bwd {U : Type} := @R_prime_conservative_bwd U.
  Definition lift_edge {U : Type} := @R_lift U.

  (* ====================================================================== *)
  (*                        Whole Properties                                *)
  (* ====================================================================== *)

  Definition to_whole {U : Type} := @everything_relates_to_Whole U.
  Definition whole_loop {U : Type} := @Whole_self_loop U.
  Definition whole_terminal {U : Type} := @Whole_terminal U.
  Definition no_isolated {U : Type} := @no_isolated_entities U.

  (* ====================================================================== *)
  (*                        Embedding Properties                            *)
  (* ====================================================================== *)

  Definition elem_inj {U : Type} := @elem_injective U.
  Definition whole_fresh {U : Type} := @Whole_fresh U.
  Definition whole_fresh_sym {U : Type} := @Whole_fresh_sym U.
  Definition nonempty {U : Type} := @relation_nonempty U.

  (* ====================================================================== *)
  (*                        Inversion                                       *)
  (* ====================================================================== *)

  Definition case {U : Type} := @Ux_case U.
  Definition to_elem_inv {U : Type} := @R_prime_to_elem_inv U.
  Definition from_whole_inv {U : Type} := @R_prime_from_Whole_inv U.

  (* ====================================================================== *)
  (*                        Property Preservation                           *)
  (* ====================================================================== *)

  Definition preserves_refl {U : Type} := @R_prime_preserves_reflexive U.
  Definition sym_on_elems {U : Type} := @R_prime_symmetric_on_elems U.
  Definition trans_on_elems {U : Type} := @R_prime_transitive_on_elems U.
  Definition monotone {U : Type} := @R_prime_monotone U.
  Definition equiv {U : Type} := @R_prime_equiv U.

  (* ====================================================================== *)
  (*                        Extension Infrastructure                        *)
  (* ====================================================================== *)

  Definition serial_extension := Extension.serial_extension.
  Definition compose := @Extension.compose.
  Definition id_extension := Extension.id_extension.

End P1.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: HINT DATABASES                               *)
(*                                                                            *)
(* ========================================================================== *)

(** Core hints for Proposition 01. *)

#[export] Hint Rewrite
  @R_prime_conservative
  : prop1.

#[export] Hint Resolve
  proposition_01
  proposition_01_constructive
  pointed_seriality
  weak_seriality
  everything_relates_to_Whole
  Whole_self_loop
  Whole_terminal
  no_isolated_entities
  elem_injective
  Whole_fresh
  Whole_fresh_sym
  relation_nonempty
  R_prime_conservative_bwd
  R_lift
  R_prime_preserves_reflexive
  : prop1.

(** Extension infrastructure hints. *)

#[export] Hint Resolve
  UE.serial
  UE.point_self_loop
  UE.point_terminal
  UE.point_fresh
  UE.elem_injective
  UE.conservative
  UE.lift_preserves
  UE.no_dead_ends
  : prop1_ext.

#[export] Hint Extern 1 (exists _, R_prime _ _ _) =>
  exists Whole; apply UE.serial : prop1.

#[export] Hint Extern 1 (R_prime _ _ Whole) =>
  apply UE.serial : prop1.

#[export] Hint Extern 1 (~ R_prime _ Whole (elem _)) =>
  apply Whole_terminal : prop1.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: TACTICS                                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Tactic to prove seriality goals. *)
Ltac prove_seriality :=
  match goal with
  | |- exists y, R_prime _ _ y => exists Whole; apply UE.serial
  | |- exists y, UE.lift _ _ y => exists UE.Whole; apply UE.serial
  | |- R_prime _ _ Whole => apply UE.serial
  | |- UE.lift _ _ UE.Whole => apply UE.serial
  | |- exists y, _ => exists Whole; apply UE.serial
  end.

(** Tactic to simplify R_prime expressions. *)
Ltac rprime_simpl :=
  unfold R_prime, elem, Whole, Ux;
  unfold UE.lift, UE.elem, UE.Whole, UE.Carrier;
  unfold WholeCompletion.lift_rel, WholeCompletion.inject, WholeCompletion.point;
  simpl.

(** Tactic to prove conservativity goals. *)
Ltac rprime_conservative :=
  match goal with
  | |- R_prime _ (elem _) (elem _) => apply R_prime_conservative_bwd
  | |- R_prime _ (elem _) (elem _) <-> _ => apply R_prime_conservative
  | H : R_prime _ (elem _) (elem _) |- _ => apply R_prime_conservative in H
  end.

(** Tactic for case analysis on Ux elements. *)
Ltac ux_destruct x :=
  destruct (Ux_case _ x) as [Hwhole | [u Helem]];
  [ (* x = Whole *) subst x | (* x = elem u *) subst x ].

(** Tactic for inversion on R_prime. *)
Ltac rprime_inv :=
  match goal with
  | H : R_prime _ Whole ?y |- _ =>
      apply R_prime_from_Whole_inv in H; subst y
  | H : R_prime _ ?x (elem ?b) |- _ =>
      let a := fresh "a" in
      let Heq := fresh "Heq" in
      let HR := fresh "HR" in
      destruct (R_prime_to_elem_inv _ _ x b H) as [a [Heq HR]]; subst x
  end.

(** Combined automation tactic. *)
Ltac prop1_auto :=
  auto with prop1;
  try prove_seriality;
  try rprime_conservative.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: ARGUMENTS & IMPLICIT HANDLING               *)
(*                                                                            *)
(* ========================================================================== *)

Arguments Ux U : clear implicits.
Arguments Whole {U}.
Arguments elem {U} u.
Arguments R_prime {U} R x y.
Arguments witness {U} x.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: NOTATION SCOPES                             *)
(*                                                                            *)
(* ========================================================================== *)

(** Declare a scope for Proposition 01 notations. *)
Declare Scope prop1_scope.
Delimit Scope prop1_scope with p1.

Notation "R '^'" := (R_prime R) (at level 30, no associativity) : prop1_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: AXIOM AUDIT                                 *)
(*                                                                            *)
(*  Verification that this file uses ZERO AXIOMS.                             *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)

  Definition test_Whole : @Whole nat = @None nat.
  Proof. reflexivity. Qed.

  Definition test_elem : @elem nat 42 = Some 42.
  Proof. reflexivity. Qed.

  Definition test_R_prime_Whole_Whole :
    R_prime (fun _ _ : nat => False) (@Whole nat) (@Whole nat) = True.
  Proof. reflexivity. Qed.

  Definition test_R_prime_elem_Whole :
    R_prime (fun _ _ : nat => False) (elem 42) Whole = True.
  Proof. reflexivity. Qed.

  Definition test_R_prime_Whole_elem :
    R_prime (fun _ _ : nat => True) (@Whole nat) (elem 0) = False.
  Proof. reflexivity. Qed.

  Definition test_R_prime_elem_elem :
    R_prime lt (elem 3) (elem 5) = (3 < 5).
  Proof. reflexivity. Qed.

  Definition test_witness : @witness nat (elem 5) = Whole.
  Proof. reflexivity. Qed.

  Definition test_Ux : Ux nat = option nat.
  Proof. reflexivity. Qed.

End AxiomAudit.

(* Live axiom audit   all should show "Closed under the global context" *)
Print Assumptions proposition_01.
Print Assumptions P1.serial.
Print Assumptions P1.whole_loop.
Print Assumptions P1.no_isolated.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============

  PUBLIC API MODULE (P1):
    P1.Carrier U        = Ux U (the extended type)
    P1.whole            = Whole (terminal element)
    P1.embed            = elem (injection)
    P1.lift             = R_prime (relation lifting)
    P1.serial           = proposition_01
    P1.conservative     = R_prime_conservative
    P1.to_whole         = everything_relates_to_Whole
    P1.whole_terminal   = Whole_terminal
    P1.elem_inj         = elem_injective

  TYPES:
    Ux U                = option U (the extended universe)

  CONSTRUCTORS:
    Whole               = None (the terminal element)
    elem u              = Some u (embedding)

  RELATION:
    R_prime R           = the serial completion of R
    R^ (in prop1_scope) = R_prime R

  MAIN THEOREMS:
    proposition_01              : forall U R x, exists y, R_prime R x y
    pointed_seriality           : exists w, forall x, R_prime R x w
    proposition_01_constructive : R_prime R x (witness x)

  KEY PROPERTIES:
    R_prime_conservative        : R_prime R (elem a) (elem b) <-> R a b
    everything_relates_to_Whole : R_prime R x Whole
    Whole_terminal              : ~ R_prime R Whole (elem b)
    no_isolated_entities        : ~ exists x, forall y, ~ R_prime R x y
    elem_injective              : elem a = elem b -> a = b
    Whole_fresh                 : elem u <> Whole

  INVERSION:
    Ux_case                     : x = Whole \/ exists u, x = elem u
    R_prime_to_elem_inv         : R_prime R x (elem b) -> exists a, ...
    R_prime_from_Whole_inv      : R_prime R Whole y -> y = Whole

  PROPERTY PRESERVATION:
    R_prime_preserves_reflexive : Reflexive R -> Reflexive (R_prime R)
    R_prime_monotone            : (R <= S) -> (R_prime R <= R_prime S)

  HINT DATABASES:
    prop1     : core lemmas for Proposition 01
    prop1_ext : extension infrastructure lemmas

    Usage: auto with prop1. / auto with prop1_ext.

  TACTICS:
    prove_seriality     : prove seriality goals
    rprime_simpl        : unfold and simplify R_prime
    rprime_conservative : handle conservativity
    ux_destruct x       : case split on Whole / elem
    rprime_inv          : inversion on R_prime hypotheses
    prop1_auto          : combined automation

  NOTATION SCOPE (prop1_scope):
    R^        = R_prime R

    Usage: Open Scope prop1_scope.

  EXTENSION INFRASTRUCTURE:
    Extension.serial_extension U  : SerialExtension U
    Extension.compose E1 E2       : composition of extensions
    Extension.id_extension U      : identity extension

  AXIOM STATUS
  ============

  This file uses ZERO AXIOMS. All theorems are fully polymorphic in U.
  Run `Print Assumptions proposition_01.` to verify: output should be
  "Closed under the global context".

  COMPILATION
  ===========

  Requires: Top__Extensions__Prelude.v (and its dependencies)

    coqc Top__Extensions__Base.v
    coqc Top__Extensions__WholeCompletion.v
    coqc Top__Extensions__Composition.v
    coqc Top__Extensions__Prelude.v
    coqc Top__Propositions__Prop_01.v

  USAGE EXAMPLE
  =============

    Require Import Top__Propositions__Prop_01.

    (* Use the P1 module for clean access *)
    Check P1.serial.   (* forall U R x, exists y, P1.lift R x y *)

    (* Use tactics for proofs *)
    Goal forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      exists y, R_prime R x y.
    Proof. intros U R x. prove_seriality. Qed.

    (* Use hint databases *)
    Goal forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      R_prime R x Whole.
    Proof. intros. auto with prop1. Qed.
*)
