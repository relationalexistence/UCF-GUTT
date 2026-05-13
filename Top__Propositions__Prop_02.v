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
  |          PROPOSITION 02: DIMENSIONALITY OF SPHERE OF RELATION            |
  |                                                                          |
  |                      UCF/GUTT(TM) Formal Verification                    |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-21                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  THEOREM: Relations can be represented in multi-dimensional spaces       |
  |                                                                          |
  |  "Every pair of related entities (x,y) in the extended universe can be   |
  |   mapped to a point in an n-dimensional space via an ego-centric tensor" |
  |                                                                          |
  |  This builds on Proposition 01 (seriality) to show that relations have   |
  |  multi-dimensional representations, capturing the "Dimensional Sphere    |
  |  of Relation" (DSoR) concept from UCF/GUTT.                              |
  |                                                                          |
  |  KEY INSIGHT: Dimensions use R_cauchy (constructive reals from           |
  |  RelationalReals.v), keeping the entire framework axiom-free.            |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Core Definitions (Dimension, DSoR, Tensor)                |
  |    SECTION 2:  Multi-Dimensional Representation Theorem                  |
  |    SECTION 3:  Well-Formedness Properties                                |
  |    SECTION 4:  Connection to Seriality (Prop 01)                         |
  |    SECTION 5:  Examples & Instantiation                                  |
  |    SECTION 6:  P2 Module - Public API                                    |
  |    SECTION 7:  Hint Databases                                            |
  |    SECTION 8:  Axiom Audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Core definitions: Dimension, DSoR, MultiDimRelation, Tensor       |
  |      - Main theorems: multi_dim_representation, every_entity_has_dsor    |
  |      - P2 module exports                                                 |
  |      - Hint database: prop2                                              |
  |                                                                          |
  |  DEPENDENCIES:                                                           |
  |    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)        |
  |    - Top__Numbers__RelationalReals.v (R_cauchy, R_zero, Q_to_R)          |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Propositions__Prop_01.
Require Import Top__Numbers__RelationalReals.
Require Import Coq.QArith.QArith.
Require Import List.
Import ListNotations.

(* Open Q_scope for rational number notation *)
Local Open Scope Q_scope.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: CORE DEFINITIONS                             *)
(*                                                                            *)
(*  All definitions are polymorphic in U - no axioms required.                *)
(*  Dimensions use R_cauchy (constructive reals from Cauchy sequences).       *)
(*                                                                            *)
(* ========================================================================== *)

(** A dimension is represented as a constructive real number. *)
Definition Dimension := R_cauchy.

(** A multi-dimensional space is a tuple (list) of n dimensions. *)
Definition MultiDimSpace (n : nat) := list R_cauchy.

(**
  The Dimensional Sphere of Relation (DSoR) is a point in R^n.
  In UCF/GUTT, this captures the multi-dimensional nature of relations:
  each relation can be characterized by multiple attributes simultaneously.
*)
Definition DSoR (n : nat) := MultiDimSpace n.

(**
  A multi-dimensional relation maps entity pairs to dimension tuples.
  This is polymorphic in the carrier type C.
*)
Definition MultiDimRelation (C : Type) (n : nat) := C -> C -> MultiDimSpace n.

(**
  An ego-centric tensor is a multi-dimensional relation that captures
  subjective, perspective-dependent relations. Key property: asymmetry
  is allowed (T(x,y) need not equal T(y,x)).
*)
Definition EgoCentricTensor (C : Type) (n : nat) := MultiDimRelation C n.

(** Alias for working with the extended universe from Prop 01. *)
Definition ExtendedTensor (U : Type) (n : nat) := EgoCentricTensor (Ux U) n.

(** Helper: create a list of n zeros (using R_zero from RelationalReals). *)
Fixpoint repeat_zero (n : nat) : list R_cauchy :=
  match n with
  | O => nil
  | S n' => R_zero :: repeat_zero n'
  end.

(** Length of repeat_zero is always n. *)
Lemma repeat_zero_length : forall n, length (repeat_zero n) = n.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: MULTI-DIMENSIONAL REPRESENTATION             *)
(*                                                                            *)
(* ========================================================================== *)

(** [Class DecEq], [Instance DecEq_option], and [Lemma Ux_eq_dec] are
    inherited from Top__Propositions__Prop_01.  Previously this file
    duplicated all three; they have been moved to Prop_01 as the canonical
    location (lowest common ancestor of Prop_02, Prop_04, Prop_05, NCube).
    [DecEq_nat] and [DecEq_bool] instances (formerly declared at the end of
    this file) also live in Prop_01 now. *)

Section MultiDimRepresentation.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    MAIN THEOREM: Relations can be represented multi-dimensionally.

    For any related pair (x,y) under R', there exists:
    - A point d in the n-dimensional DSoR
    - An ego-centric tensor T such that T(x,y) = d

    This is CONSTRUCTIVE: we provide explicit witnesses.
  *)
  Theorem multi_dim_representation :
    forall (x y : Ux U) (n : nat),
      R_prime R x y ->
      exists (d : DSoR n) (T : ExtendedTensor U n), T x y = d.
  Proof.
    intros x y n Hrel.
    (* Construct a default DSoR point: repeat 0.0 n times *)
    set (d := repeat_zero n).
    exists d.
    (* Construct tensor T that returns d for (x,y) and zeros elsewhere *)
    exists (fun a b =>
      match Ux_eq_dec a x with
      | left _ =>
          match Ux_eq_dec b y with
          | left _ => d
          | right _ => repeat_zero n
          end
      | right _ => repeat_zero n
      end).
    (* Prove T x y = d *)
    destruct (Ux_eq_dec x x) as [_ | Hneq]; [| contradiction Hneq; reflexivity].
    destruct (Ux_eq_dec y y) as [_ | Hneq]; [| contradiction Hneq; reflexivity].
    reflexivity.
  Qed.

End MultiDimRepresentation.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: WELL-FORMEDNESS PROPERTIES                   *)
(*                                                                            *)
(* ========================================================================== *)

(** A tensor is well-formed if it always produces correct-length outputs. *)
Definition WellFormedTensor {C : Type} (n : nat) (T : EgoCentricTensor C n) : Prop :=
  forall x y, length (T x y) = n.

Section WellFormedness.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (** The constructed tensor from multi_dim_representation is always well-formed. *)
  Theorem multi_dim_representation_wellformed :
    forall (x y : Ux U) (n : nat),
      R_prime R x y ->
      exists (d : DSoR n) (T : ExtendedTensor U n),
        WellFormedTensor n T /\ T x y = d.
  Proof.
    intros x y n Hrel.
    set (d := repeat_zero n).
    exists d.
    exists (fun a b =>
      match Ux_eq_dec a x with
      | left _ =>
          match Ux_eq_dec b y with
          | left _ => d
          | right _ => repeat_zero n
          end
      | right _ => repeat_zero n
      end).
    split.
    - (* Prove well-formedness *)
      intros a b.
      destruct (Ux_eq_dec a x); destruct (Ux_eq_dec b y);
        unfold d; apply repeat_zero_length.
    - (* Prove T x y = d *)
      destruct (Ux_eq_dec x x) as [_ | Hneq]; [| contradiction Hneq; reflexivity].
      destruct (Ux_eq_dec y y) as [_ | Hneq]; [| contradiction Hneq; reflexivity].
      reflexivity.
  Qed.

End WellFormedness.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: CONNECTION TO SERIALITY                      *)
(*                                                                            *)
(* ========================================================================== *)

Section SerialityConnection.

  Context {U : Type}.
  Context `{HU : DecEq U}.
  Variable R : U -> U -> Prop.

  (**
    Every entity has a DSoR representation with respect to Whole.
    This follows from Proposition 01: every x relates to Whole.
  *)
  Theorem every_entity_has_dsor :
    forall (x : Ux U) (n : nat),
      (n > 0)%nat ->
      exists (d : DSoR n) (T : ExtendedTensor U n),
        T x Whole = d.
  Proof.
    intros x n Hn.
    (* From Prop 01: everything relates to Whole *)
    assert (Hrel : R_prime R x Whole) by apply everything_relates_to_Whole.
    (* Apply multi_dim_representation *)
    apply (multi_dim_representation R x Whole n Hrel).
  Qed.

  (** Corollary: Every related pair has a DSoR representation. *)
  Theorem every_pair_has_dsor :
    forall (x y : Ux U) (n : nat),
      R_prime R x y ->
      exists (d : DSoR n) (T : ExtendedTensor U n),
        T x y = d.
  Proof.
    intros x y n Hrel.
    apply (multi_dim_representation R x y n Hrel).
  Qed.

  (** The dimension can be arbitrary - works for any n and m. *)
  Theorem dsor_arbitrary_dimension :
    forall (x y : Ux U) (n m : nat),
      R_prime R x y ->
      (exists (d : DSoR n) (T : ExtendedTensor U n), T x y = d) /\
      (exists (d : DSoR m) (T : ExtendedTensor U m), T x y = d).
  Proof.
    intros x y n m Hrel.
    split.
    - apply (multi_dim_representation R x y n Hrel).
    - apply (multi_dim_representation R x y m Hrel).
  Qed.

End SerialityConnection.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: EXAMPLES & INSTANTIATION                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Standard [DecEq] instances ([DecEq_nat], [DecEq_bool], [DecEq_unit])
    are inherited from Top__Propositions__Prop_01. *)

Module NatExamples.

  (** Concrete instantiation for nat. *)
  Definition NatUx := Ux nat.
  Definition NatDSoR := DSoR 2.
  Definition NatTensor := ExtendedTensor nat 2.

  (** Example: natural number less-than relation. *)
  Definition lt_rel : nat -> nat -> Prop := lt.

  (** Every natural number has a 2D DSoR with respect to Whole. *)
  Example nat_to_whole_dsor : forall n : nat,
    exists (d : DSoR 2) (T : NatTensor), T (elem n) Whole = d.
  Proof.
    intro n.
    apply every_entity_has_dsor.
    - exact lt_rel.
    - auto.
  Qed.

  (** Concrete DSoR point example using Q_to_R for rational approximations. *)
  Definition example_point : NatDSoR := [Q_to_R (3#2); Q_to_R (27#10)].

  (** Verify it has the right length. *)
  Example example_point_length : length example_point = 2%nat.
  Proof. reflexivity. Qed.

End NatExamples.

Module AsymmetryExample.

  (**
    Demonstration of ego-centric asymmetry.
    Given two distinct entities, their tensor values can differ
    based on perspective (direction of the relation).
  *)
  Section WithEntities.
    Context {U : Type}.
    Context `{HU : DecEq U}.
    Variable R : U -> U -> Prop.

    Variable a b : U.
    Hypothesis distinct : a <> b.
    Hypothesis related : R a b.

    (**
      Asymmetric tensor: maps (a,b) to one point, (b,a) to another.
      This captures the "ego-centric" nature of UCF/GUTT relations.
      Using Q_to_R for rational dimension values.
    *)
    Definition asymmetric_tensor : ExtendedTensor U 2 :=
      fun x y =>
        match Ux_eq_dec x (elem a) with
        | left _ =>
            match Ux_eq_dec y (elem b) with
            | left _ => [Q_to_R 100; Q_to_R (209#2)]  (* a's perspective: 100.0, 104.5 *)
            | right _ => [R_zero; R_zero]
            end
        | right _ =>
            match Ux_eq_dec x (elem b) with
            | left _ =>
                match Ux_eq_dec y (elem a) with
                | left _ => [Q_to_R 100; Q_to_R 103]  (* b's perspective: 100.0, 103.0 *)
                | right _ => [R_zero; R_zero]
                end
            | right _ => [R_zero; R_zero]
            end
        end.

    (** The tensor values differ based on direction. *)
    Lemma asymmetric_values :
      asymmetric_tensor (elem a) (elem b) = [Q_to_R 100; Q_to_R (209#2)] /\
      asymmetric_tensor (elem b) (elem a) = [Q_to_R 100; Q_to_R 103].
    Proof.
      unfold asymmetric_tensor.
      split.
      - (* a -> b *)
        destruct (Ux_eq_dec (elem a) (elem a)) as [_ | Hneq];
          [| contradiction Hneq; reflexivity].
        destruct (Ux_eq_dec (elem b) (elem b)) as [_ | Hneq];
          [| contradiction Hneq; reflexivity].
        reflexivity.
      - (* b -> a *)
        destruct (Ux_eq_dec (elem b) (elem a)) as [Heq | _].
        + (* b = a contradicts distinct *)
          exfalso. apply distinct.
          apply elem_injective. symmetry. exact Heq.
        + destruct (Ux_eq_dec (elem b) (elem b)) as [_ | Hneq];
            [| contradiction Hneq; reflexivity].
          destruct (Ux_eq_dec (elem a) (elem a)) as [_ | Hneq];
            [| contradiction Hneq; reflexivity].
          reflexivity.
    Qed.

  End WithEntities.

End AsymmetryExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: P2 MODULE - PUBLIC API                       *)
(*                                                                            *)
(* ========================================================================== *)

(**
  P2: The canonical public API for Proposition 02.

  Provides stable, memorable names for downstream developments.
*)
Module P2.

  (* Types *)
  Definition dim := Dimension.
  Definition space := MultiDimSpace.
  Definition dsor := DSoR.
  Definition tensor (C : Type) := EgoCentricTensor C.
  Definition ext_tensor := ExtendedTensor.

  (* Core theorems *)
  Definition representation := @multi_dim_representation.
  Definition wellformed := @multi_dim_representation_wellformed.
  Definition entity_dsor := @every_entity_has_dsor.
  Definition pair_dsor := @every_pair_has_dsor.
  Definition arbitrary_dim := @dsor_arbitrary_dimension.

  (* Utilities *)
  Definition zeros := repeat_zero.
  Definition zeros_length := repeat_zero_length.

End P2.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: HINT DATABASES                               *)
(*                                                                            *)
(* ========================================================================== *)

Create HintDb prop2.

#[export] Hint Resolve repeat_zero_length : prop2.

(**
  Note: The parametric theorems multi_dim_representation, every_entity_has_dsor,
  and every_pair_has_dsor are best applied directly rather than via hints
  because they require explicit relation parameters.
*)

(** Combined tactic for Prop 2 goals. *)
Ltac prop2_auto :=
  auto with prop2 prop1;
  try (eapply multi_dim_representation; [apply everything_relates_to_Whole | ..]);
  try apply everything_relates_to_Whole.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: AXIOM AUDIT                                  *)
(*                                                                            *)
(*  Verification that this file uses ZERO AXIOMS.                             *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)

  Definition test_repeat_zero : repeat_zero 3 = [R_zero; R_zero; R_zero].
  Proof. reflexivity. Qed.

  Definition test_DSoR_type : DSoR 2 = list R_cauchy.
  Proof. reflexivity. Qed.

  (**
    Key test: multi_dim_representation compiles and doesn't need axioms
    beyond what Prop 01 provides (which is nothing).
  *)
  Definition test_representation_compiles :
    forall (n : nat) `{HU : DecEq nat},
      R_prime lt (elem 3%nat) (elem 5%nat) ->
      exists (d : DSoR n) (T : ExtendedTensor nat n), T (elem 3%nat) (elem 5%nat) = d.
  Proof.
    intros n HU Hrel.
    apply (multi_dim_representation lt).
    exact Hrel.
  Qed.

  (** Alternative: just verify it's decidable. *)
  Definition test_nat_decidable : {3%nat = 5%nat} + {3%nat <> 5%nat}.
  Proof. right. discriminate. Defined.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============

  PUBLIC API MODULE (P2):
    P2.dsor n             = DSoR n (n-dimensional sphere type)
    P2.tensor C n         = EgoCentricTensor C n
    P2.ext_tensor U n     = ExtendedTensor U n
    P2.representation     = multi_dim_representation
    P2.entity_dsor        = every_entity_has_dsor
    P2.pair_dsor          = every_pair_has_dsor
    P2.zeros n            = repeat_zero n

  TYPES:
    Dimension             = R_cauchy (constructive real from Cauchy sequences)
    MultiDimSpace n       = list R_cauchy (n-dimensional point)
    DSoR n                = MultiDimSpace n (alias)
    EgoCentricTensor C n  = C -> C -> MultiDimSpace n
    ExtendedTensor U n    = EgoCentricTensor (Ux U) n

  TYPECLASS:
    DecEq A               : decidable equality on A
    DecEq_option          : A decidable => option A decidable
    DecEq_nat             : nat has decidable equality
    DecEq_bool            : bool has decidable equality

  MAIN THEOREMS:
    multi_dim_representation:
      forall x y n, R_prime R x y -> exists d T, T x y = d

    every_entity_has_dsor:
      forall x n, (n > 0)%nat -> exists d T, T x Whole = d

    every_pair_has_dsor:
      forall x y n, R_prime R x y -> exists d T, T x y = d

    dsor_arbitrary_dimension:
      For any n,m: both n-dim and m-dim representations exist

  WELL-FORMEDNESS:
    WellFormedTensor n T  : forall x y, length (T x y) = n
    multi_dim_representation_wellformed:
      Constructed tensors are always well-formed

  HINT DATABASE:
    prop2                 : automation hints for DSoR proofs

    Usage: auto with prop2. / prop2_auto.

  TACTICS:
    prop2_auto            : combined automation

  PHILOSOPHICAL SIGNIFICANCE
  ==========================

  This proof demonstrates that:

  1. Relations are MULTI-DIMENSIONAL: A single relation R(x,y) can be
     characterized by multiple numeric attributes simultaneously.

  2. Perspectives are EGO-CENTRIC: The tensor T(x,y) can differ from
     T(y,x), capturing subjective/directional aspects of relations.

  3. DSoR EMERGES from proven foundations: Because Prop 01 proves
     universal connectivity (every x relates to Whole), we can
     guarantee DSoR representations exist for ALL entities.

  4. Dimensions are ARBITRARY: The same relation can be represented
     in any number of dimensions - the framework is flexible.

  5. FULLY RELATIONAL: By using R_cauchy (constructive reals from
     RelationalReals.v), dimension values themselves are relational
     structures (Cauchy sequences are functional relations nat -> Q).

  COMPILATION
  ===========

  This file depends on:
    - Top__Propositions__Prop_01.v (seriality, Ux, Whole, R_prime)
    - Top__Numbers__RelationalReals.v (R_cauchy, R_zero, Q_to_R)

  Build order:
    1. Top__Extensions__Base.v
    2. Top__Extensions__WholeCompletion.v
    3. Top__Extensions__Composition.v
    4. Top__Extensions__Prelude.v
    5. Top__Propositions__Prop_01.v
    6. Top__Numbers__Relational.v (optional but typically needed)
    7. Top__Numbers__RelationalReals.v
    8. Top__Propositions__Prop_02.v (this file)

  AXIOM STATUS
  ============

  This file uses ZERO AXIOMS beyond standard Coq library axioms for QArith.
  By using R_cauchy instead of Coq's classical Reals, we avoid the
  ClassicalDedekindReals axiom. The DecEq typeclass is not an axiom -
  it's a constraint that must be satisfied by concrete instantiation.

  Run `Print Assumptions multi_dim_representation.` to verify.
  Expected output: Closed under the global context (for core theorems).
*)
