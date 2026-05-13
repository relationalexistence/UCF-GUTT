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
  |                 Top__Extensions__RelationalUIP.v                        |
  |                                                                          |
  |        UCF-Native Relational Uniqueness of Identity Proofs              |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-03-19                                                     |
  |  LAYER:   3 (→ Base, WholeCompletion, Composition, Prelude, Extras)      |
  |  COMPATIBILITY: Coq 8.18+                                               |
  |                                                                          |
  |  PURPOSE:                                                                |
  |    Coq's standard Eqdep module (Coq.Logic.Eqdep) introduces the axiom   |
  |    Eq_rect_eq.eq_rect_eq (UIP: Uniqueness of Identity Proofs) as a      |
  |    bare postulate. This file derives UIP for the types that arise in     |
  |    UCF/GUTT — specifically nat-indexed relational structures — as a      |
  |    THEOREM, using only Coq's CIC and the decidability of equality on     |
  |    the index type.                                                       |
  |                                                                          |
  |  UCF PHILOSOPHICAL GROUNDING:                                            |
  |    In UCF/GUTT, all mathematical structure emerges from relations.       |
  |    The natural numbers arise as relational cardinality indices —         |
  |    the "depth" of a nested relational structure (VDRel, NRT, RCube).     |
  |    Comparing two relational depths is always decidable: given any two    |
  |    depths n, m, exactly one of n = m or n ≠ m holds, and we can         |
  |    compute which. This is not an assumption — it is a relational         |
  |    necessity encoded in the structure of counting itself.                |
  |                                                                          |
  |    By Hedberg's theorem (1998), decidable equality on a type T implies   |
  |    UIP for T: any two proofs of (a = b) for a b : T are propositionally  |
  |    equal. Coq's Eqdep_dec module provides exactly this derivation,       |
  |    and it introduces ZERO axioms (verified: Print Assumptions confirms   |
  |    "Closed under the global context" for all exports).                   |
  |                                                                          |
  |    Therefore: UIP for nat is a UCF theorem, not an assumption.           |
  |    More generally: UIP for any decidably-equal type T is a theorem.     |
  |    This module makes that derivation explicit and re-exports it under    |
  |    UCF-meaningful names.                                                 |
  |                                                                          |
  |  DESIGN NOTE:                                                            |
  |    In NCube.v (v1.1.0), we went further: the three lemmas that           |
  |    previously required `dependent destruction` (and hence UIP) now use  |
  |    the VDRel_S_is_node inversion principle, which needs NO UIP at all.  |
  |    Similarly, vdpath_0_is_rreach uses behavioral extensionality (plain   |
  |    structural induction), requiring NO UIP.                              |
  |                                                                          |
  |    This module therefore serves two purposes:                            |
  |      (1) Principled record: documents the UCF justification for why UIP  |
  |          holds as a theorem for relational index types.                  |
  |      (2) Forward compatibility: any future UCF development that          |
  |          genuinely needs UIP (e.g. for transport lemmas in dependent     |
  |          types over relational indices) can import this module instead   |
  |          of Coq.Logic.Eqdep, keeping the zero-axiom guarantee.          |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  Hedberg's Theorem — Decidability → UIP                   |
  |    SECTION 2:  UCF Index Types — nat and bool                           |
  |    SECTION 3:  Relational Structural Lemmas                              |
  |    SECTION 4:  eq_rect_eq — the Eqdep axiom as a theorem                |
  |    SECTION 5:  RelationalUIP Module — Public API                        |
  |    SECTION 6:  Hint Databases                                            |
  |    SECTION 7:  Axiom Audit                                               |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Prelude.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 1: HEDBERG'S THEOREM — DECIDABILITY IMPLIES UIP                *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Hedberg's theorem: if equality on T is decidable, then UIP holds for T.
  This is already proved in Coq.Logic.Eqdep_dec as [UIP_dec].
  We re-state it here under UCF names for clarity.
*)

(** UCF name for Hedberg's theorem. *)
Theorem hedberg_uip :
  forall (T : Type),
  (forall (a b : T), {a = b} + {a <> b}) ->
  forall (a b : T) (p q : a = b), p = q.
Proof.
  intros T Hdec a b p q.
  apply UIP_dec. exact Hdec.
Qed.

(** Reflexivity instance: any proof of (a = a) equals eq_refl. *)
Theorem hedberg_uip_refl :
  forall (T : Type),
  (forall (a b : T), {a = b} + {a <> b}) ->
  forall (a : T) (p : a = a), p = eq_refl.
Proof.
  intros T Hdec a p.
  apply (UIP_dec Hdec).
Qed.

(** K axiom (Streicher's K) for decidably-equal types: a theorem, not an axiom. *)
Theorem hedberg_K :
  forall (T : Type),
  (forall (a b : T), {a = b} + {a <> b}) ->
  forall (a : T) (P : a = a -> Prop),
  P eq_refl ->
  forall (p : a = a), P p.
Proof.
  intros T Hdec a P Hrefl p.
  rewrite (UIP_dec Hdec p eq_refl).
  exact Hrefl.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 2: UCF INDEX TYPES — nat AND bool                              *)
(*                                                                            *)
(* ========================================================================== *)

(**
  The primary index type in UCF/GUTT is nat, used as:
    - Relational depth in VDRel U d
    - Cube dimension in RCube_n n U
    - Nesting level in NRT structures
  Nat equality is decidable (Nat.eq_dec). Therefore UIP holds for nat.
*)

(** UIP for nat — the foundational instance. *)
Theorem uip_nat : forall (n m : nat) (p q : n = m), p = q.
Proof.
  intros n m p q. apply UIP_dec. exact Nat.eq_dec.
Qed.

(** K for nat. *)
Theorem K_nat : forall (n : nat) (P : n = n -> Prop),
  P eq_refl -> forall (p : n = n), P p.
Proof.
  intros n P Hrefl p.
  rewrite (UIP_dec Nat.eq_dec p eq_refl). exact Hrefl.
Qed.

(** eq_rect_eq for nat — the exact statement of Coq.Logic.Eqdep's axiom,
    but proved as a theorem via decidability. *)
Theorem eq_rect_eq_nat :
  forall (n : nat) (P : nat -> Type) (x : P n) (h : n = n),
  eq_rect n P x n h = x.
Proof.
  intros n P x h.
  rewrite (UIP_dec Nat.eq_dec h eq_refl).
  reflexivity.
Qed.

(** UIP for bool — used in some relational Boolean-valued structures. *)
Theorem uip_bool : forall (b1 b2 : bool) (p q : b1 = b2), p = q.
Proof.
  intros b1 b2 p q. apply UIP_dec. exact Bool.bool_dec.
Qed.

(** eq_rect_eq for bool. *)
Theorem eq_rect_eq_bool :
  forall (b : bool) (P : bool -> Type) (x : P b) (h : b = b),
  eq_rect b P x b h = x.
Proof.
  intros b P x h.
  rewrite (UIP_dec Bool.bool_dec h eq_refl).
  reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 3: RELATIONAL STRUCTURAL LEMMAS                                *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Transport lemma: transporting across a proof of (n = m) and back gives
  the identity. Used when working with dependent types indexed by nat.
*)
Theorem transport_roundtrip :
  forall (n m : nat) (p : n = m) (P : nat -> Type) (x : P n),
  eq_rect m P (eq_rect n P x m p) n (eq_sym p) = x.
Proof.
  intros n m p P x.
  destruct p. reflexivity.
Qed.

(**
  Dependent pair equality for nat-indexed types: if the indices are equal
  and the payloads are equal after transport, the pairs are equal.
*)
Theorem sigma_nat_eq :
  forall (P : nat -> Type) (n m : nat) (x : P n) (y : P m) (Heq : n = m),
  eq_rect n P x m Heq = y ->
  existT P n x = existT P m y.
Proof.
  intros P n m x y Heq Htrans.
  destruct Heq. simpl in Htrans. subst y. reflexivity.
Qed.

(**
  Injectivity of existT for nat-indexed types — a theorem, not an axiom.
  This is the statement that Coq.Logic.Eqdep.inj_pair2 provides, but that
  file introduces it as an axiom. Here it follows from UIP for nat.
*)
Theorem inj_pair2_nat :
  forall (P : nat -> Type) (n : nat) (x y : P n),
  existT P n x = existT P n y -> x = y.
Proof.
  intros P n x y H.
  exact (inj_pair2_eq_dec nat Nat.eq_dec P n x y H).
Qed.

(**
  The key UCF structural fact: relational depth equality is decidable,
  so any identity proof on depths is unique.
*)
Theorem relational_depth_uip :
  forall (d1 d2 : nat) (p q : d1 = d2), p = q.
Proof.
  exact uip_nat.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 4: eq_rect_eq — THE Eqdep AXIOM AS A UCF THEOREM               *)
(*                                                                            *)
(* ========================================================================== *)

(**
  The statement that Coq.Logic.Eqdep postulates as an AXIOM for all types:

    (* stdlib Coq.Logic.Eqdep postulates: *)
    eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type)
      (x : Q p) (h : p = p), x = eq_rect p Q x p h.

  In UCF, this holds as a THEOREM for any type with decidable equality.
  For the nat-indexed types that arise in UCF/GUTT, it is always applicable.
*)

(** eq_rect_eq for any decidably-equal type — the general form. *)
Theorem ucf_eq_rect_eq :
  forall (T : Type),
  (forall (a b : T), {a = b} + {a <> b}) ->
  forall (p : T) (Q : T -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h.
Proof.
  intros T Hdec p Q x h.
  rewrite (UIP_dec Hdec h eq_refl).
  reflexivity.
Qed.

(** Specialisation to nat — the exact form that NCube.v needed. *)
Corollary ucf_eq_rect_eq_nat :
  forall (p : nat) (Q : nat -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h.
Proof.
  intros. apply ucf_eq_rect_eq. exact Nat.eq_dec.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 5: RelationalUIP MODULE — PUBLIC API                           *)
(*                                                                            *)
(* ========================================================================== *)

Module RelationalUIP.

  (** Hedberg's theorem: decidable equality → UIP. *)
  Definition hedberg       := hedberg_uip.

  (** UIP for nat (relational depth indices). *)
  Definition uip_nat       := uip_nat.

  (** K for nat. *)
  Definition K_nat         := K_nat.

  (** eq_rect_eq for nat. *)
  Definition eq_rect_eq    := eq_rect_eq_nat.

  (** UIP for bool. *)
  Definition uip_bool      := uip_bool.

  (** Injectivity of existT for nat-indexed types. *)
  Definition inj_pair2     := inj_pair2_nat.

  (** Relational depth UIP (alias). *)
  Definition depth_uip     := relational_depth_uip.

  (** Transport roundtrip. *)
  Definition transport_rt  := transport_roundtrip.

  (** Sigma equality for nat-indexed types. *)
  Definition sigma_eq      := sigma_nat_eq.

  (**
    UCF eq_rect_eq: the Eqdep axiom as a theorem for decidable types.
    Prefer this over importing Coq.Logic.Eqdep.
  *)
  Definition eq_rect_eq_dec := ucf_eq_rect_eq.
  Definition eq_rect_eq_nat := ucf_eq_rect_eq_nat.

End RelationalUIP.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 6: HINT DATABASES                                               *)
(*                                                                            *)
(* ========================================================================== *)

#[export] Hint Resolve
  hedberg_uip
  hedberg_uip_refl
  uip_nat
  uip_bool
  inj_pair2_nat
  relational_depth_uip
  : relational_uip.

#[export] Hint Rewrite
  @eq_rect_eq_nat
  @eq_rect_eq_bool
  : relational_uip_rw.

(* ========================================================================== *)
(*                                                                            *)
(*    SECTION 7: AXIOM AUDIT                                                  *)
(*                                                                            *)
(* ========================================================================== *)

(**
  AXIOM AUDIT RESULTS:

  All theorems in this file are CLOSED UNDER THE GLOBAL CONTEXT.
  Zero axioms beyond Coq's CIC are introduced.

  The derivation chain:
    Nat.eq_dec          (stdlib, axiom-free)
      → UIP_dec         (Coq.Logic.Eqdep_dec, axiom-free)
        → uip_nat       (this file, axiom-free)
          → K_nat, eq_rect_eq_nat, inj_pair2_nat, ...  (all axiom-free)

  Contrast with Coq.Logic.Eqdep, which introduces [as an Axiom]:
    eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type)
      (x : Q p) (h : p = p), x = eq_rect p Q x p h.
  as a bare axiom — true in any model of CIC satisfying UIP (e.g. set-theoretic
  models) but not provable in pure CIC for all types.

  UCF resolves this by restricting to the types that actually arise in
  UCF/GUTT (nat-indexed relational structures), for which decidability
  gives UIP constructively.

  NOTE: The wider question of whether UIP holds for all types is
  independent of CIC (it fails in Homotopy Type Theory). UCF takes
  no position on the general question; it simply observes that the
  types it needs UIP for are decidable, making UIP a theorem there.
*)

Print Assumptions hedberg_uip.
Print Assumptions uip_nat.
Print Assumptions K_nat.
Print Assumptions eq_rect_eq_nat.
Print Assumptions inj_pair2_nat.
Print Assumptions ucf_eq_rect_eq.
Print Assumptions transport_roundtrip.
