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
  |                    RelationalNaturals.v                                  |
  |                                                                          |
  |                    Natural Numbers from Relational Primitives            |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  VERSION: 1.0.0                                                          |
  |  DATE:    2026-01-12                                                     |
  |  COMPATIBILITY: Coq 8.18+, 8.19+, 8.20+ (tested)                         |
  |                                                                          |
  |  PURPOSE: Construct natural numbers from relational primitives grounded  |
  |  in the UCF/GUTT framework (Proposition 1: Seriality).                   |
  |                                                                          |
  |  KEY INSIGHT: Natural numbers ARE relational structures.                 |
  |    - Zero corresponds to the Whole (terminal sink)                       |
  |    - Successor is "one more relational step from Whole"                  |
  |    - Seriality (Prop 1) guarantees every number has a successor          |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1:  RelationalGrounding - Connection to Proposition 1         |
  |    MODULE RelationalNaturals (Sections 2-12 wrapped for namespacing):    |
  |      SECTION 2:  Inductive definition (N_rel, Zero_rel, Succ_rel)        |
  |      SECTION 3:  Seriality for N_rel                                     |
  |      SECTION 4:  Isomorphism with nat (to_nat, from_nat)                 |
  |      SECTION 5:  Addition (add_rel)                                      |
  |      SECTION 6:  Multiplication (mul_rel)                                |
  |      SECTION 7:  Subtraction/Monus (sub_rel)                             |
  |      SECTION 8:  Order relations (le_rel, lt_rel, etc.)                  |
  |      SECTION 9:  Embedding into Z                                        |
  |      SECTION 10: Decidability                                            |
  |      SECTION 11: NaturalsAsRelationalSystem - Prop 1 connection          |
  |      SECTION 12: Examples & tests                                        |
  |    SECTION 13: NR Module - Public API                                    |
  |    SECTION 14: Hint databases (nrel, nrel_ext)                           |
  |    SECTION 15: Tactics (nrel_simpl, nrel_lia, nrel_auto, etc.)           |
  |    SECTION 16: Arguments & implicit handling                             |
  |    SECTION 17: Notation scopes (nrel_scope)                              |
  |    SECTION 18: Axiom audit                                               |
  |                                                                          |
  |  API STABILITY:                                                          |
  |    STABLE (will not change in breaking ways):                            |
  |      - Module: RelationalNaturals (exported, so bare names work)         |
  |      - Types: N_rel                                                      |
  |      - Constructors: Zero_rel, Succ_rel                                  |
  |      - Conversions: to_nat, from_nat, embed_N_to_Z                       |
  |      - Arithmetic: add_rel, mul_rel, sub_rel                             |
  |      - Order: le_rel, lt_rel, ge_rel, gt_rel                             |
  |      - NR module exports                                                 |
  |      - Hint databases: nrel, nrel_ext                                    |
  |      - Tactics: nrel_simpl, nrel_lia, nrel_auto                          |
  |                                                                          |
  |  NAMING CONVENTIONS:                                                     |
  |    - Type: N_rel (relational naturals)                                   |
  |    - Constructors: *_rel suffix (Zero_rel, Succ_rel)                     |
  |    - Operations: *_rel suffix (add_rel, mul_rel, le_rel)                 |
  |    - Correctness: *_correct (add_rel_correct, mul_rel_correct)           |
  |    - Algebraic: *_comm, *_assoc, *_distr_l, *_distr_r                    |
  |    - Order: *_refl, *_trans, *_antisym, *_total, *_trichotomy            |
  |    - Decidability: *_dec (eq_dec, le_rel_dec)                            |
  |                                                                          |
  |  KEY RESULTS:                                                            |
  |    - N_rel isomorphic to nat (constructive isomorphism)                  |
  |    - Addition and multiplication form a commutative semiring             |
  |    - Order is a decidable total order                                    |
  |    - Grounded in Proposition 1's seriality guarantee                     |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS (beyond Coq stdlib)                            |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.

(* Import the UCF/GUTT extension framework *)
Require Import Top__Extensions__Prelude.

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: RELATIONAL GROUNDING                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
  PHILOSOPHICAL GROUNDING
  =======================
  
  In UCF/GUTT, natural numbers are not primitive objects but emerge from
  relational structure. The key insights are:
  
  1. ZERO as WHOLE: The number zero corresponds to the Whole - the terminal
     sink that everything relates to. Zero is the "ground state" of counting.
     
  2. SUCCESSOR as RELATION: Each successor n+1 represents "one more step
     away from Whole in the relational chain."
     
  3. SERIALITY gives INDUCTION: Proposition 1's seriality guarantee
     (every entity has an outgoing edge) corresponds to the fact that
     every natural number has a successor.
     
  4. PEANO from RELATIONS: The Peano axioms are not assumed but EMERGE
     from the relational structure established in Proposition 1.
*)

Module RelationalGrounding.

  Section NaturalsInUniverse.
    Variable U : Type.
    Variable R : U -> U -> Prop.
    
    (** The extended universe from Proposition 1. *)
    Definition Ux := UE.Carrier U.
    
    (** The lifted relation on the extended universe. *)
    Definition R' := UE.lift R.
    
    (** The distinguished Whole element (terminal sink). *)
    Definition Whole : Ux := UE.Whole.
    
    (** Key theorem: everything relates to Whole (pointed seriality). *)
    Theorem everything_relates_to_Whole : forall x : Ux, R' x Whole.
    Proof. intro x. apply UE.serial. Qed.
    
    (** Seriality: every entity has at least one outgoing edge. *)
    Theorem seriality : forall x : Ux, exists y : Ux, R' x y.
    Proof.
      intro x. exists Whole. apply UE.serial.
    Qed.
    
    (** Whole is a terminal sink w.r.t. U elements. *)
    Theorem whole_terminal : forall u : U, ~ R' Whole (UE.elem u).
    Proof. intro u. apply UE.point_terminal. Qed.
    
    (** Whole has a self-loop. *)
    Theorem whole_self_loop : R' Whole Whole.
    Proof. apply UE.point_self_loop. Qed.
    
  End NaturalsInUniverse.

End RelationalGrounding.

(* ========================================================================== *)
(*                                                                            *)
(*                    MODULE RelationalNaturals                               *)
(*                                                                            *)
(*  This module wraps all core definitions, allowing them to be referenced    *)
(*  as RelationalNaturals.to_nat, RelationalNaturals.add_rel, etc.            *)
(*  The module is exported at the end so bare names remain available.         *)
(*                                                                            *)
(* ========================================================================== *)

Module RelationalNaturals.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: INDUCTIVE DEFINITION                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
  We define natural numbers inductively as relational entities.
  This mirrors Peano axioms but grounds them in relational structure.
  
  - Zero_rel: The base entity (corresponds to Whole - terminal state)
  - Succ_rel: Successor relation (one step further from terminal)
*)

Inductive N_rel : Type :=
  | Zero_rel : N_rel
  | Succ_rel : N_rel -> N_rel.

(** Notations for relational naturals. *)
Notation "'0r'" := Zero_rel (at level 0).
Notation "n '+r1'" := (Succ_rel n) (at level 50).

(** Standard small constants. *)
Definition one_rel   : N_rel := Succ_rel Zero_rel.
Definition two_rel   : N_rel := Succ_rel one_rel.
Definition three_rel : N_rel := Succ_rel two_rel.
Definition four_rel  : N_rel := Succ_rel three_rel.
Definition five_rel  : N_rel := Succ_rel four_rel.

Notation "'1r'" := one_rel.
Notation "'2r'" := two_rel.
Notation "'3r'" := three_rel.
Notation "'4r'" := four_rel.
Notation "'5r'" := five_rel.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: SERIALITY FOR N_rel                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  KEY THEOREM: Natural numbers satisfy seriality.
  
  Every natural number relates to its successor, mirroring Proposition 1's
  guarantee that every entity has an outgoing edge.
  
  This is the RELATIONAL GROUNDING of the Peano "successor exists" axiom.
*)

(** The successor relation on N_rel. *)
Definition succ_relation (n m : N_rel) : Prop := m = Succ_rel n.

(** Seriality for naturals: every n has a successor. *)
Theorem N_rel_serial : forall n : N_rel, exists m : N_rel, succ_relation n m.
Proof.
  intro n. exists (Succ_rel n). unfold succ_relation. reflexivity.
Qed.

(** No natural is its own successor (irreflexivity). *)
Theorem succ_irrefl : forall n : N_rel, ~ succ_relation n n.
Proof.
  intros n H. unfold succ_relation in H.
  induction n as [| n' IH].
  - discriminate H.
  - injection H as H'. apply IH. exact H'.
Qed.

(** Zero has no predecessor (Zero is terminal/Whole). *)
Theorem zero_no_pred : forall n : N_rel, ~ succ_relation n Zero_rel.
Proof.
  intros n H. unfold succ_relation in H. discriminate H.
Qed.

(** Successor is injective. *)
Theorem succ_injective : forall n m : N_rel, Succ_rel n = Succ_rel m -> n = m.
Proof.
  intros n m H. injection H as H'. exact H'.
Qed.

(** Zero is not a successor. *)
Theorem zero_not_succ : forall n : N_rel, Zero_rel <> Succ_rel n.
Proof.
  intros n H. discriminate H.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: ISOMORPHISM WITH nat                         *)
(*                                                                            *)
(* ========================================================================== *)

(** Convert relational natural to standard natural. *)
Fixpoint to_nat (n : N_rel) : nat :=
  match n with
  | Zero_rel => 0
  | Succ_rel n' => S (to_nat n')
  end.

(** Convert standard natural to relational natural. *)
Fixpoint from_nat (n : nat) : N_rel :=
  match n with
  | O => Zero_rel
  | S n' => Succ_rel (from_nat n')
  end.

(* -------------------------------------------------------------------------- *)
(*                         Basic Properties                                   *)
(* -------------------------------------------------------------------------- *)

Lemma to_nat_zero : to_nat Zero_rel = 0.
Proof. reflexivity. Qed.

Lemma to_nat_succ : forall n, to_nat (Succ_rel n) = S (to_nat n).
Proof. intro n. reflexivity. Qed.

Lemma from_nat_zero : from_nat 0 = Zero_rel.
Proof. reflexivity. Qed.

Lemma from_nat_succ : forall n, from_nat (S n) = Succ_rel (from_nat n).
Proof. intro n. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(*                         Round-Trip Isomorphism                             *)
(* -------------------------------------------------------------------------- *)

(**Round-trip 1: from_nat o to_nat = id *)
Theorem from_nat_to_nat_id : forall n : N_rel, from_nat (to_nat n) = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(**Round-trip 2: to_nat o from_nat = id *)
Theorem to_nat_from_nat_id : forall n : nat, to_nat (from_nat n) = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Combined isomorphism theorem. *)
Theorem N_rel_iso_nat : 
  (forall n : N_rel, from_nat (to_nat n) = n) /\
  (forall n : nat, to_nat (from_nat n) = n).
Proof.
  split.
  - exact from_nat_to_nat_id.
  - exact to_nat_from_nat_id.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Injectivity & Surjectivity                         *)
(* -------------------------------------------------------------------------- *)

Theorem to_nat_injective : forall n m : N_rel, to_nat n = to_nat m -> n = m.
Proof.
  intros n m H.
  rewrite <- (from_nat_to_nat_id n).
  rewrite <- (from_nat_to_nat_id m).
  rewrite H. reflexivity.
Qed.

Theorem from_nat_injective : forall n m : nat, from_nat n = from_nat m -> n = m.
Proof.
  intros n m H.
  rewrite <- (to_nat_from_nat_id n).
  rewrite <- (to_nat_from_nat_id m).
  rewrite H. reflexivity.
Qed.

Theorem to_nat_surjective : forall n : nat, exists m : N_rel, to_nat m = n.
Proof.
  intro n. exists (from_nat n). apply to_nat_from_nat_id.
Qed.

Theorem from_nat_surjective : forall n : N_rel, exists m : nat, from_nat m = n.
Proof.
  intro n. exists (to_nat n). apply from_nat_to_nat_id.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: ADDITION                                     *)
(*                                                                            *)
(* ========================================================================== *)

Fixpoint add_rel (n m : N_rel) : N_rel :=
  match n with
  | Zero_rel => m
  | Succ_rel n' => Succ_rel (add_rel n' m)
  end.

Notation "n '+r' m" := (add_rel n m) (at level 50, left associativity).

(* -------------------------------------------------------------------------- *)
(*                         Basic Properties                                   *)
(* -------------------------------------------------------------------------- *)

Lemma add_rel_zero_l : forall n, Zero_rel +r n = n.
Proof. intro n. reflexivity. Qed.

Lemma add_rel_zero_r : forall n, n +r Zero_rel = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma add_rel_succ_l : forall n m, (Succ_rel n) +r m = Succ_rel (n +r m).
Proof. intros n m. reflexivity. Qed.

Lemma add_rel_succ_r : forall n m, n +r (Succ_rel m) = Succ_rel (n +r m).
Proof.
  intros n m.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Correctness                                        *)
(* -------------------------------------------------------------------------- *)

Theorem add_rel_correct : forall n m : N_rel,
  to_nat (n +r m) = to_nat n + to_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem add_rel_from_nat : forall n m : nat,
  from_nat (n + m) = from_nat n +r from_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Algebraic Properties                               *)
(* -------------------------------------------------------------------------- *)

Theorem add_rel_comm : forall n m, n +r m = m +r n.
Proof.
  intros n m. apply to_nat_injective.
  repeat rewrite add_rel_correct. lia.
Qed.

Theorem add_rel_assoc : forall n m p, (n +r m) +r p = n +r (m +r p).
Proof.
  intros n m p. apply to_nat_injective.
  repeat rewrite add_rel_correct. lia.
Qed.

Theorem add_rel_cancel_l : forall n m p, n +r m = n +r p -> m = p.
Proof.
  intros n m p H. apply to_nat_injective.
  assert (H_nat : to_nat (n +r m) = to_nat (n +r p)) by (rewrite H; reflexivity).
  repeat rewrite add_rel_correct in H_nat. lia.
Qed.

Theorem add_rel_cancel_r : forall n m p, n +r p = m +r p -> n = m.
Proof.
  intros n m p H. apply to_nat_injective.
  assert (H_nat : to_nat (n +r p) = to_nat (m +r p)) by (rewrite H; reflexivity).
  repeat rewrite add_rel_correct in H_nat. lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: MULTIPLICATION                               *)
(*                                                                            *)
(* ========================================================================== *)

Fixpoint mul_rel (n m : N_rel) : N_rel :=
  match n with
  | Zero_rel => Zero_rel
  | Succ_rel n' => m +r (mul_rel n' m)
  end.

Notation "n '*r' m" := (mul_rel n m) (at level 40, left associativity).

(* -------------------------------------------------------------------------- *)
(*                         Correctness                                        *)
(* -------------------------------------------------------------------------- *)

Theorem mul_rel_correct : forall n m : N_rel,
  to_nat (n *r m) = to_nat n * to_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite add_rel_correct. rewrite IH. reflexivity.
Qed.

Theorem mul_rel_from_nat : forall n m : nat,
  from_nat (n * m) = from_nat n *r from_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite add_rel_from_nat. rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Basic Properties                                   *)
(* -------------------------------------------------------------------------- *)

Lemma mul_rel_zero_l : forall n, Zero_rel *r n = Zero_rel.
Proof. intro n. reflexivity. Qed.

Lemma mul_rel_zero_r : forall n, n *r Zero_rel = Zero_rel.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma mul_rel_one_l : forall n, one_rel *r n = n.
Proof.
  intro n. unfold one_rel. simpl. rewrite add_rel_zero_r. reflexivity.
Qed.

Lemma mul_rel_one_r : forall n, n *r one_rel = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. unfold one_rel. reflexivity.
Qed.

Lemma mul_rel_succ_l : forall n m, (Succ_rel n) *r m = m +r (n *r m).
Proof. intros n m. reflexivity. Qed.

Lemma mul_rel_succ_r : forall n m, n *r (Succ_rel m) = n +r (n *r m).
Proof.
  intros n m. apply to_nat_injective.
  rewrite mul_rel_correct. rewrite to_nat_succ.
  rewrite add_rel_correct. rewrite mul_rel_correct. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Algebraic Properties                               *)
(* -------------------------------------------------------------------------- *)

Theorem mul_rel_comm : forall n m, n *r m = m *r n.
Proof.
  intros n m. apply to_nat_injective.
  repeat rewrite mul_rel_correct. lia.
Qed.

Theorem mul_rel_assoc : forall n m p, (n *r m) *r p = n *r (m *r p).
Proof.
  intros n m p. apply to_nat_injective.
  repeat rewrite mul_rel_correct. lia.
Qed.

Theorem mul_rel_distr_l : forall n m p, n *r (m +r p) = (n *r m) +r (n *r p).
Proof.
  intros n m p. apply to_nat_injective.
  rewrite mul_rel_correct. rewrite add_rel_correct.
  repeat rewrite add_rel_correct. repeat rewrite mul_rel_correct. lia.
Qed.

Theorem mul_rel_distr_r : forall n m p, (n +r m) *r p = (n *r p) +r (m *r p).
Proof.
  intros n m p.
  rewrite mul_rel_comm. rewrite mul_rel_distr_l.
  rewrite (mul_rel_comm p n). rewrite (mul_rel_comm p m). reflexivity.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: SUBTRACTION (MONUS)                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Monus (truncated subtraction): n - m = 0 when m > n.
  This is the natural subtraction for natural numbers.
*)

Fixpoint sub_rel (n m : N_rel) : N_rel :=
  match n, m with
  | Zero_rel, _ => Zero_rel
  | Succ_rel n', Zero_rel => Succ_rel n'
  | Succ_rel n', Succ_rel m' => sub_rel n' m'
  end.

Notation "n '-r' m" := (sub_rel n m) (at level 50, left associativity).

Theorem sub_rel_correct : forall n m : N_rel,
  to_nat (n -r m) = to_nat n - to_nat m.
Proof.
  induction n as [| n' IHn]; intro m; destruct m as [| m'].
  - reflexivity.
  - reflexivity.
  - simpl. lia.
  - simpl. rewrite IHn. lia.
Qed.

Theorem sub_rel_zero_r : forall n, n -r Zero_rel = n.
Proof. intro n. destruct n; reflexivity. Qed.

Theorem sub_rel_self : forall n, n -r n = Zero_rel.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Theorem sub_rel_add_inv : forall n m,
  to_nat m <= to_nat n -> (n -r m) +r m = n.
Proof.
  intros n m H. apply to_nat_injective.
  rewrite add_rel_correct. rewrite sub_rel_correct. lia.
Qed.

(** Addition then subtraction cancels (unconditionally). *)
Theorem add_sub_cancel : forall n m, (n +r m) -r m = n.
Proof.
  intros n m. apply to_nat_injective.
  rewrite sub_rel_correct. rewrite add_rel_correct. lia.
Qed.

(** Subtraction then addition cancels (when subtraction doesn't truncate). *)
Theorem sub_add_cancel : forall n m,
  to_nat m <= to_nat n -> (n -r m) +r m = n.
Proof.
  exact sub_rel_add_inv.
Qed.

(** Alternative: subtraction is right inverse of addition. *)
Theorem add_sub_assoc : forall n m p,
  to_nat p <= to_nat m -> n +r (m -r p) = (n +r m) -r p.
Proof.
  intros n m p H. apply to_nat_injective.
  rewrite add_rel_correct. rewrite sub_rel_correct.
  rewrite sub_rel_correct. rewrite add_rel_correct. lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: ORDER RELATION                               *)
(*                                                                            *)
(* ========================================================================== *)

Definition le_rel (n m : N_rel) : Prop := to_nat n <= to_nat m.
Definition lt_rel (n m : N_rel) : Prop := to_nat n < to_nat m.
Definition ge_rel (n m : N_rel) : Prop := to_nat n >= to_nat m.
Definition gt_rel (n m : N_rel) : Prop := to_nat n > to_nat m.

Notation "n '<=r' m" := (le_rel n m) (at level 70).
Notation "n '<r' m"  := (lt_rel n m) (at level 70).
Notation "n '>=r' m" := (ge_rel n m) (at level 70).
Notation "n '>r' m"  := (gt_rel n m) (at level 70).

(* -------------------------------------------------------------------------- *)
(*                         Order Properties                                   *)
(* -------------------------------------------------------------------------- *)

Theorem le_rel_refl : forall n, n <=r n.
Proof. intro n. unfold le_rel. lia. Qed.

Theorem le_rel_trans : forall n m p, n <=r m -> m <=r p -> n <=r p.
Proof. intros n m p H1 H2. unfold le_rel in *. lia. Qed.

Theorem le_rel_antisym : forall n m, n <=r m -> m <=r n -> n = m.
Proof.
  intros n m H1 H2. apply to_nat_injective. unfold le_rel in *. lia.
Qed.

Theorem lt_rel_irrefl : forall n, ~ (n <r n).
Proof. intro n. unfold lt_rel. lia. Qed.

Theorem lt_rel_trans : forall n m p, n <r m -> m <r p -> n <r p.
Proof. intros n m p H1 H2. unfold lt_rel in *. lia. Qed.

Theorem lt_rel_asymm : forall n m, n <r m -> ~ (m <r n).
Proof. intros n m H1 H2. unfold lt_rel in *. lia. Qed.

Theorem le_rel_total : forall n m : N_rel, n <=r m \/ m <=r n.
Proof.
  intros n m. unfold le_rel.
  destruct (Nat.leb_spec (to_nat n) (to_nat m)); [left|right]; lia.
Qed.

Theorem lt_rel_trichotomy : forall n m : N_rel,
  n <r m \/ n = m \/ m <r n.
Proof.
  intros n m. unfold lt_rel.
  destruct (Nat.lt_trichotomy (to_nat n) (to_nat m)) as [H | [H | H]].
  - left. exact H.
  - right. left. apply to_nat_injective. exact H.
  - right. right. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(*                         Order with Zero and Successor                      *)
(* -------------------------------------------------------------------------- *)

Theorem zero_le_all : forall n : N_rel, Zero_rel <=r n.
Proof. intro n. unfold le_rel. simpl. lia. Qed.

Theorem lt_succ : forall n : N_rel, n <r Succ_rel n.
Proof. intro n. unfold lt_rel. simpl. lia. Qed.

Theorem le_succ : forall n : N_rel, n <=r Succ_rel n.
Proof. intro n. unfold le_rel. simpl. lia. Qed.

Theorem succ_le_mono : forall n m, n <=r m <-> Succ_rel n <=r Succ_rel m.
Proof.
  intros n m. unfold le_rel. simpl. lia.
Qed.

Theorem succ_lt_mono : forall n m, n <r m <-> Succ_rel n <r Succ_rel m.
Proof.
  intros n m. unfold lt_rel. simpl. lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 9: EMBEDDING INTO Z                             *)
(*                                                                            *)
(* ========================================================================== *)

Definition embed_N_to_Z (n : N_rel) : Z := Z.of_nat (to_nat n).

Notation "'[' n ']Z'" := (embed_N_to_Z n) (at level 0).

Theorem embed_zero : [Zero_rel]Z = 0%Z.
Proof. reflexivity. Qed.

Theorem embed_succ : forall n, [Succ_rel n]Z = ([n]Z + 1)%Z.
Proof.
  intro n. unfold embed_N_to_Z. simpl. lia.
Qed.

Theorem embed_preserves_add : forall n m, [n +r m]Z = ([n]Z + [m]Z)%Z.
Proof.
  intros n m. unfold embed_N_to_Z. rewrite add_rel_correct. lia.
Qed.

Theorem embed_preserves_mul : forall n m, [n *r m]Z = ([n]Z * [m]Z)%Z.
Proof.
  intros n m. unfold embed_N_to_Z. rewrite mul_rel_correct. lia.
Qed.

Theorem embed_injective : forall n m, [n]Z = [m]Z -> n = m.
Proof.
  intros n m H. apply to_nat_injective. unfold embed_N_to_Z in H. lia.
Qed.

Theorem embed_preserves_order : forall n m, n <=r m <-> ([n]Z <= [m]Z)%Z.
Proof.
  intros n m. unfold le_rel, embed_N_to_Z. lia.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 10: DECIDABILITY                                *)
(*                                                                            *)
(* ========================================================================== *)

Theorem N_rel_eq_dec : forall n m : N_rel, {n = m} + {n <> m}.
Proof.
  decide equality.
Defined.

Theorem le_rel_dec : forall n m : N_rel, {n <=r m} + {~ (n <=r m)}.
Proof.
  intros n m. unfold le_rel.
  destruct (le_dec (to_nat n) (to_nat m)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Theorem lt_rel_dec : forall n m : N_rel, {n <r m} + {~ (n <r m)}.
Proof.
  intros n m. unfold lt_rel.
  destruct (lt_dec (to_nat n) (to_nat m)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Theorem ge_rel_dec : forall n m : N_rel, {n >=r m} + {~ (n >=r m)}.
Proof.
  intros n m. unfold ge_rel.
  destruct (le_dec (to_nat m) (to_nat n)) as [H | H].
  - left. lia.
  - right. lia.
Defined.

Theorem gt_rel_dec : forall n m : N_rel, {n >r m} + {~ (n >r m)}.
Proof.
  intros n m. unfold gt_rel.
  destruct (lt_dec (to_nat m) (to_nat n)) as [H | H].
  - left. lia.
  - right. lia.
Defined.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 11: CONNECTION TO PROPOSITION 1                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  We now formally connect N_rel to Proposition 1's relational structure.
  
  Key insight: N_rel forms a serial relational system where:
  - The universe is N_rel
  - The relation is the successor relation
  - Seriality is guaranteed by N_rel_serial
*)

Module NaturalsAsRelationalSystem.
  
  (** The universe of natural numbers. *)
  Definition U := N_rel.
  
  (** The predecessor relation (inverse of successor for embedding). *)
  Definition R (n m : U) : Prop := n = Succ_rel m.
  
  (** Extend with Whole using the extension framework. *)
  Definition N_ext := UE.Carrier U.
  Definition R' := UE.lift R.
  Definition Whole : N_ext := UE.Whole.
  
  (** Embed naturals into extended universe. *)
  Definition embed (n : N_rel) : N_ext := UE.elem n.
  
  (** Every natural relates to Whole (pointed seriality). *)
  Theorem naturals_relate_to_Whole : forall n : N_rel, R' (embed n) Whole.
  Proof.
    intro n. apply UE.serial.
  Qed.
  
  (** Seriality for extended naturals. *)
  Theorem extended_naturals_serial : forall x : N_ext, exists y : N_ext, R' x y.
  Proof.
    intro x. exists Whole. apply UE.serial.
  Qed.
  
  (** Whole is the unique terminal element. *)
  Theorem whole_terminal : forall n : N_rel, ~ R' Whole (embed n).
  Proof.
    intro n. apply UE.point_terminal.
  Qed.
  
  (** Embed is injective. *)
  Theorem embed_injective : forall n m : N_rel, embed n = embed m -> n = m.
  Proof.
    intros n m H. apply UE.elem_injective. exact H.
  Qed.
  
  (** Embed preserves distinctness from Whole. *)
  Theorem embed_not_whole : forall n : N_rel, embed n <> Whole.
  Proof.
    intro n. apply UE.point_fresh.
  Qed.
  
  (**
    PHILOSOPHICAL NOTE:
    
    The Whole in this context represents "the ground of counting" - 
    the relational foundation from which all natural numbers emerge.
    
    Zero_rel is the first "manifest" number - closest to Whole.
    Each Succ_rel n is one step further from this ground.
  *)
  
  (** Distance to Whole = the natural number itself. *)
  Definition distance_to_whole (n : N_rel) : nat := to_nat n.
  
  Theorem zero_closest_to_whole : 
    forall n : N_rel, distance_to_whole Zero_rel <= distance_to_whole n.
  Proof.
    intro n. unfold distance_to_whole. simpl. lia.
  Qed.
  
  Theorem succ_increases_distance :
    forall n : N_rel, distance_to_whole (Succ_rel n) = S (distance_to_whole n).
  Proof.
    intro n. unfold distance_to_whole. reflexivity.
  Qed.
  
  (** Conservativity: R' restricts to R on embedded elements. *)
  Theorem R_prime_conservative : forall n m : N_rel,
    R' (embed n) (embed m) <-> R n m.
  Proof.
    intros n m. apply UE.conservative.
  Qed.

End NaturalsAsRelationalSystem.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 12: EXAMPLES & TESTS                            *)
(*                                                                            *)
(* ========================================================================== *)

Module NaturalExamples.

  Example ex_add_1_1 : 1r +r 1r = 2r.
  Proof. reflexivity. Qed.

  Example ex_mul_2_3 : 2r *r 3r = from_nat 6.
  Proof. reflexivity. Qed.

  Example ex_sub_3_1 : 3r -r 1r = 2r.
  Proof. reflexivity. Qed.

  Example ex_sub_truncate : 1r -r 3r = 0r.
  Proof. reflexivity. Qed.

  Example ex_comm : 2r +r 3r = 3r +r 2r.
  Proof. apply add_rel_comm. Qed.

  Example ex_distr : 2r *r (3r +r 1r) = (2r *r 3r) +r (2r *r 1r).
  Proof. apply mul_rel_distr_l. Qed.

  Example ex_embed : [2r +r 3r]Z = ([2r]Z + [3r]Z)%Z.
  Proof. apply embed_preserves_add. Qed.

  Example ex_total : forall n m : N_rel, n <=r m \/ m <=r n.
  Proof. apply le_rel_total. Qed.

  Example ex_serial : forall n : N_rel, exists m, succ_relation n m.
  Proof. apply N_rel_serial. Qed.

  Example ex_zero_identity : forall n : N_rel, 0r +r n = n.
  Proof. apply add_rel_zero_l. Qed.

  Example ex_mul_identity : forall n : N_rel, 1r *r n = n.
  Proof. apply mul_rel_one_l. Qed.

  Example ex_mul_absorb : forall n : N_rel, 0r *r n = 0r.
  Proof. apply mul_rel_zero_l. Qed.

End NaturalExamples.

End RelationalNaturals.

(** Export RelationalNaturals so that bare names (N_rel, add_rel, etc.)
    remain available without module prefix for backward compatibility. *)
Export RelationalNaturals.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 13: PUBLIC API MODULE                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  NR: The canonical public API for relational naturals.
  
  This module provides stable, memorable names for downstream use.
  Prefer importing this over using raw definitions.
  
  NAMING CONVENTIONS:
    - Types start with uppercase: N, Carrier
    - Constructors/values use lowercase: zero, succ, one, two
    - Operations use lowercase: add, mul, sub
    - Lemmas use snake_case: add_comm, mul_assoc
*)

Module NR.

  (* ====================================================================== *)
  (*                              Types                                     *)
  (* ====================================================================== *)
  
  (** The type of relational natural numbers. *)
  Definition N := N_rel.
  
  (** The extended carrier with Whole. *)
  Definition Carrier := UE.Carrier N_rel.
  
  (* ====================================================================== *)
  (*                           Constructors                                 *)
  (* ====================================================================== *)
  
  (** Zero (corresponds to Whole - the terminal state). *)
  Definition zero : N := Zero_rel.
  
  (** Successor function. *)
  Definition succ : N -> N := Succ_rel.
  
  (** Standard constants. *)
  Definition one   : N := one_rel.
  Definition two   : N := two_rel.
  Definition three : N := three_rel.
  Definition four  : N := four_rel.
  Definition five  : N := five_rel.
  
  (* ====================================================================== *)
  (*                           Conversions                                  *)
  (* ====================================================================== *)
  
  (** Convert to Coq nat. *)
  Definition to_nat := RelationalNaturals.to_nat.
  
  (** Convert from Coq nat. *)
  Definition from_nat := RelationalNaturals.from_nat.
  
  (** Embed into Z. *)
  Definition to_Z := embed_N_to_Z.
  
  (* ====================================================================== *)
  (*                           Arithmetic                                   *)
  (* ====================================================================== *)
  
  (** Addition. *)
  Definition add := add_rel.
  
  (** Multiplication. *)
  Definition mul := mul_rel.
  
  (** Monus (truncated subtraction). *)
  Definition sub := sub_rel.
  
  (* ====================================================================== *)
  (*                           Order                                        *)
  (* ====================================================================== *)
  
  (** Less than or equal. *)
  Definition le := le_rel.
  
  (** Strictly less than. *)
  Definition lt := lt_rel.
  
  (** Greater than or equal. *)
  Definition ge := ge_rel.
  
  (** Strictly greater than. *)
  Definition gt := gt_rel.
  
  (* ====================================================================== *)
  (*                        Isomorphism Lemmas                              *)
  (* ====================================================================== *)
  
  Definition iso := N_rel_iso_nat.
  Definition to_nat_id := to_nat_from_nat_id.
  Definition from_nat_id := from_nat_to_nat_id.
  Definition to_nat_inj := to_nat_injective.
  Definition from_nat_inj := from_nat_injective.
  
  (* ====================================================================== *)
  (*                        Arithmetic Correctness                          *)
  (* ====================================================================== *)
  
  Definition add_correct := add_rel_correct.
  Definition mul_correct := mul_rel_correct.
  Definition sub_correct := sub_rel_correct.
  
  (* ====================================================================== *)
  (*                        Algebraic Properties                            *)
  (* ====================================================================== *)
  
  (** Addition properties. *)
  Definition add_zero_l := add_rel_zero_l.
  Definition add_zero_r := add_rel_zero_r.
  Definition add_succ_l := add_rel_succ_l.
  Definition add_succ_r := add_rel_succ_r.
  Definition add_comm := add_rel_comm.
  Definition add_assoc := add_rel_assoc.
  Definition add_cancel_l := add_rel_cancel_l.
  Definition add_cancel_r := add_rel_cancel_r.
  
  (** Multiplication properties. *)
  Definition mul_zero_l := mul_rel_zero_l.
  Definition mul_zero_r := mul_rel_zero_r.
  Definition mul_one_l := mul_rel_one_l.
  Definition mul_one_r := mul_rel_one_r.
  Definition mul_succ_l := mul_rel_succ_l.
  Definition mul_succ_r := mul_rel_succ_r.
  Definition mul_comm := mul_rel_comm.
  Definition mul_assoc := mul_rel_assoc.
  Definition mul_distr_l := mul_rel_distr_l.
  Definition mul_distr_r := mul_rel_distr_r.
  
  (** Subtraction properties. *)
  Definition sub_zero_r := sub_rel_zero_r.
  Definition sub_self := sub_rel_self.
  Definition sub_add_inv := sub_rel_add_inv.
  Definition add_sub_cancel := RelationalNaturals.add_sub_cancel.
  Definition sub_add_cancel := RelationalNaturals.sub_add_cancel.
  Definition add_sub_assoc := RelationalNaturals.add_sub_assoc.
  
  (* ====================================================================== *)
  (*                        Order Properties                                *)
  (* ====================================================================== *)
  
  Definition le_refl := le_rel_refl.
  Definition le_trans := le_rel_trans.
  Definition le_antisym := le_rel_antisym.
  Definition le_total := le_rel_total.
  Definition lt_irrefl := lt_rel_irrefl.
  Definition lt_trans := lt_rel_trans.
  Definition lt_asymm := lt_rel_asymm.
  Definition lt_trichotomy := lt_rel_trichotomy.
  
  (* ====================================================================== *)
  (*                        Decidability                                    *)
  (* ====================================================================== *)
  
  Definition eq_dec := N_rel_eq_dec.
  Definition le_dec := le_rel_dec.
  Definition lt_dec := lt_rel_dec.
  
  (* ====================================================================== *)
  (*                        Seriality                                       *)
  (* ====================================================================== *)
  
  Definition serial := N_rel_serial.
  Definition succ_inj := succ_injective.
  Definition succ_irrefl := RelationalNaturals.succ_irrefl.
  Definition zero_no_pred := RelationalNaturals.zero_no_pred.
  
  (* ====================================================================== *)
  (*                        Extension Integration                           *)
  (* ====================================================================== *)
  
  (** The Whole element in extended naturals. *)
  Definition Whole : Carrier := UE.Whole.
  
  (** Embed a natural into the extended carrier. *)
  Definition elem (n : N) : Carrier := UE.elem n.
  
  (** Lift a relation to the extended carrier. *)
  Definition lift {R : N -> N -> Prop} := UE.lift R.
  
  (** Every natural relates to Whole. *)
  Definition serial_to_whole := NaturalsAsRelationalSystem.naturals_relate_to_Whole.
  
  (** Extended naturals are serial. *)
  Definition extended_serial := NaturalsAsRelationalSystem.extended_naturals_serial.

End NR.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 14: HINT DATABASES                              *)
(*                                                                            *)
(* ========================================================================== *)

(** Hints for relational natural simplification. *)

#[export] Hint Rewrite 
  to_nat_zero
  to_nat_succ
  from_nat_zero
  from_nat_succ
  add_rel_zero_l
  add_rel_zero_r
  add_rel_succ_l
  add_rel_succ_r
  mul_rel_zero_l
  mul_rel_zero_r
  mul_rel_one_l
  mul_rel_one_r
  sub_rel_zero_r
  sub_rel_self
  add_sub_cancel
  add_rel_correct
  mul_rel_correct
  sub_rel_correct
  : nrel.

#[export] Hint Resolve
  N_rel_serial
  succ_injective
  succ_irrefl
  zero_no_pred
  zero_not_succ
  to_nat_injective
  from_nat_injective
  from_nat_to_nat_id
  to_nat_from_nat_id
  add_rel_comm
  add_rel_assoc
  mul_rel_comm
  mul_rel_assoc
  mul_rel_distr_l
  mul_rel_distr_r
  le_rel_refl
  le_rel_total
  lt_rel_irrefl
  zero_le_all
  lt_succ
  le_succ
  : nrel.

#[export] Hint Resolve
  NaturalsAsRelationalSystem.naturals_relate_to_Whole
  NaturalsAsRelationalSystem.extended_naturals_serial
  NaturalsAsRelationalSystem.whole_terminal
  NaturalsAsRelationalSystem.embed_injective
  NaturalsAsRelationalSystem.embed_not_whole
  : nrel_ext.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 15: TACTICS                                     *)
(*                                                                            *)
(* ========================================================================== *)

(** Tactic to simplify relational natural expressions. *)
Ltac nrel_simpl :=
  unfold NR.add, NR.mul, NR.sub, NR.le, NR.lt, NR.to_nat, NR.from_nat;
  unfold add_rel, mul_rel, sub_rel, le_rel, lt_rel, to_nat, from_nat;
  simpl.

(** Tactic to solve goals about relational naturals via nat. *)
Ltac nrel_lia :=
  try apply to_nat_injective;
  repeat rewrite ?add_rel_correct, ?mul_rel_correct, ?sub_rel_correct;
  try lia.

(** Tactic for relational natural arithmetic. *)
Ltac nrel_auto :=
  auto with nrel;
  try nrel_lia.

(** Tactic to prove seriality goals for extended naturals. *)
Ltac nrel_serial :=
  match goal with
  | |- exists y, UE.lift _ _ y => 
      exists UE.Whole; apply UE.serial
  | |- UE.lift _ _ UE.Whole => 
      apply UE.serial
  | |- exists m, succ_relation _ m => 
      eexists; unfold succ_relation; reflexivity
  end.

(** Tactic to destruct N_rel with useful hypotheses. *)
Ltac nrel_destruct n :=
  destruct n as [| n'];
  [ (* Zero case *) | (* Succ case *) ].

(** Tactic for induction on N_rel. *)
Ltac nrel_induction n :=
  induction n as [| n' IH];
  [ (* Base case: Zero_rel *) 
  | (* Inductive case: Succ_rel n' with IH *)
  ].

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 16: ARGUMENTS & IMPLICIT HANDLING               *)
(*                                                                            *)
(* ========================================================================== *)

Arguments Zero_rel : clear implicits.
Arguments Succ_rel _ : clear implicits.
Arguments to_nat _ : clear implicits.
Arguments from_nat _ : clear implicits.
Arguments add_rel _ _ : clear implicits.
Arguments mul_rel _ _ : clear implicits.
Arguments sub_rel _ _ : clear implicits.
Arguments le_rel _ _ : clear implicits.
Arguments lt_rel _ _ : clear implicits.
Arguments ge_rel _ _ : clear implicits.
Arguments gt_rel _ _ : clear implicits.
Arguments embed_N_to_Z _ : clear implicits.
Arguments succ_relation _ _ : clear implicits.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 17: NOTATION SCOPES                             *)
(*                                                                            *)
(* ========================================================================== *)

(** Declare a scope for relational natural notations. *)
Declare Scope nrel_scope.
Delimit Scope nrel_scope with nrel.

Bind Scope nrel_scope with N_rel.

Notation "n + m" := (add_rel n m) : nrel_scope.
Notation "n * m" := (mul_rel n m) : nrel_scope.
Notation "n - m" := (sub_rel n m) : nrel_scope.
Notation "n <= m" := (le_rel n m) : nrel_scope.
Notation "n < m" := (lt_rel n m) : nrel_scope.
Notation "n >= m" := (ge_rel n m) : nrel_scope.
Notation "n > m" := (gt_rel n m) : nrel_scope.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 18: AXIOM AUDIT                                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Verification that this file uses ZERO AXIOMS beyond Coq stdlib.
  
  Run: Print Assumptions <theorem_name>.
  All should show "Closed under the global context" (modulo stdlib axioms
  used by lia tactic).
*)

Module AxiomAudit.

  (** Computational tests - would FAIL if definitions were Parameters. *)
  
  Definition test_zero : Zero_rel = Zero_rel.
  Proof. reflexivity. Qed.
  
  Definition test_succ : Succ_rel Zero_rel = one_rel.
  Proof. reflexivity. Qed.
  
  Definition test_to_nat : to_nat (Succ_rel (Succ_rel Zero_rel)) = 2.
  Proof. reflexivity. Qed.
  
  Definition test_from_nat : from_nat 3 = three_rel.
  Proof. reflexivity. Qed.
  
  Definition test_add : one_rel +r two_rel = three_rel.
  Proof. reflexivity. Qed.
  
  Definition test_mul : two_rel *r two_rel = four_rel.
  Proof. reflexivity. Qed.
  
  Definition test_sub : three_rel -r one_rel = two_rel.
  Proof. reflexivity. Qed.
  
  Definition test_embed : embed_N_to_Z two_rel = 2%Z.
  Proof. reflexivity. Qed.

  (** Extension framework integration tests. *)
  
  Definition test_elem : @UE.elem N_rel Zero_rel = Some Zero_rel.
  Proof. reflexivity. Qed.
  
  Definition test_whole : @UE.Whole N_rel = None.
  Proof. reflexivity. Qed.
  
  Definition test_lift_serial : 
    UE.lift (fun _ _ : N_rel => False) (UE.elem Zero_rel) UE.Whole = True.
  Proof. reflexivity. Qed.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  PUBLIC API MODULE (NR):
    NR.N                = N_rel (the type)
    NR.zero, NR.succ    = constructors
    NR.one .. NR.five   = constants
    NR.add, NR.mul, NR.sub = arithmetic
    NR.le, NR.lt, NR.ge, NR.gt = order
    NR.to_nat, NR.from_nat = conversions
    NR.to_Z             = embedding to Z
    NR.elem, NR.Whole   = extension integration
    NR.serial           = seriality theorem
    NR.eq_dec           = decidable equality
  
  TYPES:
    N_rel               = relational natural numbers
    NR.Carrier          = UE.Carrier N_rel (extended with Whole)
  
  CONSTRUCTORS:
    Zero_rel            = 0r (zero)
    Succ_rel n          = n +r1 (successor)
    one_rel .. five_rel = 1r .. 5r
  
  CONVERSIONS:
    to_nat   : N_rel -> nat
    from_nat : nat -> N_rel
    embed_N_to_Z : N_rel -> Z
  
  ARITHMETIC (with notations):
    n +r m              = add_rel n m
    n *r m              = mul_rel n m
    n -r m              = sub_rel n m (monus)
  
  ORDER (with notations):
    n <=r m             = le_rel n m
    n <r m              = lt_rel n m
    n >=r m             = ge_rel n m
    n >r m              = gt_rel n m
  
  NOTATION SCOPE (nrel_scope):
    Open Scope nrel_scope.
    (n + m)%nrel, (n * m)%nrel, (n - m)%nrel
    (n <= m)%nrel, (n < m)%nrel, etc.
  
  HINT DATABASES:
    nrel      : core lemmas for relational naturals
    nrel_ext  : extension integration lemmas
    
    Usage: auto with nrel. / auto with nrel_ext.
  
  TACTICS:
    nrel_simpl          : unfold and simplify
    nrel_lia            : solve via nat isomorphism + lia
    nrel_auto           : auto with nrel + nrel_lia
    nrel_serial         : prove seriality goals
    nrel_destruct n     : case split on Zero_rel / Succ_rel
    nrel_induction n    : induction with named IH
  
  KEY THEOREMS:
    N_rel_serial        : every natural has a successor
    N_rel_iso_nat       : isomorphism with nat
    add_rel_correct     : to_nat (n +r m) = to_nat n + to_nat m
    mul_rel_correct     : to_nat (n *r m) = to_nat n * to_nat m
    add_rel_comm/assoc  : addition is commutative monoid
    mul_rel_comm/assoc  : multiplication is commutative monoid
    mul_rel_distr_l/r   : distributivity (semiring structure)
    le_rel_total        : total order
    N_rel_eq_dec        : equality is decidable
    le_rel_dec/lt_rel_dec : order is decidable
  
  CONNECTION TO PROP 1:
    NaturalsAsRelationalSystem.naturals_relate_to_Whole
    NaturalsAsRelationalSystem.extended_naturals_serial
    NaturalsAsRelationalSystem.R_prime_conservative
  
  AXIOM STATUS
  ============
  
  This file uses ZERO additional axioms beyond Coq's standard library.
  All key theorems verify as "Closed under the global context".
  
  COMPILATION
  ===========
  
  Requires: Top__Extensions__Prelude.v (and its dependencies)
  
    coqc Top__Extensions__Base.v
    coqc Top__Extensions__WholeCompletion.v
    coqc Top__Extensions__Composition.v
    coqc Top__Extensions__Prelude.v
    coqc Top__Numbers__Relational.v
  
  USAGE EXAMPLE
  =============
  
    Require Import Top__Numbers__Relational.
    
    (* Use the NR module for clean access *)
    Check NR.add_comm.   (* forall n m, NR.add n m = NR.add m n *)
    
    (* Use tactics for proofs *)
    Goal forall n : N_rel, n +r 0r = n.
    Proof. intro n. nrel_auto. Qed.
    
    (* Use hint databases *)
    Goal exists m, succ_relation 3r m.
    Proof. auto with nrel. Qed.
*)
