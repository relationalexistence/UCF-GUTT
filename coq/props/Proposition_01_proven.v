(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
*)
(*
  +===========================================================================+
  |                                                                           |
  |              PROPOSITION 1: SERIALITY VIA WHOLE-COMPLETION                |
  |                                                                           |
  |                         UCF/GUTT(TM) Formal Verification                     |
  |                                                                           |
  +===========================================================================+
  |                                                                           |
  |  THEOREM: forallx in U_x, existsy in U_x: R'(x,y)                                        |
  |                                                                           |
  |  "Every entity in the extended universe has at least one outgoing edge"  |
  |                                                                           |
  |  This is SERIALITY (every node has a successor), not pairwise            |
  |  connectivity. The construction adds a terminal sink (Whole) that        |
  |  every entity relates to, guaranteeing seriality by definition.          |
  |                                                                           |
  +===========================================================================+
  |                                                                           |
  |  IMPORTANT CLARIFICATION:                                                 |
  |                                                                           |
  |  Proposition 1 holds for ALL base relations R because R' is DEFINED      |
  |  to relate every x to Whole. This is a definitional/constructive         |
  |  principle, not a constraint discovered about arbitrary relations.       |
  |                                                                           |
  |  The philosophical claim is: by EXTENDING any universe U with the Whole, |
  |  and DEFINING R' to include universal Whole-targeting, we transform      |
  |  "no entity is isolated" from an assumption into a construction.         |
  |                                                                           |
  +===========================================================================+
  |                                                                           |
  |  STATUS: [ok] ZERO AXIOMS                                                    |
  |          [ok] ZERO ADMITS                                                    |
  |          [ok] FULLY CONSTRUCTIVE                                             |
  |          [ok] MACHINE VERIFIED (Coq 8.18+)                                   |
  |                                                                           |
  +===========================================================================+
  |                                                                           |
  |  USAGE: Import Core and ignore build artifacts (.glob, .aux, .vo, etc.)  |
  |         BackwardCompat is provided only for legacy code compatibility.   |
  |                                                                           |
  |  (C) 2023-2025 Michael Fillippini. All Rights Reserved.                     |
  |  UCF/GUTT(TM) Research & Evaluation License v1.1                             |
  |                                                                           |
  +===========================================================================+
*)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

(* ========================================================================== *)
(*                                                                            *)
(*                        MODULE: Core (Fully Closed)                         *)
(*                                                                            *)
(*  All theorems here are explicitly quantified over U and R.                 *)
(*  Print Assumptions shows: "Closed under the global context"                *)
(*                                                                            *)
(*  This is the CANONICAL interface. New code should use Core.*              *)
(*                                                                            *)
(* ========================================================================== *)

Module Core.

  (* ------------------------------------------------------------------------ *)
  (*                    Serial Completion (Whole-Completion)                  *)
  (* ------------------------------------------------------------------------ *)
  
  (*
    The "serial completion" pattern:
    
    Given any universe U and relation R, we construct:
    - An extended universe Ux = U  cup  {Whole}
    - An extended relation R' that adds Whole as a terminal sink w.r.t. U
    
    This makes R' serial (every element has an outgoing edge)
    while preserving R on the original universe (conservative extension).
    
    Terminology:
    - "Serial" = every node has at least one successor (outgoing edge)
    - "Terminal sink w.r.t. U" = Whole has no outgoing edges TO U
      (but Whole does have a self-loop: R'(Whole,Whole) = True)
    - This is NOT pairwise connectivity; we only guarantee seriality
  *)

  (* Extended universe: U_x = U  cup  {Whole} via option type *)
  Definition Ux (U : Type) : Type := option U.

  (* Constructors with implicit type argument for ergonomics *)
  Definition Whole {U : Type} : Ux U := None.
  Definition elem  {U : Type} (e : U) : Ux U := Some e.

  (*
    Extended relation R' (the serial completion of R):
    
    1. R'(Some a, Some b) := R a b    -- conservative: restricts to R on U
    2. R'(x, None) := True            -- completion: everything relates to Whole
    3. R'(None, Some _) := False      -- Whole is terminal sink w.r.t. U
    
    Note: R'(Whole, Whole) = True (self-loop on the sink).
    This construction guarantees seriality.
  *)
  Definition R_prime {U : Type} (R : U -> U -> Prop) (x y : Ux U) : Prop :=
    match x, y with
    | Some a, Some b => R a b
    | _,      None   => True
    | None,   Some _ => False
    end.

  (* Named serial completion operator with explicit arity *)
  Definition serial_completion {U : Type} (R : U -> U -> Prop) : Ux U -> Ux U -> Prop :=
    R_prime R.

  (* ------------------------------------------------------------------------ *)
  (*                    PROPOSITION 1: Seriality                              *)
  (* ------------------------------------------------------------------------ *)

  (*
    MAIN THEOREM: R' is serial (every entity has an outgoing edge).
    
    Proof: The witness is always Whole. By construction, R'(x, Whole) = True.
    This is the core insight: seriality is CONSTRUCTED by definition of R'.
  *)
  Theorem proposition_1 :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      exists y : Ux U, R_prime R x y.
  Proof.
    intros U R x.
    exists Whole.
    cbn; destruct x; exact I.
  Qed.

  (* Alternate name emphasizing what we actually prove *)
  Definition seriality := proposition_1.

  (* Constructive witness function *)
  Definition witness {U : Type} : Ux U -> Ux U := fun _ => Whole.

  Theorem proposition_1_constructive :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      R_prime R x (witness x).
  Proof.
    intros U R x.
    cbn; destruct x; exact I.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                         Key Properties of R'                             *)
  (* ------------------------------------------------------------------------ *)

  (* R' is a conservative extension: it restricts to R on U * U *)
  Lemma R_prime_restricts :
    forall (U : Type) (R : U -> U -> Prop) (a b : U),
      R_prime R (elem a) (elem b) <-> R a b.
  Proof.
    intros; cbn; tauto.
  Qed.

  (* Lift lemma: any base edge lifts to extended universe *)
  Lemma R_lift :
    forall (U : Type) (R : U -> U -> Prop) (a b : U),
      R a b -> R_prime R (elem a) (elem b).
  Proof.
    intros; cbn; assumption.
  Qed.

  (* Everything relates to Whole (this IS the definition, made explicit) *)
  Lemma everything_relates_to_Whole :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      R_prime R x Whole.
  Proof.
    intros; cbn; destruct x; exact I.
  Qed.

  (* Whole has a self-loop *)
  Lemma Whole_self_relates :
    forall (U : Type) (R : U -> U -> Prop),
      R_prime R Whole Whole.
  Proof.
    intros; exact I.
  Qed.

  (* Whole is a terminal sink w.r.t. U (no outgoing edges to U elements) *)
  Lemma Whole_terminal_sink :
    forall (U : Type) (R : U -> U -> Prop) (b : U),
      ~ R_prime R Whole (elem b).
  Proof.
    intros; cbn; tauto.
  Qed.

  (* Legacy alias *)
  Definition Whole_no_outgoing := Whole_terminal_sink.

  (* ------------------------------------------------------------------------ *)
  (*                           Derived Properties                             *)
  (* ------------------------------------------------------------------------ *)

  (* No entity is isolated (contrapositive of seriality) *)
  Theorem no_isolated_entities :
    forall (U : Type) (R : U -> U -> Prop),
      ~ exists x : Ux U, forall y : Ux U, ~ R_prime R x y.
  Proof.
    intros U R [x Hx].
    apply (Hx Whole).
    apply everything_relates_to_Whole.
  Qed.

  (* R' is serial: same statement as proposition_1, semantic alias *)
  Notation R_prime_is_serial := proposition_1 (only parsing).

  (* R' is total to Whole: same as everything_relates_to_Whole *)
  Notation R_prime_total_to_Whole := everything_relates_to_Whole (only parsing).

  (* ------------------------------------------------------------------------ *)
  (*                    Adjacency and Reachability                            *)
  (* ------------------------------------------------------------------------ *)

  (* 
    is_adjacent: 1-step connection via R' 
    This is what R_prime directly gives us.
  *)
  Definition is_adjacent {U : Type} (R : U -> U -> Prop) (x y : Ux U) : Prop :=
    R_prime R x y.

  Lemma all_adjacent_to_Whole :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      is_adjacent R x Whole.
  Proof.
    intros; apply everything_relates_to_Whole.
  Qed.

  Lemma one_step_adjacent :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      exists y : Ux U, is_adjacent R x y.
  Proof.
    intros; exists Whole; apply everything_relates_to_Whole.
  Qed.

  (*
    reachable: multi-step path via reflexive-transitive closure of R'
    This is true graph-theoretic reachability.
  *)
  Definition reachable {U : Type} (R : U -> U -> Prop) : Ux U -> Ux U -> Prop :=
    clos_refl_trans (Ux U) (R_prime R).

  (* Everything is reachable from itself (reflexivity) *)
  Lemma reachable_refl :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      reachable R x x.
  Proof.
    intros; apply rt_refl.
  Qed.

  (* If adjacent, then reachable (1-step implies reachability) *)
  Lemma adjacent_implies_reachable :
    forall (U : Type) (R : U -> U -> Prop) (x y : Ux U),
      is_adjacent R x y -> reachable R x y.
  Proof.
    intros; apply rt_step; assumption.
  Qed.

  (* Everything reaches Whole in one step *)
  Lemma all_reach_Whole :
    forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
      reachable R x Whole.
  Proof.
    intros; apply rt_step; apply everything_relates_to_Whole.
  Qed.

  (* Reachability is transitive *)
  Lemma reachable_trans :
    forall (U : Type) (R : U -> U -> Prop) (x y z : Ux U),
      reachable R x y -> reachable R y z -> reachable R x z.
  Proof.
    intros; eapply rt_trans; eassumption.
  Qed.

  (*
    Common successor: any two elements have a common successor (Whole).
    This is what people often MEAN by "no isolation" - everyone is
    connected THROUGH the Whole, even if not directly to each other.
  *)
  Lemma common_successor :
    forall (U : Type) (R : U -> U -> Prop) (x y : Ux U),
      exists z : Ux U, reachable R x z /\ reachable R y z.
  Proof.
    intros.
    exists Whole.
    split; apply all_reach_Whole.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                    Decidability (Conditional)                            *)
  (* ------------------------------------------------------------------------ *)

  Theorem R_prime_decidable :
    forall (U : Type) (R : U -> U -> Prop),
      (forall a b : U, {R a b} + {~ R a b}) ->
      forall (x y : Ux U), {R_prime R x y} + {~ R_prime R x y}.
  Proof.
    intros U R Hdec x y.
    destruct x as [a|], y as [b|]; cbn.
    - apply Hdec.
    - left; exact I.
    - right; tauto.
    - left; exact I.
  Qed.

End Core.

(* ========================================================================== *)
(*                                                                            *)
(*               MODULE: ConcreteExample (Worst-Case Sanity Check)            *)
(*                                                                            *)
(*  Instantiates U := nat, R := False (empty relation).                       *)
(*  Demonstrates that seriality holds even with NO base edges.                *)
(*                                                                            *)
(* ========================================================================== *)

Module ConcreteExample.

  Definition U : Type := nat.
  Definition R : U -> U -> Prop := fun _ _ => False.

  (* Reuse Core definitions *)
  Definition Ux : Type := Core.Ux U.
  Definition Whole : Ux := @Core.Whole U.
  Definition R_prime : Ux -> Ux -> Prop := Core.R_prime R.

  (* Seriality follows from Core.proposition_1 *)
  Theorem seriality :
    forall x : Ux, exists y : Ux, R_prime x y.
  Proof.
    intro x; exact (Core.proposition_1 U R x).
  Qed.

  (* Legacy alias *)
  Definition connectivity := seriality.

  (* Verify R is indeed empty on U *)
  Lemma R_is_empty : forall a b : U, ~ R a b.
  Proof.
    intros; cbn; tauto.
  Qed.

  (* But R' has edges (to Whole) *)
  Lemma R_prime_has_edges : exists x y : Ux, R_prime x y.
  Proof.
    exists Whole, Whole; exact I.
  Qed.

End ConcreteExample.

(* ========================================================================== *)
(*                                                                            *)
(*              MODULE: BackwardCompat (Legacy Parameterized API)             *)
(*                                                                            *)
(*  Provides the same API as the original Proposition_01_proven.v for         *)
(*  compatibility with existing files that import this module.                *)
(*                                                                            *)
(*  Note: Print Assumptions will show U, R as parameters (expected).          *)
(*  For truly closed theorems, use Core.* with explicit quantification.       *)
(*                                                                            *)
(* ========================================================================== *)

Module BackwardCompat.

  Parameter U : Type.
  Parameter R : U -> U -> Prop.

  (* Definitions delegating to Core *)
  Definition Ux : Type := Core.Ux U.
  Definition elem (e : U) : Ux := @Core.elem U e.
  Definition Whole : Ux := @Core.Whole U.
  Definition R_prime (x y : Ux) : Prop := Core.R_prime R x y.
  Definition witness (x : Ux) : Ux := @Core.witness U x.

  (* Main theorems - delegate to Core *)
  Definition refined_proposition_1 : forall x : Ux, exists y : Ux, R_prime x y :=
    Core.proposition_1 U R.

  Definition refined_proposition_1_constructive : forall x : Ux, R_prime x (witness x) :=
    Core.proposition_1_constructive U R.

  (* Properties - delegate to Core *)
  Lemma R_prime_restricts :
    forall (a b : U), R_prime (elem a) (elem b) <-> R a b.
  Proof. intros; apply Core.R_prime_restricts. Qed.

  Definition R_lift : forall (a b : U), R a b -> R_prime (elem a) (elem b) :=
    Core.R_lift U R.

  Definition everything_relates_to_Whole : forall x : Ux, R_prime x Whole :=
    Core.everything_relates_to_Whole U R.

  Definition Whole_terminal_sink : forall (b : U), ~ R_prime Whole (elem b) :=
    Core.Whole_terminal_sink U R.

  (* Legacy alias *)
  Definition Whole_no_outgoing := Whole_terminal_sink.

  Definition Whole_relates_to_Whole : R_prime Whole Whole :=
    Core.Whole_self_relates U R.

  (* Derived - aliases *)
  Definition R_prime_is_serial := refined_proposition_1.
  Definition R_prime_total_to_Whole := everything_relates_to_Whole.

  Theorem no_isolated_entities :
    ~ exists x : Ux, forall y : Ux, ~ R_prime x y.
  Proof.
    intros [x Hx]; apply (Hx Whole); apply everything_relates_to_Whole.
  Qed.

  (* Adjacency - delegate to Core *)
  Definition is_adjacent (x y : Ux) : Prop := Core.is_adjacent R x y.
  Definition all_adjacent_to_Whole : forall x : Ux, is_adjacent x Whole :=
    Core.all_adjacent_to_Whole U R.

  Lemma one_step_adjacent : forall x : Ux, exists y : Ux, is_adjacent x y.
  Proof. intro x; exists Whole; apply all_adjacent_to_Whole. Qed.

  (* Reachability - delegate to Core *)
  Definition reachable : Ux -> Ux -> Prop := Core.reachable R.
  Definition all_reach_Whole : forall x : Ux, reachable x Whole :=
    Core.all_reach_Whole U R.

  Definition common_successor : forall (x y : Ux), exists z, reachable x z /\ reachable y z :=
    Core.common_successor U R.

  (* Decidability *)
  Section Decidability.
    Hypothesis R_decidable : forall (a b : U), {R a b} + {~ R a b}.

    Definition R_prime_decidable : forall (x y : Ux), {R_prime x y} + {~ R_prime x y} :=
      Core.R_prime_decidable U R R_decidable.
  End Decidability.

  (* Original comparison section *)
  Section OriginalComparison.
    Hypothesis original_seriality : forall x : U, exists y : U, R x y.

    Theorem original_embedded_in_refined :
      forall x : U, exists y : Ux, R_prime (elem x) y.
    Proof.
      intro x.
      destruct (original_seriality x) as [y Hxy].
      exists (elem y); cbn; exact Hxy.
    Qed.
  End OriginalComparison.

  (* Exports with UCF_GUTT prefix *)
  Definition UCF_GUTT_Proposition_1_Refined := refined_proposition_1.
  Definition UCF_GUTT_Whole_Universal := everything_relates_to_Whole.
  Definition UCF_GUTT_R_Restriction := R_prime_restricts.
  Definition UCF_GUTT_No_Isolation := no_isolated_entities.
  Definition UCF_GUTT_Witness := witness.
  Definition UCF_GUTT_Witness_Works := refined_proposition_1_constructive.

End BackwardCompat.

(* ========================================================================== *)
(*                                                                            *)
(*                      TOP-LEVEL EXPORTS (Legacy Support)                    *)
(*                                                                            *)
(*  These re-exports maintain compatibility with files that do:               *)
(*    Require Import Proposition_01_proven.                                   *)
(*    Check refined_proposition_1.                                            *)
(*                                                                            *)
(*  NOTE: U and R are NOT exported at top level to avoid namespace pollution. *)
(*  Use BackwardCompat.U / BackwardCompat.R if you need direct access.        *)
(*                                                                            *)
(* ========================================================================== *)

(* Core definitions *)
Definition Ux := BackwardCompat.Ux.
Definition elem := BackwardCompat.elem.
Definition Whole := BackwardCompat.Whole.
Definition R_prime := BackwardCompat.R_prime.
Definition witness := BackwardCompat.witness.

(* Main theorems *)
Definition refined_proposition_1 := BackwardCompat.refined_proposition_1.
Definition refined_proposition_1_constructive := BackwardCompat.refined_proposition_1_constructive.

(* Properties *)
Definition R_prime_restricts := BackwardCompat.R_prime_restricts.
Definition R_lift := BackwardCompat.R_lift.
Definition everything_relates_to_Whole := BackwardCompat.everything_relates_to_Whole.
Definition Whole_terminal_sink := BackwardCompat.Whole_terminal_sink.
Definition Whole_no_outgoing := BackwardCompat.Whole_no_outgoing.
Definition Whole_relates_to_Whole := BackwardCompat.Whole_relates_to_Whole.
Definition R_prime_is_serial := BackwardCompat.R_prime_is_serial.
Definition R_prime_total_to_Whole := BackwardCompat.R_prime_total_to_Whole.
Definition no_isolated_entities := BackwardCompat.no_isolated_entities.

(* Adjacency and reachability *)
Definition is_adjacent := BackwardCompat.is_adjacent.
Definition all_adjacent_to_Whole := BackwardCompat.all_adjacent_to_Whole.
Definition one_step_adjacent := BackwardCompat.one_step_adjacent.
Definition reachable := BackwardCompat.reachable.
Definition all_reach_Whole := BackwardCompat.all_reach_Whole.
Definition common_successor := BackwardCompat.common_successor.

(* UCF_GUTT prefixed exports *)
Definition UCF_GUTT_Proposition_1_Refined := BackwardCompat.UCF_GUTT_Proposition_1_Refined.
Definition UCF_GUTT_Whole_Universal := BackwardCompat.UCF_GUTT_Whole_Universal.
Definition UCF_GUTT_R_Restriction := BackwardCompat.UCF_GUTT_R_Restriction.
Definition UCF_GUTT_No_Isolation := BackwardCompat.UCF_GUTT_No_Isolation.
Definition UCF_GUTT_Witness := BackwardCompat.UCF_GUTT_Witness.
Definition UCF_GUTT_Witness_Works := BackwardCompat.UCF_GUTT_Witness_Works.

(* Explicit access to parameters via module - NO top-level U/R pollution *)
Module Params := BackwardCompat.

(* ========================================================================== *)
(*                           VERIFICATION SUMMARY                             *)
(* ========================================================================== *)

(*
  +===========================================================================+
  |                           VERIFICATION SUMMARY                            |
  +===========================================================================+
  |                                                                           |
  |  Theorem: forallx in U_x, existsy in U_x: R'(x,y)    [SERIALITY, not connectivity]       |
  |                                                                           |
  |  This theorem holds BY CONSTRUCTION: R' is defined so that               |
  |  R'(x, Whole) = True for all x. The Whole is a terminal sink w.r.t. U.   |
  |                                                                           |
  |  TERMINOLOGY:                                                             |
  |    * Seriality = every node has at least one successor (outgoing edge)   |
  |    * Terminal sink w.r.t. U = no outgoing edges to U (but has self-loop) |
  |    * This is NOT pairwise connectivity; we guarantee only seriality      |
  |    * common_successor provides: forallx,y. existsz. reachable x z /\ reachable y z  |
  |                                                                           |
  |  CONSTRUCTION PATTERN: Serial Completion (Whole-Completion)               |
  |    Given (U, R), construct (Ux, R') where:                                |
  |    - Ux = U  cup  {Whole}                                                     |
  |    - R' extends R with universal Whole-targeting                          |
  |    - R' is serial by construction                                         |
  |    - R' is a conservative extension of R                                  |
  |                                                                           |
  |  Three formulations provided:                                             |
  |                                                                           |
  |  1. Core.proposition_1 (CLOSED - CANONICAL)                               |
  |     - Explicit forall U R quantification                                       |
  |     - Print Assumptions: "Closed under the global context"                |
  |                                                                           |
  |  2. ConcreteExample.seriality                                             |
  |     - U = nat, R = False (empty relation)                                 |
  |     - Demonstrates worst-case still works                                 |
  |                                                                           |
  |  3. BackwardCompat.refined_proposition_1                                  |
  |     - Parameter U, R for legacy imports                                   |
  |     - Print Assumptions shows U, R (expected)                             |
  |                                                                           |
  |  Key Lemmas:                                                              |
  |    * R_prime_restricts : R'(elem a, elem b) <-> R a b                       |
  |    * R_lift : R a b -> R'(elem a, elem b)                                  |
  |    * everything_relates_to_Whole : R'(x, Whole)                           |
  |    * Whole_terminal_sink : ~R'(Whole, elem b)                             |
  |    * common_successor : forallx,y. existsz. reach x z /\ reach y z                   |
  |                                                                           |
  |  Proof Method:                                                            |
  |    * Witness: Whole (always works by definition of R')                    |
  |    * Fully constructive (no classical logic)                              |
  |    * Proof obligation reduces to True; solved by exact I                  |
  |                                                                           |
  |  Key Insight:                                                             |
  |    By extending any universe with the Whole and defining R' to include    |
  |    universal Whole-targeting, "no entity is isolated" becomes a           |
  |    mathematical necessity rather than an empirical assumption.            |
  |                                                                           |
  +===========================================================================+
*)
