(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
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
  |  THEOREM: forall x in U_x, exists y in U_x : R'(x,y)                     |
  |                                                                          |
  |  "Every entity in the extended universe has at least one outgoing edge"  |
  |                                                                          |
  |  This is SERIALITY (every node has a successor), achieved by adding      |
  |  the Whole as a terminal sink that every entity relates to.              |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  COMPILATION:                                                            |
  |                                                                          |
  |    cd Library/props                                                      |
  |    coqc -R ../src UCF.GUTT.Extensions Proposition_01.v                   |
  |                                                                          |
  |  Or from Library root:                                                   |
  |    coqc -R src UCF.GUTT.Extensions props/Proposition_01.v                |
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

(* ========================================================================== *)
(*                                                                            *)
(*                    CORE DEFINITIONS                                        *)
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

(** Semantic alias. *)
Definition serial_completion {U : Type} := @R_prime U.

(* ========================================================================== *)
(*                                                                            *)
(*                    PROPOSITION 01: MAIN THEOREM                            *)
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

(* ========================================================================== *)
(*                                                                            *)
(*                    KEY PROPERTIES                                          *)
(*                                                                            *)
(* ========================================================================== *)

(** R' is a conservative extension: restricts to R on U x U. *)
Lemma R_prime_restricts :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R_prime R (elem a) (elem b) <-> R a b.
Proof.
  intros U R a b. apply UE.conservative.
Qed.

(** Any edge in R lifts to R'. *)
Lemma R_lift :
  forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R a b -> R_prime R (elem a) (elem b).
Proof.
  intros U R a b H. apply UE.lift_preserves. exact H.
Qed.

(** Everything relates to Whole. *)
Lemma everything_relates_to_Whole :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
    R_prime R x Whole.
Proof.
  intros U R x. apply UE.serial.
Qed.

(** Whole has a self-loop. *)
Lemma Whole_self_relates :
  forall (U : Type) (R : U -> U -> Prop),
    R_prime R (@Whole U) (@Whole U).
Proof.
  intros U R. apply UE.point_self_loop.
Qed.

(** Whole is terminal sink w.r.t. U (cannot reach any element from Whole). *)
Lemma Whole_terminal_sink :
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

(** elem is injective. *)
Lemma elem_injective :
  forall (U : Type) (a b : U), elem a = elem b -> a = b.
Proof.
  intros U a b H. apply UE.elem_injective. exact H.
Qed.

(** Whole is fresh (not in the image of elem). *)
Lemma Whole_fresh :
  forall (U : Type) (u : U), elem u <> (@Whole U).
Proof.
  intros U u. apply UE.point_fresh.
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
(*                    INVERSION PRINCIPLES                                    *)
(*                                                                            *)
(* ========================================================================== *)

(** Case analysis on Ux elements. *)
Lemma Ux_case : forall (U : Type) (x : Ux U),
  x = Whole \/ exists u : U, x = elem u.
Proof.
  intros U x. apply UE.carrier_case.
Qed.

(** If R'(x, elem b) then x = elem a for some a with R a b. *)
Lemma R_prime_to_elem_inv :
  forall (U : Type) (R : U -> U -> Prop) (x : Ux U) (b : U),
    R_prime R x (elem b) -> exists a : U, x = elem a /\ R a b.
Proof.
  intros U R x b H. apply UE.lift_to_elem_inv. exact H.
Qed.

(** If R'(Whole, y) then y = Whole. *)
Lemma R_prime_from_Whole_inv :
  forall (U : Type) (R : U -> U -> Prop) (y : Ux U),
    R_prime R Whole y -> y = Whole.
Proof.
  intros U R y H. 
  unfold R_prime, Whole in H.
  apply WholeCompletion.lift_rel_from_point_inv in H. exact H.
Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXTENSION INFRASTRUCTURE                                *)
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

End Extension.

(* ========================================================================== *)
(*                                                                            *)
(*                    TACTICS                                                 *)
(*                                                                            *)
(* ========================================================================== *)

(** Tactic to prove seriality goals. *)
Ltac prove_seriality :=
  match goal with
  | |- exists y, R_prime _ _ y => exists Whole; apply UE.serial
  | |- exists y, UE.lift _ _ y => exists UE.Whole; apply UE.serial
  | |- R_prime _ _ Whole => apply UE.serial
  | |- UE.lift _ _ UE.Whole => apply UE.serial
  end.

(** Tactic to simplify R_prime expressions. *)
Ltac rprime_simpl :=
  unfold R_prime, elem, Whole;
  ue_simpl.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLES                                                *)
(*                                                                            *)
(* ========================================================================== *)

Module Examples.

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

End Examples.

(* ========================================================================== *)
(*                                                                            *)
(*                    AXIOM AUDIT                                             *)
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

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    DOCUMENTATION                                           *)
(*                                                                            *)
(* ========================================================================== *)

(**
  QUICK REFERENCE
  ===============
  
  Types:
    Ux U            = option U (the extended universe)
  
  Constructors:
    Whole           = None (the terminal element)
    elem u          = Some u (embedding)
  
  Relation:
    R_prime R       = the serial completion of R
  
  Main Theorem:
    proposition_01  : forall U R x, exists y, R_prime R x y
    seriality       : (alias for proposition_01)
  
  Key Properties:
    R_prime_restricts           : R_prime R (elem a) (elem b) <-> R a b
    everything_relates_to_Whole : R_prime R x Whole
    Whole_terminal_sink         : ~ R_prime R Whole (elem b)
    no_isolated_entities        : ~ exists x, forall y, ~ R_prime R x y
  
  Extension Infrastructure:
    Extension.serial_extension U  : SerialExtension U
    Extension.compose E1 E2       : composition of extensions
    Extension.id_extension U      : identity extension
  
  COMPILATION
  ===========
  
  From Library/props:
    coqc -R ../src UCF.GUTT.Extensions Proposition_01.v
  
  From Library root:
    coqc -R src UCF.GUTT.Extensions props/Proposition_01.v
  
  AXIOM STATUS
  ============
  
  This file uses ZERO AXIOMS. All theorems are fully polymorphic in U.
  Run `Print Assumptions proposition_01.` to verify: output should be
  "Closed under the global context".
*)
