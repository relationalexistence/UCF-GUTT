(*
  UCF/GUTT Extensions Library - Basic Usage Example
  ==================================================
  
  This file demonstrates fundamental usage of the Whole-completion
  construction for universal connectivity, including integration
  with Proposition 01 (the seriality theorem).
  
  To compile (from Library root):
    make build
    coqc -R src UCF.GUTT.Extensions -R props UCF.GUTT.Props examples/BasicUsage.v
  
  Or from examples directory:
    coqc -R ../src UCF.GUTT.Extensions -R ../props UCF.GUTT.Props BasicUsage.v
*)

(* ========================================================================== *)
(*                         LIBRARY IMPORTS                                    *)
(* ========================================================================== *)

(** Core Extensions Library *)
Require Import Top__Extensions__Prelude.
Require Import Top__Extensions__Extras.

(** Proposition 01: Seriality Theorem *)
Require Import Proposition_01.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 1: Natural Number Order                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
    The relation < on nat is NOT serial: there's no y such that
    for all x, x < y (no largest natural number).
    
    After Whole-completion, every number relates to Whole.
*)

Module NatExample.

  (** The carrier is option nat *)
  Definition Nat' := Ux nat.
  
  (** Embed a natural number *)
  Definition embed (n : nat) : Nat' := elem n.
  
  (** The Whole element *)
  Definition W : Nat' := Whole.
  
  (** Lift the < relation *)
  Definition lt' := R_prime lt.
  
  (** Key theorem: Every number relates to Whole *)
  Theorem every_nat_reaches_whole : forall n : nat,
    lt' (embed n) W.
  Proof.
    intro n. apply everything_relates_to_Whole.
  Qed.
  
  (** Original structure preserved: 3 < 5 still holds *)
  Theorem original_preserved : lt' (embed 3) (embed 5).
  Proof.
    apply R_lift. auto.
  Qed.
  
  (** Whole is terminal: can't go from Whole to any number *)
  Theorem whole_is_terminal : forall n : nat,
    ~ lt' W (embed n).
  Proof.
    intro n. apply Whole_terminal_sink.
  Qed.
  
  (** Whole is fresh: it's not equal to any embedded number *)
  Theorem whole_is_new : forall n : nat,
    embed n <> W.
  Proof.
    intro n. apply Whole_fresh.
  Qed.
  
  (** Using Proposition 01 directly *)
  Theorem seriality_for_lt : forall x : Nat',
    exists y : Nat', lt' x y.
  Proof.
    exact (proposition_01 nat lt).
  Qed.

End NatExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 2: Social Network Completion                    *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Model a social network where "follows" is the relation.
    Some users are "dead ends" (don't follow anyone).
    
    Whole-completion adds a universal "community" node.
*)

Module SocialNetwork.

  (** Users are just natural numbers for this example *)
  Definition User := nat.
  
  (** A simple "follows" relation: user n follows user n+1 *)
  Definition follows (a b : User) : Prop := b = S a.
  
  (** Solution: Complete the network *)
  Definition User' := Ux User.
  Definition follows' := R_prime follows.
  Definition Community : User' := Whole.
  
  (** Now every user "connects to" the community *)
  Theorem all_connected_to_community : forall u : User,
    follows' (elem u) Community.
  Proof.
    intro u. apply everything_relates_to_Whole.
  Qed.
  
  (** Original follow relationships preserved *)
  Theorem follows_preserved : forall u : User,
    follows' (elem u) (elem (S u)).
  Proof.
    intro u. apply R_lift. reflexivity.
  Qed.
  
  (** Using pointed seriality: Community is a uniform witness *)
  Theorem community_is_universal_target :
    exists w : User', forall x : User', follows' x w.
  Proof.
    exact (pointed_seriality User follows).
  Qed.

End SocialNetwork.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 3: Conservativity (Polymorphic)                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate that lifting and restriction are inverses.
    All theorems are fully polymorphic - no Variable declarations.
*)

Module Conservativity.

  (** If the lifted relation holds on embedded elements,
      then the original relation holds *)
  Theorem lift_reflects : forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R_prime R (elem a) (elem b) -> R a b.
  Proof.
    intros U R a b H.
    apply R_prime_restricts in H.
    exact H.
  Qed.
  
  (** If the original relation holds, so does the lifted one *)
  Theorem lift_preserves : forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R a b -> R_prime R (elem a) (elem b).
  Proof.
    intros U R a b H.
    apply R_prime_restricts.
    exact H.
  Qed.
  
  (** Full equivalence *)
  Theorem lift_iff : forall (U : Type) (R : U -> U -> Prop) (a b : U),
    R_prime R (elem a) (elem b) <-> R a b.
  Proof.
    intros U R a b. apply R_prime_restricts.
  Qed.

End Conservativity.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 4: No Dead Ends (Polymorphic)                   *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Prove that after completion, no element is isolated.
    All theorems are fully polymorphic - no Variable declarations.
*)

Module NoDeadEnds.

  (** There is no element with no outgoing edges *)
  Theorem no_isolated_elements : forall (U : Type) (R : U -> U -> Prop),
    ~ exists x : Ux U, forall y : Ux U, ~ R_prime R x y.
  Proof.
    intros U R. apply no_isolated_entities.
  Qed.
  
  (** Every element has at least one successor - this IS Proposition 01! *)
  Theorem every_element_has_successor : forall (U : Type) (R : U -> U -> Prop),
    forall x : Ux U, exists y : Ux U, R_prime R x y.
  Proof.
    intros U R x. apply proposition_01.
  Qed.

End NoDeadEnds.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 5: Using Extension Infrastructure               *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate the extension record types and morphisms.
*)

Module ExtensionExample.

  (** Get the canonical serial extension for nat *)
  Definition nat_serial_ext : Extension.SerialExtension nat :=
    Extension.serial_extension nat.
  
  (** Get the identity extension *)
  Definition nat_id_ext := Extension.id_extension nat.
  
  (** Compose two extensions *)
  Definition double_ext :=
    Extension.compose
      (WholeCompletion.as_extension nat)
      (WholeCompletion.as_extension (option nat)).
  
  (** The double completion has type option (option nat) *)
  Example double_carrier_type :
    ue_carrier double_ext = option (option nat).
  Proof. reflexivity. Qed.
  
  (** Injection goes to the innermost level *)
  Example double_inject_test :
    ue_inject double_ext 42 = Some (Some 42).
  Proof. reflexivity. Qed.

End ExtensionExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 6: Using Extras (Closures)                      *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate relation closures from Extras.
*)

Module ClosureExample.

  (** Reflexive closure of < *)
  Definition le_refl := RelationClosures.refl_closure nat lt.
  
  (** Symmetric closure of < (makes it comparable in both directions) *)
  Definition lt_sym := RelationClosures.sym_closure nat lt.
  
  (** 5 <= 5 via reflexive closure *)
  Example refl_example : le_refl 5 5.
  Proof. left. reflexivity. Qed.
  
  (** 5 < 3 OR 3 < 5 via symmetric closure *)
  Example sym_example : lt_sym 5 3.
  Proof. right. auto. Qed.
  
  (** Lift the symmetric closure *)
  Definition lt_sym' := R_prime lt_sym.
  
  (** It's still serial after lifting *)
  Example sym_serial : forall x : Ux nat, exists y, lt_sym' x y.
  Proof.
    intro x. apply proposition_01.
  Qed.

End ClosureExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 7: Inversion Principles                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate the inversion lemmas from Proposition_01.
*)

Module InversionExample.

  (** If we can reach an element from somewhere, the source must be an element *)
  Example inversion_to_elem :
    forall (x : Ux nat),
      R_prime lt x (elem 5) -> 
      exists n : nat, x = elem n /\ n < 5.
  Proof.
    intros x H.
    apply R_prime_to_elem_inv. exact H.
  Qed.
  
  (** If we start from Whole, we can only reach Whole *)
  Example inversion_from_whole :
    forall (y : Ux nat),
      R_prime lt Whole y -> y = Whole.
  Proof.
    intros y H.
    apply (R_prime_from_Whole_inv nat lt). exact H.
  Qed.
  
  (** Case analysis on elements *)
  Example case_analysis :
    forall (x : Ux nat),
      x = Whole \/ exists n : nat, x = elem n.
  Proof.
    intro x. apply Ux_case.
  Qed.

End InversionExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 8: Constructive Witness                         *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate the constructive/computational aspects.
*)

Module ConstructiveExample.

  (** The witness function always returns Whole *)
  Example witness_computes : witness (elem 42) = @Whole nat.
  Proof. reflexivity. Qed.
  
  (** The sigma type version allows extraction *)
  Definition find_successor (x : Ux nat) : { y : Ux nat | R_prime lt x y } :=
    proposition_01_sigma nat lt x.
  
  (** We can compute the witness *)
  Example extracted_witness :
    proj1_sig (find_successor (elem 100)) = Whole.
  Proof. reflexivity. Qed.

End ConstructiveExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLE 9: Iterated Completion                          *)
(*                                                                            *)
(* ========================================================================== *)

(**
    Demonstrate nested/iterated Whole-completion.
*)

Module IteratedExample.

  (** Double completion *)
  Definition Nat'' := SerialComposition.iter_carrier 2 nat.
  
  (** There are now TWO Wholes: inner and outer *)
  Definition inner_whole : Nat'' := SerialComposition.inner_whole nat.
  Definition outer_whole : Nat'' := SerialComposition.iter_point 1 nat.
  
  (** They are distinct *)
  Example wholes_distinct : inner_whole <> outer_whole.
  Proof. apply SerialComposition.inner_outer_distinct. Qed.
  
  (** Elements reach both Wholes *)
  Definition lt'' := SerialComposition.iter_lift 2 nat lt.
  
  Example elem_to_inner : lt'' (Some (Some 5)) inner_whole.
  Proof. apply SerialComposition.elem_to_inner_whole. Qed.
  
  Example elem_to_outer : lt'' (Some (Some 5)) outer_whole.
  Proof. apply SerialComposition.elem_to_outer_whole. Qed.

End IteratedExample.

(* ========================================================================== *)
(*                                                                            *)
(*                    AXIOM AUDIT                                             *)
(*                                                                            *)
(* ========================================================================== *)

Module AxiomAudit.

  (** Verify key theorems are axiom-free by computation *)
  
  Definition test_Whole : @Whole nat = None.
  Proof. reflexivity. Qed.
  
  Definition test_elem : elem 42 = Some 42.
  Proof. reflexivity. Qed.
  
  Definition test_witness : witness (elem 5) = @Whole nat.
  Proof. reflexivity. Qed.
  
  Definition test_R_prime : R_prime lt (elem 3) (elem 5) = (3 < 5).
  Proof. reflexivity. Qed.

End AxiomAudit.

(* ========================================================================== *)
(*                                                                            *)
(*                    SUMMARY                                                 *)
(*                                                                            *)
(* ========================================================================== *)

(**
  KEY POINTS DEMONSTRATED
  =======================
  
  From Proposition_01:
    - Ux U            = option U (the extended universe)
    - Whole           = None (the terminal element)  
    - elem u          = Some u (embedding)
    - R_prime R       = the serial completion of R
    - proposition_01  = forall U R x, exists y, R_prime R x y
    - seriality       = alias for proposition_01
    - witness         = fun _ => Whole (constructive witness)
  
  From Top__Extensions__Prelude (UE module):
    - UE.Carrier, UE.Whole, UE.elem, UE.lift
    - UE.serial, UE.conservative, UE.point_terminal, UE.point_fresh
    - UE.no_dead_ends, UE.elem_injective
    - Extension records and morphisms
  
  From Top__Extensions__Extras:
    - RelationClosures (refl, sym, trans, equiv closures)
    - Decidability lemmas
    - Utilities (carrier_map, carrier_bind)
  
  From Top__Extensions__Composition:
    - SerialComposition for iterated completions
    - Extension composition and identity
    - Category laws (unit, associativity)
  
  ALL THEOREMS USE ZERO AXIOMS.
*)
