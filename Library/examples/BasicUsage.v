(*
  UCF/GUTT Extensions Library - Basic Usage Example
  ==================================================
  
  This file demonstrates fundamental usage of the Whole-completion
  construction for universal connectivity.
  
  To compile:
    coqc -R ../src UCF.GUTT.Extensions BasicUsage.v
*)

Require Import Top__Extensions__Prelude.

(** =========================================
    EXAMPLE 1: Completing Natural Number Order
    =========================================
    
    The relation < on nat is NOT serial: there's no y such that
    for all x, x < y (no largest natural number).
    
    After Whole-completion, every number relates to Whole.
*)

Module NatExample.

  (** The carrier is option nat *)
  Definition Nat' := UE.Carrier nat.
  
  (** Embed a natural number *)
  Definition embed (n : nat) : Nat' := UE.elem n.
  
  (** The Whole element *)
  Definition W : Nat' := UE.Whole.
  
  (** Lift the < relation *)
  Definition lt' := UE.lift lt.
  
  (** Key theorem: Every number relates to Whole *)
  Theorem every_nat_reaches_whole : forall n : nat,
    lt' (embed n) W.
  Proof.
    intro n. apply UE.serial.
  Qed.
  
  (** Original structure preserved: 3 < 5 still holds *)
  Theorem original_preserved : lt' (embed 3) (embed 5).
  Proof.
    apply UE.lift_preserves. auto.
  Qed.
  
  (** Whole is terminal: can't go from Whole to any number *)
  Theorem whole_is_terminal : forall n : nat,
    ~ lt' W (embed n).
  Proof.
    intro n. apply UE.point_terminal.
  Qed.
  
  (** Whole is fresh: it's not equal to any embedded number *)
  Theorem whole_is_new : forall n : nat,
    embed n <> W.
  Proof.
    intro n. apply UE.point_fresh.
  Qed.

End NatExample.

(** =========================================
    EXAMPLE 2: Social Network Completion
    =========================================
    
    Model a social network where "follows" is the relation.
    Some users are "dead ends" (don't follow anyone).
    
    Whole-completion adds a universal "community" node.
*)

Module SocialNetwork.

  (** Users are just natural numbers for this example *)
  Definition User := nat.
  
  (** A simple "follows" relation: user n follows user n+1 *)
  Definition follows (a b : User) : Prop := b = S a.
  
  (** Problem: User 0 doesn't follow anyone going backwards.
      User 100 is a dead end if no one is > 100. *)
  
  (** Solution: Complete the network *)
  Definition User' := UE.Carrier User.
  Definition follows' := UE.lift follows.
  Definition Community : User' := UE.Whole.
  
  (** Now every user "connects to" the community *)
  Theorem all_connected_to_community : forall u : User,
    follows' (UE.elem u) Community.
  Proof.
    intro u. apply UE.serial.
  Qed.
  
  (** Original follow relationships preserved *)
  Theorem follows_preserved : forall u : User,
    follows' (UE.elem u) (UE.elem (S u)).
  Proof.
    intro u. apply UE.lift_preserves. reflexivity.
  Qed.

End SocialNetwork.

(** =========================================
    EXAMPLE 3: Using Conservativity
    =========================================
    
    Demonstrate that lifting and restriction are inverses.
*)

Module Conservativity.

  Variable U : Type.
  Variable R : U -> U -> Prop.
  
  (** If the lifted relation holds on embedded elements,
      then the original relation holds *)
  Theorem lift_reflects : forall a b : U,
    UE.lift R (UE.elem a) (UE.elem b) -> R a b.
  Proof.
    intros a b H.
    apply UE.conservative in H.
    exact H.
  Qed.
  
  (** If the original relation holds, so does the lifted one *)
  Theorem lift_preserves : forall a b : U,
    R a b -> UE.lift R (UE.elem a) (UE.elem b).
  Proof.
    intros a b H.
    apply UE.conservative.
    exact H.
  Qed.
  
  (** Full equivalence *)
  Theorem lift_iff : forall a b : U,
    UE.lift R (UE.elem a) (UE.elem b) <-> R a b.
  Proof.
    intros a b. apply UE.conservative.
  Qed.

End Conservativity.

(** =========================================
    EXAMPLE 4: No Dead Ends
    =========================================
    
    Prove that after completion, no element is isolated.
*)

Module NoDeadEnds.

  Variable U : Type.
  Variable R : U -> U -> Prop.
  
  (** There is no element with no outgoing edges *)
  Theorem no_isolated_elements :
    ~ exists x : UE.Carrier U, 
        forall y : UE.Carrier U, ~ UE.lift R x y.
  Proof.
    apply UE.no_dead_ends.
  Qed.
  
  (** Every element has at least one successor *)
  Theorem every_element_has_successor :
    forall x : UE.Carrier U,
      exists y : UE.Carrier U, UE.lift R x y.
  Proof.
    intro x.
    exists UE.Whole.
    apply UE.serial.
  Qed.

End NoDeadEnds.

(** =========================================
    SUMMARY
    =========================================
    
    Key points demonstrated:
    
    1. UE.Carrier U = option U (the extended universe)
    2. UE.elem u embeds u into the extension
    3. UE.Whole is the universal sink
    4. UE.lift R extends R to the completion
    5. UE.serial proves everything reaches Whole
    6. UE.conservative proves original structure preserved
    7. UE.point_terminal proves Whole is a sink
    8. UE.point_fresh proves Whole is genuinely new
    9. UE.no_dead_ends proves no isolated elements
    
    All theorems are proven with ZERO AXIOMS.
*)
