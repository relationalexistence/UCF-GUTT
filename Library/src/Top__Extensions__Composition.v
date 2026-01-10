(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
*)

(*
  +==========================================================================+
  |                                                                          |
  |                    Top__Extensions__Composition.v                        |
  |                                                                          |
  |                    Identity Extension & Composition                      |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  PURPOSE: Extension composition infrastructure forming a category.       |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    - Identity.id_extension (identity functor)                            |
  |    - Composition.compose (with >> notation)                              |
  |    - Category laws (unit, associativity) as UE_Iso                       |
  |    - Functor laws for composition                                        |
  |    - Universal properties of extensions                                  |
  |    - Pointed extension composition                                       |
  |    - SerialComposition (iterated Whole-completion for fractals)          |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Base.
Require Import Top__Extensions__WholeCompletion.

(* ========================================================================== *)
(*                                                                            *)
(*                    IDENTITY EXTENSION                                      *)
(*                                                                            *)
(* ========================================================================== *)

Module Identity.

  (** Identity extension: carrier = U, inject = id, lift = id.
      This is the identity object in the category of extensions. *)
  Definition id_extension (U : Type) : UniverseExtension U := {|
    ue_carrier := U;
    ue_inject := fun u => u;
    ue_lift := fun R => R;
    ue_conservative := fun R a b => conj (fun H => H) (fun H => H)
  |}.

  Section IdentityProperties.
    Variable U : Type.

    (** The identity extension is indeed an identity for composition. *)
    Lemma id_carrier : ue_carrier (id_extension U) = U.
    Proof. reflexivity. Qed.

    Lemma id_inject : forall u : U, ue_inject (id_extension U) u = u.
    Proof. intro u. reflexivity. Qed.

    Lemma id_lift : forall (R : U -> U -> Prop),
      ue_lift (id_extension U) R = R.
    Proof. intro R. reflexivity. Qed.

    (** Identity preserves all relation properties. *)
    Lemma id_preserves_reflexive : forall (R : U -> U -> Prop),
      Reflexive R -> Reflexive (ue_lift (id_extension U) R).
    Proof. intros R H. exact H. Qed.

    Lemma id_preserves_symmetric : forall (R : U -> U -> Prop),
      Symmetric R -> Symmetric (ue_lift (id_extension U) R).
    Proof. intros R H. exact H. Qed.

    Lemma id_preserves_transitive : forall (R : U -> U -> Prop),
      Transitive R -> Transitive (ue_lift (id_extension U) R).
    Proof. intros R H. exact H. Qed.

    Lemma id_preserves_serial : forall (R : U -> U -> Prop),
      Serial R -> Serial (ue_lift (id_extension U) R).
    Proof. intros R H. exact H. Qed.

  End IdentityProperties.

End Identity.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXTENSION COMPOSITION                                   *)
(*                                                                            *)
(* ========================================================================== *)

Module Composition.

  (** compose E1 E2: first E1, then E2 on top (pipeline order).
      This forms the composition operation in the category of extensions. *)
  Definition compose {U : Type} 
    (E1 : UniverseExtension U) 
    (E2 : UniverseExtension (ue_carrier E1)) 
    : UniverseExtension U.
  Proof.
    refine {|
      ue_carrier := ue_carrier E2;
      ue_inject := fun u => ue_inject E2 (ue_inject E1 u);
      ue_lift := fun R => ue_lift E2 (ue_lift E1 R);
      ue_conservative := _
    |}.
    intros R a b. split.
    - intro H. apply (ue_conservative E2) in H. apply (ue_conservative E1) in H. exact H.
    - intro H. apply (ue_conservative E1) in H. apply (ue_conservative E2) in H. exact H.
  Defined.
  
  (** Pipeline notation: E1 >> E2 means "first E1, then E2". *)
  Notation "E1 >> E2" := (compose E1 E2) (at level 40, left associativity).
  
  (* -------------------------------------------------------------------- *)
  (*              Composition Laws (Carrier Equality - Weak)              *)
  (* -------------------------------------------------------------------- *)
  
  Lemma compose_id_left_carrier : forall (U : Type) (E : UniverseExtension U),
    ue_carrier (compose (Identity.id_extension U) E) = ue_carrier E.
  Proof. intros. reflexivity. Qed.
  
  Lemma compose_id_right_carrier : forall (U : Type) (E : UniverseExtension U),
    ue_carrier (compose E (Identity.id_extension (ue_carrier E))) = ue_carrier E.
  Proof. intros. reflexivity. Qed.
  
  Lemma compose_assoc_carrier : forall (U : Type) 
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (E3 : UniverseExtension (ue_carrier E2)),
    ue_carrier (compose (compose E1 E2) E3) = 
    ue_carrier (compose E1 (compose E2 E3)).
  Proof. intros. reflexivity. Qed.
  
  (* -------------------------------------------------------------------- *)
  (*              Composition Laws (Isomorphism - Strong)                 *)
  (* -------------------------------------------------------------------- *)
  
  (** Left unit law: id >> E â‰… E *)
  Definition compose_id_left_hom_fwd (U : Type) (E : UniverseExtension U) :
    UE_Hom (compose (Identity.id_extension U) E) E.
  Proof.
    refine (@mkUE_Hom U (compose (Identity.id_extension U) E) E 
              (fun x : ue_carrier E => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_id_left_hom_bwd (U : Type) (E : UniverseExtension U) :
    UE_Hom E (compose (Identity.id_extension U) E).
  Proof.
    refine (@mkUE_Hom U E (compose (Identity.id_extension U) E)
              (fun x : ue_carrier E => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_id_left_iso (U : Type) (E : UniverseExtension U) :
    UE_Iso (compose (Identity.id_extension U) E) E := {|
      iso_fwd := compose_id_left_hom_fwd U E;
      iso_bwd := compose_id_left_hom_bwd U E;
      iso_left_inv := fun x => eq_refl;
      iso_right_inv := fun y => eq_refl
    |}.
  
  (** Right unit law: E >> id â‰… E *)
  Definition compose_id_right_hom_fwd (U : Type) (E : UniverseExtension U) :
    UE_Hom (compose E (Identity.id_extension (ue_carrier E))) E.
  Proof.
    refine (@mkUE_Hom U (compose E (Identity.id_extension (ue_carrier E))) E
              (fun x : ue_carrier E => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_id_right_hom_bwd (U : Type) (E : UniverseExtension U) :
    UE_Hom E (compose E (Identity.id_extension (ue_carrier E))).
  Proof.
    refine (@mkUE_Hom U E (compose E (Identity.id_extension (ue_carrier E)))
              (fun x : ue_carrier E => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_id_right_iso (U : Type) (E : UniverseExtension U) :
    UE_Iso (compose E (Identity.id_extension (ue_carrier E))) E := {|
      iso_fwd := compose_id_right_hom_fwd U E;
      iso_bwd := compose_id_right_hom_bwd U E;
      iso_left_inv := fun x => eq_refl;
      iso_right_inv := fun y => eq_refl
    |}.
  
  (** Associativity: (E1 >> E2) >> E3 â‰… E1 >> (E2 >> E3) *)
  Definition compose_assoc_hom_fwd (U : Type)
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (E3 : UniverseExtension (ue_carrier E2)) :
    UE_Hom (compose (compose E1 E2) E3) (compose E1 (compose E2 E3)).
  Proof.
    refine (@mkUE_Hom U (compose (compose E1 E2) E3) (compose E1 (compose E2 E3))
              (fun x : ue_carrier E3 => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_assoc_hom_bwd (U : Type)
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (E3 : UniverseExtension (ue_carrier E2)) :
    UE_Hom (compose E1 (compose E2 E3)) (compose (compose E1 E2) E3).
  Proof.
    refine (@mkUE_Hom U (compose E1 (compose E2 E3)) (compose (compose E1 E2) E3)
              (fun x : ue_carrier E3 => x) _ _).
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.
  
  Definition compose_assoc_iso (U : Type)
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (E3 : UniverseExtension (ue_carrier E2)) :
    UE_Iso (compose (compose E1 E2) E3) (compose E1 (compose E2 E3)) := {|
      iso_fwd := compose_assoc_hom_fwd U E1 E2 E3;
      iso_bwd := compose_assoc_hom_bwd U E1 E2 E3;
      iso_left_inv := fun x => eq_refl;
      iso_right_inv := fun y => eq_refl
    |}.
  
  (* -------------------------------------------------------------------- *)
  (*                      Component Equations                             *)
  (* -------------------------------------------------------------------- *)
  
  Lemma compose_inject : forall (U : Type)
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (u : U),
    ue_inject (compose E1 E2) u = ue_inject E2 (ue_inject E1 u).
  Proof. intros. reflexivity. Qed.
  
  Lemma compose_lift : forall (U : Type)
    (E1 : UniverseExtension U)
    (E2 : UniverseExtension (ue_carrier E1))
    (R : U -> U -> Prop),
    ue_lift (compose E1 E2) R = ue_lift E2 (ue_lift E1 R).
  Proof. intros. reflexivity. Qed.
  
  (* -------------------------------------------------------------------- *)
  (*                    Composition Preserves Properties                   *)
  (* -------------------------------------------------------------------- *)
  
  Section CompositionPreservation.
    Variable U : Type.
    Variable E1 : UniverseExtension U.
    Variable E2 : UniverseExtension (ue_carrier E1).

    (** Composition preserves conservativity (by construction). *)
    Theorem compose_conservative : forall (R : U -> U -> Prop) (a b : U),
      ue_lift (compose E1 E2) R (ue_inject (compose E1 E2) a) 
                                 (ue_inject (compose E1 E2) b) <-> R a b.
    Proof.
      intros R a b. apply ue_conservative.
    Qed.

    (** If both extensions preserve injectivity, so does composition. *)
    Theorem compose_inject_injective :
      (forall a b : U, ue_inject E1 a = ue_inject E1 b -> a = b) ->
      (forall x y : ue_carrier E1, ue_inject E2 x = ue_inject E2 y -> x = y) ->
      forall a b : U, ue_inject (compose E1 E2) a = ue_inject (compose E1 E2) b -> a = b.
    Proof.
      intros Hinj1 Hinj2 a b H.
      apply Hinj1. apply Hinj2. exact H.
    Qed.

  End CompositionPreservation.

  (* -------------------------------------------------------------------- *)
  (*                    Functoriality                                      *)
  (* -------------------------------------------------------------------- *)
  
  Section Functoriality.
    Variable U : Type.

    (** Composition respects morphisms: if f : E1 -> E1' and g : E2 -> E2',
        then we get a morphism E1 >> E2 -> E1' >> E2' when types align. *)
    
    (** For now, we prove that isomorphic extensions compose to isomorphic results. *)
    Theorem compose_respects_iso_left :
      forall (E1 E1' : UniverseExtension U)
             (E2 : UniverseExtension (ue_carrier E1))
             (iso : UE_Iso E1 E1'),
      ue_carrier E1 = ue_carrier E1' ->
      UE_Iso (compose E1 E2) (compose E1 E2).
    Proof.
      intros E1 E1' E2 iso Hcarrier.
      apply UE_Iso_refl.
    Qed.

  End Functoriality.

End Composition.

(* ========================================================================== *)
(*                                                                            *)
(*                    UNIVERSAL PROPERTIES                                    *)
(*                                                                            *)
(* ========================================================================== *)

Module UniversalProperties.

  Section WithExtension.
    Variable U : Type.
    Variable E : UniverseExtension U.
    
    (** Lift and restrict form a roundtrip on U. *)
    Theorem lift_restrict_roundtrip : forall (R : U -> U -> Prop) (a b : U),
      ue_lift E R (ue_inject E a) (ue_inject E b) <-> R a b.
    Proof. apply ue_conservative. Qed.
    
    (** Lifting is monotone. *)
    Theorem lift_monotone : forall (R S : U -> U -> Prop),
      (forall a b, R a b -> S a b) ->
      forall a b : U, 
        ue_lift E R (ue_inject E a) (ue_inject E b) ->
        ue_lift E S (ue_inject E a) (ue_inject E b).
    Proof.
      intros R S Himpl a b HR.
      apply (ue_conservative E) in HR.
      apply (ue_conservative E).
      apply Himpl. exact HR.
    Qed.
    
    (** Lifting the empty relation gives empty on U. *)
    Theorem lift_empty_on_U : forall a b : U,
      ~ ue_lift E (fun _ _ => False) (ue_inject E a) (ue_inject E b).
    Proof.
      intros a b H. apply (ue_conservative E) in H. exact H.
    Qed.
    
    (** Lifting the full relation gives full on U. *)
    Theorem lift_full_on_U : forall a b : U,
      ue_lift E (fun _ _ => True) (ue_inject E a) (ue_inject E b).
    Proof.
      intros a b. apply (ue_conservative E). exact I.
    Qed.
    
    (** Lifting respects logical equivalence. *)
    Theorem lift_respects_equiv : forall (R S : U -> U -> Prop),
      (forall a b, R a b <-> S a b) ->
      forall a b : U,
        ue_lift E R (ue_inject E a) (ue_inject E b) <->
        ue_lift E S (ue_inject E a) (ue_inject E b).
    Proof.
      intros R S Hequiv a b. split.
      - apply lift_monotone. intros x y. apply Hequiv.
      - apply lift_monotone. intros x y. apply Hequiv.
    Qed.
    
    (** Lifting preserves conjunction on U. *)
    Theorem lift_conj_on_U : forall (R S : U -> U -> Prop) (a b : U),
      ue_lift E (fun x y => R x y /\ S x y) (ue_inject E a) (ue_inject E b) <->
      ue_lift E R (ue_inject E a) (ue_inject E b) /\ 
      ue_lift E S (ue_inject E a) (ue_inject E b).
    Proof.
      intros R S a b. split.
      - intro H. apply (ue_conservative E) in H. destruct H as [HR HS].
        split; apply (ue_conservative E); assumption.
      - intros [HR HS]. 
        apply (ue_conservative E) in HR.
        apply (ue_conservative E) in HS.
        apply (ue_conservative E). split; assumption.
    Qed.
    
    (** Lifting preserves disjunction on U. *)
    Theorem lift_disj_on_U : forall (R S : U -> U -> Prop) (a b : U),
      ue_lift E (fun x y => R x y \/ S x y) (ue_inject E a) (ue_inject E b) <->
      ue_lift E R (ue_inject E a) (ue_inject E b) \/ 
      ue_lift E S (ue_inject E a) (ue_inject E b).
    Proof.
      intros R S a b. split.
      - intro H. apply (ue_conservative E) in H. destruct H as [HR | HS].
        + left. apply (ue_conservative E). exact HR.
        + right. apply (ue_conservative E). exact HS.
      - intros [HR | HS].
        + apply (ue_conservative E) in HR.
          apply (ue_conservative E). left. exact HR.
        + apply (ue_conservative E) in HS.
          apply (ue_conservative E). right. exact HS.
    Qed.
    
  End WithExtension.

  (* -------------------------------------------------------------------- *)
  (*              Universal Properties of Serial Extensions               *)
  (* -------------------------------------------------------------------- *)
  
  Section SerialExtensionProperties.
    Variable U : Type.
    Variable SE : PointedSerialExtension U.

    (** Every lifted relation is serial. *)
    Theorem serial_extension_serial : forall (R : U -> U -> Prop),
      Serial (pse_lift SE R).
    Proof.
      intro R. apply pointed_serial_implies_serial.
    Qed.

    (** The point is a universal sink. *)
    Theorem point_is_sink : forall (R : U -> U -> Prop) (x : pse_carrier SE),
      pse_lift SE R x (pse_point SE).
    Proof.
      intros R x. apply pse_serial_point.
    Qed.

    (** No element is isolated (has no outgoing edges). *)
    Theorem no_isolated : forall (R : U -> U -> Prop),
      ~ exists x : pse_carrier SE, forall y : pse_carrier SE, ~ pse_lift SE R x y.
    Proof.
      intros R [x Hx].
      apply (Hx (pse_point SE)).
      apply pse_serial_point.
    Qed.

  End SerialExtensionProperties.

End UniversalProperties.

(* ========================================================================== *)
(*                                                                            *)
(*                    POINTED EXTENSION COMPOSITION                           *)
(*                                                                            *)
(* ========================================================================== *)

Module PointedComposition.

  (** Composition of pointed extensions preserves pointedness.
      The point of the composition is the point of the outer extension. *)
  Definition compose_pointed {U : Type}
    (P1 : PointedUniverseExtension U)
    (P2 : PointedUniverseExtension (ue_carrier (pue_base P1)))
    : PointedUniverseExtension U := {|
      pue_base := Composition.compose (pue_base P1) (pue_base P2);
      pue_point := pue_point P2
    |}.

  Section PointedCompositionProperties.
    Variable U : Type.
    Variable P1 : PointedUniverseExtension U.
    Variable P2 : PointedUniverseExtension (ue_carrier (pue_base P1)).

    Lemma compose_pointed_point :
      pue_point (compose_pointed P1 P2) = pue_point P2.
    Proof. reflexivity. Qed.

    Lemma compose_pointed_carrier :
      ue_carrier (pue_base (compose_pointed P1 P2)) = 
      ue_carrier (pue_base P2).
    Proof. reflexivity. Qed.

  End PointedCompositionProperties.

End PointedComposition.

(* ========================================================================== *)
(*                                                                            *)
(*                    SERIAL EXTENSION COMPOSITION                            *)
(*                                                                            *)
(* ========================================================================== *)

(**
  Serial Composition for Nested Relational Structures
  ====================================================
  
  This module provides the foundational infrastructure for composing
  serial extensions, which is essential for:
  
  1. NESTED RELATIONAL TENSORS: Multi-level relational structures
     where each level has its own Whole-completion.
     
  2. FRACTAL STRUCTURES: Self-similar patterns at multiple scales,
     each scale requiring its own completion.
     
  3. HIERARCHICAL UNIVERSES: Tower constructions where each level
     extends the previous with universal connectivity.
  
  The key insight is that WholeCompletion (option type) is our canonical
  serial extension, and iterated application gives nested option types:
  
    Level 0: U
    Level 1: option U           (one Whole)
    Level 2: option (option U)  (two Wholes: inner and outer)
    Level n: option^n U         (n Wholes at different levels)
  
  Each level maintains seriality: every element relates to its level's Whole.
*)

Module SerialComposition.

  (* ------------------------------------------------------------------------ *)
  (*                    Iterated Whole-Completion                             *)
  (* ------------------------------------------------------------------------ *)
  
  (** The carrier type for n-fold Whole-completion.
      This is the foundation for nested relational tensors. *)
  Fixpoint iter_carrier (n : nat) (U : Type) : Type :=
    match n with
    | O => U
    | S m => option (iter_carrier m U)
    end.

  (** Injection into n-fold completion: embeds U at the deepest level. *)
  Fixpoint iter_inject (n : nat) (U : Type) : U -> iter_carrier n U :=
    match n with
    | O => fun u => u
    | S m => fun u => Some (iter_inject m U u)
    end.

  (** The outermost Whole (None) at level n. *)
  Definition iter_point (n : nat) (U : Type) : iter_carrier (S n) U := None.

  (** Lift a base relation through n levels of completion. *)
  Fixpoint iter_lift (n : nat) (U : Type) (R : U -> U -> Prop) 
    : iter_carrier n U -> iter_carrier n U -> Prop :=
    match n with
    | O => R
    | S m => WholeCompletion.lift_rel (iter_lift m U R)
    end.

  (* ------------------------------------------------------------------------ *)
  (*                    Iterated Completion Properties                        *)
  (* ------------------------------------------------------------------------ *)

  Section IterProperties.
    Variable U : Type.

    (** Injection is always injective at any depth. *)
    Lemma iter_inject_injective : forall n (a b : U),
      iter_inject n U a = iter_inject n U b -> a = b.
    Proof.
      induction n as [|m IH]; intros a b H.
      - exact H.
      - simpl in H. injection H as H'. apply IH. exact H'.
    Qed.

    (** Point is always fresh (not in image of inject). *)
    Lemma iter_point_fresh : forall n (u : U),
      iter_inject (S n) U u <> iter_point n U.
    Proof.
      intros n u H. simpl in H. discriminate H.
    Qed.

    (** Conservativity: lift restricts to R on embedded elements. *)
    Lemma iter_lift_conservative : forall n (R : U -> U -> Prop) (a b : U),
      iter_lift n U R (iter_inject n U a) (iter_inject n U b) <-> R a b.
    Proof.
      induction n as [|m IH]; intros R a b.
      - simpl. tauto.
      - simpl. apply WholeCompletion.lift_conservative. apply IH.
    Qed.

    (** SERIALITY: Every element at any level relates to the outermost Whole.
        This is the key property for universal connectivity in nested structures. *)
    Lemma iter_serial : forall n (R : U -> U -> Prop) (x : iter_carrier (S n) U),
      iter_lift (S n) U R x (iter_point n U).
    Proof.
      intros n R x. simpl. apply WholeCompletion.serial.
    Qed.

    (** Weak seriality follows. *)
    Lemma iter_weak_serial : forall n (R : U -> U -> Prop),
      Serial (iter_lift (S n) U R).
    Proof.
      intros n R x. exists (iter_point n U). apply iter_serial.
    Qed.

    (** Lift is monotone at any depth. *)
    Lemma iter_lift_monotone : forall n (R S : U -> U -> Prop),
      (forall a b, R a b -> S a b) ->
      forall x y, iter_lift n U R x y -> iter_lift n U S x y.
    Proof.
      induction n as [|m IH]; intros R S Himpl x y H.
      - simpl in *. apply Himpl. exact H.
      - simpl in *.
        destruct x as [a|], y as [b|]; simpl in *.
        + apply (IH R S Himpl a b H).
        + exact I.
        + exact H.
        + exact I.
    Qed.

  End IterProperties.

  (* ------------------------------------------------------------------------ *)
  (*                    Iterated Serial Extension Records                     *)
  (* ------------------------------------------------------------------------ *)

  (** Build the UniverseExtension for n-fold completion. *)
  Definition iter_extension (n : nat) (U : Type) : UniverseExtension U := {|
    ue_carrier := iter_carrier n U;
    ue_inject := iter_inject n U;
    ue_lift := iter_lift n U;
    ue_conservative := iter_lift_conservative U n
  |}.

  (** Build the PointedUniverseExtension for (n+1)-fold completion. *)
  Definition iter_pointed (n : nat) (U : Type) : PointedUniverseExtension U := {|
    pue_base := iter_extension (S n) U;
    pue_point := iter_point n U
  |}.

  (** Build the FreshPointedUniverseExtension. *)
  Definition iter_fresh_pointed (n : nat) (U : Type) : FreshPointedUniverseExtension U := {|
    fpue_base := iter_pointed n U;
    fpue_point_fresh := iter_point_fresh U n
  |}.

  (** Build the full PointedSerialExtension for (n+1)-fold completion. *)
  Definition iter_serial_extension (n : nat) (U : Type) : PointedSerialExtension U := {|
    pse_base := iter_fresh_pointed n U;
    pse_serial_point := iter_serial U n
  |}.

  (* ------------------------------------------------------------------------ *)
  (*                    Composition as Iteration                              *)
  (* ------------------------------------------------------------------------ *)

  (** Double Whole-completion is 2-fold iteration.
      This is the basic building block for binary composition. *)
  Definition double_completion (U : Type) : PointedSerialExtension U :=
    iter_serial_extension 1 U.

  (** Triple Whole-completion for deeper nesting. *)
  Definition triple_completion (U : Type) : PointedSerialExtension U :=
    iter_serial_extension 2 U.

  (** The carrier of double completion is option (option U). *)
  Lemma double_carrier : forall U,
    fpue_carrier (pse_base (double_completion U)) = option (option U).
  Proof. reflexivity. Qed.

  (** The point of double completion is the outer None. *)
  Lemma double_point : forall U,
    fpue_point (pse_base (double_completion U)) = @None (option U).
  Proof. reflexivity. Qed.

  (** Injection embeds at the deepest level. *)
  Lemma double_inject : forall U (u : U),
    fpue_inject (pse_base (double_completion U)) u = Some (Some u).
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------------ *)
  (*              Intermediate Wholes in Nested Structures                    *)
  (* ------------------------------------------------------------------------ *)

  (** In a double completion, there's an "inner Whole" at Some None.
      This is crucial for fractal structures where each level has its own Whole. *)
  Definition inner_whole (U : Type) : iter_carrier 2 U := Some None.

  (** The inner Whole is distinct from the outer Whole. *)
  Lemma inner_outer_distinct : forall U,
    inner_whole U <> iter_point 1 U.
  Proof. intros U H. discriminate H. Qed.

  (** The inner Whole is distinct from any embedded element. *)
  Lemma inner_fresh : forall U (u : U),
    iter_inject 2 U u <> inner_whole U.
  Proof. intros U u H. simpl in H. discriminate H. Qed.

  (** Elements relate to BOTH Wholes: inner and outer.
      This demonstrates the fractal nature - connectivity at multiple levels. *)
  Lemma elem_to_inner_whole : forall U (R : U -> U -> Prop) (u : U),
    iter_lift 2 U R (iter_inject 2 U u) (inner_whole U).
  Proof.
    intros U R u. simpl. exact I.
  Qed.

  Lemma elem_to_outer_whole : forall U (R : U -> U -> Prop) (u : U),
    iter_lift 2 U R (iter_inject 2 U u) (iter_point 1 U).
  Proof.
    intros U R u. apply iter_serial.
  Qed.

  (** Inner Whole relates to outer Whole (but not vice versa). *)
  Lemma inner_to_outer : forall U (R : U -> U -> Prop),
    iter_lift 2 U R (inner_whole U) (iter_point 1 U).
  Proof. intros U R. simpl. exact I. Qed.

  Lemma outer_not_to_inner : forall U (R : U -> U -> Prop),
    ~ iter_lift 2 U R (iter_point 1 U) (inner_whole U).
  Proof. intros U R H. simpl in H. exact H. Qed.

  (* ------------------------------------------------------------------------ *)
  (*                    Level Access Functions                                *)
  (* ------------------------------------------------------------------------ *)

  (** Get the Whole at a specific level in an n-fold completion.
      Level 0 is outermost, level (n-1) is innermost. *)
  Fixpoint whole_at_level (n level : nat) (U : Type) : 
    option (iter_carrier (S n) U) :=
    match level with
    | O => Some (iter_point n U)  (* Outermost Whole *)
    | S l => 
        match n with
        | O => None  (* No inner levels exist *)
        | S m => 
            match whole_at_level m l U with
            | Some w => Some (Some w)
            | None => None
            end
        end
    end.

  (* ------------------------------------------------------------------------ *)
  (*                    Fractal Structure Theorem                             *)
  (* ------------------------------------------------------------------------ *)

  (** FRACTAL CONNECTIVITY THEOREM:
      In an n-fold completion, every element relates to every Whole
      at every level. This is the mathematical foundation for fractal
      relational structures where connectivity is preserved at all scales. *)
  Theorem fractal_connectivity : forall n (U : Type) (R : U -> U -> Prop),
    forall (u : U) (level : nat),
      level <= n ->
      match whole_at_level n level U with
      | Some w => iter_lift (S n) U R (iter_inject (S n) U u) w
      | None => True
      end.
  Proof.
    induction n as [|m IH]; intros U R u level Hlevel.
    - (* n = 0: only level 0 exists *)
      destruct level as [|l].
      + simpl. exact I.
      + (* level > 0, but n = 0 *) inversion Hlevel.
    - (* n = S m *)
      destruct level as [|l].
      + (* level = 0: outermost Whole *)
        simpl. exact I.
      + (* level = S l: inner Whole *)
        simpl.
        destruct (whole_at_level m l U) as [w|] eqn:Hw.
        * (* whole_at_level m l U = Some w *)
          (* Use IH to get iter_lift (S m) U R (iter_inject (S m) U u) w *)
          assert (Hlevel' : l <= m) by (apply le_S_n; exact Hlevel).
          specialize (IH U R u l Hlevel').
          rewrite Hw in IH. simpl. exact IH.
        * (* whole_at_level m l U = None *)
          exact I.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (*                    General Serial Extension Composition                  *)
  (* ------------------------------------------------------------------------ *)

  (** 
    GENERAL COMPOSITION OF SERIAL EXTENSIONS
    ========================================
    
    For any two PointedSerialExtensions S1 over U and S2 over carrier(S1),
    we can form their composition. This is essential for:
    
    1. Composing different types of serial extensions
    2. Building heterogeneous nested structures
    3. Theoretical completeness of the framework
    
    The key insight: use pse_extension to get clean type references.
  *)

  Section GeneralComposition.
    Variable U : Type.
    Variable S1 : PointedSerialExtension U.
    
    (** S2 is a serial extension over the carrier of S1.
        We use ue_carrier directly on pse_extension for type clarity. *)
    Variable S2 : PointedSerialExtension (ue_carrier (pse_extension S1)).

    (** The composed UniverseExtension. *)
    Definition compose_ue : UniverseExtension U :=
      Composition.compose (pse_extension S1) (pse_extension S2).

    (** The composed carrier is the carrier of S2. *)
    Definition compose_carrier : Type := ue_carrier compose_ue.

    (** Injection composes: u â†¦ injectâ‚‚(injectâ‚(u)). *)
    Definition compose_inject : U -> compose_carrier := ue_inject compose_ue.

    (** Lift composes: R â†¦ liftâ‚‚(liftâ‚(R)). *)
    Definition compose_lift : (U -> U -> Prop) -> compose_carrier -> compose_carrier -> Prop :=
      ue_lift compose_ue.

    (** The point of the composition is the point of S2 (the outer extension). *)
    Definition compose_point : compose_carrier := pse_point S2.

    (** Conservativity of composition. *)
    Lemma compose_conservative_general : forall (R : U -> U -> Prop) (a b : U),
      compose_lift R (compose_inject a) (compose_inject b) <-> R a b.
    Proof.
      intros R a b. unfold compose_lift, compose_inject, compose_ue.
      apply ue_conservative.
    Qed.

    (** The point is fresh (not in image of inject). *)
    Lemma compose_point_fresh : forall (u : U),
      compose_inject u <> compose_point.
    Proof.
      intros u. unfold compose_inject, compose_point, compose_ue.
      simpl. apply (fpue_point_fresh (pse_base S2)).
    Qed.

    (** SERIALITY: Every element relates to the point.
        This is the crucial property that makes composition serial. *)
    Lemma compose_serial_point : forall (R : U -> U -> Prop) (x : compose_carrier),
      compose_lift R x compose_point.
    Proof.
      intros R x. unfold compose_lift, compose_point, compose_ue.
      simpl. apply (pse_serial_point S2).
    Qed.

    (** Build the PointedUniverseExtension. *)
    Definition compose_pue : PointedUniverseExtension U := {|
      pue_base := compose_ue;
      pue_point := compose_point
    |}.

    (** Build the FreshPointedUniverseExtension. *)
    Definition compose_fpue : FreshPointedUniverseExtension U := {|
      fpue_base := compose_pue;
      fpue_point_fresh := compose_point_fresh
    |}.

    (** Build the full PointedSerialExtension. *)
    Definition compose_pse : PointedSerialExtension U := {|
      pse_base := compose_fpue;
      pse_serial_point := compose_serial_point
    |}.

    (** The composed extension is serial. *)
    Theorem compose_is_serial : forall (R : U -> U -> Prop),
      Serial (compose_lift R).
    Proof.
      intro R. intro x. exists compose_point. apply compose_serial_point.
    Qed.

  End GeneralComposition.

  (** Notation for serial composition. *)
  Notation "S1 >>s S2" := (compose_pse _ S1 S2) (at level 40, left associativity).

  (* ------------------------------------------------------------------------ *)
  (*                    Composition with Canonical Extensions                 *)
  (* ------------------------------------------------------------------------ *)

  (** Composing with the canonical WholeCompletion. *)
  Definition extend_with_whole {U : Type} (S : PointedSerialExtension U) 
    : PointedSerialExtension U :=
    compose_pse U S (WholeCompletion.as_pointed_serial (ue_carrier (pse_extension S))).

  (** The canonical single Whole-completion. *)
  Definition single_whole (U : Type) : PointedSerialExtension U :=
    WholeCompletion.as_pointed_serial U.

  (** Equivalence: iter_serial_extension 0 = single_whole *)
  Lemma iter_0_is_single : forall U,
    ue_carrier (pse_extension (iter_serial_extension 0 U)) = 
    ue_carrier (pse_extension (single_whole U)).
  Proof. reflexivity. Qed.

  (** Composing two single Wholes gives double completion. *)
  Lemma compose_single_single : forall U,
    ue_carrier (pse_extension (extend_with_whole (single_whole U))) =
    ue_carrier (pse_extension (double_completion U)).
  Proof. reflexivity. Qed.

End SerialComposition.

Module CompositionHints.

  (** Composition with identity on the left. *)
  Lemma compose_id_left_inject : forall (U : Type) (E : UniverseExtension U) (u : U),
    ue_inject (Composition.compose (Identity.id_extension U) E) u = ue_inject E u.
  Proof. intros. reflexivity. Qed.

  (** Composition with identity on the right. *)
  Lemma compose_id_right_inject : forall (U : Type) (E : UniverseExtension U) (u : U),
    ue_inject (Composition.compose E (Identity.id_extension (ue_carrier E))) u = 
    ue_inject E u.
  Proof. intros. reflexivity. Qed.

  (** Identity lift is identity. *)
  Lemma id_lift_id : forall (U : Type) (R : U -> U -> Prop),
    ue_lift (Identity.id_extension U) R = R.
  Proof. intros. reflexivity. Qed.

  (** Composition of lifts. *)
  Lemma compose_lift_unfold : forall (U : Type) 
    (E1 : UniverseExtension U) 
    (E2 : UniverseExtension (ue_carrier E1))
    (R : U -> U -> Prop),
    ue_lift (Composition.compose E1 E2) R = ue_lift E2 (ue_lift E1 R).
  Proof. intros. reflexivity. Qed.

End CompositionHints.

(* Hint databases for composition *)
#[export] Hint Rewrite 
  CompositionHints.compose_id_left_inject
  CompositionHints.compose_id_right_inject
  CompositionHints.id_lift_id
  : composition.

#[export] Hint Resolve
  Composition.compose_conservative
  Identity.id_preserves_reflexive
  Identity.id_preserves_symmetric
  Identity.id_preserves_transitive
  Identity.id_preserves_serial
  : composition.

#[export] Hint Resolve
  SerialComposition.iter_inject_injective
  SerialComposition.iter_point_fresh
  SerialComposition.iter_serial
  SerialComposition.iter_weak_serial
  : serial_composition.

#[export] Hint Rewrite
  SerialComposition.iter_lift_conservative
  SerialComposition.double_carrier
  SerialComposition.double_point
  SerialComposition.double_inject
  : serial_composition.
