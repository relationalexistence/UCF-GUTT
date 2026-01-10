(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
*)

(*
  +==========================================================================+
  |                                                                          |
  |                    Top__Extensions__Extras.v                             |
  |                                                                          |
  |                    Optional Utilities & Examples                         |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  PURPOSE: Non-essential utilities that extend the core library.          |
  |  These are imported separately to avoid compilation overhead for         |
  |  developments that don't need them.                                      |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    - RelationClosures (refl, sym, trans, equiv closures)                 |
  |    - Decidability lemmas for WholeCompletion                             |
  |    - Boolean decidability instance                                       |
  |    - WholeCompletion structural analysis                                 |
  |    - Examples (NatLt, EmptyRelation, CompositionExample)                 |
  |    - Utility functions and combinators                                   |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.ArithRing.

Require Import Top__Extensions__Base.
Require Import Top__Extensions__WholeCompletion.
Require Import Top__Extensions__Composition.

(* ========================================================================== *)
(*                                                                            *)
(*                    RELATION CLOSURES                                       *)
(*                                                                            *)
(* ========================================================================== *)

Module RelationClosures.

  Section WithU.
    Variable U : Type.
    
    (* -------------------------------------------------------------------- *)
    (*                    Basic Closure Operations                          *)
    (* -------------------------------------------------------------------- *)
    
    (** Reflexive closure: add self-loops. *)
    Definition refl_closure (R : U -> U -> Prop) (x y : U) : Prop :=
      x = y \/ R x y.
    
    (** Symmetric closure: add reverse edges. *)
    Definition sym_closure (R : U -> U -> Prop) (x y : U) : Prop :=
      R x y \/ R y x.
    
    (** Transitive closure: via stdlib clos_trans. *)
    Definition trans_closure (R : U -> U -> Prop) : U -> U -> Prop :=
      clos_trans U R.
    
    (** Reflexive-transitive closure: via stdlib clos_refl_trans. *)
    Definition refl_trans_closure (R : U -> U -> Prop) : U -> U -> Prop :=
      clos_refl_trans U R.
    
    (** Reflexive-symmetric closure. *)
    Definition refl_sym_closure (R : U -> U -> Prop) (x y : U) : Prop :=
      x = y \/ R x y \/ R y x.
    
    (** Symmetric-transitive closure. *)
    Definition sym_trans_closure (R : U -> U -> Prop) : U -> U -> Prop :=
      clos_trans U (sym_closure R).
    
    (** Equivalence closure (reflexive-symmetric-transitive). *)
    Definition equiv_closure (R : U -> U -> Prop) : U -> U -> Prop :=
      clos_refl_trans U (sym_closure R).
    
    (* -------------------------------------------------------------------- *)
    (*                    Closure Property Lemmas                           *)
    (* -------------------------------------------------------------------- *)
    
    (** Reflexive closure is reflexive. *)
    Lemma refl_closure_refl : forall R, reflexive U (refl_closure R).
    Proof. intros R x. left. reflexivity. Qed.
    
    (** Reflexive closure contains R. *)
    Lemma refl_closure_incl : forall R x y, R x y -> refl_closure R x y.
    Proof. intros R x y H. right. exact H. Qed.
    
    (** Reflexive closure is minimal. *)
    Lemma refl_closure_minimal : forall R S,
      reflexive U S -> (forall x y, R x y -> S x y) ->
      forall x y, refl_closure R x y -> S x y.
    Proof.
      intros R S Hrefl Hincl x y [Heq | HR].
      - rewrite Heq. apply Hrefl.
      - apply Hincl. exact HR.
    Qed.
    
    (** Symmetric closure is symmetric. *)
    Lemma sym_closure_sym : forall R, symmetric U (sym_closure R).
    Proof. intros R x y [H|H]; [right|left]; exact H. Qed.
    
    (** Symmetric closure contains R. *)
    Lemma sym_closure_incl : forall R x y, R x y -> sym_closure R x y.
    Proof. intros R x y H. left. exact H. Qed.
    
    (** Symmetric closure is minimal. *)
    Lemma sym_closure_minimal : forall R S,
      symmetric U S -> (forall x y, R x y -> S x y) ->
      forall x y, sym_closure R x y -> S x y.
    Proof.
      intros R S Hsym Hincl x y [HR | HR].
      - apply Hincl. exact HR.
      - apply Hsym. apply Hincl. exact HR.
    Qed.
    
    (** Transitive closure is transitive. *)
    Lemma trans_closure_trans : forall R, transitive U (trans_closure R).
    Proof. intros R x y z Hxy Hyz. eapply t_trans; eauto. Qed.
    
    (** Transitive closure contains R. *)
    Lemma trans_closure_incl : forall R x y, R x y -> trans_closure R x y.
    Proof. intros R x y H. apply t_step. exact H. Qed.
    
    (** Transitive closure is minimal. *)
    Lemma trans_closure_minimal : forall R S,
      transitive U S -> (forall x y, R x y -> S x y) ->
      forall x y, trans_closure R x y -> S x y.
    Proof.
      intros R S Htrans Hincl x y H.
      induction H as [x y HR | x y z Hxy IHxy Hyz IHyz].
      - apply Hincl. exact HR.
      - apply (Htrans x y z IHxy IHyz).
    Qed.
    
    (** Reflexive-transitive closure is reflexive. *)
    Lemma refl_trans_refl : forall R, reflexive U (refl_trans_closure R).
    Proof. intros R x. apply rt_refl. Qed.
    
    (** Reflexive-transitive closure is transitive. *)
    Lemma refl_trans_trans : forall R, transitive U (refl_trans_closure R).
    Proof. intros R x y z. apply rt_trans. Qed.
    
    (** Reflexive-transitive closure contains R. *)
    Lemma refl_trans_incl : forall R x y, R x y -> refl_trans_closure R x y.
    Proof. intros R x y H. apply rt_step. exact H. Qed.
    
    (** Reflexive-transitive closure is minimal preorder containing R. *)
    Lemma refl_trans_minimal : forall R S,
      reflexive U S -> transitive U S -> (forall x y, R x y -> S x y) ->
      forall x y, refl_trans_closure R x y -> S x y.
    Proof.
      intros R S Hrefl Htrans Hincl x y H.
      induction H as [x y HR | x | x y z Hxy IHxy Hyz IHyz].
      - apply Hincl. exact HR.
      - apply Hrefl.
      - apply (Htrans x y z IHxy IHyz).
    Qed.
    
    (** Equivalence closure is an equivalence relation. *)
    Lemma equiv_closure_refl : forall R, reflexive U (equiv_closure R).
    Proof. intros R x. apply rt_refl. Qed.
    
    Lemma equiv_closure_sym : forall R, symmetric U (equiv_closure R).
    Proof.
      intros R x y H.
      induction H as [x y [HR|HR] | x | x y z Hxy IHxy Hyz IHyz].
      - apply rt_step. right. exact HR.
      - apply rt_step. left. exact HR.
      - apply rt_refl.
      - apply (rt_trans U (sym_closure R) z y x IHyz IHxy).
    Qed.
    
    Lemma equiv_closure_trans : forall R, transitive U (equiv_closure R).
    Proof. intros R x y z. apply rt_trans. Qed.
    
    Lemma equiv_closure_equiv : forall R, 
      Equivalence R -> (forall x y, equiv_closure R x y <-> R x y).
    Proof.
      intros R [Hrefl [Hsym Htrans]] x y. split.
      - intro H. apply refl_trans_minimal with (S := R) in H; auto.
        intros a b [Hab | Hba].
        + exact Hab.
        + apply Hsym. exact Hba.
      - intro H. apply rt_step. left. exact H.
    Qed.
    
    (* -------------------------------------------------------------------- *)
    (*                    Closure Monotonicity                              *)
    (* -------------------------------------------------------------------- *)
    
    Lemma refl_closure_mono : forall R S,
      (forall x y, R x y -> S x y) ->
      forall x y, refl_closure R x y -> refl_closure S x y.
    Proof.
      intros R S Hincl x y [Heq | HR].
      - left. exact Heq.
      - right. apply Hincl. exact HR.
    Qed.
    
    Lemma sym_closure_mono : forall R S,
      (forall x y, R x y -> S x y) ->
      forall x y, sym_closure R x y -> sym_closure S x y.
    Proof.
      intros R S Hincl x y [HR | HR].
      - left. apply Hincl. exact HR.
      - right. apply Hincl. exact HR.
    Qed.
    
    Lemma trans_closure_mono : forall R S,
      (forall x y, R x y -> S x y) ->
      forall x y, trans_closure R x y -> trans_closure S x y.
    Proof.
      intros R S Hincl x y H.
      induction H as [x y HR | x y z Hxy IHxy Hyz IHyz].
      - apply t_step. apply Hincl. exact HR.
      - apply (t_trans U S x y z IHxy IHyz).
    Qed.
    
  End WithU.

End RelationClosures.

(* ========================================================================== *)
(*                                                                            *)
(*                    DECIDABILITY                                            *)
(*                                                                            *)
(* ========================================================================== *)

Module Decidability.

  (** Decidability for WholeCompletion's lift_rel. *)
  Lemma whole_completion_decidable : forall (U : Type) (R : U -> U -> Prop),
    (forall a b : U, {R a b} + {~ R a b}) ->
    forall x y : WholeCompletion.carrier U, 
      {WholeCompletion.lift_rel R x y} + {~ WholeCompletion.lift_rel R x y}.
  Proof.
    intros U R Rdec x y.
    unfold WholeCompletion.lift_rel.
    destruct x as [a|], y as [b|].
    - apply Rdec.
    - left. exact I.
    - right. intro H. exact H.
    - left. exact I.
  Defined.

  (** Decidability of carrier equality given decidable U. *)
  Lemma carrier_eq_decidable : forall (U : Type),
    (forall a b : U, {a = b} + {a <> b}) ->
    forall x y : WholeCompletion.carrier U, {x = y} + {x <> y}.
  Proof.
    intros U Udec. apply WholeCompletion.carrier_eq_dec. exact Udec.
  Defined.

  (** Decidability for reflexive closure. *)
  Lemma refl_closure_decidable : forall (U : Type) (R : U -> U -> Prop),
    (forall a b : U, {a = b} + {a <> b}) ->
    (forall a b : U, {R a b} + {~ R a b}) ->
    forall a b : U, {RelationClosures.refl_closure U R a b} + 
                    {~ RelationClosures.refl_closure U R a b}.
  Proof.
    intros U R Ueq Rdec a b.
    unfold RelationClosures.refl_closure.
    destruct (Ueq a b) as [Heq | Hneq].
    - left. left. exact Heq.
    - destruct (Rdec a b) as [HR | HnR].
      + left. right. exact HR.
      + right. intros [Heq | HR].
        * apply Hneq. exact Heq.
        * apply HnR. exact HR.
  Defined.

  (** Decidability for symmetric closure. *)
  Lemma sym_closure_decidable : forall (U : Type) (R : U -> U -> Prop),
    (forall a b : U, {R a b} + {~ R a b}) ->
    forall a b : U, {RelationClosures.sym_closure U R a b} + 
                    {~ RelationClosures.sym_closure U R a b}.
  Proof.
    intros U R Rdec a b.
    unfold RelationClosures.sym_closure.
    destruct (Rdec a b) as [Hab | Hnab].
    - left. left. exact Hab.
    - destruct (Rdec b a) as [Hba | Hnba].
      + left. right. exact Hba.
      + right. intros [H | H]; [apply Hnab | apply Hnba]; exact H.
  Defined.

End Decidability.

(* ========================================================================== *)
(*                                                                            *)
(*                    STRUCTURAL ANALYSIS                                     *)
(*                                                                            *)
(* ========================================================================== *)

Module StructuralAnalysis.

  Section WithU.
    Variable U : Type.

    (** Classification of carrier elements. *)
    Inductive CarrierClass : WholeCompletion.carrier U -> Type :=
    | IsElem : forall u : U, CarrierClass (WholeCompletion.inject u)
    | IsWhole : CarrierClass WholeCompletion.point.

    (** Every carrier element has a classification. *)
    Definition classify (x : WholeCompletion.carrier U) : CarrierClass x :=
      match x with
      | Some u => IsElem u
      | None => IsWhole
      end.

    (** Extract element if not point. *)
    Definition get_elem (x : WholeCompletion.carrier U) : option U :=
      match x with
      | Some u => Some u
      | None => None
      end.

    (** Check if element is point. *)
    Definition is_point (x : WholeCompletion.carrier U) : bool :=
      match x with
      | Some _ => false
      | None => true
      end.

    (** Check if element is from U. *)
    Definition is_elem (x : WholeCompletion.carrier U) : bool :=
      match x with
      | Some _ => true
      | None => false
      end.

    Lemma is_point_spec : forall x,
      is_point x = true <-> x = WholeCompletion.point.
    Proof.
      intro x. destruct x; simpl; split; intro H; try reflexivity; try discriminate.
    Qed.

    Lemma is_elem_spec : forall x,
      is_elem x = true <-> exists u, x = WholeCompletion.inject u.
    Proof.
      intro x. destruct x as [u|]; simpl; split; intro H.
      - exists u. reflexivity.
      - reflexivity.
      - discriminate.
      - destruct H as [u Hu]. discriminate.
    Qed.

    Lemma is_point_is_elem_exclusive : forall x,
      is_point x = negb (is_elem x).
    Proof.
      intro x. destruct x; reflexivity.
    Qed.

    (** Count elements (for finite U). *)
    (** The carrier has exactly |U| + 1 elements. *)

  End WithU.

End StructuralAnalysis.

(* ========================================================================== *)
(*                                                                            *)
(*                    UTILITY FUNCTIONS                                       *)
(*                                                                            *)
(* ========================================================================== *)

Module Utilities.

  (** Map a function over the carrier (treating point specially). *)
  Definition carrier_map {U V : Type} 
    (f : U -> V) 
    (x : WholeCompletion.carrier U) : WholeCompletion.carrier V :=
    match x with
    | Some u => Some (f u)
    | None => None
    end.

  Lemma carrier_map_inject : forall {U V : Type} (f : U -> V) (u : U),
    carrier_map f (WholeCompletion.inject u) = WholeCompletion.inject (f u).
  Proof. intros. reflexivity. Qed.

  Lemma carrier_map_point : forall {U V : Type} (f : U -> V),
    carrier_map f WholeCompletion.point = WholeCompletion.point.
  Proof. intros. reflexivity. Qed.

  Lemma carrier_map_id : forall {U : Type} (x : WholeCompletion.carrier U),
    carrier_map (fun u => u) x = x.
  Proof. intros U x. unfold WholeCompletion.carrier in x. destruct x; reflexivity. Qed.

  Lemma carrier_map_compose : forall {U V W : Type} (f : U -> V) (g : V -> W) x,
    carrier_map g (carrier_map f x) = carrier_map (fun u => g (f u)) x.
  Proof. intros U V W f g x. destruct x; reflexivity. Qed.

  (** Bind operation for carrier (monadic). *)
  Definition carrier_bind {U V : Type}
    (x : WholeCompletion.carrier U)
    (f : U -> WholeCompletion.carrier V) : WholeCompletion.carrier V :=
    match x with
    | Some u => f u
    | None => None
    end.

  Lemma carrier_bind_inject : forall {U V : Type} (f : U -> WholeCompletion.carrier V) (u : U),
    carrier_bind (WholeCompletion.inject u) f = f u.
  Proof. intros. reflexivity. Qed.

  Lemma carrier_bind_point : forall {U V : Type} (f : U -> WholeCompletion.carrier V),
    carrier_bind WholeCompletion.point f = WholeCompletion.point.
  Proof. intros. reflexivity. Qed.

  (** Monad laws. *)
  Lemma carrier_bind_left_id : forall {U V : Type} (u : U) (f : U -> WholeCompletion.carrier V),
    carrier_bind (WholeCompletion.inject u) f = f u.
  Proof. intros. reflexivity. Qed.

  Lemma carrier_bind_right_id : forall {U : Type} (x : WholeCompletion.carrier U),
    carrier_bind x WholeCompletion.inject = x.
  Proof. intros U x. destruct x; reflexivity. Qed.

  Lemma carrier_bind_assoc : forall {U V W : Type} 
    (x : WholeCompletion.carrier U)
    (f : U -> WholeCompletion.carrier V)
    (g : V -> WholeCompletion.carrier W),
    carrier_bind (carrier_bind x f) g = carrier_bind x (fun u => carrier_bind (f u) g).
  Proof. intros U V W x f g. destruct x; reflexivity. Qed.

End Utilities.

(* ========================================================================== *)
(*                                                                            *)
(*                    EXAMPLES                                                *)
(*                                                                            *)
(* ========================================================================== *)

Module Examples.

  (* -------------------------------------------------------------------- *)
  (*                    Natural Number Examples                           *)
  (* -------------------------------------------------------------------- *)
  
  Module NatLt.
    Definition PSE := WholeCompletion.as_pointed_serial nat.
    
    Example lift_3_lt_5 : 
      WholeCompletion.lift_rel lt 
        (WholeCompletion.inject 3) 
        (WholeCompletion.inject 5).
    Proof. apply WholeCompletion.lift_preserves. auto. Qed.
    
    Example five_has_successor :
      exists y, WholeCompletion.lift_rel lt (WholeCompletion.inject 5) y.
    Proof.
      exists WholeCompletion.point.
      apply WholeCompletion.serial.
    Qed.
    
    Example weak_serial_nat : @Serial (WholeCompletion.carrier nat) (WholeCompletion.lift_rel lt).
    Proof. apply WholeCompletion.weak_serial. Qed.

    (** Every number relates to point. *)
    Example every_nat_to_point : forall n : nat,
      WholeCompletion.lift_rel lt (WholeCompletion.inject n) WholeCompletion.point.
    Proof. intro n. apply WholeCompletion.serial. Qed.

    (** Point is a dead-end for the < relation (can't reach any nat from point). *)
    Example point_is_dead_end : forall n : nat,
      ~ WholeCompletion.lift_rel lt WholeCompletion.point (WholeCompletion.inject n).
    Proof. intro n. apply WholeCompletion.point_terminal. Qed.

  End NatLt.
  
  (* -------------------------------------------------------------------- *)
  (*                    Empty Relation Example                            *)
  (* -------------------------------------------------------------------- *)
  
  Module EmptyRelation.
    Definition R : nat -> nat -> Prop := fun _ _ => False.
    
    Example seriality_from_nothing :
      forall x, exists y, WholeCompletion.lift_rel R x y.
    Proof.
      intro x. exists WholeCompletion.point. apply WholeCompletion.serial.
    Qed.

    (** No edges between elements, but all elements reach point. *)
    Example no_elem_edges : forall a b : nat,
      ~ WholeCompletion.lift_rel R (WholeCompletion.inject a) (WholeCompletion.inject b).
    Proof.
      intros a b H. unfold R in H. simpl in H. exact H.
    Qed.

  End EmptyRelation.
  
  (* -------------------------------------------------------------------- *)
  (*                    Full Relation Example                             *)
  (* -------------------------------------------------------------------- *)
  
  Module FullRelation.
    Definition R : nat -> nat -> Prop := fun _ _ => True.

    Example full_is_lifted : forall a b : nat,
      WholeCompletion.lift_rel R (WholeCompletion.inject a) (WholeCompletion.inject b).
    Proof.
      intros a b. unfold R. simpl. exact I.
    Qed.

    (** Full relation is reflexive and symmetric under lifting. *)
    Example full_lifted_reflexive : forall a : nat,
      WholeCompletion.lift_rel R (WholeCompletion.inject a) (WholeCompletion.inject a).
    Proof. intro a. simpl. exact I. Qed.

  End FullRelation.
  
  (* -------------------------------------------------------------------- *)
  (*                    Composition Example                               *)
  (* -------------------------------------------------------------------- *)
  
  Module CompositionExample.
    Import Composition.
    
    (** Double completion: U -> option U -> option (option U). *)
    Definition double_complete (U : Type) : UniverseExtension U :=
      WholeCompletion.as_extension U >> WholeCompletion.as_extension (option U).
    
    (** The carrier is option (option U). *)
    Example carrier_type : forall U,
      ue_carrier (double_complete U) = option (option U).
    Proof. reflexivity. Qed.

    (** The injection embeds U into the innermost layer. *)
    Example inject_type : forall (U : Type) (u : U),
      ue_inject (double_complete U) u = Some (Some u).
    Proof. reflexivity. Qed.

    (** There are three levels now:
        - Some (Some u) : original elements
        - Some None     : inner point (first completion's point)
        - None          : outer point (second completion's point) *)
    
    Example inner_point : forall U,
      @ue_inject (option U) (WholeCompletion.as_extension (option U)) None = Some None.
    Proof. reflexivity. Qed.

    Example outer_point : forall U,
      WholeCompletion.point = @None (option U).
    Proof. reflexivity. Qed.

  End CompositionExample.
  
  (* -------------------------------------------------------------------- *)
  (*                    Identity Extension Example                        *)
  (* -------------------------------------------------------------------- *)
  
  Module IdentityExample.
    
    (** Identity extension doesn't change anything. *)
    Example id_carrier : forall U, ue_carrier (Identity.id_extension U) = U.
    Proof. reflexivity. Qed.

    Example id_inject : forall (U : Type) (u : U), 
      ue_inject (Identity.id_extension U) u = u.
    Proof. reflexivity. Qed.

    Example id_lift : forall (U : Type) (R : U -> U -> Prop),
      ue_lift (Identity.id_extension U) R = R.
    Proof. reflexivity. Qed.

    (** Serial relations stay serial under identity. *)
    Example id_preserves_serial : forall (U : Type) (R : U -> U -> Prop),
      Serial R -> Serial (ue_lift (Identity.id_extension U) R).
    Proof. intros U R H. exact H. Qed.

  End IdentityExample.
  
  (* -------------------------------------------------------------------- *)
  (*                    Symmetric Relation Example                        *)
  (* -------------------------------------------------------------------- *)
  
  Module SymmetricRelation.
    (** Symmetric relation: equality on nat. *)
    Definition eq_rel : nat -> nat -> Prop := fun x y => x = y.

    Example eq_is_symmetric : Symmetric eq_rel.
    Proof. intros x y H. symmetry. exact H. Qed.

    (** Lifting preserves symmetry between elements. *)
    Example lift_symmetric_example : forall a b : nat,
      WholeCompletion.lift_rel eq_rel (WholeCompletion.inject a) (WholeCompletion.inject b) ->
      WholeCompletion.lift_rel eq_rel (WholeCompletion.inject b) (WholeCompletion.inject a).
    Proof.
      intros a b H. apply WholeCompletion.lift_symmetric_on_elems.
      - exact eq_is_symmetric.
      - exact H.
    Qed.

    (** Note: Full symmetry doesn't hold because Whole -> elem is False. *)
    Example symmetry_breaks_at_point : forall n : nat,
      WholeCompletion.lift_rel eq_rel (WholeCompletion.inject n) WholeCompletion.point /\
      ~ WholeCompletion.lift_rel eq_rel WholeCompletion.point (WholeCompletion.inject n).
    Proof.
      intro n. split.
      - apply WholeCompletion.serial.
      - apply WholeCompletion.point_terminal.
    Qed.

    (** Symmetric closure example. *)
    Definition lt_sym := RelationClosures.sym_closure nat lt.

    Example sym_closure_contains_both : 
      lt_sym 3 5 /\ lt_sym 5 3.
    Proof.
      split.
      - left. auto.
      - right. auto.
    Qed.

  End SymmetricRelation.
  
  (* -------------------------------------------------------------------- *)
  (*                    Equivalence Relation Example                      *)
  (* -------------------------------------------------------------------- *)
  
  Module EquivalenceRelation.
    (** Equivalence relation: mod 2 congruence. *)
    Definition mod2_eq (x y : nat) : Prop := 
      Nat.even x = Nat.even y.

    Example mod2_refl : Reflexive mod2_eq.
    Proof. intro x. unfold mod2_eq. reflexivity. Qed.

    Example mod2_sym : Symmetric mod2_eq.
    Proof. intros x y H. unfold mod2_eq in *. symmetry. exact H. Qed.

    Example mod2_trans : Transitive mod2_eq.
    Proof.
      intros x y z Hxy Hyz. unfold mod2_eq in *.
      rewrite Hxy. exact Hyz.
    Qed.

    Example mod2_equiv : Equivalence mod2_eq.
    Proof. split; [exact mod2_refl | split; [exact mod2_sym | exact mod2_trans]]. Qed.

    (** Lifting preserves equivalence properties between elements. *)
    Example lift_mod2_refl_on_elems : forall n : nat,
      WholeCompletion.lift_rel mod2_eq 
        (WholeCompletion.inject n) (WholeCompletion.inject n).
    Proof.
      intro n. apply WholeCompletion.lift_preserves. apply mod2_refl.
    Qed.

    (** Equivalence classes: 0 â‰¡ 2, 1 â‰¡ 3. *)
    Example zero_equiv_two : 
      WholeCompletion.lift_rel mod2_eq 
        (WholeCompletion.inject 0) (WholeCompletion.inject 2).
    Proof.
      apply WholeCompletion.lift_preserves. unfold mod2_eq. reflexivity.
    Qed.

    Example one_equiv_three :
      WholeCompletion.lift_rel mod2_eq 
        (WholeCompletion.inject 1) (WholeCompletion.inject 3).
    Proof.
      apply WholeCompletion.lift_preserves. unfold mod2_eq. reflexivity.
    Qed.

    Example zero_not_equiv_one :
      ~ WholeCompletion.lift_rel mod2_eq 
          (WholeCompletion.inject 0) (WholeCompletion.inject 1).
    Proof.
      intro H. apply WholeCompletion.lift_conservative in H.
      unfold mod2_eq in H. simpl in H. discriminate H.
    Qed.

    (** Equivalence closure example: making < into an equivalence. *)
    Definition lt_equiv := RelationClosures.equiv_closure nat lt.

    (** In the equivalence closure of <, all nats are related 
        (since 0 < 1, 1 < 2, etc. form a connected chain). *)
    Example zero_one_in_closure : lt_equiv 0 1.
    Proof.
      apply rt_step. left. auto.
    Qed.

    Example one_zero_in_closure : lt_equiv 1 0.
    Proof.
      apply rt_step. right. auto.
    Qed.

  End EquivalenceRelation.
  
  (* -------------------------------------------------------------------- *)
  (*                    Transitive Relation Example                       *)
  (* -------------------------------------------------------------------- *)
  
  Module TransitiveRelation.
    (** Transitive relation: divisibility. *)
    Definition divides (x y : nat) : Prop := exists k, y = k * x.

    Example divides_refl : forall n, divides n n.
    Proof. intro n. exists 1. ring. Qed.

    Example divides_trans : Transitive divides.
    Proof.
      intros x y z [k1 Hk1] [k2 Hk2].
      exists (k2 * k1). rewrite Hk2, Hk1. ring.
    Qed.

    Example two_divides_four :
      WholeCompletion.lift_rel divides 
        (WholeCompletion.inject 2) (WholeCompletion.inject 4).
    Proof.
      apply WholeCompletion.lift_preserves. exists 2. reflexivity.
    Qed.

    Example four_divides_twelve :
      WholeCompletion.lift_rel divides 
        (WholeCompletion.inject 4) (WholeCompletion.inject 12).
    Proof.
      apply WholeCompletion.lift_preserves. exists 3. reflexivity.
    Qed.

    (** Transitivity works through lift. *)
    Example two_divides_twelve_via_four :
      WholeCompletion.lift_rel divides 
        (WholeCompletion.inject 2) (WholeCompletion.inject 12).
    Proof.
      apply WholeCompletion.lift_transitive_on_elems with (b := 4).
      - exact divides_trans.
      - exact two_divides_four.
      - exact four_divides_twelve.
    Qed.

  End TransitiveRelation.

End Examples.
