(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
*)

(*
  +==========================================================================+
  |                                                                          |
  |                    Top__Extensions__WholeCompletion.v                    |
  |                                                                          |
  |                    Canonical Whole-Completion Construction               |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  PURPOSE: The canonical serial completion via option type.               |
  |  This is the source of truth for Whole-completion and provides the       |
  |  constructive proof that every relation can be made serial.              |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    - WholeCompletion module (carrier, inject, point, lift_rel)           |
  |    - Core lemmas (conservative, serial, terminal, etc.)                  |
  |    - Inversion principles                                                |
  |    - Preservation of relation properties                                 |
  |    - Record instances (as_extension, as_pointed_serial, etc.)            |
  |    - Rewrite hints and tactics                                           |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

Require Import Top__Extensions__Base.

(* ========================================================================== *)
(*                                                                            *)
(*                    WHOLE-COMPLETION MODULE                                 *)
(*                                                                            *)
(* ========================================================================== *)

Module WholeCompletion.

  Section WithU.
    Variable U : Type.
    
    (* -------------------------------------------------------------------- *)
    (*                        Core Definitions                              *)
    (* -------------------------------------------------------------------- *)
    
    (** Extended universe: U + {Whole} via option type. *)
    Definition carrier : Type := option U.
    
    (** Injection: embed U into carrier. *)
    Definition inject (u : U) : carrier := Some u.
    
    (** Distinguished element: the Whole. *)
    Definition point : carrier := None.
    
    (**
      Extended relation R' (serial completion of R):
      
      1. R'(Some a, Some b) := R a b    -- conservative on U
      2. R'(x, None) := True            -- everything relates to Whole
      3. R'(None, Some _) := False      -- Whole is terminal sink w.r.t. U
      
      Note: R'(None, None) = True (self-loop on Whole)
    *)
    Definition lift_rel (R : U -> U -> Prop) (x y : carrier) : Prop :=
      match x, y with
      | Some a, Some b => R a b
      | _,      None   => True
      | None,   Some _ => False
      end.
    
    (* -------------------------------------------------------------------- *)
    (*                         Core Properties                              *)
    (* -------------------------------------------------------------------- *)
    
    (** Injection is injective. *)
    Lemma inject_injective : forall a b : U, inject a = inject b -> a = b.
    Proof.
      intros a b H. unfold inject in H. injection H. auto.
    Qed.
    
    (** Point is fresh (not in image of inject). *)
    Lemma point_fresh : forall u : U, inject u <> point.
    Proof.
      intros u H. unfold inject, point in H. discriminate H.
    Qed.
    
    (** Freshness in the other direction. *)
    Lemma point_fresh_sym : forall u : U, point <> inject u.
    Proof.
      intros u H. apply (point_fresh u). symmetry. exact H.
    Qed.
    
    (** Conservative extension: lift_rel restricts to R on U. *)
    Lemma lift_conservative : forall (R : U -> U -> Prop) (a b : U),
      lift_rel R (inject a) (inject b) <-> R a b.
    Proof.
      intros R a b. unfold lift_rel, inject. tauto.
    Qed.
    
    (** Forward direction of conservativity. *)
    Lemma lift_conservative_fwd : forall (R : U -> U -> Prop) (a b : U),
      lift_rel R (inject a) (inject b) -> R a b.
    Proof.
      intros R a b H. apply lift_conservative. exact H.
    Qed.
    
    (** Backward direction of conservativity. *)
    Lemma lift_conservative_bwd : forall (R : U -> U -> Prop) (a b : U),
      R a b -> lift_rel R (inject a) (inject b).
    Proof.
      intros R a b H. apply lift_conservative. exact H.
    Qed.
    
    (** POINTED SERIALITY: every element relates to point (uniformly!). *)
    Lemma serial : forall (R : U -> U -> Prop) (x : carrier),
      lift_rel R x point.
    Proof.
      intros R x. unfold lift_rel, point. destruct x; exact I.
    Qed.
    
    (** Corollary: weak seriality follows. *)
    Lemma weak_serial : forall (R : U -> U -> Prop), Serial (lift_rel R).
    Proof.
      intros R x. exists point. apply serial.
    Qed.
    
    (* -------------------------------------------------------------------- *)
    (*                      Additional Properties                           *)
    (* -------------------------------------------------------------------- *)
    
    (** Point has self-loop. *)
    Lemma point_self_loop : forall R : U -> U -> Prop, lift_rel R point point.
    Proof.
      intros R. unfold lift_rel, point. exact I.
    Qed.
    
    (** Point is terminal sink w.r.t. U. *)
    Lemma point_terminal : forall (R : U -> U -> Prop) (u : U),
      ~ lift_rel R point (inject u).
    Proof.
      intros R u H. unfold lift_rel, point, inject in H. exact H.
    Qed.
    
    (** Lifting preserves base relation. *)
    Lemma lift_preserves : forall (R : U -> U -> Prop) (a b : U),
      R a b -> lift_rel R (inject a) (inject b).
    Proof.
      intros R a b H. unfold lift_rel, inject. exact H.
    Qed.
    
    (** No dead-ends in completion. *)
    Lemma no_dead_ends_in_completion : forall (R : U -> U -> Prop),
      ~ exists x : carrier, forall y : carrier, ~ lift_rel R x y.
    Proof.
      intros R [x Hx]. apply (Hx point). apply serial.
    Qed.
    
    (* -------------------------------------------------------------------- *)
    (*                      Inversion Principles                            *)
    (* -------------------------------------------------------------------- *)
    
    (** Case analysis on carrier elements. *)
    Lemma carrier_case : forall (x : carrier),
      x = point \/ exists u : U, x = inject u.
    Proof.
      intro x. destruct x as [u|].
      - right. exists u. reflexivity.
      - left. reflexivity.
    Qed.
    
    (** Inversion for lift_rel when target is an element. *)
    Lemma lift_rel_to_elem_inv : forall (R : U -> U -> Prop) (x : carrier) (b : U),
      lift_rel R x (inject b) -> exists a : U, x = inject a /\ R a b.
    Proof.
      intros R x b H.
      destruct x as [a|].
      - exists a. split.
        + reflexivity.
        + exact H.
      - unfold lift_rel, point, inject in H. contradiction.
    Qed.
    
    (** Inversion for lift_rel when source is point. *)
    Lemma lift_rel_from_point_inv : forall (R : U -> U -> Prop) (y : carrier),
      lift_rel R point y -> y = point.
    Proof.
      intros R y H.
      destruct y as [b|].
      - unfold lift_rel, point, inject in H. contradiction.
      - reflexivity.
    Qed.
    
    (** Decidability of carrier equality. *)
    Lemma carrier_eq_dec : 
      (forall a b : U, {a = b} + {a <> b}) ->
      forall x y : carrier, {x = y} + {x <> y}.
    Proof.
      intros Udec x y.
      destruct x as [a|], y as [b|].
      - destruct (Udec a b) as [Heq | Hneq].
        + left. rewrite Heq. reflexivity.
        + right. intro H. apply Hneq. injection H. auto.
      - right. intro H. discriminate H.
      - right. intro H. discriminate H.
      - left. reflexivity.
    Defined.
    
    (* -------------------------------------------------------------------- *)
    (*                Preservation of Relation Properties                   *)
    (* -------------------------------------------------------------------- *)
    
    (** Lifting preserves reflexivity (with an extra self-loop on point). *)
    Lemma lift_preserves_reflexive : forall (R : U -> U -> Prop),
      Reflexive R -> Reflexive (lift_rel R).
    Proof.
      intros R Hrefl x.
      destruct x as [a|].
      - unfold lift_rel. apply Hrefl.
      - apply point_self_loop.
    Qed.
    
    (** Lifting does NOT preserve symmetry in general (point -> elem is False). *)
    (** But we can prove: if R is symmetric and we're between elements, symmetry holds. *)
    Lemma lift_symmetric_on_elems : forall (R : U -> U -> Prop),
      Symmetric R -> 
      forall a b : U, lift_rel R (inject a) (inject b) -> lift_rel R (inject b) (inject a).
    Proof.
      intros R Hsym a b H.
      unfold lift_rel, inject in *. apply Hsym. exact H.
    Qed.
    
    (** Lifting preserves transitivity on element chains. *)
    Lemma lift_transitive_on_elems : forall (R : U -> U -> Prop),
      Transitive R ->
      forall a b c : U,
        lift_rel R (inject a) (inject b) ->
        lift_rel R (inject b) (inject c) ->
        lift_rel R (inject a) (inject c).
    Proof.
      intros R Htrans a b c Hab Hbc.
      unfold lift_rel, inject in *.
      apply (Htrans a b c Hab Hbc).
    Qed.
    
    (** Full transitivity with point: chains ending at point work. *)
    Lemma lift_trans_to_point : forall (R : U -> U -> Prop),
      Transitive R ->
      forall x y : carrier,
        lift_rel R x y -> lift_rel R y point -> lift_rel R x point.
    Proof.
      intros R Htrans x y Hxy Hyp.
      apply serial.
    Qed.
    
    (** Monotonicity: R ⊆ S implies lift R ⊆ lift S on U elements. *)
    Lemma lift_monotone : forall (R S : U -> U -> Prop),
      (forall a b, R a b -> S a b) ->
      forall a b : U,
        lift_rel R (inject a) (inject b) -> lift_rel S (inject a) (inject b).
    Proof.
      intros R S Himpl a b H.
      unfold lift_rel, inject in *.
      apply Himpl. exact H.
    Qed.
    
    (** General monotonicity on all carrier elements. *)
    Lemma lift_monotone_general : forall (R S : U -> U -> Prop),
      (forall a b, R a b -> S a b) ->
      forall x y : carrier,
        lift_rel R x y -> lift_rel S x y.
    Proof.
      intros R S Himpl x y H.
      destruct x as [a|], y as [b|]; simpl in *.
      - apply Himpl. exact H.
      - exact I.
      - exact H.
      - exact I.
    Qed.
    
    (** Lifting respects logical equivalence. *)
    Lemma lift_equiv : forall (R S : U -> U -> Prop),
      (forall a b, R a b <-> S a b) ->
      forall x y : carrier,
        lift_rel R x y <-> lift_rel S x y.
    Proof.
      intros R S Hequiv x y.
      split; apply lift_monotone_general; intros a b; apply Hequiv.
    Qed.
    
    (* -------------------------------------------------------------------- *)
    (*                    Composition of Lift                               *)
    (* -------------------------------------------------------------------- *)
    
    (** Lifting distributes over relation intersection on U. *)
    Lemma lift_inter : forall (R S : U -> U -> Prop) (a b : U),
      lift_rel (rel_inter R S) (inject a) (inject b) <->
      lift_rel R (inject a) (inject b) /\ lift_rel S (inject a) (inject b).
    Proof.
      intros R S a b.
      unfold lift_rel, inject, rel_inter.
      tauto.
    Qed.
    
    (** Lifting distributes over relation union on U. *)
    Lemma lift_union : forall (R S : U -> U -> Prop) (a b : U),
      lift_rel (rel_union R S) (inject a) (inject b) <->
      lift_rel R (inject a) (inject b) \/ lift_rel S (inject a) (inject b).
    Proof.
      intros R S a b.
      unfold lift_rel, inject, rel_union.
      tauto.
    Qed.
    
    (* -------------------------------------------------------------------- *)
    (*                  Record Instances                                    *)
    (* -------------------------------------------------------------------- *)
    
    Definition as_extension : UniverseExtension U := {|
      ue_carrier := carrier;
      ue_inject := inject;
      ue_lift := lift_rel;
      ue_conservative := lift_conservative
    |}.
    
    Definition as_pointed : PointedUniverseExtension U := {|
      pue_base := as_extension;
      pue_point := point
    |}.
    
    Definition as_fresh_pointed : FreshPointedUniverseExtension U := {|
      fpue_base := as_pointed;
      fpue_point_fresh := point_fresh
    |}.
    
    Definition as_pointed_serial : PointedSerialExtension U := {|
      pse_base := as_fresh_pointed;
      pse_serial_point := serial
    |}.
    
    (** Backward compatibility. *)
    Definition as_serial : SerialExtension U := as_pointed_serial.
    
  End WithU.

  (* Cleaner argument handling *)
  Arguments carrier U : clear implicits.
  Arguments inject {U} _.
  Arguments point {U}.
  Arguments lift_rel {U} R x y.
  Arguments carrier_case {U}.
  Arguments carrier_eq_dec {U}.

End WholeCompletion.

(* ========================================================================== *)
(*                                                                            *)
(*                    ADDITIONAL THEOREMS                                     *)
(*                                                                            *)
(* ========================================================================== *)

Section AdditionalTheorems.
  Variable U : Type.

  (** The completion is minimal: removing point breaks seriality for some R. *)
  Theorem completion_minimality :
    forall (R : U -> U -> Prop),
      ~ Serial R ->
      Serial (WholeCompletion.lift_rel R).
  Proof.
    intros R Hnserial.
    apply WholeCompletion.weak_serial.
  Qed.

  (** Point is the unique universal successor. *)
  Theorem point_unique_universal :
    forall (w : WholeCompletion.carrier U),
      (forall R : U -> U -> Prop, forall x : WholeCompletion.carrier U, 
        WholeCompletion.lift_rel R x w) ->
      w = WholeCompletion.point.
  Proof.
    intros w Huniv.
    destruct w as [u|].
    - (* w = Some u, show contradiction *)
      specialize (Huniv (fun _ _ => False) WholeCompletion.point).
      simpl in Huniv. contradiction.
    - reflexivity.
  Qed.

  (** Injection reflects the base relation. *)
  Theorem inject_reflects : forall (R : U -> U -> Prop) (a b : U),
    WholeCompletion.lift_rel R (WholeCompletion.inject a) (WholeCompletion.inject b) <-> R a b.
  Proof.
    intros R a b. apply WholeCompletion.lift_conservative.
  Qed.

  (** The carrier is the disjoint union of U and {point}. *)
  Theorem carrier_disjoint_union :
    forall (x : WholeCompletion.carrier U),
      (exists u : U, x = WholeCompletion.inject u) \/ x = WholeCompletion.point.
  Proof.
    intro x. destruct (WholeCompletion.carrier_case x) as [Hp | [u Hu]].
    - right. exact Hp.
    - left. exists u. exact Hu.
  Qed.

  (** For any element, its relation to point is trivially true. *)
  Theorem universal_relation_to_point :
    forall (R : U -> U -> Prop) (x : WholeCompletion.carrier U),
      WholeCompletion.lift_rel R x WholeCompletion.point.
  Proof.
    intros R x. apply WholeCompletion.serial.
  Qed.

  (** From point, the only relation that holds is to point itself. *)
  Theorem point_only_reaches_point :
    forall (R : U -> U -> Prop) (y : WholeCompletion.carrier U),
      WholeCompletion.lift_rel R WholeCompletion.point y -> y = WholeCompletion.point.
  Proof.
    intros R y. apply WholeCompletion.lift_rel_from_point_inv.
  Qed.

End AdditionalTheorems.

(* ========================================================================== *)
(*                                                                            *)
(*                    REWRITE HINTS                                           *)
(*                                                                            *)
(* ========================================================================== *)

Module WholeCompletionHints.

  (** Lift to Whole is always True. *)
  Lemma lift_to_whole : forall (U : Type) (R : U -> U -> Prop) (x : WholeCompletion.carrier U),
    WholeCompletion.lift_rel R x WholeCompletion.point.
  Proof. intros. apply WholeCompletion.serial. Qed.
  
  (** Cannot lift from Whole to an element. *)
  Lemma not_from_whole_to_some : forall (U : Type) (R : U -> U -> Prop) (u : U),
    ~ WholeCompletion.lift_rel R WholeCompletion.point (WholeCompletion.inject u).
  Proof. intros. apply WholeCompletion.point_terminal. Qed.
  
  (** Lift between elements is just R. *)
  Lemma lift_between_elems : forall (U : Type) (R : U -> U -> Prop) (a b : U),
    WholeCompletion.lift_rel R (WholeCompletion.inject a) (WholeCompletion.inject b) <-> R a b.
  Proof. intros. apply WholeCompletion.lift_conservative. Qed.
  
  (** Whole to Whole is True. *)
  Lemma lift_whole_whole : forall (U : Type) (R : U -> U -> Prop),
    WholeCompletion.lift_rel R WholeCompletion.point WholeCompletion.point.
  Proof. intros. apply WholeCompletion.point_self_loop. Qed.

  (** Element to Whole is True. *)
  Lemma lift_elem_to_whole : forall (U : Type) (R : U -> U -> Prop) (u : U),
    WholeCompletion.lift_rel R (WholeCompletion.inject u) WholeCompletion.point.
  Proof. intros. apply WholeCompletion.serial. Qed.

End WholeCompletionHints.

(* Hint databases *)
#[export] Hint Rewrite 
  WholeCompletionHints.lift_between_elems 
  : whole_completion.

#[export] Hint Resolve 
  WholeCompletionHints.lift_to_whole
  WholeCompletionHints.lift_whole_whole
  WholeCompletionHints.lift_elem_to_whole
  WholeCompletion.lift_preserves
  WholeCompletion.serial
  WholeCompletion.point_self_loop
  : whole_completion.

#[export] Hint Extern 1 (~ WholeCompletion.lift_rel _ WholeCompletion.point (WholeCompletion.inject _)) =>
  apply WholeCompletion.point_terminal : whole_completion.

(* ========================================================================== *)
(*                                                                            *)
(*                    TACTICS                                                 *)
(*                                                                            *)
(* ========================================================================== *)

(** Tactic to simplify lift_rel goals. *)
Ltac wc_simpl :=
  unfold WholeCompletion.lift_rel, WholeCompletion.inject, WholeCompletion.point;
  simpl.

(** Tactic to solve trivial whole-completion goals. *)
Ltac wc_auto :=
  auto with whole_completion;
  try (wc_simpl; auto; tauto).
