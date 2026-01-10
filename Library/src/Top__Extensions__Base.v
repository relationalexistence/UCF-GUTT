(*
  UCF/GUTT(TM) Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
*)

(*
  +==========================================================================+
  |                                                                          |
  |                    Top__Extensions__Base.v                               |
  |                                                                          |
  |              Foundation: Record Definitions, Properties & Morphisms      |
  |                                                                          |
  +==========================================================================+
  |                                                                          |
  |  PURPOSE: Core record types and categorical infrastructure for           |
  |  universe extensions. This is the minimal foundation upon which all      |
  |  other constructions depend.                                             |
  |                                                                          |
  |  CONTENTS:                                                               |
  |    SECTION 1: Relation Properties (Serial, Total, Reflexive, etc.)       |
  |    SECTION 2: Marker Types (abstract coefficients)                       |
  |    SECTION 3: UniverseExtension Record                                   |
  |    SECTION 4: Extension Morphisms (Hom, Iso, Category Laws)              |
  |    SECTION 5: Pointed Extensions                                         |
  |    SECTION 6: Fresh Pointed Extensions                                   |
  |    SECTION 7: Pointed-Serial Extensions                                  |
  |    SECTION 8: Derived Theorems & Corollaries                             |
  |                                                                          |
  |  STATUS: [ok] ZERO AXIOMS                                                |
  |          [ok] ZERO ADMITS                                                |
  |          [ok] NO DEPENDENCIES (self-contained)                           |
  |          [ok] LIBRARY QUALITY                                            |
  |                                                                          |
  +==========================================================================+
*)

(* Disable auto template polymorphism for cleaner library exports *)
Unset Auto Template Polymorphism.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 1: RELATION PROPERTIES                          *)
(*                                                                            *)
(* ========================================================================== *)

(** Weak seriality: every element has at least one outgoing edge. *)
Definition Serial {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x : A, exists y : A, Rel x y.

(** Totality: for any two elements, at least one direction holds. *)
Definition Total {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y : A, Rel x y \/ Rel y x.

(** Left-totality: every element has at least one predecessor. *)
Definition LeftTotal {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall y : A, exists x : A, Rel x y.

(** Functional: each element has at most one successor. *)
Definition Functional {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y z : A, Rel x y -> Rel x z -> y = z.

(** Injective: each element has at most one predecessor. *)
Definition Injective {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y z : A, Rel x z -> Rel y z -> x = y.

(** Standard relation properties. *)
Definition Reflexive {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x : A, Rel x x.

Definition Irreflexive {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x : A, ~ Rel x x.

Definition Symmetric {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y : A, Rel x y -> Rel y x.

Definition Antisymmetric {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y : A, Rel x y -> Rel y x -> x = y.

Definition Asymmetric {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y : A, Rel x y -> ~ Rel y x.

Definition Transitive {A : Type} (Rel : A -> A -> Prop) : Prop :=
  forall x y z : A, Rel x y -> Rel y z -> Rel x z.

(** Composite properties. *)
Definition Equivalence {A : Type} (Rel : A -> A -> Prop) : Prop :=
  Reflexive Rel /\ Symmetric Rel /\ Transitive Rel.

Definition Preorder {A : Type} (Rel : A -> A -> Prop) : Prop :=
  Reflexive Rel /\ Transitive Rel.

Definition PartialOrder {A : Type} (Rel : A -> A -> Prop) : Prop :=
  Reflexive Rel /\ Antisymmetric Rel /\ Transitive Rel.

Definition StrictOrder {A : Type} (Rel : A -> A -> Prop) : Prop :=
  Irreflexive Rel /\ Transitive Rel.

(* -------------------------------------------------------------------------- *)
(*                      Theorems About Relation Properties                    *)
(* -------------------------------------------------------------------------- *)

Section RelationTheorems.
  Variable A : Type.
  Variable Rel : A -> A -> Prop.

  Theorem serial_nonempty (a : A) : Serial Rel -> exists b : A, Rel a b.
  Proof. intro Hserial. apply Hserial. Qed.

  Theorem total_implies_serial : Total Rel -> Serial Rel.
  Proof.
    intros Htotal x.
    destruct (Htotal x x) as [H | H]; exists x; exact H.
  Qed.

  Theorem reflexive_implies_serial : Reflexive Rel -> Serial Rel.
  Proof. intros Hrefl x. exists x. apply Hrefl. Qed.

  Theorem asymmetric_implies_irreflexive : Asymmetric Rel -> Irreflexive Rel.
  Proof. intros Hasym x Hxx. apply (Hasym x x Hxx Hxx). Qed.

  Theorem strict_order_asymmetric : StrictOrder Rel -> Asymmetric Rel.
  Proof.
    intros [Hirr Htrans] x y Hxy Hyx.
    apply (Hirr x). apply (Htrans x y x Hxy Hyx).
  Qed.

  Theorem equivalence_refl : Equivalence Rel -> Reflexive Rel.
  Proof. intros [H _]. exact H. Qed.

  Theorem equivalence_sym : Equivalence Rel -> Symmetric Rel.
  Proof. intros [_ [H _]]. exact H. Qed.

  Theorem equivalence_trans : Equivalence Rel -> Transitive Rel.
  Proof. intros [_ [_ H]]. exact H. Qed.

  Theorem equivalence_is_preorder : Equivalence Rel -> Preorder Rel.
  Proof. intros [Hrefl [_ Htrans]]. split; assumption. Qed.

End RelationTheorems.

(* -------------------------------------------------------------------------- *)
(*                      Relation Transformers                                 *)
(* -------------------------------------------------------------------------- *)

Section RelationTransformers.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition inverse (x y : A) : Prop := R y x.
  Definition complement (x y : A) : Prop := ~ R x y.

  Definition rel_compose (S : A -> A -> Prop) (x z : A) : Prop :=
    exists y : A, R x y /\ S y z.

  Definition rel_union (S : A -> A -> Prop) (x y : A) : Prop :=
    R x y \/ S x y.

  Definition rel_inter (S : A -> A -> Prop) (x y : A) : Prop :=
    R x y /\ S x y.

  (** Inverse relation definition for external use. *)
  Definition inv_rel (S : A -> A -> Prop) (x y : A) : Prop := S y x.

  (** Inverse of inverse is the original relation. *)
  Theorem inverse_involutive : forall (S : A -> A -> Prop) x y, 
    inv_rel (inv_rel S) x y <-> S x y.
  Proof. intros S x y. unfold inv_rel. tauto. Qed.

  Theorem inverse_preserves_reflexive : Reflexive R -> Reflexive inverse.
  Proof. intros Hrefl x. unfold inverse. apply Hrefl. Qed.

  Theorem inverse_preserves_symmetric : Symmetric R -> Symmetric inverse.
  Proof. intros Hsym x y. unfold inverse. apply Hsym. Qed.

  Theorem inverse_preserves_transitive : Transitive R -> Transitive inverse.
  Proof.
    intros Htrans x y z Hxy Hyz. unfold inverse in *.
    apply (Htrans z y x Hyz Hxy).
  Qed.

  Theorem left_total_inverse_serial : LeftTotal R -> Serial inverse.
  Proof.
    intros Hlt x. destruct (Hlt x) as [y Hy].
    exists y. unfold inverse. exact Hy.
  Qed.

End RelationTransformers.

Arguments inverse {A} R x y.
Arguments complement {A} R x y.
Arguments rel_compose {A} R S x z.
Arguments rel_union {A} R S x y.
Arguments rel_inter {A} R S x y.
Arguments inv_rel {A} S x y.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 2: MARKER TYPES                                 *)
(*                                                                            *)
(* ========================================================================== *)

Class Markers := {
  marker_type : Type;
  marker_zero : marker_type;
  marker_one : marker_type;
  marker_distinct : marker_zero <> marker_one
}.

Notation M := marker_type.
Notation m0 := marker_zero.
Notation m1 := marker_one.

Section MarkerLemmas.
  Context `{Mrk : Markers}.

  Lemma marker_distinct_sym : marker_one <> marker_zero.
  Proof. intro Heq. apply marker_distinct. symmetry. exact Heq. Qed.

  Lemma marker_distinct_stable : ~ ~ (marker_zero <> marker_one).
  Proof. intro H. apply H. exact marker_distinct. Qed.

End MarkerLemmas.

(** Boolean markers: the canonical axiom-free instance. *)
#[export] Instance BoolMarkers : Markers := {|
  marker_type := bool;
  marker_zero := false;
  marker_one := true;
  marker_distinct := fun H => 
    match H in (_ = b) return (if b then False else True) with
    | eq_refl => I
    end
|}.

Lemma bool_markers_sound : @marker_zero BoolMarkers <> @marker_one BoolMarkers.
Proof. exact (@marker_distinct BoolMarkers). Qed.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 3: UNIVERSE EXTENSION RECORD                    *)
(*                                                                            *)
(* ========================================================================== *)

Record UniverseExtension (U : Type) := mkUniverseExtension {
  ue_carrier : Type;
  ue_inject : U -> ue_carrier;
  ue_lift : (U -> U -> Prop) -> (ue_carrier -> ue_carrier -> Prop);
  ue_conservative : forall (R : U -> U -> Prop) (a b : U),
    ue_lift R (ue_inject a) (ue_inject b) <-> R a b
}.

Arguments ue_carrier {U}.
Arguments ue_inject {U} _ _.
Arguments ue_lift {U} _ _ _ _.
Arguments ue_conservative {U}.

Section UniverseExtensionLemmas.
  Variable U : Type.
  Variable E : UniverseExtension U.

  Lemma ue_conservative_fwd : forall (R : U -> U -> Prop) (a b : U),
    ue_lift E R (ue_inject E a) (ue_inject E b) -> R a b.
  Proof. intros R a b H. apply (ue_conservative E). exact H. Qed.

  Lemma ue_conservative_bwd : forall (R : U -> U -> Prop) (a b : U),
    R a b -> ue_lift E R (ue_inject E a) (ue_inject E b).
  Proof. intros R a b H. apply (ue_conservative E). exact H. Qed.

  Lemma ue_lift_empty : forall a b : U,
    ~ ue_lift E (fun _ _ => False) (ue_inject E a) (ue_inject E b).
  Proof. intros a b H. apply (ue_conservative E) in H. exact H. Qed.

  Lemma ue_lift_full : forall a b : U,
    ue_lift E (fun _ _ => True) (ue_inject E a) (ue_inject E b).
  Proof. intros a b. apply (ue_conservative E). exact I. Qed.

  Lemma ue_lift_monotone : forall (R S : U -> U -> Prop),
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

  Lemma ue_lift_equiv : forall (R S : U -> U -> Prop),
    (forall a b, R a b <-> S a b) ->
    forall a b : U,
      ue_lift E R (ue_inject E a) (ue_inject E b) <->
      ue_lift E S (ue_inject E a) (ue_inject E b).
  Proof.
    intros R S Hequiv a b. split.
    - apply ue_lift_monotone. intros x y. apply Hequiv.
    - apply ue_lift_monotone. intros x y. apply Hequiv.
  Qed.

End UniverseExtensionLemmas.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 4: EXTENSION MORPHISMS                          *)
(*                                                                            *)
(* ========================================================================== *)

Record UE_Hom {U : Type} (E1 E2 : UniverseExtension U) := mkUE_Hom {
  hom_map : ue_carrier E1 -> ue_carrier E2;
  hom_inject_commutes : forall (u : U),
    hom_map (ue_inject E1 u) = ue_inject E2 u;
  hom_lift_preserves : forall (R : U -> U -> Prop) (x y : ue_carrier E1),
    ue_lift E1 R x y -> ue_lift E2 R (hom_map x) (hom_map y)
}.

Arguments hom_map {U E1 E2}.
Arguments hom_inject_commutes {U E1 E2}.
Arguments hom_lift_preserves {U E1 E2}.

Record UE_Iso {U : Type} (E1 E2 : UniverseExtension U) := mkUE_Iso {
  iso_fwd : UE_Hom E1 E2;
  iso_bwd : UE_Hom E2 E1;
  iso_left_inv : forall (x : ue_carrier E1),
    hom_map iso_bwd (hom_map iso_fwd x) = x;
  iso_right_inv : forall (y : ue_carrier E2),
    hom_map iso_fwd (hom_map iso_bwd y) = y
}.

Arguments iso_fwd {U E1 E2}.
Arguments iso_bwd {U E1 E2}.
Arguments iso_left_inv {U E1 E2}.
Arguments iso_right_inv {U E1 E2}.

(* -------------------------------------------------------------------------- *)
(*                          Category Laws                                     *)
(* -------------------------------------------------------------------------- *)

Section CategoryLaws.
  Variable U : Type.

  Definition UE_Hom_id (E : UniverseExtension U) : UE_Hom E E.
  Proof.
    refine {| hom_map := fun x => x |}.
    - intro u. reflexivity.
    - intros R x y H. exact H.
  Defined.

  Definition UE_Hom_compose {E1 E2 E3 : UniverseExtension U}
    (f : UE_Hom E1 E2) (g : UE_Hom E2 E3) : UE_Hom E1 E3.
  Proof.
    refine {| hom_map := fun x => hom_map g (hom_map f x) |}.
    - intro u. rewrite hom_inject_commutes. apply hom_inject_commutes.
    - intros R x y H. apply hom_lift_preserves. apply hom_lift_preserves. exact H.
  Defined.

  Theorem hom_id_left : forall {E1 E2 : UniverseExtension U} (f : UE_Hom E1 E2),
    forall x, hom_map (UE_Hom_compose (UE_Hom_id E1) f) x = hom_map f x.
  Proof. intros E1 E2 f x. reflexivity. Qed.

  Theorem hom_id_right : forall {E1 E2 : UniverseExtension U} (f : UE_Hom E1 E2),
    forall x, hom_map (UE_Hom_compose f (UE_Hom_id E2)) x = hom_map f x.
  Proof. intros E1 E2 f x. reflexivity. Qed.

  Theorem hom_compose_assoc : forall {E1 E2 E3 E4 : UniverseExtension U}
    (f : UE_Hom E1 E2) (g : UE_Hom E2 E3) (h : UE_Hom E3 E4),
    forall x, 
      hom_map (UE_Hom_compose (UE_Hom_compose f g) h) x = 
      hom_map (UE_Hom_compose f (UE_Hom_compose g h)) x.
  Proof. intros E1 E2 E3 E4 f g h x. reflexivity. Qed.

  Definition UE_Iso_refl (E : UniverseExtension U) : UE_Iso E E.
  Proof.
    refine {| iso_fwd := UE_Hom_id E; iso_bwd := UE_Hom_id E |}.
    - intro x. reflexivity.
    - intro y. reflexivity.
  Defined.

  Definition UE_Iso_sym {E1 E2 : UniverseExtension U}
    (iso : UE_Iso E1 E2) : UE_Iso E2 E1.
  Proof.
    refine {| iso_fwd := iso_bwd iso; iso_bwd := iso_fwd iso |}.
    - intro x. apply iso_right_inv.
    - intro y. apply iso_left_inv.
  Defined.

  Definition UE_Iso_trans {E1 E2 E3 : UniverseExtension U}
    (iso12 : UE_Iso E1 E2) (iso23 : UE_Iso E2 E3) : UE_Iso E1 E3.
  Proof.
    refine {|
      iso_fwd := UE_Hom_compose (iso_fwd iso12) (iso_fwd iso23);
      iso_bwd := UE_Hom_compose (iso_bwd iso23) (iso_bwd iso12)
    |}.
    - intro x. simpl.
      rewrite (iso_left_inv iso23).
      rewrite (iso_left_inv iso12).
      reflexivity.
    - intro y. simpl.
      rewrite (iso_right_inv iso12).
      rewrite (iso_right_inv iso23).
      reflexivity.
  Defined.

  Theorem iso_preserves_inject_distinct {E1 E2 : UniverseExtension U} 
    (iso : UE_Iso E1 E2) :
    forall a b : U, ue_inject E1 a <> ue_inject E1 b -> 
                    ue_inject E2 a <> ue_inject E2 b.
  Proof.
    intros a b Hneq Heq. apply Hneq.
    rewrite <- (iso_left_inv iso (ue_inject E1 a)).
    rewrite <- (iso_left_inv iso (ue_inject E1 b)).
    rewrite (hom_inject_commutes (iso_fwd iso) a).
    rewrite (hom_inject_commutes (iso_fwd iso) b).
    rewrite Heq. reflexivity.
  Qed.

End CategoryLaws.

Arguments UE_Hom_id {U}.
Arguments UE_Hom_compose {U E1 E2 E3}.
Arguments UE_Iso_refl {U}.
Arguments UE_Iso_sym {U E1 E2}.
Arguments UE_Iso_trans {U E1 E2 E3}.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 5: POINTED EXTENSIONS                           *)
(*                                                                            *)
(* ========================================================================== *)

Record PointedUniverseExtension (U : Type) := mkPointedUE {
  pue_base :> UniverseExtension U;
  pue_point : ue_carrier pue_base
}.

Arguments pue_base {U}.
Arguments pue_point {U}.

Section PointedLemmas.
  Variable U : Type.
  Variable P : PointedUniverseExtension U.

  Lemma pointed_carrier_inhabited : ue_carrier (pue_base P).
  Proof. exact (pue_point P). Qed.

  Lemma pointed_nonempty : exists x : ue_carrier (pue_base P), True.
  Proof. exists (pue_point P). exact I. Qed.

End PointedLemmas.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 6: FRESH POINTED EXTENSIONS                     *)
(*                                                                            *)
(* ========================================================================== *)

Record FreshPointedUniverseExtension (U : Type) := mkFreshPointedUE {
  fpue_base :> PointedUniverseExtension U;
  fpue_point_fresh : forall (u : U), 
    ue_inject (pue_base fpue_base) u <> pue_point fpue_base
}.

Arguments fpue_base {U}.
Arguments fpue_point_fresh {U}.

Section FreshPointedAccessors.
  Variable U : Type.
  Variable F : FreshPointedUniverseExtension U.
  
  Definition fpue_carrier : Type := ue_carrier (pue_base (fpue_base F)).
  Definition fpue_inject : U -> fpue_carrier := ue_inject (pue_base (fpue_base F)).
  Definition fpue_lift : (U -> U -> Prop) -> (fpue_carrier -> fpue_carrier -> Prop) := 
    ue_lift (pue_base (fpue_base F)).
  Definition fpue_point : fpue_carrier := pue_point (fpue_base F).
  
End FreshPointedAccessors.

Arguments fpue_carrier {U}.
Arguments fpue_inject {U} _ _.
Arguments fpue_lift {U} _ _ _ _.
Arguments fpue_point {U}.

Section FreshPointedLemmas.
  Variable U : Type.
  Variable F : FreshPointedUniverseExtension U.

  Lemma fpue_point_fresh_sym : forall (u : U),
    pue_point (fpue_base F) <> ue_inject (pue_base (fpue_base F)) u.
  Proof. intros u Heq. apply (fpue_point_fresh F u). symmetry. exact Heq. Qed.

  Lemma fpue_carrier_has_two (u : U) : fpue_inject F u <> fpue_point F.
  Proof. apply fpue_point_fresh. Qed.

End FreshPointedLemmas.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 7: POINTED-SERIAL EXTENSIONS                    *)
(*                                                                            *)
(* ========================================================================== *)

Record PointedSerialExtension (U : Type) := mkPointedSerialExt {
  pse_base :> FreshPointedUniverseExtension U;
  pse_serial_point : forall (R : U -> U -> Prop) (x : fpue_carrier pse_base),
    fpue_lift pse_base R x (fpue_point pse_base)
}.

Arguments pse_base {U}.
Arguments pse_serial_point {U}.

Definition SerialExtension := PointedSerialExtension.
Definition mkSerialExt := mkPointedSerialExt.
Definition se_base {U} := @pse_base U.
Definition se_serial {U} := @pse_serial_point U.

(* -------------------------------------------------------------------------- *)
(*                    Direct Accessors (bypass nesting)                       *)
(* -------------------------------------------------------------------------- *)

(** These accessors go directly to the underlying UniverseExtension,
    avoiding the accessor chain that causes type unification issues. *)

Section DirectAccessors.
  Variable U : Type.
  Variable S : PointedSerialExtension U.
  
  (** Direct path to the underlying UniverseExtension. *)
  Definition pse_extension : UniverseExtension U :=
    pue_base (fpue_base (pse_base S)).
  
  (** Carrier type via direct path. *)
  Definition pse_carrier : Type := ue_carrier pse_extension.
  
  (** Injection via direct path. *)
  Definition pse_inject : U -> pse_carrier := ue_inject pse_extension.
  
  (** Lift via direct path. *)
  Definition pse_lift : (U -> U -> Prop) -> (pse_carrier -> pse_carrier -> Prop) := 
    ue_lift pse_extension.
  
  (** Point via direct path. *)
  Definition pse_point : pse_carrier := pue_point (fpue_base (pse_base S)).
  
  (** Equivalence lemmas showing these match the nested accessors. *)
  Lemma pse_carrier_eq : pse_carrier = fpue_carrier (pse_base S).
  Proof. reflexivity. Qed.
  
  Lemma pse_inject_eq : pse_inject = fpue_inject (pse_base S).
  Proof. reflexivity. Qed.
  
  Lemma pse_lift_eq : pse_lift = fpue_lift (pse_base S).
  Proof. reflexivity. Qed.
  
  Lemma pse_point_eq : pse_point = fpue_point (pse_base S).
  Proof. reflexivity. Qed.

End DirectAccessors.

Arguments pse_extension {U}.
Arguments pse_carrier {U}.
Arguments pse_inject {U} _ _.
Arguments pse_lift {U} _ _ _ _.
Arguments pse_point {U}.

Definition se_extension {U} := @pse_extension U.
Definition se_carrier {U} := @pse_carrier U.
Definition se_inject {U} := @pse_inject U.
Definition se_lift {U} := @pse_lift U.
Definition se_point {U} := @pse_point U.

(* ========================================================================== *)
(*                                                                            *)
(*                    SECTION 8: DERIVED THEOREMS & COROLLARIES               *)
(*                                                                            *)
(* ========================================================================== *)

Section PointedSerialTheorems.
  Variable U : Type.
  Variable pse : PointedSerialExtension U.

  Theorem pointed_serial_implies_serial :
    forall (R : U -> U -> Prop), Serial (pse_lift pse R).
  Proof.
    intros R x. exists (pse_point pse). apply pse_serial_point.
  Qed.

  Definition pse_serial_exists :
    forall (R : U -> U -> Prop) (x : pse_carrier pse), exists y, pse_lift pse R x y.
  Proof.
    intros R x. exists (pse_point pse). apply pse_serial_point.
  Defined.

  Theorem pse_no_dead_ends : forall (R : U -> U -> Prop),
    ~ exists x : pse_carrier pse, forall y : pse_carrier pse, ~ pse_lift pse R x y.
  Proof.
    intros R [x Hx]. apply (Hx (pse_point pse)). apply pse_serial_point.
  Qed.

  Theorem pse_point_reachable : forall (R : U -> U -> Prop) (x : pse_carrier pse),
    pse_lift pse R x (pse_point pse).
  Proof. intros R x. apply pse_serial_point. Qed.

  Theorem pse_point_self_loop : forall (R : U -> U -> Prop),
    pse_lift pse R (pse_point pse) (pse_point pse).
  Proof. intro R. apply pse_serial_point. Qed.

  Theorem pse_uniform_witness : forall (R : U -> U -> Prop),
    exists w : pse_carrier pse, forall x : pse_carrier pse, pse_lift pse R x w.
  Proof.
    intro R. exists (pse_point pse). intro x. apply pse_serial_point.
  Qed.

  Theorem pse_lift_nonempty : forall (R : U -> U -> Prop),
    exists x y : pse_carrier pse, pse_lift pse R x y.
  Proof.
    intro R. exists (pse_point pse), (pse_point pse). apply pse_serial_point.
  Qed.

End PointedSerialTheorems.

Definition se_serial_exists {U : Type} := @pse_serial_exists U.
