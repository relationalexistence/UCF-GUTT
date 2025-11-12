(**
  MetricCore.v
  ============
  Foundational metric/pseudometric infrastructure with ZERO global axioms.
  
  Contents:
  - PseudoMetricSpace typeclass (nonneg, sym, triangle)
  - MetricSpace typeclass (adds separation)
  - Zero pseudometric (trivial instance)
  - Optional EqDec typeclass + discrete metric
  - Product pseudometric for composition
  
  Dependencies: Reals, Lra, Morphisms, RelationClasses
  Part of: UCF/GUTT Proposition 18 - Distance of Relation
*)

From Coq Require Import Reals.
From Coq Require Import micromega.Lra.
From Coq Require Import Morphisms RelationClasses.

Set Implicit Arguments.
Local Open Scope R_scope.

(* ================================================================ *)
(* Pseudometric Space - Core Typeclass                              *)
(* ================================================================ *)

Class PseudoMetricSpace (U : Type) := {
  d : U -> U -> R;
  d_nonneg   : forall x y, 0 <= d x y;
  d_sym      : forall x y, d x y = d y x;
  d_triangle : forall x y z, d x z <= d x y + d y z
}.

(* Metric Space adds separation: d(x,y) = 0 ⟹ x = y *)
Definition MetricSpace (U : Type) {H : PseudoMetricSpace U} : Prop :=
  forall x y, d x y = 0 -> x = y.

(* ================================================================ *)
(* Trivial Zero Pseudometric                                        *)
(* ================================================================ *)

Instance zero_pseudometric (U : Type) : PseudoMetricSpace U.
Proof.
  refine {| d _ _ := 0 |}.
  - (* d_nonneg *) intros; lra.
  - (* d_sym *) intros; lra.
  - (* d_triangle *) intros; lra.
Defined.

(* ================================================================ *)
(* Optional Decidable Equality (NOT a global axiom)                 *)
(* ================================================================ *)

Class EqDec (U : Type) := {
  eq_dec : forall (x y : U), {x = y} + {x <> y}
}.

(* ================================================================ *)
(* Discrete Metric (requires EqDec instance)                        *)
(* ================================================================ *)

Section DiscreteMetric.
  Context {U : Type} {E : EqDec U}.

  Definition d_discrete (x y : U) : R :=
    if eq_dec x y then 0 else 1.

  #[export] Instance discrete_pseudometric : PseudoMetricSpace U.
  Proof.
    refine {| d := d_discrete |}.
    - (* d_nonneg *)
      intros x y. unfold d_discrete.
      destruct (eq_dec x y); lra.
    - (* d_sym *)
      intros x y. unfold d_discrete.
      destruct (eq_dec x y), (eq_dec y x); try congruence; reflexivity.
    - (* d_triangle *)
      intros x y z. unfold d_discrete.
      destruct (eq_dec x z) as [Hz | Hnz].
      + (* x = z, so d(x,z) = 0 *)
        subst z.
        destruct (eq_dec x y); destruct (eq_dec y x); lra.
      + (* x ≠ z, so d(x,z) = 1. Must show 1 ≤ d(x,y) + d(y,z) *)
        remember (if eq_dec x y then 0 else 1) as a.
        remember (if eq_dec y z then 0 else 1) as b.
        (* If both a=0 and b=0, then x=y=z, contradicting x≠z *)
        assert (1 <= a + b).
        {
          destruct (eq_dec x y); subst; simpl in *.
          - (* x = y, so a = 0 *)
            destruct (eq_dec y z); subst; simpl in *.
            + (* y = z, so x = z *) exfalso. apply Hnz. reflexivity.
            + (* y ≠ z, so b = 1 *) lra.
          - (* x ≠ y, so a = 1 *)
            destruct (eq_dec y z); subst; simpl in *; lra.
        }
        lra.
  Defined.

  Lemma discrete_is_metric : @MetricSpace U discrete_pseudometric.
  Proof.
    intros x y H.
    unfold d, discrete_pseudometric, d_discrete in H.
    destruct (eq_dec x y); [assumption|lra].
  Qed.

End DiscreteMetric.

(* ================================================================ *)
(* Product Pseudometric (weighted ℓ¹ composition)                   *)
(* ================================================================ *)

Section ProductPseudo.
  Context {U V : Type}.
  Context `{PU : PseudoMetricSpace U}.
  Context `{PV : PseudoMetricSpace V}.
  
  Variables (α β : R).
  Hypothesis α_nonneg : 0 <= α.
  Hypothesis β_nonneg : 0 <= β.

  Definition d_prod (p q : U * V) : R :=
    α * d (fst p) (fst q) + β * d (snd p) (snd q).

  Instance prod_pseudometric : PseudoMetricSpace (U * V).
  Proof.
    refine {| d := d_prod |}.
    - (* d_nonneg *)
      intros [x1 x2] [y1 y2]. unfold d_prod. simpl.
      apply Rplus_le_le_0_compat;
        apply Rmult_le_pos; try assumption; apply d_nonneg.
    - (* d_sym *)
      intros [x1 x2] [y1 y2]. unfold d_prod. simpl.
      rewrite d_sym, (d_sym (snd (x1, x2))).
      reflexivity.
    - (* d_triangle *)
      intros [x1 x2] [y1 y2] [z1 z2]. unfold d_prod. simpl.
      (* d(x,z) ≤ d(x,y) + d(y,z) componentwise *)
      assert (Hd1 : d x1 z1 <= d x1 y1 + d y1 z1) by apply d_triangle.
      assert (Hd2 : d x2 z2 <= d x2 y2 + d y2 z2) by apply d_triangle.
      (* Multiply by weights and add *)
      assert (α * d x1 z1 <= α * (d x1 y1 + d y1 z1)).
      { apply Rmult_le_compat_l; assumption. }
      assert (β * d x2 z2 <= β * (d x2 y2 + d y2 z2)).
      { apply Rmult_le_compat_l; assumption. }
      lra.
  Qed.

End ProductPseudo.

(* ================================================================ *)
(* Hint Database                                                    *)
(* ================================================================ *)

#[export] Hint Resolve d_nonneg d_sym d_triangle : core.
