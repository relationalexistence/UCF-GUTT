(*
  Standalone: Crisp projector + Dynamics + NRT (no external imports from your prior files)
  Coq ≥ 8.12
*
 UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
  See LICENSE, NOTICE, and TRADEMARKS in the repo root.
)

From Coq Require Import Reals.
From Coq Require Import Logic.FunctionalExtensionality.
Local Open Scope R_scope.
From Coq Require Import micromega.Lra.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.


(* ---------- Core types (parametric) ---------- *)

Section CrispCore.
  Context {A B : Type}.

  (* real-valued tensor on A×B *)
  Definition KRel := A -> B -> R.
  Definition BoolRel := A -> B -> bool.

  (* 0/1 embedding and 1/2-threshold readout *)
  Definition F_embed (r : BoolRel) : KRel :=
    fun x y => if r x y then 1%R else 0%R.

  Definition U_thresh (t : KRel) : BoolRel :=
    fun x y => if Rlt_dec (/2)%R (t x y) then true else false.

  (* U ∘ F = id, pointwise and as function equality *)
  Lemma UoF_id_pt :
    forall (r : BoolRel) (x : A) (y : B),
      U_thresh (F_embed r) x y = r x y.
  Proof.
    intros r x y. unfold U_thresh, F_embed.
    destruct (r x y) eqn:E; cbn.
    - destruct (Rlt_dec (/2)%R 1%R) as [H|H]; [reflexivity|]; exfalso; lra.
    - destruct (Rlt_dec (/2)%R 0%R) as [H|H]; [lra|reflexivity].
  Qed.

  Lemma UoF_id_fun : forall r : BoolRel, U_thresh (F_embed r) = r.
  Proof.
    intros r.
    apply functional_extensionality; intro x.
    apply functional_extensionality; intro y.
    apply UoF_id_pt.
  Qed.

  (* The crisp projector *)
  Definition FU (t : KRel) : KRel := F_embed (U_thresh t).

  (* Characterizations *)
  Definition Crisp_fun (t : KRel) : Prop := exists r, t = F_embed r.
  Definition Crisp_pt  (t : KRel) : Prop := exists r, forall x y, t x y = F_embed r x y.

  Lemma crisp_fun_iff_FU_fixed_fun :
    forall t, Crisp_fun t <-> FU t = t.
  Proof.
    intro t; split.
    - intros [r Hr]. subst. unfold FU. now rewrite (UoF_id_fun r).
    - intro Hfix. exists (U_thresh t). unfold FU in Hfix. now symmetry.
  Qed.

  Lemma crisp_pt_iff_FU_fixed_pt :
    forall t, Crisp_pt t <-> (forall x y, FU t x y = t x y).
  Proof.
    intro t; split.
    - intros [r Hr] x y.
      assert (Ht : t = F_embed r).
      { apply functional_extensionality; intro x0.
        apply functional_extensionality; intro y0.
        exact (Hr x0 y0). }
      rewrite Ht. unfold FU. now rewrite (UoF_id_fun r).
    - intro Hpt. exists (U_thresh t). intros x y.
      unfold FU. now rewrite <- (Hpt x y).
  Qed.

  Lemma FU_idempotent : forall t, FU (FU t) = FU t.
  Proof. intro t. unfold FU. now rewrite (UoF_id_fun (U_thresh t)). Qed.

  Lemma FU_is_boolean : forall t x y, FU t x y = 1%R \/ FU t x y = 0%R.
  Proof.
    intros t x y. unfold FU, F_embed, U_thresh. cbn.
    destruct (Rlt_dec (/2)%R (t x y)); [left|right]; reflexivity.
  Qed.

  Lemma crisp_stable : forall t, (exists r, t = F_embed r) -> FU t = t.
  Proof. intro t. apply (proj1 (crisp_fun_iff_FU_fixed_fun t)). Qed.

  Lemma fixed_are_crisp : forall t, FU t = t -> exists r, t = F_embed r.
  Proof. intro t. apply (proj2 (crisp_fun_iff_FU_fixed_fun t)). Qed.

End CrispCore.

(* ---------- Dynamics layer: evolve + crisp ---------- *)

Section Dynamics.
  Context {A B : Type}.

  (* Reuse the earlier definitions; do NOT re-declare them. *)
  Local Notation KRel     := (A -> B -> R).
  Local Notation BoolRel  := (A -> B -> bool).
  Local Notation FU       := (@FU A B).
  Local Notation F_embed  := (@F_embed A B).
  Local Notation U_thresh := (@U_thresh A B).

  (* Abstract time monoid *)
  Variable Time : Type.
  Variable comp : Time -> Time -> Time.
  Variable e : Time.
  Hypothesis comp_assoc : forall a b c, comp a (comp b c) = comp (comp a b) c.
  Hypothesis comp_e_l   : forall a, comp e a = a.
  Hypothesis comp_e_r   : forall a, comp a e = a.

  (* Evolution *)
  Variable E : Time -> KRel -> KRel.
  Hypothesis E_semigroup : forall t1 t2 T, E (comp t1 t2) T = E t1 (E t2 T).
  Hypothesis E_id        : forall T, E e T = T.

  (* Projected (crisp) evolution *)
  Definition Ehat (t:Time) (T:KRel) : KRel := FU (E t T).

  (* Strong compatibility: evolve then crisp = crisp then evolve *)
  Hypothesis E_comm_FU : forall t T, FU (E t T) = E t (FU T).

  Lemma crisp_invariant :
    forall t T, FU T = T -> FU (E t T) = E t T.
  Proof. intros t T H; rewrite E_comm_FU, H; reflexivity. Qed.

Lemma Ehat_semigroup :
  forall a b T, Ehat (comp a b) T = Ehat a (Ehat b T).
Proof.
  intros a b T; unfold Ehat.
  rewrite E_semigroup.
  (* Commute FU past E a on both sides, but do it via named equalities *)
  pose proof (E_comm_FU a (E b T))          as H1.  (* FU (E a (E b T)) = E a (FU (E b T)) *)
  pose proof (E_comm_FU a (FU (E b T)))     as H2.  (* FU (E a (FU (E b T))) = E a (FU (FU (E b T))) *)
  rewrite H1; rewrite H2.
  (* Now goal: E a (FU (E b T)) = E a (FU (FU (E b T))) *)
  pose proof (FU_idempotent (E b T)) as Hid.        (* FU (FU (E b T)) = FU (E b T) *)
  (* Turn argument equality into equality after E a by mapping with f_equal *)
  apply (f_equal (fun X => E a X)) in Hid.
  (* Hid : E a (FU (FU (E b T))) = E a (FU (E b T)) *)
  exact (eq_sym Hid).
Qed.



  Lemma Ehat_id : forall T, Ehat e T = FU T.
  Proof. intro T; unfold Ehat; now rewrite E_id. Qed.

End Dynamics.


(* ---------- Symmetry + NRT nesting ---------- *)

Section Symmetry_NRT.
  Context {A B : Type}.

  (* Reuse earlier definitions; do NOT re-declare them. *)
  Local Notation KRel     := (A -> B -> R).
  Local Notation BoolRel  := (A -> B -> bool).
  Local Notation FU       := (@FU A B).
  Local Notation F_embed  := (@F_embed A B).
  Local Notation U_thresh := (@U_thresh A B).

  (* Group structure and actions *)
  Variable G : Type.
  Variable eG : G.
  Variable inv : G -> G.
  Variable op  : G -> G -> G.
  Hypothesis G_laws :
    forall g h k, op g (op h k) = op (op g h) k /\
                  op eG g = g /\ op g eG = g /\
                  op g (inv g) = eG /\ op (inv g) g = eG.

  Variable actA : G -> A -> A.
  Variable actB : G -> B -> B.

  (* Pushforward (relabel indices by g) *)
  Definition push (g:G) (T:KRel) : KRel :=
    fun x y => T (actA (inv g) x) (actB (inv g) y).

  (* Equivariance for embed/readout *)
  Hypothesis F_embed_equiv :
    forall g r,
      push g (F_embed r)
      = F_embed (fun x y => r (actA (inv g) x) (actB (inv g) y)).

  Hypothesis U_thresh_equiv :
    forall g T,
      U_thresh (push g T)
      = (fun x y => U_thresh T (actA (inv g) x) (actB (inv g) y)).

  (* Then FU is equivariant *)
  Lemma FU_equiv : forall g T, push g (FU T) = FU (push g T).
  Proof.
    intros g T. unfold FU. rewrite F_embed_equiv, U_thresh_equiv. reflexivity.
  Qed.

  (* NRT: fold with an associative op on tensors *)
  Variable opT : KRel -> KRel -> KRel.
  Variable I   : KRel.
  Hypothesis opT_assoc : forall X Y Z, opT X (opT Y Z) = opT (opT X Y) Z.
  Hypothesis opT_I_l   : forall X, opT I X = X.
  Hypothesis opT_I_r   : forall X, opT X I = X.

  Hypothesis opT_equiv : forall g X Y, push g (opT X Y) = opT (push g X) (push g Y).
  Hypothesis I_equiv   : forall g, push g I = I.

  (* Optional: FU distributes over opT *)
  Hypothesis FU_morphism : forall X Y, FU (opT X Y) = opT (FU X) (FU Y).
  Hypothesis FU_I        : FU I = I.

  Fixpoint nest (xs : list KRel) : KRel :=
    match xs with
    | nil   => I
    | h::t  => opT h (nest t)
    end.

  Lemma nest_equiv : forall g xs, push g (nest xs) = nest (map (push g) xs).
  Proof.
    intros g xs; induction xs as [|h t IH]; cbn.
    - apply I_equiv.
    - now rewrite opT_equiv, IH.
  Qed.

  Lemma FU_nest : forall xs, FU (nest xs) = nest (map FU xs).
  Proof.
    intro xs; induction xs as [|h t IH]; cbn.
    - now rewrite FU_I.
    - now rewrite FU_morphism, IH.
  Qed.

  Lemma nest_crisp_if_all_crisp :
    forall xs, (forall h, In h xs -> FU h = h) -> FU (nest xs) = nest xs.
  Proof.
    intros xs Hall. rewrite FU_nest.
    induction xs as [|h t IH]; cbn; [reflexivity|].
    rewrite Hall by (left; reflexivity).
    f_equal. apply IH. intros k Hk. apply Hall. right. exact Hk.
  Qed.

End Symmetry_NRT.

