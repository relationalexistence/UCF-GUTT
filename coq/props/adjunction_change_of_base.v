(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.

  adjunction_change_of_base.v
  --------------------------------
  Boolean relations  ——F⟶  K-weighted relations
         ↑  U
  (Galois connection on each hom-poset; U ∘ F = id, F ∘ U ≤ id)
*)

Set Implicit Arguments.
From Coq Require Import Bool.Bool.

Section ChangeOfBaseAdjunction.

  (* ---- 0. Ordered carrier K and an embedding 2 ↪ K ---- *)

  Variable K  : Type.
  Variable kle : K -> K -> Prop.              (* order on K *)
  Hypothesis kle_refl  : forall k, kle k k.
  Hypothesis kle_trans : forall a b c, kle a b -> kle b c -> kle a c.

  Variable k0 : K.                            (* bottom element in K *)
  Hypothesis k0_is_bottom : forall k, kle k0 k.

  (* Embedding/projection between booleans and K *)
  Variable eta : bool -> K.                   (* 2 → K *)
  Variable pi  : K -> bool.                   (* K → 2 *)

  (* Scalar-level adjunction laws *)
  Hypothesis pi_eta_id : forall b : bool, pi (eta b) = b.     (* U ∘ F = id on 2 *)
  Hypothesis eta_pi_le : forall k : K, kle (eta (pi k)) k.    (* F ∘ U ≤ id on K *)

  (* Anchor false at bottom *)
  Hypothesis eta_false_is_k0 : eta false = k0.

  (* Boolean order  b1 ≤ b2  ≡  (b1=true → b2=true) *)
  Definition ble (b1 b2 : bool) : Prop := (b1 = true -> b2 = true).

  (* Monotonicity of scalar maps as order morphisms *)
  Hypothesis pi_monotone  : forall k1 k2, kle k1 k2 -> ble (pi k1) (pi k2).
  Hypothesis eta_monotone : forall b1 b2, ble b1 b2 -> kle (eta b1) (eta b2).

  (* ---- 1. Orders on relations (pointwise) ---- *)

  Definition BoolRel (A B : Type) := A -> B -> bool.
  Definition KRel    (A B : Type) := A -> B -> K.

  Definition brel_le {A B : Type} (r1 r2 : BoolRel A B) : Prop :=
    forall x y, ble (r1 x y) (r2 x y).

  Definition krel_le {A B : Type} (s1 s2 : KRel A B) : Prop :=
    forall x y, kle (s1 x y) (s2 x y).

  Lemma ble_refl (b : bool) : ble b b.      Proof. intros H; exact H. Qed.
  Lemma ble_trans (b1 b2 b3 : bool) :
    ble b1 b2 -> ble b2 b3 -> ble b1 b3.     Proof. firstorder. Qed.

  Lemma brel_le_refl (A B : Type) (r : BoolRel A B) :
    brel_le r r.                              Proof. intros x y; apply ble_refl. Qed.
  Lemma brel_le_trans (A B : Type) (r1 r2 r3 : BoolRel A B) :
    brel_le r1 r2 -> brel_le r2 r3 -> brel_le r1 r3.
  Proof. intros H12 H23 x y; eapply ble_trans; [apply H12|apply H23]. Qed.

  Lemma krel_le_refl (A B : Type) (s : KRel A B) :
    krel_le s s.                              Proof. intros x y; apply kle_refl. Qed.
  Lemma krel_le_trans (A B : Type) (s1 s2 s3 : KRel A B) :
    krel_le s1 s2 -> krel_le s2 s3 -> krel_le s1 s3.
  Proof. intros H12 H23 x y; eapply kle_trans; [apply H12|apply H23]. Qed.

  (* ---- 2. Change-of-base on hom-sets: F and U ---- *)

  Definition F {A B : Type} (r : BoolRel A B) : KRel A B :=
    fun x y => eta (r x y).

  Definition U {A B : Type} (s : KRel A B) : BoolRel A B :=
    fun x y => pi (s x y).

  Lemma F_monotone (A B : Type) :
    forall (r1 r2 : BoolRel A B),
      brel_le r1 r2 -> krel_le (@F A B r1) (@F A B r2).
  Proof. intros r1 r2 H x y; apply eta_monotone, H. Qed.

  Lemma U_monotone (A B : Type) :
    forall (s1 s2 : KRel A B),
      krel_le s1 s2 -> brel_le (@U A B s1) (@U A B s2).
  Proof.
    intros s1 s2 H x y.
    unfold U.
    (* Goal: ble (pi (s1 x y)) (pi (s2 x y)). *)
    apply pi_monotone, H.
  Qed.

  (* ---- 3. Unit/Counit (triangle) laws, pointwise ---- *)

  Lemma UF_id_pt (A B : Type) (r : BoolRel A B) :
    forall x y, (@U A B (@F A B r)) x y = r x y.
  Proof. intros x y; unfold U, F; now rewrite pi_eta_id. Qed.

  Lemma FU_le (A B : Type) (s : KRel A B) :
    krel_le (@F A B (@U A B s)) s.
  Proof. intros x y; unfold F, U; apply eta_pi_le. Qed.

  (* ---- 4. Hom-set adjunction (Galois connection) ---- *)

Lemma hom_adj (A B : Type) (r : BoolRel A B) (s : KRel A B) :
  krel_le (@F A B r) s <-> brel_le r (@U A B s).
Proof.
  split.
  - (* -> direction *)
    intros H x y. unfold ble. intro Hrtrue.
    set (k1 := eta (r x y)).
    set (k2 := s x y).
    assert (Hle : kle k1 k2) by (subst; apply H).
    apply pi_monotone in Hle.
    replace (pi k1) with (pi (eta (r x y))) in Hle by (unfold k1; reflexivity).
    rewrite pi_eta_id in Hle.
    rewrite Hrtrue in Hle.
    apply Hle.
    reflexivity.
  - (* <- direction *)

  intros H x y.
  destruct (r x y) eqn:Rxy.
  + (* true case ... as you had ... *)
    specialize (H x y). unfold ble in H.
    assert (Hpi : pi (s x y) = true) by (apply H; exact Rxy).
    eapply kle_trans.
    * apply eta_monotone. intros _; exact Hpi.
    * apply eta_pi_le.
  + (* r x y = false *)
    change (kle (eta (r x y)) (s x y)).  (* <-- expose r x y *)
    rewrite Rxy.
    rewrite eta_false_is_k0.
    apply k0_is_bottom.

Qed.


(* End the abstract section *)
End ChangeOfBaseAdjunction.
