(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

(* === Module: BoundaryCore === *)
Require Import Reals Psatz.
Open Scope R_scope.

Module BoundaryCore.

  Section Boundary.
    Variables (X Y : Type) (g : X -> R) (h : Y -> R).

    (* States for the detector (purely about the denominator) *)
    Inductive RelationalState :=
    | RS_Related      (* h(y) <> 0 *)
    | RS_Boundary     (* h(y) = 0  *)
    | RS_Undefined.   (* placeholder; not used here *)

    Definition relational_boundary (x : X) (y : Y) : RelationalState :=
      let denom := h y in
      match Rlt_dec denom 0 with
      | left _  => RS_Related
      | right _ =>
        match Rgt_dec denom 0 with
        | left _  => RS_Related
        | right _ => RS_Boundary  (* denom >= 0 and denom <= 0 ⇒ denom = 0 *)
        end
      end.

    (* Contexts *)
    Inductive RelCtx := RC_Space | RC_Time | RC_Info.

    (* Minimal extended-real/NaN tag *)
    Inductive ExtR :=
    | Finite  : R -> ExtR
    | Pinfty  : ExtR
    | Minfty  : ExtR
    | NaN     : ExtR.

    (* Option-typed division *)
    Definition safe_div (x : X) (y : Y) : option R :=
      if Req_EM_T (h y) 0 then None else Some (g x / h y).

    (* Contextual boundary handler *)
    Definition boundary_handle (ctx : RelCtx) (o : option R) : ExtR :=
      match o with
      | Some r => Finite r
      | None =>
          match ctx with
          | RC_Space => Pinfty
          | RC_Time  => Finite 0
          | RC_Info  => NaN
          end
      end.

    (* Total, contextual division *)
    Definition contextual_div (ctx : RelCtx) (x : X) (y : Y) : ExtR :=
      boundary_handle ctx (safe_div x y).

    (* --- Lemmas --- *)

    Lemma safe_div_correct :
      forall x y, h y <> 0 -> safe_div x y = Some (g x / h y).
    Proof.
      intros x y Hnz. unfold safe_div.
      destruct (Req_EM_T (h y) 0) as [H|H]; congruence.
    Qed.

    Lemma boundary_handle_conservative :
      forall ctx r, boundary_handle ctx (Some r) = Finite r.
    Proof. reflexivity. Qed.

    Corollary contextual_div_agrees_with_classical :
      forall ctx x y, h y <> 0 ->
        contextual_div ctx x y = Finite (g x / h y).
    Proof.
      intros ctx x y Hnz.
      unfold contextual_div. rewrite (safe_div_correct x y Hnz).
      now rewrite boundary_handle_conservative.
    Qed.

    Theorem boundary_on_zero :
      forall x y, h y = 0 -> relational_boundary x y = RS_Boundary.
    Proof.
      intros x y Hy. unfold relational_boundary. rewrite Hy.
      destruct (Rlt_dec 0 0); [exfalso; lra|].
      destruct (Rgt_dec 0 0); [exfalso; lra|].
      reflexivity.
    Qed.

    Theorem detector_nonzero_is_related :
      forall x y, h y <> 0 -> relational_boundary x y = RS_Related.
    Proof.
      intros x y Hnz. unfold relational_boundary.
      destruct (Rlt_dec (h y) 0) as [Hlt|Hnlt]; [reflexivity|].
      destruct (Rgt_dec (h y) 0) as [Hgt|Hngt]; [reflexivity|].
      exfalso; apply Hnz; lra.
    Qed.

    Theorem contextual_space_maps_boundary_to_infty :
      forall x y, h y = 0 -> contextual_div RC_Space x y = Pinfty.
    Proof.
      intros x y Hy. unfold contextual_div, safe_div, boundary_handle.
      rewrite Hy. destruct (Req_EM_T 0 0); [|congruence]. reflexivity.
    Qed.

    Theorem contextual_time_maps_boundary_to_zero :
      forall x y, h y = 0 -> contextual_div RC_Time x y = Finite 0.
    Proof.
      intros x y Hy. unfold contextual_div, safe_div, boundary_handle.
      rewrite Hy. destruct (Req_EM_T 0 0); [|congruence]. reflexivity.
    Qed.

    Theorem contextual_info_maps_boundary_to_NaN :
      forall x y, h y = 0 -> contextual_div RC_Info x y = NaN.
    Proof.
      intros x y Hy. unfold contextual_div, safe_div, boundary_handle.
      rewrite Hy. destruct (Req_EM_T 0 0); [|congruence]. reflexivity.
    Qed.

  End Boundary.

End BoundaryCore.


(* === Module: Adapters (on top of BoundaryCore) === *)
Require Import Reals Psatz.
Open Scope R_scope.

From Coq Require Import Logic.Decidable.


Module Adapters.

  (* Re-export names for convenience *)
  Export BoundaryCore.

  Section Ergonomics.
    Variables (X Y : Type) (g : X -> R) (h : Y -> R).

    (* Notations *)
    Infix "÷?" := (safe_div X Y g h) (at level 40, left associativity).
    (* contextual_div is total, takes a ctx *)
    Notation "⟦ x / y ⟧[ ctx ]" :=
      (contextual_div X Y g h ctx x y)
      (at level 41, no associativity).

    (* A simple interpretation from ExtR to R per context *)
    Definition interpret_ExtR (ctx : RelCtx) (z : ExtR) : R :=
      match z with
      | Finite r => r
      | Pinfty   => match ctx with RC_Space => 1 | _ => 0 end
      | Minfty   => match ctx with RC_Space => -1 | _ => 0 end
      | NaN      => 0
      end.

    Lemma interpret_agrees_when_nonzero :
      forall ctx x y, h y <> 0 ->
        interpret_ExtR ctx (contextual_div X Y g h ctx x y) = g x / h y.
    Proof.
      intros. unfold interpret_ExtR.
      rewrite (contextual_div_agrees_with_classical X Y g h ctx x y H).
      reflexivity.
    Qed.
  End Ergonomics.

  (* A tiny runnable demo with concrete g,h *)
  Section Demo.
    Definition X := R. Definition Y := R.
    Definition g (x : R) := 2 * x + 1.
    Definition h (y : R) := y - 3.

    Example demo_nonzero :
      contextual_div X Y g h RC_Space 0 5 = Finite (g 0 / h 5).
    Proof.
      unfold h; cbn. assert (Hnz : h 5 <> 0) by (cbv; lra).
      now apply (contextual_div_agrees_with_classical X Y g h RC_Space 0 5).
    Qed.

Example demo_boundary_space :
  contextual_div X Y g h RC_Space 7 3 = Pinfty.
Proof.
  apply (contextual_space_maps_boundary_to_infty X Y g h 7 3).
  unfold h; lra.  (* shows: h 3 = 3 - 3 = 0 *)
Qed.

Example demo_boundary_time :
  contextual_div X Y g h RC_Time 7 3 = Finite 0.
Proof.
  apply (contextual_time_maps_boundary_to_zero X Y g h 7 3).
  unfold h; lra.
Qed.

Example demo_boundary_info :
  contextual_div X Y g h RC_Info 7 3 = NaN.
Proof.
  apply (contextual_info_maps_boundary_to_NaN X Y g h 7 3).
  unfold h; lra.
Qed.

  End Demo.

End Adapters.

(* === Module: MeadowCore === *)
Require Import Reals.
Open Scope R_scope.

Module MeadowCore.

  Class Meadow (M : Type) := {
    mz   : M;                        (* 0 *)
    mo   : M;                        (* 1 *)
    madd : M -> M -> M;
    mmul : M -> M -> M;
    inv  : M -> M;                   (* total inverse *)

    (* Ring-ish laws (abbreviated interface) *)
    add_comm   : forall a b, madd a b = madd b a;
    add_assoc  : forall a b c, madd a (madd b c) = madd (madd a b) c;
    add_zero_l : forall a, madd mz a = a;
    add_opp_l  : forall a, exists a', madd a' a = mz;

    mul_comm   : forall a b, mmul a b = mmul b a;
    mul_assoc  : forall a b c, mmul a (mmul b c) = mmul (mmul a b) c;
    mul_one_l  : forall a, mmul mo a = a;

    mul_distr_l : forall a b c, mmul a (madd b c) = madd (mmul a b) (mmul a c);

    (* Meadow axioms *)
    inv_involutive : forall a, inv (inv a) = a;
    inv_mul        : forall a b, inv (mmul a b) = mmul (inv a) (inv b);
    inv_zero       : inv mz = mz;

    (* Restricted inverse law: away from 0, a * inv a = 1 *)
    rinv_law       : forall a, a <> mz -> mmul a (inv a) = mo
  }.

  Section MeadowOps.
    Context {M : Type} `{Meadow M}.

    (* Division via total inverse *)
    Definition div (a b : M) : M := mmul a (inv b).

    Infix "⊕" := madd (at level 50, left associativity).
    Infix "⊗" := mmul (at level 40, left associativity).

(* Right identity, derived from left identity + commutativity *)
Lemma mul_one_r : forall a, a ⊗ mo = a.
Proof.
  intro a. rewrite (mul_comm a mo). apply mul_one_l.
Qed.

(* Cancellation on the right when denominator ≠ 0 *)
Lemma cancel_right_nonzero :
  forall a b, b <> mz -> (a ⊗ inv b) ⊗ b = a.
Proof.
  intros a b Hb.
  (* Reassociate to expose inv b ⊗ b *)
  rewrite <- (mul_assoc a (inv b) b).
  (* Commute inner factors to get b ⊗ inv b *)
  rewrite (mul_comm (inv b) b).
  (* Use the restricted inverse law: b ⊗ inv b = mo *)
  rewrite (rinv_law b Hb).
  (* Simplify with right identity *)
  apply mul_one_r.
Qed.


  End MeadowOps.

End MeadowCore.

(* === Module: BridgeRwrap (totalized meadow over R) === *)
Require Import Reals Psatz Program.
Open Scope R_scope.

Module BridgeRwrap.
  Import MeadowCore.

  (* Wrap R so we can give a Meadow instance without overlapping instances *)
  Record Rwrap := { unR : R }.

  (* ---------- Small real-lemmas we’ll use ---------- *)

  Lemma Rinv_neq_0 (x : R) : x <> 0 -> / x <> 0.
  Proof. apply Rinv_neq_0_compat. Qed.

  Lemma Rmult_eq0_destr (a b : R) :
    a * b = 0 -> a = 0 \/ b = 0.
  Proof. apply Rmult_integral. Qed.

  Lemma Rmult_neq0_intro (a b : R) :
    a <> 0 -> b <> 0 -> a * b <> 0.
  Proof. intros Ha Hb H; apply Rmult_integral in H; tauto. Qed.

  (* ---------- Totalized inverse: 0^{-1} := 0, else /x ---------- *)

  Definition rinv_total (x : R) : R :=
    if Req_EM_T x 0 then 0 else / x.

  Lemma rinv_total_zero : rinv_total 0 = 0.
  Proof.
    unfold rinv_total.
    destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|contradiction].
  Qed.

  Lemma rinv_total_nonzero x : x <> 0 -> rinv_total x = / x.
  Proof.
    intros Hx. unfold rinv_total.
    destruct (Req_EM_T x 0) as [Hx0|Hx0]; [subst; tauto|reflexivity].
  Qed.

  Lemma rinv_total_involutive x :
    rinv_total (rinv_total x) = x.
  Proof.
    destruct (Req_EM_T x 0) as [->|Hx].
    - (* x = 0 *)
      repeat rewrite rinv_total_zero; reflexivity.
    - (* x <> 0 *)
      rewrite (rinv_total_nonzero _ Hx).
      assert (/ x <> 0) by (apply Rinv_neq_0; exact Hx).
      rewrite (rinv_total_nonzero _ H).
      field_simplify; [reflexivity|assumption].
  Qed.

Lemma rinv_total_mult (a b : R) :
  rinv_total (a * b) = rinv_total a * rinv_total b.
Proof.
  unfold rinv_total.
  (* First split on whether a*b = 0 *)
  destruct (Req_EM_T (a*b) 0) as [Hab|Hnab]; cbn.
  - (* a*b = 0 *)
    destruct (Req_EM_T a 0) as [Ha|Ha]; cbn.
    + (* a = 0 *)
      destruct (Req_EM_T b 0) as [Hb|Hb]; cbn.
      * (* b = 0 *) now rewrite Rmult_0_l.
      * (* b <> 0 *) now rewrite Rmult_0_l.
    + (* a <> 0 *)
      destruct (Req_EM_T b 0) as [Hb|Hb]; cbn.
      * (* b = 0 *) now rewrite Rmult_0_r.
      * (* a <> 0, b <> 0 but a*b=0 — impossible *)
        exfalso. apply Rmult_integral in Hab. tauto.
  - (* a*b <> 0 *)
    destruct (Req_EM_T a 0) as [Ha|Ha]; cbn.
    + (* a = 0 contradicts a*b <> 0 *)
      exfalso. apply Hnab. subst a. now rewrite Rmult_0_l.
    + destruct (Req_EM_T b 0) as [Hb|Hb]; cbn.
      * (* b = 0 contradicts a*b <> 0 *)
        exfalso. apply Hnab. subst b. now rewrite Rmult_0_r.
      * (* both nonzero *)
        now rewrite Rinv_mult_distr by (assumption || assumption).
Qed.


  Lemma rinv_total_rinv a :
    a <> 0 -> a * rinv_total a = 1.
  Proof. intro Ha; rewrite (rinv_total_nonzero _ Ha); field; exact Ha. Qed.

  (* ---------- Obligation-solving helper ---------- *)

  Ltac crush_Rwrap :=
    repeat match goal with
           | x : Rwrap |- _ => destruct x
           end;
    cbn; try lra; try nra.

  (* Use a local Obligation Tactic so the easy field laws solve themselves *)
  Local Obligation Tactic := try (intros; crush_Rwrap).


Require Import Reals Psatz Program.
Open Scope R_scope.

(* ---------- Minimal Meadow class ---------- *)
Class Meadow (M : Type) := {
  mz   : M;                        (* 0 *)
  mo   : M;                        (* 1 *)
  madd : M -> M -> M;
  mmul : M -> M -> M;
  inv  : M -> M;                   (* total inverse *)

  (* Ring-ish laws (abbreviated interface) *)
  add_comm   : forall a b, madd a b = madd b a;
  add_assoc  : forall a b c, madd a (madd b c) = madd (madd a b) c;
  add_zero_l : forall a, madd mz a = a;
  add_opp_l  : forall a, exists a', madd a' a = mz;

  mul_comm   : forall a b, mmul a b = mmul b a;
  mul_assoc  : forall a b c, mmul a (mmul b c) = mmul (mmul a b) c;
  mul_one_l  : forall a, mmul mo a = a;

  mul_distr_l : forall a b c, mmul a (madd b c) = madd (mmul a b) (mmul a c);

  (* Meadow axioms *)
  inv_involutive : forall a, inv (inv a) = a;
  inv_mul        : forall a b, inv (mmul a b) = mmul (inv a) (inv b);
  inv_zero       : inv mz = mz;

  (* Restricted inverse law: away from 0, a * inv a = 1 *)
  rinv_law       : forall a, a <> mz -> mmul a (inv a) = mo
}.

(* ---------- R wrapper ---------- *)
Module BridgeRwrap.

  Record Rwrap := { unR : R }.

  (* totalized inverse on R: 0^{-1} := 0, else /x *)
  Definition rinv_total (x : R) : R :=
    if Req_EM_T x 0 then 0 else / x.

  Lemma Rinv_neq_0 (x : R) : x <> 0 -> / x <> 0.
  Proof. apply Rinv_neq_0_compat. Qed.

  Lemma rinv_total_zero : rinv_total 0 = 0.
  Proof.
    unfold rinv_total.
    destruct (Req_EM_T 0 0) as [_|H]; [reflexivity|contradiction].
  Qed.

  Lemma rinv_total_nonzero x : x <> 0 -> rinv_total x = / x.
  Proof.
    intros Hx. unfold rinv_total.
    destruct (Req_EM_T x 0) as [Hx0|Hx0]; [subst; tauto|reflexivity].
  Qed.

  Lemma rinv_total_involutive x :
    rinv_total (rinv_total x) = x.
  Proof.
    destruct (Req_EM_T x 0) as [->|Hx].
    - repeat rewrite rinv_total_zero; reflexivity.
    - rewrite (rinv_total_nonzero _ Hx).
      assert (/ x <> 0) by (apply Rinv_neq_0; exact Hx).
      rewrite (rinv_total_nonzero _ H).
      field_simplify; [reflexivity|assumption].
  Qed.

  Lemma rinv_total_mult (a b : R) :
    rinv_total (a * b) = rinv_total a * rinv_total b.
  Proof.
    unfold rinv_total.
    (* Case on a*b first *)
    destruct (Req_EM_T (a*b) 0) as [Hab|Hnab]; cbn.
    - (* a*b = 0 *)
      destruct (Req_EM_T a 0) as [Ha|Ha]; cbn.
      + destruct (Req_EM_T b 0) as [Hb|Hb]; cbn; now rewrite Rmult_0_l.
      + destruct (Req_EM_T b 0) as [Hb|Hb]; cbn.
        * now rewrite Rmult_0_r.
        * exfalso. apply Rmult_integral in Hab. tauto.
    - (* a*b <> 0 *)
      destruct (Req_EM_T a 0) as [Ha|Ha]; cbn.
      + exfalso. apply Hnab. subst a. now rewrite Rmult_0_l.
      + destruct (Req_EM_T b 0) as [Hb|Hb]; cbn.
        * exfalso. apply Hnab. subst b. now rewrite Rmult_0_r.
        * now rewrite Rinv_mult_distr by (assumption || assumption).
  Qed.

  Lemma rinv_total_rinv a :
    a <> 0 -> a * rinv_total a = 1.
  Proof. intro Ha; rewrite (rinv_total_nonzero _ Ha); field; exact Ha. Qed.

(* ---------- Discharge the Meadow obligations in the class-field order ---------- *)

Program Instance Rwrap_Meadow : Meadow Rwrap := {
  mz   := {| unR := 0 |};
  mo   := {| unR := 1 |};
  madd a b := {| unR := unR a + unR b |};
  mmul a b := {| unR := unR a * unR b |};
  inv  a   := {| unR := rinv_total (unR a) |}
}.

(* 1. add_comm *)
Next Obligation.
  destruct a as [x], b as [y]. cbn.
  rewrite Rplus_comm. reflexivity.
Qed.

(* 2. add_assoc *)
Next Obligation.
  destruct a as [x], b as [y], c as [z]. cbn.
  rewrite Rplus_assoc. reflexivity.
Qed.

(* 3. add_zero_l *)
Next Obligation.
  destruct a as [x]. cbn.
  rewrite Rplus_0_l. reflexivity.
Qed.

(* 4. add_opp_l *)
Next Obligation.
  destruct a as [x].
  exists {| unR := - x |}. cbn.
  rewrite Rplus_opp_l. reflexivity.
Qed.

(* 5. mul_comm *)
Next Obligation.
  destruct a as [x], b as [y]. cbn.
  rewrite Rmult_comm. reflexivity.
Qed.

(* 6. mul_assoc *)
Next Obligation.
  destruct a as [x], b as [y], c as [z]. cbn.
  rewrite Rmult_assoc. reflexivity.
Qed.

(* 7. mul_one_l *)
Next Obligation.
  destruct a as [x]. cbn.
  rewrite Rmult_1_l. reflexivity.
Qed.

(* 8. mul_distr_l *)
Next Obligation.
  destruct a as [x], b as [y], c as [z]. cbn.
  rewrite Rmult_plus_distr_l. reflexivity.
Qed.

(* 9. inv_involutive *)
Next Obligation.
  destruct a as [x]. cbn.
  f_equal.                       (* reduce record equality to field equality *)
  apply rinv_total_involutive.
Qed.

(* 10. inv_mul *)
Next Obligation.
  destruct a as [x], b as [y]. cbn.
  f_equal.                       (* reduce record equality to field equality *)
  apply rinv_total_mult.
Qed.

(* 11. inv_zero *)
Next Obligation.
  cbn. f_equal. apply rinv_total_zero.
Qed.


(* 12. rinv_law: a ≠ mz -> a * inv a = mo *)
Next Obligation.
  destruct a as [x]. cbn.
  (* hypothesis is already present as H : {| unR := x |} <> {| unR := 0 |} *)
  assert (Hx : x <> 0).
  { intro H0. apply H. now f_equal. }

  (* reduce record equality to field equality *)
  f_equal.
  rewrite (rinv_total_nonzero _ Hx).
  field; exact Hx.
Qed.




End BridgeRwrap.







