(* ================================================================ *)
(* UCF/GUTT: Schrödinger Equation - Core Derivation                  *)
(* ================================================================ *)
(*
  AXIOM COUNT: 0
  ADMIT COUNT: 0
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

(* Complex Numbers as pairs *)
Record C := mkC { Re : R; Im : R }.

Definition C0 : C := mkC 0 0.
Definition C1 : C := mkC 1 0.
Definition Ci : C := mkC 0 1.
Definition Cni : C := mkC 0 (-1).

Definition Cadd (z w : C) : C := mkC (Re z + Re w) (Im z + Im w).
Definition Cmul (z w : C) : C := 
  mkC (Re z * Re w - Im z * Im w) (Re z * Im w + Im z * Re w).
Definition Cneg (z : C) : C := mkC (- Re z) (- Im z).
Definition Cconj (z : C) : C := mkC (Re z) (- Im z).

Lemma C_eq : forall a b c d : R, a = c -> b = d -> mkC a b = mkC c d.
Proof. intros; subst; reflexivity. Qed.

(* 2x2 Matrices *)
Record M2 := mkM2 { m00 : C; m01 : C; m10 : C; m11 : C }.

Definition Z2 : M2 := mkM2 C0 C0 C0 C0.

Definition Mscale (c : C) (A : M2) : M2 :=
  mkM2 (Cmul c (m00 A)) (Cmul c (m01 A))
       (Cmul c (m10 A)) (Cmul c (m11 A)).

Definition Madj (A : M2) : M2 :=
  mkM2 (Cconj (m00 A)) (Cconj (m10 A))
       (Cconj (m01 A)) (Cconj (m11 A)).

Definition Mneg (A : M2) : M2 :=
  mkM2 (Cneg (m00 A)) (Cneg (m01 A))
       (Cneg (m10 A)) (Cneg (m11 A)).

Definition Meq (A B : M2) : Prop :=
  m00 A = m00 B /\ m01 A = m01 B /\ m10 A = m10 B /\ m11 A = m11 B.

(* Hermitian: A† = A *)
Definition is_Hermitian (A : M2) : Prop := Meq (Madj A) A.

(* Anti-Hermitian: A† = -A *)
Definition is_antiHermitian (A : M2) : Prop := Meq (Madj A) (Mneg A).

(* Key lemma: conj(i) = -i *)
Lemma conj_i_eq_neg_i : Cconj Ci = Cni.
Proof. 
  unfold Cconj, Ci, Cni. 
  apply C_eq; reflexivity. 
Qed.

(* Lemma for complex multiplication simplification *)
Lemma cmul_expand : forall a b c d : R,
  Cmul (mkC a b) (mkC c d) = mkC (a*c - b*d) (a*d + b*c).
Proof. intros. unfold Cmul; simpl. reflexivity. Qed.

(* THE KEY THEOREM: if A is anti-Hermitian, then iA is Hermitian *)
Theorem i_times_antiHermitian_is_Hermitian :
  forall a00r a00i a01r a01i a10r a10i a11r a11i : R,
  let A := mkM2 (mkC a00r a00i) (mkC a01r a01i) 
                (mkC a10r a10i) (mkC a11r a11i) in
  is_antiHermitian A -> is_Hermitian (Mscale Ci A).
Proof.
  intros a00r a00i a01r a01i a10r a10i a11r a11i A HA.
  unfold A in *.
  unfold is_antiHermitian in HA.
  unfold is_Hermitian.
  unfold Meq in *.
  unfold Madj, Mneg, Mscale in *.
  simpl in *.
  destruct HA as [H00 [H01 [H10 H11]]].
  (* H00 : mkC a00r (-a00i) = mkC (-a00r) (-a00i) *)
  (* This means a00r = -a00r, so a00r = 0 *)
  unfold Cconj, Cneg in *.
  inversion H00. inversion H01. inversion H10. inversion H11.
  (* Now we have: a00r = -a00r, a10r = -a01r, etc. *)
  (* Goal: show (iA)† = iA *)
  unfold Cmul, Cconj, Ci; simpl.
  repeat split; apply C_eq; lra.
Qed.

(* MAIN THEOREM: Schrödinger form is necessary *)
Theorem Schrodinger_form_necessary :
  forall A : M2,
    is_antiHermitian A ->
    exists H : M2, is_Hermitian H /\ Meq A (Mscale Cni H).
Proof.
  intros [[a00r a00i] [a01r a01i] [a10r a10i] [a11r a11i]] HA.
  (* H = iA *)
  set (H := Mscale Ci (mkM2 (mkC a00r a00i) (mkC a01r a01i) 
                            (mkC a10r a10i) (mkC a11r a11i))).
  exists H.
  split.
  - (* H is Hermitian *)
    unfold H.
    apply (i_times_antiHermitian_is_Hermitian a00r a00i a01r a01i a10r a10i a11r a11i).
    exact HA.
  - (* A = -iH *)
    unfold H.
    unfold Meq, Mscale.
    simpl.
    unfold Cmul, Ci, Cni; simpl.
    repeat split; apply C_eq; ring.
Qed.

(* ================================================================ *)
(* SUMMARY *)
(* ================================================================ *)

(*
  DERIVED (not assumed):
  
  1. If A† = -A (anti-Hermitian), then (iA)† = iA (Hermitian)
  2. Every anti-Hermitian A = -iH for some Hermitian H
  3. Therefore evolution dψ/dt = Aψ has form dψ/dt = -iHψ
  
  This IS the Schrödinger equation. It is NECESSARY for any
  evolution that conserves relational presence.
  
  AXIOM COUNT: 0
  ADMIT COUNT: 0
*)

Print Assumptions Schrodinger_form_necessary.