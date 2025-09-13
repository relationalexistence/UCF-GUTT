(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

(*
  UCF_GUTT_Contains_Alena_With_Discrete_Conservation.v
  =====================================================

  Purpose

  -------

  A self-contained Coq note that (i) formalizes the δ-kernel containment of the

  Alena Tensor inside a UCF/GUTT relational induction (A1–A4), and (ii) provides

  both a degenerate and a non-degenerate discrete conservation witness (A5).

  All entities are Module-scoped to avoid name clashes.

  Build: Coq ≥ 8.12, no external libs

  > coqc UCF_GUTT_Contains_Alena_With_Discrete_Conservation.v

*)







From Coq Require Import Reals FunctionalExtensionality.



Local Open Scope R_scope.







(* ========================================== *)



(* Module 1 — AbstractCore (δ-kernel, A1–A4)  *)



(* ========================================== *)



Module AbstractCore.



  Section Core.



    (* Abstract scalar field with ring-like ops. *)



    Variable K : Type.



    Variable Kzero Kone : K.



    Variable Kadd Kmul Ksub : K -> K -> K.



    Variable Kopp Kinv : K -> K.



    Infix "+" := Kadd.



    Infix "*" := Kmul.



    Infix "-" := Ksub.



    Notation "- x" := (Kopp x).







    (* Indices and tensors *)



    Variable Idx : Type.



    Definition V1 := Idx -> K.



    Definition T2 := Idx -> Idx -> K.







    (* Metric and inverse *)



    Variable g ginv : T2.







    (* Antisymmetric field F; symmetric g^{-1} *)



    Variable F : T2.



    Hypothesis F_skew   : forall i j, F i j = Kopp (F j i).



    Hypothesis ginv_sym : forall i j, ginv i j = ginv j i.







    (* Pointwise ops *)



    Variable outer : V1 -> V1 -> T2.



    Variable scale : K -> T2 -> T2.



    Variable add2  : T2 -> T2 -> T2.



    Variable sub2  : T2 -> T2 -> T2.



    Infix "⊕" := add2  (at level 40, left associativity).



    Infix "⊖" := sub2  (at level 40, left associativity).







    (* Abstract double-sum over Idx×Idx *)



    Variable sumII : (Idx -> Idx -> K) -> K.







    (* Contractions with g^{-1} *)



    Definition contract (A B : T2) : T2 :=



      fun i j => sumII (fun mu nu => A i mu * ginv mu nu * B nu j).







    Definition dcontract2 (X : T2) : K :=



      sumII (fun rho sigma => X rho sigma *



             sumII (fun lam kap => ginv rho lam * ginv sigma kap * X lam kap)).







    Definition trace_ginv (X : T2) : K :=



      sumII (fun mu nu => ginv mu nu * X mu nu).







    (* Positive normalizer *)



    Variable normpos : T2 -> K.



    Hypothesis normpos_pos : forall X, normpos X <> Kzero.







    Definition normalize (X : T2) : T2 :=



      fun i j => (Kinv (normpos X)) * X i j.







    (* Kernel application *)



    Variable ApplyK : T2 -> T2 -> T2 -> T2.



    Definition H_of (Kker : T2) (F0 : T2) : T2 := normalize (ApplyK Kker F0 F0).







    (* δ-kernel property *)



    Definition DeltaKernel (Kδ : T2) : Prop :=



      forall A B i j,



        ApplyK Kδ A B i j = sumII (fun mu nu => A i mu * ginv mu nu * B nu j).







    (* δ-collapse lemma *)



    Lemma delta_collapse :



      forall Kδ, DeltaKernel Kδ -> H_of Kδ F = normalize (contract F F).



    Proof.



      intros Kδ Hδ. unfold H_of.



      assert (core : ApplyK Kδ F F = contract F F).



      { extensionality i; extensionality j. unfold contract. rewrite Hδ. reflexivity. }



      now rewrite core.



    Qed.







    (* Derived canonical objects *)



    Definition C : T2 := contract F F.



    Definition h : T2 := normalize C.







    (* Scalars & stress–energy *)



    Variable K_quarter : K.            (* 1/4 *)



    Definition xi_inv : K := K_quarter * (trace_ginv h).



    Definition xi     : K := Kinv xi_inv.







    Variable mu0 : K.                  (* vacuum permeability param *)



    Definition Four : K := Kadd Kone (Kadd Kone (Kadd Kone Kone)).



    Definition lambda_const : K := Kinv (Four * mu0).







    Definition F2 : K := dcontract2 C.



    Definition Lambda_rho : K := lambda_const * F2.







    Variable Uvec : V1.



    Variable rho c2 : K.







    Definition T_alena : T2 :=



      let matter   := scale rho (outer Uvec Uvec) in



      let pressure := (c2 * rho) + Lambda_rho in



      let geom     := g ⊖ (scale xi h) in



      matter ⊖ (scale pressure geom).







    Definition T_ucf (Kδ : T2) : T2 :=



      let matter   := scale rho (outer Uvec Uvec) in



      let pressure := (c2 * rho) + Lambda_rho in



      let Hloc     := H_of Kδ F in



      let geom     := g ⊖ (scale xi Hloc) in



      matter ⊖ (scale pressure geom).







    (* === Theorems A1–A4 (δ-local containment) === *)



    Theorem A1_induced_metric :



      forall Kδ, DeltaKernel Kδ -> H_of Kδ F = h.



    Proof. intros Kδ HK. unfold h. now apply delta_collapse. Qed.







    Theorem A2_coupling_scalar :



      forall Kδ, DeltaKernel Kδ ->



        xi_inv = K_quarter * (trace_ginv (H_of Kδ F)).



    Proof. intros Kδ HK. unfold xi_inv. now rewrite (A1_induced_metric Kδ HK). Qed.







    Theorem A3_scalar_invariant_defn :



      Lambda_rho = lambda_const * F2.



    Proof. reflexivity. Qed.







    Theorem A4_stress_energy :



      forall Kδ, DeltaKernel Kδ -> T_ucf Kδ = T_alena.



    Proof. intros Kδ HK. unfold T_ucf, T_alena. now rewrite (A1_induced_metric Kδ HK). Qed.



  End Core.



End AbstractCore.











(* ============================================ *)



(* Module 2 — Concrete4D (ℝ, Minkowski, A1–A4)  *)



(* ============================================ *)



Module Concrete4D.



  Inductive Ix := I0 | I1 | I2 | I3.







  Definition sumI  (f : Ix -> R) : R := f I0 + f I1 + f I2 + f I3.



  Definition sumII (f : Ix -> Ix -> R) : R := sumI (fun i => sumI (fun j => f i j)).







  Definition V1 := Ix -> R.



  Definition T2 := Ix -> Ix -> R.







  Definition outer (u v : V1) : T2 := fun i j => u i * v j.



  Definition scale (a : R) (X : T2) : T2 := fun i j => a * X i j.



  Definition add2  (X Y : T2) : T2 := fun i j => X i j + Y i j.



  Definition sub2  (X Y : T2) : T2 := fun i j => X i j - Y i j.



  Infix "⊕" := add2  (at level 40).



  Infix "⊖" := sub2  (at level 40).







  Definition g : T2 := fun i j =>



    match i, j with



    | I0, I0 => -1 | I1, I1 => 1 | I2, I2 => 1 | I3, I3 => 1 | _, _ => 0 end.



  Definition ginv : T2 := g.







  Variable F : T2.



  Variable Uvec : V1.



  Variable mu0 c2 rho : R.







  Hypothesis F_skew   : forall i j, F i j = - F j i.



  Lemma ginv_sym  : forall i j, ginv i j = ginv j i.



  Proof. intros i j; destruct i, j; reflexivity. Qed.







  Definition contract (A B : T2) : T2 :=



    fun i j => sumII (fun mu nu => A i mu * ginv mu nu * B nu j).







  Definition dcontract2 (X : T2) : R :=



    sumII (fun rho' sigma => X rho' sigma *



      sumII (fun lam kap => ginv rho' lam * ginv sigma kap * X lam kap)).







  Definition trace_ginv (X : T2) : R := sumII (fun mu nu => ginv mu nu * X mu nu).







  Definition denom (X : T2) : R := sqrt (1 + Rsqr (dcontract2 X)).



  Lemma denom_pos : forall X, denom X > 0.



  Proof.



    intro X. unfold denom. apply sqrt_lt_R0.



    apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply Rle_0_sqr].



  Qed.







  Definition normalize (X : T2) : T2 := fun i j => X i j / denom X.







  Definition ApplyK (K : T2) (A B : T2) : T2 :=



    fun i j => sumII (fun mu nu => A i mu * K mu nu * B nu j).







  Definition Kdelta : T2 := ginv.



  Lemma DeltaKernel_concrete : forall A B i j,



      ApplyK Kdelta A B i j = sumII (fun mu nu => A i mu * ginv mu nu * B nu j).



  Proof. reflexivity. Qed.







  Definition C : T2 := contract F F.



  Definition h : T2 := normalize C.



  Definition H : T2 := normalize (ApplyK Kdelta F F).







  Definition k_quarter : R := /4.



  Definition xi_inv : R := k_quarter * (trace_ginv h).



  Definition xi     : R := / xi_inv.







  Definition F2 : R := dcontract2 C.



  Definition lambda_const : R := / (4 * mu0).



  Definition Lambda_rho : R := lambda_const * F2.







  Definition T_ucf : T2 :=



    let matter   := scale rho (outer Uvec Uvec) in



    let pressure := (c2 * rho) + Lambda_rho in



    let geom     := g ⊖ (scale xi H) in



    matter ⊖ (scale pressure geom).







  Definition T_alena : T2 :=



    let matter   := scale rho (outer Uvec Uvec) in



    let pressure := (c2 * rho) + Lambda_rho in



    let geom     := g ⊖ (scale xi h) in



    matter ⊖ (scale pressure geom).







  Theorem A1_induced_metric_4D : H = h.



  Proof. unfold H, h, C, Kdelta, ApplyK, contract, normalize; reflexivity. Qed.







  Theorem A2_coupling_scalar_4D :



    xi_inv = k_quarter * (trace_ginv H).



  Proof. unfold xi_inv. now rewrite A1_induced_metric_4D. Qed.







  Theorem A3_scalar_invariant_defn_4D :



    Lambda_rho = lambda_const * F2.



  Proof. reflexivity. Qed.







  Theorem A4_stress_energy_4D : T_ucf = T_alena.



  Proof. unfold T_ucf, T_alena. now rewrite A1_induced_metric_4D. Qed.



End Concrete4D.











(* ===================================================== *)



(* Module 3 — DiscreteConservation (degenerate A5)       *)



(* ===================================================== *)



Module DiscreteConservation.



  Inductive Ix := I0 | I1 | I2 | I3.



  Definition V1 := Ix -> R.



  Definition T2 := Ix -> Ix -> R.







  Definition Dc (_ : Ix) (X : T2) : T2 := fun _ _ => 0.







  Definition sumI (f : Ix -> R) : R := f I0 + f I1 + f I2 + f I3.







  Definition Div (T : T2) : V1 := fun alpha => sumI (fun beta => Dc beta T alpha beta).







  Theorem A5_conservation_degenerate : forall T alpha, Div T alpha = 0.



  Proof. intros T alpha. unfold Div, Dc, sumI. repeat rewrite Rplus_0_l; reflexivity. Qed.



End DiscreteConservation.











(* ===================================================== *)



(* Module 4 — NonlocalHooks (ε scaffolding)              *)



(* ===================================================== *)



Module NonlocalHooks.



  Parameter Eps : Type.



  Parameter eps0 : Eps.



  Parameter normE : Eps -> R.







  Inductive Ix := I0 | I1 | I2 | I3.



  Definition T2 := Ix -> Ix -> R.



  Parameter K_of_eps : Eps -> T2.







  Parameter ginv : T2.



  Axiom K_eps0_is_ginv : K_of_eps eps0 = ginv.







  Definition phase_shift (e:Eps) : R := normE e.



  Definition birefringence (e:Eps) : R := (normE e) / 2.



End NonlocalHooks.











(* ===================================================== *)



(* Module 5 — DiscreteConservationFD (non-degenerate A5) *)



(*   Forward-difference on a tiny 4D lattice of positions *)



(*   and conservation for position-independent fields     *)



(* ===================================================== *)



Module DiscreteConservationFD.



  Inductive Ix := I0 | I1 | I2 | I3.







  Inductive Bit := Z0 | Z1.



  Definition Pos := Ix -> Bit.







  Definition Ix_eq_dec (x y:Ix) : {x=y}+{x<>y}. Proof. decide equality. Qed.







  Definition flip (b:Ix) (p:Pos) : Pos :=



    fun k => if Ix_eq_dec k b then (match p k with Z0 => Z1 | Z1 => Z0 end) else p k.







  Definition T2F := Pos -> Ix -> Ix -> R.



  Definition V1F := Pos -> Ix -> R.



  Definition SF  := Pos -> R.







  Definition DbT (b:Ix) (X:T2F) : T2F := fun p i j => X (flip b p) i j - X p i j.



  Definition DbV (b:Ix) (u:V1F) : V1F := fun p i => u (flip b p) i - u p i.







  Definition scaleC (a:R) (X:T2F)  : T2F := fun p i j => a * X p i j.



  Definition outerF (u v:V1F) : T2F := fun p i j => u p i * v p j.







  Definition sumI (f : Ix -> R) : R := f I0 + f I1 + f I2 + f I3.



  Definition Div (T:T2F) : Pos -> Ix -> R :=



    fun p alpha => sumI (fun beta => DbT beta T p alpha beta).







  Definition constV (u:V1F) : Prop := forall b p i, DbV b u p i = 0.



  Definition constT (X:T2F) : Prop := forall b p i j, DbT b X p i j = 0.







  (* Modern helper: x - y = 0 -> x = y *)



  Lemma minus0_eq : forall x y:R, x - y = 0 -> x = y.



  Proof. intros x y H. apply (Rminus_diag_uniq x y). exact H. Qed.







  Lemma DbT_outerF_const :



    forall b (u v:V1F),



      constV u -> constV v ->



      forall p i j, DbT b (outerF u v) p i j = 0.



  Proof.



    intros b u v Hu Hv p i j.



    unfold DbT, outerF, DbV, constV in *.



    specialize (Hu b p i). specialize (Hv b p j).



    apply minus0_eq in Hu. apply minus0_eq in Hv.



    rewrite Hu, Hv. change (u p i * v p j - u p i * v p j = 0).



    now rewrite Rminus_diag_eq.



  Qed.







  Variables (rho c2 xi : R).



  Variable  Uvec : V1F.



  Variable  g    : T2F.



  Variable  H    : T2F.







  Hypothesis Uvec_const : constV Uvec.



  Hypothesis g_const    : constT g.



  Hypothesis H_const    : constT H.







  Definition matter : T2F := fun p => scaleC rho (outerF Uvec Uvec) p.



  Definition pressure : R := (c2 * rho).



  Definition geom : T2F := fun p i j => g p i j - xi * H p i j.



  Definition Tfield : T2F := fun p i j => matter p i j - pressure * geom p i j.







  Lemma DbT_matter_zero : forall b p i j, DbT b matter p i j = 0.



  Proof.



    intros b p i j.



    unfold DbT, matter, scaleC, outerF.



    (* Use DbV = 0 -> equality of shifted and unshifted values *)



    pose proof (Uvec_const b p i) as Hui.



    pose proof (Uvec_const b p j) as Hvj.



    unfold DbV in Hui. unfold DbV in Hvj.



    apply minus0_eq in Hui. apply minus0_eq in Hvj.



    rewrite Hui, Hvj.



    change (rho * (Uvec p i * Uvec p j) - rho * (Uvec p i * Uvec p j) = 0).



    now rewrite Rminus_diag_eq.



  Qed.







  Lemma DbT_g_zero : forall b p i j, DbT b g p i j = 0.



  Proof. intros b p i j. apply g_const. Qed.







  Lemma DbT_H_zero : forall b p i j, DbT b H p i j = 0.



  Proof. intros b p i j. apply H_const. Qed.







  Lemma DbT_geom_zero : forall b p i j, DbT b geom p i j = 0.



  Proof.



    intros b p i j. unfold DbT, geom.



    (* Turn zero diffs into equalities, then rewrite *)



    pose proof (DbT_g_zero b p i j) as Hg0.



    pose proof (DbT_H_zero b p i j) as Hh0.



    unfold DbT in Hg0. unfold DbT in Hh0.



    apply minus0_eq in Hg0. apply minus0_eq in Hh0.



    rewrite Hg0, Hh0. now rewrite Rminus_diag_eq.



  Qed.







Theorem A5_conservation_fd_static : forall p alpha, Div Tfield p alpha = 0.



Proof.



  intros p alpha. unfold Div, sumI.



  (* For each beta, show the forward difference of Tfield vanishes *)



  assert (Hz : forall b, DbT b Tfield p alpha b = 0).



  { intro b.



    (* Unfold the definitions to expose the structure to the rewrite tactic *)



    unfold Tfield, DbT.







    (* Convert the forward-difference lemmas into equality rewrite rules *)



    pose proof (DbT_matter_zero b p alpha b) as Hm.



    pose proof (DbT_geom_zero   b p alpha b) as Hg.



    unfold DbT in Hm, Hg.



    apply minus0_eq in Hm.



    apply minus0_eq in Hg.







    (* The goal is now:



       (matter (flip b p) alpha b - pressure * geom (flip b p) alpha b) -



       (matter p alpha b - pressure * geom p alpha b) = 0







       Rewrite using the equalities for matter and geom. *)



    rewrite Hm, Hg.







    (* The goal becomes (X - Y) - (X - Y) = 0, which is trivial. *)



    now apply Rminus_diag_eq.



  }



  (* The rest of the proof is unchanged and correct *)



  rewrite (Hz I0), (Hz I1), (Hz I2), (Hz I3).



  repeat rewrite Rplus_0_l. repeat rewrite Rplus_0_r. reflexivity.



Qed.







(* ================================================================ *)



(* Module 6 — DiscreteConservationFD_Var (position-dependent P)     *)



(*   Adds a discrete product rule and conservation with variable P   *)



(*   under a natural cancellation hypothesis.                        *)



(* ================================================================ *)



Module DiscreteConservationFD_Var.



  Inductive Ix := I0 | I1 | I2 | I3.



  Inductive Bit := Z0 | Z1.



  Definition Pos := Ix -> Bit.







  Definition Ix_eq_dec (x y:Ix) : {x=y}+{x<>y}. Proof. decide equality. Qed.



  Definition flip (b:Ix) (p:Pos) : Pos :=



    fun k => if Ix_eq_dec k b then (match p k with Z0 => Z1 | Z1 => Z0 end) else p k.







  (* Fields *)



  Definition T2F := Pos -> Ix -> Ix -> R.



  Definition V1F := Pos -> Ix -> R.



  Definition SF  := Pos -> R.







  (* Forward differences *)



  Definition DbT (b:Ix) (X:T2F) : T2F := fun p i j => X (flip b p) i j - X p i j.



  Definition DbV (b:Ix) (u:V1F) : V1F := fun p i => u (flip b p) i - u p i.



  Definition DbS (b:Ix) (s:SF)  : SF  := fun p   => s (flip b p) - s p.







  (* Algebra on tensors *)



  Definition scaleC (a:R) (X:T2F)  : T2F := fun p i j => a * X p i j.



  Definition scaleS (s:SF) (X:T2F) : T2F := fun p i j => s p * X p i j.



  Definition outerF (u v:V1F) : T2F := fun p i j => u p i * v p j.



  Definition sub2  (X Y:T2F) : T2F := fun p i j => X p i j - Y p i j.



  Infix "⊖" := sub2 (at level 40).







  (* Sum over second index (for divergence) *)



  Definition sumI (f : Ix -> R) : R := f I0 + f I1 + f I2 + f I3.



  Definition Div (T:T2F) : Pos -> Ix -> R :=



    fun p alpha => sumI (fun beta => DbT beta T p alpha beta).







  (* Helper: x - y = 0 -> x = y *)



  Lemma minus0_eq : forall x y:R, x - y = 0 -> x = y.



  Proof. intros x y H. apply (Rminus_diag_uniq x y). exact H. Qed.







  (* Linearity of forward diff over subtraction *)



  Lemma DbT_sub2 :



    forall b (X Y:T2F) p i j,



      DbT b (X ⊖ Y) p i j = DbT b X p i j - DbT b Y p i j.



  Proof. intros; unfold DbT, sub2; ring. Qed.







  (* Product rule for a scalar field times a tensor *)



  Lemma DbT_scaleS_product :



    forall (b:Ix) (s:SF) (X:T2F) p i j,



      DbT b (scaleS s X) p i j



      = (DbS b s p) * X p i j + s (flip b p) * (DbT b X p i j).



  Proof.



    intros b s X p i j.



    unfold DbT, scaleS, DbS.



    set (s1 := s (flip b p)).



    set (s0 := s p).



    set (x1 := X (flip b p) i j).



    set (x0 := X p i j).



    replace (s1 * x1 - s0 * x0) with (s1 * (x1 - x0) + (s1 - s0) * x0)



      by (unfold s1, s0, x1, x0; ring).



    ring.



  Qed.







  (* Ingredients (mirroring DiscreteConservationFD) *)



  Variables (rho c2 xi : R).



  Variable  Uvec : V1F.



  Variable  g    : T2F.



  Variable  H    : T2F.







  Definition constV (u:V1F) : Prop := forall b p i, DbV b u p i = 0.



  Definition constT (X:T2F) : Prop := forall b p i j, DbT b X p i j = 0.







  Hypothesis Uvec_const : constV Uvec.



  Hypothesis g_const    : constT g.



  Hypothesis H_const    : constT H.







  (* Build the same pieces as before *)



  Definition matter : T2F := fun p => scaleC rho (outerF Uvec Uvec) p.



  Definition geom   : T2F := fun p i j => g p i j - xi * H p i j.







  (* Zero-difference lemmas reused *)



  Lemma DbT_matter_zero : forall b p i j, DbT b matter p i j = 0.



  Proof.



    intros b p i j.



    unfold DbT, matter, scaleC, outerF.



    pose proof (Uvec_const b p i) as Hui.



    pose proof (Uvec_const b p j) as Hvj.



    unfold DbV in Hui, Hvj. apply minus0_eq in Hui. apply minus0_eq in Hvj.



    rewrite Hui, Hvj. now rewrite Rminus_diag_eq.



  Qed.







  Lemma DbT_g_zero : forall b p i j, DbT b g p i j = 0.



  Proof. intros b p i j. apply g_const. Qed.







  Lemma DbT_H_zero : forall b p i j, DbT b H p i j = 0.



  Proof. intros b p i j. apply H_const. Qed.







  Lemma DbT_geom_zero : forall b p i j, DbT b geom p i j = 0.



  Proof.



    intros b p i j. unfold DbT, geom.



    pose proof (DbT_g_zero b p i j) as Hg0.



    pose proof (DbT_H_zero b p i j) as Hh0.



    unfold DbT in Hg0, Hh0. apply minus0_eq in Hg0. apply minus0_eq in Hh0.



    rewrite Hg0, Hh0. now rewrite Rminus_diag_eq.



  Qed.







  (* New: variable pressure field *)



  Variable P : SF.







  (* Cancellation hypothesis: Σβ (∂β P) · geom_{αβ} = 0 *)



  Hypothesis pressure_geom_cancel :



    forall p alpha, sumI (fun beta => (DbS beta P p) * geom p alpha beta) = 0.







  (* Helper to pull outer negation through finite sum *)



  Lemma opp_sumI : forall f, - (sumI f) = sumI (fun b => - f b).



  Proof. intros f. unfold sumI; repeat rewrite Ropp_plus_distr; reflexivity. Qed.







  (* Full T with variable P *)



  Definition Tfield_var : T2F := matter ⊖ (scaleS P geom).







  Theorem A5_conservation_fd_var :



    forall p alpha, Div Tfield_var p alpha = 0.



  Proof.



    intros p alpha. unfold Div, Tfield_var, sub2.



    set (Sbeta := fun beta => DbT beta Tfield_var p alpha beta).







    (* Pointwise identity for the summand *)



    assert (Hpt : forall b, Sbeta b = - ((DbS b P p) * geom p alpha b)).



    { intro b. unfold Sbeta, Tfield_var.



      rewrite DbT_sub2.



      rewrite (DbT_matter_zero b p alpha b).



      rewrite (DbT_scaleS_product b P geom p alpha b).



      rewrite (DbT_geom_zero b p alpha b).



      rewrite Rmult_0_r, Rplus_0_r. ring. }







    (* Make the goal use Sbeta explicitly so the rewrite matches *)



    change (sumI (fun beta => Sbeta beta) = 0).







    (* Replace the summand with the pointwise form *)



    assert (Heq :



      (fun beta => Sbeta beta)



      = (fun beta => - ((DbS beta P p) * geom p alpha beta))).



    { extensionality beta. apply Hpt. }



    rewrite Heq.







    (* Pull - through the finite sum and cancel via the hypothesis *)



    rewrite <- opp_sumI.



    rewrite pressure_geom_cancel.



    now rewrite Ropp_0.



  Qed.



(* ================================================================ *)

(* Module 6a — DiscreteConservationFD_Var_Derived                    *)

(*   Derive the cancellation identity from two structural hyps.      *)

(* ================================================================ *)



Module DiscreteConservationFD_Var_Derived.



  Inductive Ix := I0 | I1 | I2 | I3.

  Inductive Bit := Z0 | Z1.

  Definition Pos := Ix -> Bit.



  Definition Ix_eq_dec (x y:Ix) : {x=y}+{x<>y}. Proof. decide equality. Qed.

  Definition flip (b:Ix) (p:Pos) : Pos :=

    fun k => if Ix_eq_dec k b then (match p k with Z0 => Z1 | Z1 => Z0 end) else p k.



  (* Fields *)

  Definition T2F := Pos -> Ix -> Ix -> R.

  Definition V1F := Pos -> Ix -> R.

  Definition SF  := Pos -> R.



  (* Forward differences *)

  Definition DbT (b:Ix) (X:T2F) : T2F := fun p i j => X (flip b p) i j - X p i j.

  Definition DbV (b:Ix) (u:V1F) : V1F := fun p i => u (flip b p) i - u p i.

  Definition DbS (b:Ix) (s:SF)  : SF  := fun p   => s (flip b p) - s p.



  (* Algebra on tensors *)

  Definition scaleC (a:R) (X:T2F)  : T2F := fun p i j => a * X p i j.

  Definition scaleS (s:SF) (X:T2F) : T2F := fun p i j => s p * X p i j.

  Definition outerF (u v:V1F) : T2F := fun p i j => u p i * v p j.

  Definition sub2  (X Y:T2F)  : T2F := fun p i j => X p i j - Y p i j.

  Infix "⊖" := sub2 (at level 40).



  (* Sum over second index (for divergence) *)

  Definition sumI (f : Ix -> R) : R := f I0 + f I1 + f I2 + f I3.

  Definition Div (T:T2F) : Pos -> Ix -> R :=

    fun p alpha => sumI (fun beta => DbT beta T p alpha beta).



  (* Small helpers *)

  Lemma minus0_eq : forall x y:R, x - y = 0 -> x = y.

  Proof. intros x y H. apply (Rminus_diag_uniq x y). exact H. Qed.



  Lemma DbT_sub2 :

    forall b (X Y:T2F) p i j,

      DbT b (X ⊖ Y) p i j = DbT b X p i j - DbT b Y p i j.

  Proof. intros; unfold DbT, sub2; ring. Qed.



  Lemma DbT_scaleS_product :

    forall (b:Ix) (s:SF) (X:T2F) p i j,

      DbT b (scaleS s X) p i j

      = (DbS b s p) * X p i j + s (flip b p) * (DbT b X p i j).

  Proof.

    intros b s X p i j.

    unfold DbT, scaleS, DbS.

    set (s1 := s (flip b p)).

    set (s0 := s p).

    set (x1 := X (flip b p) i j).

    set (x0 := X p i j).

    replace (s1 * x1 - s0 * x0) with (s1 * (x1 - x0) + (s1 - s0) * x0)

      by (unfold s1, s0, x1, x0; ring).

    ring.

  Qed.



  Lemma opp_sumI : forall f, - (sumI f) = sumI (fun b => - f b).

  Proof. intros f. unfold sumI; repeat rewrite Ropp_plus_distr; reflexivity. Qed.



  (* NEW: helpers to rewrite sums cleanly *)

  Lemma sumI_ext : forall f g, (forall b, f b = g b) -> sumI f = sumI g.

  Proof.

    intros f g Heq. unfold sumI.

    rewrite (Heq I0), (Heq I1), (Heq I2), (Heq I3). reflexivity.

  Qed.



  Lemma sumI_plus : forall f g,

    sumI (fun b => f b + g b) = sumI f + sumI g.

  Proof. intros f g. unfold sumI; ring. Qed.



  (* Ingredients (as before) *)

  Variables (rho c2 xi : R).

  Variable  Uvec : V1F.

  Variable  g    : T2F.

  Variable  H    : T2F.



  Definition constV (u:V1F) : Prop := forall b p i, DbV b u p i = 0.

  Definition constT (X:T2F) : Prop := forall b p i j, DbT b X p i j = 0.



  Hypothesis Uvec_const : constV Uvec.

  Hypothesis g_const    : constT g.

  Hypothesis H_const    : constT H.



  (* Build the same pieces *)

  Definition matter : T2F := fun p => scaleC rho (outerF Uvec Uvec) p.

  Definition geom   : T2F := fun p i j => g p i j - xi * H p i j.



  (* Zero-difference lemmas reused *)

  Lemma DbT_matter_zero : forall b p i j, DbT b matter p i j = 0.

  Proof.

    intros b p i j.

    unfold DbT, matter, scaleC, outerF.

    pose proof (Uvec_const b p i) as Hui.

    pose proof (Uvec_const b p j) as Hvj.

    unfold DbV in Hui, Hvj. apply minus0_eq in Hui. apply minus0_eq in Hvj.

    rewrite Hui, Hvj. now rewrite Rminus_diag_eq.

  Qed.



  Lemma DbT_g_zero : forall b p i j, DbT b g p i j = 0.

  Proof. intros b p i j. apply g_const. Qed.



  Lemma DbT_H_zero : forall b p i j, DbT b H p i j = 0.

  Proof. intros b p i j. apply H_const. Qed.



  Lemma DbT_geom_zero : forall b p i j, DbT b geom p i j = 0.

  Proof.

    intros b p i j. unfold DbT, geom.

    pose proof (DbT_g_zero b p i j) as Hg0.

    pose proof (DbT_H_zero b p i j) as Hh0.

    unfold DbT in Hg0, Hh0. apply minus0_eq in Hg0. apply minus0_eq in Hh0.

    rewrite Hg0, Hh0. now rewrite Rminus_diag_eq.

  Qed.



  (* Variable pressure field *)

  Variable P : SF.



  (* Structural hypotheses *)

  Hypothesis eom_flux_geom :

    forall p alpha, sumI (fun beta => DbT beta (scaleS P geom) p alpha beta) = 0.



  Hypothesis metric_compat_weighted :

    forall p alpha, sumI (fun beta => (P (flip beta p)) * (DbT beta geom p alpha beta)) = 0.



  (* Derived Module-6 cancellation: Σ (ΔP) · geom = 0 *)

  Lemma pressure_geom_cancel_derived :

    forall p alpha, sumI (fun beta => (DbS beta P p) * geom p alpha beta) = 0.

  Proof.

    intros p alpha.

    (* Pointwise product rule used under sumI *)

    assert (Hpoint :

      forall b,

        DbT b (scaleS P geom) p alpha b

        = (DbS b P p) * geom p alpha b

          + (P (flip b p)) * (DbT b geom p alpha b)).

    { intro b. apply DbT_scaleS_product. }

    (* Turn pointwise equality into equality of sums *)

    pose proof (sumI_ext

      (fun b => DbT b (scaleS P geom) p alpha b)

      (fun b => (DbS b P p) * geom p alpha b

              +  (P (flip b p)) * (DbT b geom p alpha b))

      Hpoint) as Hrewrite.

    (* Start from flux EoM and rewrite *)

    pose proof (eom_flux_geom p alpha) as Hflux.

    rewrite Hrewrite in Hflux.

    rewrite sumI_plus in Hflux.

    (* Kill the weighted Δgeom term *)

    rewrite (metric_compat_weighted p alpha) in Hflux.

    rewrite Rplus_0_r in Hflux.

    exact Hflux.

  Qed.



  (* Full T with variable P *)

  Definition Tfield_var : T2F := matter ⊖ (scaleS P geom).



  Theorem A5_conservation_fd_var_derived :

    forall p alpha, Div Tfield_var p alpha = 0.

  Proof.

    intros p alpha. unfold Div, Tfield_var, sub2.

    set (Sbeta := fun beta => DbT beta Tfield_var p alpha beta).

    (* Pointwise identity for the summand *)

    assert (Hpt : forall b, Sbeta b = - ((DbS b P p) * geom p alpha b)).

    { intro b. unfold Sbeta, Tfield_var.

      rewrite DbT_sub2.

      rewrite (DbT_matter_zero b p alpha b).

      rewrite (DbT_scaleS_product b P geom p alpha b).

      rewrite (DbT_geom_zero b p alpha b).

      rewrite Rmult_0_r, Rplus_0_r. ring. }

    change (sumI (fun beta => Sbeta beta) = 0).

    assert (Heq :

      (fun beta => Sbeta beta)

      = (fun beta => - ((DbS beta P p) * geom p alpha beta))).

    { extensionality beta. apply Hpt. }

    rewrite Heq.

    rewrite <- opp_sumI.

    rewrite pressure_geom_cancel_derived.

    now rewrite Ropp_0.

  Qed.







End DiscreteConservationFD_Var_Derived.









End DiscreteConservationFD_Var.



(* ================================================================== *)

(* Module 7 — DiscreteConservationFD_VarFields                         *)

(*   Product rules + full divergence expansion when (rho,xi,U) vary   *)

(*   Reuses the context from Module 6a via Include.                    *)

(* ================================================================== *)

Module DiscreteConservationFD_VarFields.

  (* Bring all names (Ix, Bit, Pos, flip, DbT/DbV/DbS, sumI, geom, …) *)

  Include DiscreteConservationFD_Var.DiscreteConservationFD_Var_Derived.



  (* === General outer-product forward-difference (vector × vector) === *)

  Lemma DbT_outerF_product :

    forall b (u v:V1F) p i j,

      DbT b (outerF u v) p i j

      = (DbV b u p i) * v p j + u (flip b p) i * (DbV b v p j).

  Proof.

    intros b u v p i j.

    unfold DbT, outerF, DbV.

    set (u1 := u (flip b p) i). set (u0 := u p i).

    set (v1 := v (flip b p) j). set (v0 := v p j).

    replace (u1 * v1 - u0 * v0)

      with (u1 * (v1 - v0) + (u1 - u0) * v0) by ring.

    ring.

  Qed.



  (* === Allow position-dependence in rho, xi, U === *)

  Variable rhoP c2P xiP : SF.

  Variable UvecP : V1F.



  (* Matter and geometry with variable fields *)

  Definition matterP : T2F := scaleS rhoP (outerF UvecP UvecP).

  Definition geomP   : T2F := fun p i j => g p i j - xiP p * H p i j.



  (* Product-rule expansions *)

  Lemma DbT_matterP_expand :

    forall b p i j,

      DbT b matterP p i j

      = (DbS b rhoP p) * (outerF UvecP UvecP p i j)

        + rhoP (flip b p) * (DbT b (outerF UvecP UvecP) p i j).

  Proof.

    intros b p i j. unfold matterP.

    now rewrite (DbT_scaleS_product b rhoP (outerF UvecP UvecP) p i j).

  Qed.



  Lemma DbT_outerF_U_expand :

    forall b p i j,

      DbT b (outerF UvecP UvecP) p i j

      = (DbV b UvecP p i) * UvecP p j

        + UvecP (flip b p) i * (DbV b UvecP p j).

  Proof. intros; apply DbT_outerF_product. Qed.



  Lemma DbT_geomP_expand :

    forall b p i j,

      DbT b geomP p i j

      = DbT b g p i j

        - (DbS b xiP p) * H p i j

        - xiP (flip b p) * (DbT b H p i j).

  Proof.

    intros b p i j. unfold geomP, DbT, DbS.

    set (x1 := g (flip b p) i j). set (x0 := g p i j).

    set (y1 := xiP (flip b p)). set (y0 := xiP p).

    set (h1 := H (flip b p) i j). set (h0 := H p i j).

    replace ((x1 - y1 * h1) - (x0 - y0 * h0))

      with ((x1 - x0) - ((y1 - y0) * h0 + y1 * (h1 - h0))) by ring.

    ring.

  Qed.



  (* Pressure and full T with variable scalars *)

  Definition pressureP : SF := fun p => c2P p * rhoP p.

  (* Define as a true ⊖ so DbT_sub2 matches syntactically *)



Definition TfieldP : T2F := matterP ⊖ (scaleS pressureP geomP).



(* Divergence expansion: shows every extra term explicitly *)

Lemma Div_TfieldP_expanded :

  forall p alpha,

    Div TfieldP p alpha

    =

    (* from matterP *)

    sumI (fun beta => (DbS beta rhoP p) * (outerF UvecP UvecP p alpha beta))

    + sumI (fun beta => rhoP (flip beta p) *

                     ((DbV beta UvecP p alpha) * UvecP p beta

                    + UvecP (flip beta p) alpha * (DbV beta UvecP p beta)))

    (* from pressure*geomP via product rule *)

    - sumI (fun beta => (DbS beta pressureP p) * geomP p alpha beta)

    - sumI (fun beta => pressureP (flip beta p) * (DbT beta geomP p alpha beta)).

Proof.

  intros p alpha.

  unfold Div. (* The goal is now: sumI (LHS_summand) = RHS_of_sums *)



  (* We will prove this by showing that the sum on the left is equal to the

     sum of the terms on the right. The most robust way is via transitivity. *)

  

  (* First, state the combined summand from the RHS of the equation. *)

  transitivity (sumI (fun beta =>

      (DbS beta rhoP p) * (outerF UvecP UvecP p alpha beta)

      + rhoP (flip beta p) *

          ((DbV beta UvecP p alpha) * UvecP p beta +

           UvecP (flip beta p) alpha * (DbV beta UvecP p beta))

      - (DbS beta pressureP p) * geomP p alpha beta

      - pressureP (flip beta p) * (DbT beta geomP p alpha beta)

  )).





  (* --- Goal 1: Prove the LHS sum equals the combined sum --- *)

  {

    (* To prove sumI(f) = sumI(g), we can use sumI_ext to prove f=g for all points. *)

    apply sumI_ext.

    intro b. (* The goal is now the pointwise equality of the summands. *)

    

    (* Unfold all definitions to expose the base algebra. *)

    unfold TfieldP, matterP, geomP, pressureP, outerF, scaleS, sub2.

    unfold DbT, DbV, DbS.

    

    (* This is now a pure algebraic identity that ring can solve. *)

    ring.

  }



  (* --- Goal 2: Prove the combined sum equals the RHS_of_sums --- *)

  {

    (* This is a simple proof about the linearity of sumI. *)

    unfold sumI. (* Expand all sums *)

    ring. (* The equality is now a simple re-arrangement of terms. *)

  }

Qed.

End DiscreteConservationFD_VarFields.





(* ================================================================== *)

(* Module 8 — Discrete_Kernel_Hook                                    *)

(*   Minimal hook: a discrete kernel family with a delta-like limit.  *)

(*   Keeps it separate from the NonlocalHooks (continuous version).   *)

(* ================================================================== *)

Module Discrete_Kernel_Hook.

  Include DiscreteConservationFD_Var.DiscreteConservationFD_Var_Derived.



  (* A family of position-aware discrete kernels *)

  Parameter Eps : Type.

  Parameter eps0 : Eps.

  Parameter K_of_eps : Eps -> T2F.



  (* Skeleton axiom you can refine: at eps0 the kernel “acts like” g *)

  Axiom DeltaKernel_discrete :

    forall p i j, K_of_eps eps0 p i j = g p i j.



  (* Discrete kernel application *)

  Definition ApplyK_discrete (K : T2F) (A B : T2F) : T2F :=

    fun p i j => sumI (fun mu => sumI (fun nu => A p i mu * K p mu nu * B p nu j)).



  Definition H_eps (e:Eps) (F:T2F) : T2F :=

    fun p i j => ApplyK_discrete (K_of_eps e) F F p i j.



  (* In the eps0-limit, H_eps collapses to the local “contract via g” form *)

  Lemma H_eps0_is_local :

    forall F p i j,

      H_eps eps0 F p i j

      = sumI (fun mu => sumI (fun nu => F p i mu * g p mu nu * F p nu j)).

  Proof.

    intros F p i j.

    unfold H_eps, ApplyK_discrete.

    (* rewrite under both sums pointwise *)

    apply sumI_ext; intro mu.

    apply sumI_ext; intro nu.

    now rewrite DeltaKernel_discrete.

  Qed.

End Discrete_Kernel_Hook.



(* ===================================================== *)

(* Module 9 — Texture_Birefringence_Witness (fixed)      *)

(*   Explicit nonlocal/texture witness on the lattice.   *)

(* ===================================================== *)

Module Texture_Birefringence_Witness.

  Include DiscreteConservationFD_Var.DiscreteConservationFD_Var_Derived.

  Local Open Scope R_scope.



  (* --- Minimal flip-at-b helpers (avoid missing lemmas) --- *)

  Local Lemma flip_b_Z0 :

    forall b p, p b = Z0 -> (flip b p) b = Z1.

  Proof.

    intros b p Hb. unfold flip.

    destruct (Ix_eq_dec b b) as [_|C]; [|contradiction].

    rewrite Hb. reflexivity.

  Qed.



  Local Lemma flip_b_Z1 :

    forall b p, p b = Z1 -> (flip b p) b = Z0.

  Proof.

    intros b p Hb. unfold flip.

    destruct (Ix_eq_dec b b) as [_|C]; [|contradiction].

    rewrite Hb. reflexivity.

  Qed.



  (* 1) Simple antisymmetric EM-like tensor from a scalar profile s(p) *)

  Definition F_of_s (s:SF) : T2F :=

    fun p i j =>

      match i, j with

      | I1, I2 =>  s p

      | I2, I1 => -s p

      | _,   _ =>  0

      end.



  (* Local quadratic "intensity" *)

  Definition I_local (s:SF) (p:Pos) : R :=

    sumI (fun i => sumI (fun j =>

      let fij :=

        match i, j with

        | I1, I2 =>  s p

        | I2, I1 => -s p

        | _,   _ =>  0

        end in fij * fij)).



  (* Closed form: only (I1,I2) and (I2,I1) contribute *)

  Lemma I_local_closed_form :

    forall s p, I_local s p = 2 * (s p) * (s p).

  Proof.

    intros s p. unfold I_local.

    set (sp := s p).

    (* i = I0 *)

    replace (sumI (fun j =>

      let fij := match I0, j with

                 | I1, I2 => sp | I2, I1 => -sp | _, _ => 0 end in fij * fij))

      with 0 by (unfold sumI; simpl; ring).

    (* i = I1 *)

    replace (sumI (fun j =>

      let fij := match I1, j with

                 | I1, I2 => sp | I2, I1 => -sp | _, _ => 0 end in fij * fij))

      with (sp*sp) by (unfold sumI; simpl; ring).

    (* i = I2 *)

    replace (sumI (fun j =>

      let fij := match I2, j with

                 | I1, I2 => sp | I2, I1 => -sp | _, _ => 0 end in fij * fij))

      with (sp*sp) by (unfold sumI; simpl; ring).

    (* i = I3 *)

    replace (sumI (fun j =>

      let fij := match I3, j with

                 | I1, I2 => sp | I2, I1 => -sp | _, _ => 0 end in fij * fij))

      with 0 by (unfold sumI; simpl; ring).

    unfold sumI; simpl; ring.

  Qed.



  (* 2) Two-point position kernel: average over {p, flip b p} *)

  Definition I_nonlocal (b:Ix) (s:SF) (p:Pos) : R :=

    (/2) * (I_local s p + I_local s (flip b p)).



  (* Step texture along axis b *)

  Definition s_step (b:Ix) (a:R) : SF :=

    fun p => match p b with Z0 => 0 | Z1 => a end.



  (* Helper: 2 ≠ 0 without lra *)

  Local Lemma R2_neq_0 : (2)%R <> 0.

  Proof.

    apply Rgt_not_eq.                            (* want 2 > 0 *)

    apply Rlt_gt.                                (* from 0 < 2 *)

    change (0 < 1 + 1)%R.

    apply Rplus_lt_0_compat; apply Rlt_0_1.

  Qed.



  (* 3) Witness: local invariant 0 at p0, but nonlocal average = a^2 *)

  Theorem texture_bump_creates_nonlocal_excess :

    forall b a p0,

      p0 b = Z0 ->

      I_local (s_step b a) p0 = 0 /\

      I_nonlocal b (s_step b a) p0 = a*a.

  Proof.

    intros b a p0 Hb0.

    (* Local value at p0 *)

    pose proof (I_local_closed_form (s_step b a) p0) as Hloc_form.

    unfold s_step in Hloc_form; rewrite Hb0 in Hloc_form; simpl in Hloc_form.

    replace (2 * 0 * 0) with 0 in Hloc_form by ring.

    assert (Hloc : I_local (s_step b a) p0 = 0) by exact Hloc_form.



    (* Neighbor value at flip b p0 *)

    assert (Hflip : (flip b p0) b = Z1) by (apply flip_b_Z0; exact Hb0).

    pose proof (I_local_closed_form (s_step b a) (flip b p0)) as Hnb_form.

    unfold s_step in Hnb_form; rewrite Hflip in Hnb_form; simpl in Hnb_form.

    replace (2 * a * a) with (2 * (a*a)) in Hnb_form by ring.



    split.

    - exact Hloc.

    - unfold I_nonlocal.

      replace (I_local (s_step b a) p0) with 0 by exact Hloc.

      replace (I_local (s_step b a) (flip b p0)) with (2 * (a*a)) by exact Hnb_form.

      replace ((/2) * (0 + 2 * (a*a))) with (((/2) * 2) * (a*a)) by ring.

      rewrite (Rinv_l 2 R2_neq_0). ring.

  Qed.



End Texture_Birefringence_Witness.
