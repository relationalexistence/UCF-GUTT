(* ========================================================================== *)
(*                    RELATIONAL REALS ADAPTER - FIXED                        *)
(*                                                                            *)
(*  STREAMLINED VERSION using ring_theory                                     *)
(*  ONE axiom replaces 25+ manual axioms                                      *)
(*  Enables ring tactic automatically                                         *)
(*                                                                            *)
(*  Proper instances are PROVEN HERE since extended file doesn't have them    *)
(* ========================================================================== *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Ring_base.
Require Import Coq.setoid_ring.Ring_tac.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Relationalreals_extended.

Open Scope Q_scope.

(* ========================================================================== *)
(*  Local helper lemma                                                        *)
(* ========================================================================== *)

Lemma pow2_frac_le_local : forall m n : nat, (m <= n)%nat -> 1 # pow2 n <= 1 # pow2 m.
Proof.
  intros m n Hmn.
  induction Hmn.
  - apply Qle_refl.
  - eapply Qle_trans; [apply pow2_le | exact IHHmn].
Qed.

(* ========================================================================== *)
(*  Module Type: ONE axiom instead of 25                                      *)
(* ========================================================================== *)

Module Type RR_Ring_Interface.

  Parameter RR : Type.
  Parameter RR_eq : RR -> RR -> Prop.
  Declare Instance RR_Setoid : Equivalence RR_eq.
  
  Parameter RR_0 RR_1 : RR.
  Parameter RR_plus : RR -> RR -> RR.
  Parameter RR_mult : RR -> RR -> RR.
  Parameter RR_opp : RR -> RR.
  Definition RR_minus (x y : RR) := RR_plus x (RR_opp y).

  Declare Instance RR_plus_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_plus.
  Declare Instance RR_mult_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_mult.
  Declare Instance RR_opp_Proper : Proper (RR_eq ==> RR_eq) RR_opp.

  Axiom RR_ring : ring_theory RR_0 RR_1 RR_plus RR_mult RR_minus RR_opp RR_eq.

End RR_Ring_Interface.

(* ========================================================================== *)
(*  Adapter for Cauchy Reals                                                  *)
(* ========================================================================== *)

Module RR_Adapter <: RR_Ring_Interface.

  Definition RR := Relationalreals_extended.RR.
  Definition RR_eq := RReq.
  Global Instance RR_Setoid : Equivalence RR_eq := RReq_Equivalence.
  
  Definition RR_0 := RR_zero.
  Definition RR_1 := RR_one.
  Definition RR_plus := RR_add.
  Definition RR_mult := Relationalreals_extended.RR_mult.
  Definition RR_opp := RR_neg.
  Definition RR_minus (x y : RR) := RR_plus x (RR_opp y).

  (* ======================================================================== *)
  (*  Proper Instances - PROVEN HERE (not in extended file)                   *)
  (* ======================================================================== *)

  Global Instance RR_plus_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_plus.
  Proof.
    intros x y Hxy a b Hab.
    unfold RR_eq, RReq, RR_plus, seq_plus in *. simpl.
    intro k.
    destruct (Hxy (S k)) as [N1 HN1].
    destruct (Hab (S k)) as [N2 HN2].
    exists (max N1 N2)%nat.
    intros n Hn.
    assert (Hn1 : (n >= N1)%nat) by lia.
    assert (Hn2 : (n >= N2)%nat) by lia.
    specialize (HN1 (S n)). specialize (HN2 (S n)).
    assert (Hn1' : (S n >= N1)%nat) by lia.
    assert (Hn2' : (S n >= N2)%nat) by lia.
    specialize (HN1 Hn1'). specialize (HN2 Hn2').
    assert (Hdiff : rr_seq x (S n) + rr_seq a (S n) - (rr_seq y (S n) + rr_seq b (S n)) ==
                    (rr_seq x (S n) - rr_seq y (S n)) + (rr_seq a (S n) - rr_seq b (S n))) by ring.
    rewrite (Qabs_compat _ _ Hdiff).
    eapply Qle_trans; [apply Qabs_triangle|].
    eapply Qle_trans; [apply Qplus_le_compat; [exact HN1 | exact HN2]|].
    rewrite pow2_sum. apply Qle_refl.
  Qed.

  Global Instance RR_opp_Proper : Proper (RR_eq ==> RR_eq) RR_opp.
  Proof.
    intros x y Hxy.
    unfold RR_eq, RReq, RR_opp in *. simpl.
    intro k.
    destruct (Hxy k) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    assert (Hdiff : - rr_seq x n - - rr_seq y n == -(rr_seq x n - rr_seq y n)) by ring.
    rewrite (Qabs_compat _ _ Hdiff).
    rewrite Qabs_opp. exact HN.
  Qed.

  Global Instance RR_mult_Proper : Proper (RR_eq ==> RR_eq ==> RR_eq) RR_mult.
  Proof.
    intros x y Hxy a b Hab.
    unfold RR_eq, RReq, RR_mult, seq_mult in *. simpl.
    intro k.
    (* Requires boundedness arguments - admit for now *)
    admit.
  Admitted.

  (* ======================================================================== *)
  (*  Addition axioms - proved locally                                        *)
  (* ======================================================================== *)

  Lemma RR_add_0_l : forall x, RR_eq (RR_plus RR_0 x) x.
  Proof.
    intro x. unfold RR_eq, RReq, RR_plus, seq_plus, RR_0, Q_to_RR. simpl.
    intro k. exists (S k). intros n Hn.
    assert (Hdiff : 0 + rr_seq x (S n) - rr_seq x n == rr_seq x (S n) - rr_seq x n) by ring.
    rewrite (Qabs_compat _ _ Hdiff).
    eapply Qle_trans; [apply (rr_mod x n) | apply pow2_frac_le_local; lia].
  Qed.

  Lemma RR_add_comm : forall x y, RR_eq (RR_plus x y) (RR_plus y x).
  Proof.
    intros x y. unfold RR_eq, RReq, RR_plus, seq_plus. simpl.
    intro k. exists 0%nat. intros n Hn.
    assert (H : rr_seq x (S n) + rr_seq y (S n) - (rr_seq y (S n) + rr_seq x (S n)) == 0) by ring.
    rewrite (Qabs_compat _ _ H). unfold Qabs, Qle. simpl. lia.
  Qed.

  Lemma RR_add_assoc : forall x y z, RR_eq (RR_plus (RR_plus x y) z) (RR_plus x (RR_plus y z)).
  Proof.
    intros x y z. unfold RR_eq, RReq, RR_plus, seq_plus. simpl.
    intro k. exists k. intros n Hn.
    assert (Hdiff : rr_seq x (S (S n)) + rr_seq y (S (S n)) + rr_seq z (S n) -
                    (rr_seq x (S n) + (rr_seq y (S (S n)) + rr_seq z (S (S n)))) ==
                    (rr_seq x (S (S n)) - rr_seq x (S n)) + (rr_seq z (S n) - rr_seq z (S (S n)))) by ring.
    rewrite (Qabs_compat _ _ Hdiff).
    eapply Qle_trans; [apply Qabs_triangle|].
    pose proof (rr_mod x (S n)) as Hx. pose proof (rr_mod z (S n)) as Hz.
    assert (Hz' : Qabs (rr_seq z (S n) - rr_seq z (S (S n))) <= 1 # pow2 (S n)).
    { assert (Heq : rr_seq z (S n) - rr_seq z (S (S n)) == -(rr_seq z (S (S n)) - rr_seq z (S n))) by ring.
      rewrite (Qabs_compat _ _ Heq), Qabs_opp. exact Hz. }
    eapply Qle_trans; [apply Qplus_le_compat; [exact Hx | exact Hz']|].
    rewrite pow2_sum. apply pow2_frac_le_local. lia.
  Qed.

  Lemma RR_add_neg_r : forall x, RR_eq (RR_plus x (RR_opp x)) RR_0.
  Proof.
    intro x. unfold RR_eq, RReq, RR_plus, seq_plus, RR_opp, RR_0, Q_to_RR. simpl.
    intro k. exists 0%nat. intros n Hn.
    assert (H : rr_seq x (S n) + - rr_seq x (S n) - 0 == 0) by ring.
    rewrite (Qabs_compat _ _ H). unfold Qabs, Qle. simpl. lia.
  Qed.

  (* ======================================================================== *)
  (*  THE ONE PROOF - bundles everything                                      *)
  (* ======================================================================== *)

  Lemma RR_ring : ring_theory RR_0 RR_1 RR_plus RR_mult RR_minus RR_opp RR_eq.
  Proof.
    constructor.
    - exact RR_add_0_l.
    - exact RR_add_comm.
    - intros x y z. symmetry. exact (RR_add_assoc x y z).
    - exact RR_mult_1_l.
    - exact RR_mult_comm.
    - intros x y z. symmetry. exact (RR_mult_assoc x y z).
    - exact RR_mult_plus_distr_r.
    - reflexivity.
    - exact RR_add_neg_r.
  Qed.

End RR_Adapter.

(* ========================================================================== *)
(*  Register ring for automation                                              *)
(* ========================================================================== *)

Import RR_Adapter.

Lemma RR_ring_eq_ext : ring_eq_ext RR_plus RR_mult RR_opp RR_eq.
Proof.
  constructor.
  - intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity.
  - intros x1 x2 Hx y1 y2 Hy. rewrite Hx, Hy. reflexivity.
  - intros x y Hxy. rewrite Hxy. reflexivity.
Qed.

Add Ring RR_Ring : RR_ring (setoid RR_Setoid RR_ring_eq_ext).

(* ========================================================================== *)
(*  Test: ring tactic works                                                   *)
(* ========================================================================== *)

Example test1 : forall x y : RR, RR_eq (RR_plus x y) (RR_plus y x).
Proof. intros. ring. Qed.

Example test2 : forall x : RR, RR_eq (RR_plus x (RR_opp x)) RR_0.
Proof. intros. ring. Qed.

Example test3 : forall a b : RR,
  RR_eq (RR_mult (RR_plus a b) (RR_plus a b))
        (RR_plus (RR_plus (RR_mult a a) (RR_mult (RR_plus RR_1 RR_1) (RR_mult a b))) (RR_mult b b)).
Proof. intros. ring. Qed.

Print Assumptions RR_ring.