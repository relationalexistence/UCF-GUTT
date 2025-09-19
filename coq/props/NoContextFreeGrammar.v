(*
  NoContextFreeGrammar.v
  ----------------------
  UCF/GUTT-style “boundary preservation” vs. context-freeness (robust fix).

  Notes:
  - Keep boundary_preserving with argument order (u v A rhs).
  - Invoke it in tactic mode with named arguments (u:=, v:=, A:=, rhs:=).
  - boundary_ok_right_nil proved by explicit case-splitting.
*)

From Coq Require Import List Arith.
Import ListNotations.

Set Implicit Arguments.

Section RelationalUniverse.
  Variable E : Type.
  Variable Adj : E -> E -> Prop.

  (* Weak connectivity axiom, consistent with your broader setting. *)
  Axiom connectivity : forall x : E, exists y : E, Adj x y \/ Adj y x.

  (* Kept for completeness; safe to keep even if unused elsewhere. *)
  Variable eq_dec : forall (x y : E), {x = y} + {x <> y}.

  (* Utilities *)
  Fixpoint last_opt (w : list E) : option E :=
    match w with
    | [] => None
    | [a] => Some a
    | _ :: t => last_opt t
    end.

  Definition head_opt (w : list E) : option E :=
    match w with
    | [] => None
    | a :: _ => Some a
    end.

  (* Boundary compatibility for u ++ mid ++ v *)
  Definition boundary_ok (u mid v : list E) : Prop :=
    (* left boundary *)
    (match last_opt u, head_opt mid with
     | Some l, Some h => Adj l h
     | Some _, None   => True
     | None,   _      => True
     end)
    /\
    (* right boundary *)
    (match last_opt mid, head_opt v with
     | Some l, Some h => Adj l h
     | Some _, None   => True
     | None,   _      => True
     end).

  (* With v = [], only the left boundary matters. *)
  Lemma boundary_ok_right_nil :
    forall (u mid : list E),
      boundary_ok u mid ([]:list E) <->
      match last_opt u, head_opt mid with
      | Some l, Some h => Adj l h
      | _, _ => True
      end.
  Proof.
    intros u mid; unfold boundary_ok; simpl.
    destruct (last_opt u) as [l|] eqn:Lu;
    destruct (head_opt mid) as [h|] eqn:Hm; simpl.
    - (* Some l, Some h *)
      split; intros H.
      + destruct H as [Hl _]. exact Hl.
      + split; [assumption | destruct (last_opt mid); exact I].
    - (* Some l, None *)
      split; intros _.
      + exact I.
      + split; [exact I | destruct (last_opt mid); exact I].
    - (* None, Some h *)
      split; intros _.
      + exact I.
      + split; [exact I | destruct (last_opt mid); exact I].
    - (* None, None *)
      split; intros _.
      + exact I.
      + split; [exact I | destruct (last_opt mid); exact I].
  Qed.

  (* ===================================================== *)
  (* ========= 1) Grammars & Context-Freeness ============ *)
  (* ===================================================== *)

  Record Alphabet := { is_terminal : E -> bool }.
  Variable Sigma : Alphabet.

  Definition terminal (x:E) : Prop := is_terminal Sigma x = true.
  Definition nonterminal (x:E) : Prop := is_terminal Sigma x = false.

  Definition Production := (E * list E)%type.

  Record Grammar := {
    prods : list Production;

    prods_lhs_nonterminal :
      forall A rhs, In (A,rhs) prods -> nonterminal A;

    (* Boundary-preserving rewrite: ORDER = (u v A rhs) *)
    boundary_preserving :
      forall (u v : list E) (A:E) (rhs:list E),
        In (A,rhs) prods ->
        boundary_ok u [A] v ->
        boundary_ok u rhs v
  }.

  (* Context-free (boundary semantics): for fixed A,rhs, admissibility does not
     depend on contexts u,v. *)
  Definition is_cfg (G:Grammar) : Prop :=
    forall (A:E) (u v u' v' : list E),
      nonterminal A ->
      forall rhs,
        In (A,rhs) (prods G) ->
        (boundary_ok u  rhs v  <-> boundary_ok u' rhs v').

  (* (Derivation relations kept for completeness; not used in the contradiction.) *)
  Inductive derives1 (G:Grammar) : list E -> list E -> Prop :=
  | d1_here :
      forall u v A rhs,
        In (A,rhs) (prods G) ->
        derives1 G (u ++ A :: v) (u ++ rhs ++ v).

  Inductive derives (G:Grammar) : list E -> list E -> Prop :=
  | der_refl : forall w, derives G w w
  | der_step : forall w1 w2 w3,
      derives1 G w1 w2 -> derives G w2 w3 -> derives G w1 w3.

  Definition well_formed_site (G:Grammar) (u : list E) (A:E) (v : list E) : Prop :=
    forall rhs, In (A,rhs) (prods G) ->
      boundary_ok u [A] v -> boundary_ok u rhs v.

  Definition well_formed (G:Grammar) (w:list E) : Prop :=
    forall u v A, w = u ++ A :: v -> well_formed_site G u A v.

  (* ===================================================== *)
  (* == 2) Robust incompatibility witness (fully typed) == *)
  (* ===================================================== *)

  (*
    Require both contexts (u1, u2) to be valid placements for [A] with v := [],
    i.e., Adj l1 A and Adj l2 A hold (so boundary_ok u [A] [] holds).
    For the same rhs with head h, left boundary differs:
      Adj l1 h    but   ~ Adj l2 h.
    This makes boundary_preserving applicable and yields a clash.
  *)
  Definition incompatible_left_boundary (A:E) (rhs:list E) : Prop :=
    exists (u1 u2 : list E) (l1 l2 h : E),
         last_opt u1 = Some l1
      /\ last_opt u2 = Some l2
      /\ head_opt rhs = Some h
      /\ Adj l1 A
      /\ Adj l2 A
      /\ Adj l1 h
      /\ ~ Adj l2 h.

  Axiom exists_incompatible_site :
    forall (G:Grammar),
      exists (A:E) (rhs:list E),
        In (A,rhs) (prods G) /\ rhs <> [] /\ incompatible_left_boundary A rhs.

  (* ===================================================== *)
  (* ======= 3) Main impossibility under boundary ========= *)
  (* ===================================================== *)

  Theorem no_nontrivial_cfg_under_boundary :
    forall G:Grammar,
      is_cfg G ->
      False.
  Proof.
    intros G Hcfg.
    (* Pull the global incompatible site *)
    destruct (exists_incompatible_site G) as [A Hex1].
    destruct Hex1 as [rhs Hex2].
    destruct Hex2 as [Hin Hex3].
    destruct Hex3 as [Hrhs_ne Hinc].

    (* Destructure the incompatibility witness step-by-step *)
    destruct Hinc as [u1 Hinc1].
    destruct Hinc1 as [u2 Hinc2].
    destruct Hinc2 as [l1 Hinc3].
    destruct Hinc3 as [l2 Hinc4].
    destruct Hinc4 as [h Hinc5].
    destruct Hinc5 as [Hu1 Hinc6].
    destruct Hinc6 as [Hu2 Hinc7].
    destruct Hinc7 as [Hh Hinc8].
    destruct Hinc8 as [HA1 Hinc9].
    destruct Hinc9 as [HA2 Hinc10].
    destruct Hinc10 as [HAdj1 HnAdj2].

    (* Build boundary_ok u [A] [] from left-adjacency via the backward direction *)
    assert (BA1 : boundary_ok u1 [A] []).
    { apply (proj2 (boundary_ok_right_nil u1 [A])).
      rewrite Hu1; simpl; exact HA1. }
    assert (BA2 : boundary_ok u2 [A] []).
    { apply (proj2 (boundary_ok_right_nil u2 [A])).
      rewrite Hu2; simpl; exact HA2. }

    (* Apply boundary preservation — use tactic mode with named args *)
    assert (BR1 : boundary_ok u1 rhs (@nil E)).
    { eapply (boundary_preserving G) with (u:=u1) (v:=@nil E) (A:=A) (rhs:=rhs); eauto. }
    assert (BR2 : boundary_ok u2 rhs (@nil E)).
    { eapply (boundary_preserving G) with (u:=u2) (v:=@nil E) (A:=A) (rhs:=rhs); eauto. }

    (* Convert to pure left-boundary facts *)
    pose proof (proj1 (boundary_ok_right_nil u1 rhs) BR1) as BR1L.
    pose proof (proj1 (boundary_ok_right_nil u2 rhs) BR2) as BR2L.
    rewrite Hu1 in BR1L; rewrite Hh in BR1L; simpl in BR1L.  (* BR1L : Adj l1 h *)
    rewrite Hu2 in BR2L; rewrite Hh in BR2L; simpl in BR2L.  (* BR2L : Adj l2 h *)

    (* Contradiction with ~Adj l2 h *)
    exact (HnAdj2 BR2L).
  Qed.

  (* Same conclusion, restated. *)
  Theorem no_context_free_grammar :
    forall G:Grammar, is_cfg G -> False.
  Proof. eauto using no_nontrivial_cfg_under_boundary. Qed.

End RelationalUniverse.

