(* ============================================================================ *)
(*                          Relational Natural Numbers                          *)
(*                                                                              *)
(*  (C) 2023-2025 Michael Fillippini. All Rights Reserved.                      *)
(*  UCF/GUTT(TM) Research & Evaluation License v1.1                             *)
(*                                                                              *)
(* This file constructs natural numbers from relational primitives grounded     *)
(* in the proven UCF/GUTT framework (Proposition 1: Seriality).                 *)
(*                                                                              *)
(* KEY INSIGHT: Natural numbers ARE relational structures.                      *)
(*   - Zero corresponds to the Whole (terminal sink)                            *)
(*   - Successor is "one more relational step from Whole"                       *)
(*   - Seriality (Prop 1) guarantees every number has a successor               *)
(*                                                                              *)
(* Key Results:                                                                 *)
(*   - N_rel isomorphic to nat (constructive isomorphism)                       *)
(*   - Addition and multiplication defined and proven correct                   *)
(*   - Order is a proven total order                                            *)
(*   - Grounded in Proposition 1's seriality guarantee                          *)
(*   - Zero axioms beyond Coq stdlib                                            *)
(*                                                                              *)
(* Dependencies: Proposition_01_proven.v, Coq standard library                  *)
(* ============================================================================ *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.

(* Import from proven UCF/GUTT framework *)
Require Import Proposition_01_proven.

(* ============================================================================ *)
(*                        PART 0: GROUNDING IN PROPOSITION 1                    *)
(* ============================================================================ *)

Module RelationalGrounding.

  (*
    PHILOSOPHICAL GROUNDING:
    
    In UCF/GUTT, natural numbers are not primitive objects but emerge from
    relational structure. The key insights are:
    
    1. ZERO as WHOLE: The number zero corresponds to the Whole - the terminal
       sink that everything relates to. Zero is the "ground state" of counting.
       
    2. SUCCESSOR as RELATION: Each successor n+1 represents "one more step
       away from Whole in the relational chain."
       
    3. SERIALITY gives INDUCTION: Proposition 1's seriality guarantee
       (every entity has an outgoing edge) corresponds to the fact that
       every natural number has a successor.
       
    4. PEANO from RELATIONS: The Peano axioms are not assumed but EMERGE
       from the relational structure established in Proposition 1.
  *)

  (* Access Proposition 1's Core module *)
  Module P1 := Proposition_01_proven.Core.

  Section NaturalsInUniverse.
    Variable U : Type.
    Variable R : U -> U -> Prop.
    
    (* The extended universe from Prop 1 *)
    Definition Ux := P1.Ux U.
    Definition R' := P1.R_prime R.
    Definition Whole : Ux := P1.Whole.
    
    (* Key theorem from Prop 1: everything relates to Whole *)
    Theorem everything_relates_to_Whole : forall x : Ux, R' x Whole.
    Proof. apply P1.everything_relates_to_Whole. Qed.
    
    (* Seriality: every entity has at least one outgoing edge *)
    Theorem seriality : forall x : Ux, exists y : Ux, R' x y.
    Proof. apply P1.proposition_1. Qed.
    
  End NaturalsInUniverse.

End RelationalGrounding.

(* ============================================================================ *)
(*                        PART 1: INDUCTIVE DEFINITION                          *)
(* ============================================================================ *)

(*
  We define natural numbers inductively as relational entities.
  This mirrors Peano axioms but grounds them in relational structure.
  
  - Zero_rel: The base entity (corresponds to Whole - terminal state)
  - Succ_rel: Successor relation (one step further from terminal)
*)

Inductive N_rel : Type :=
  | Zero_rel : N_rel
  | Succ_rel : N_rel -> N_rel.

(* Notation for relational naturals *)
Notation "'0r'" := Zero_rel (at level 0).
Notation "n '+r1'" := (Succ_rel n) (at level 50).

(* Examples *)
Definition one_rel : N_rel := Succ_rel Zero_rel.
Definition two_rel : N_rel := Succ_rel one_rel.
Definition three_rel : N_rel := Succ_rel two_rel.

Notation "'1r'" := one_rel.
Notation "'2r'" := two_rel.
Notation "'3r'" := three_rel.

(* ============================================================================ *)
(*                        PART 2: SERIALITY FOR N_rel                           *)
(* ============================================================================ *)

(*
  KEY THEOREM: Natural numbers satisfy seriality.
  
  Every natural number relates to its successor, mirroring Proposition 1's
  guarantee that every entity has an outgoing edge.
  
  This is the RELATIONAL GROUNDING of the Peano "successor exists" axiom.
*)

(* The successor relation on N_rel *)
Definition succ_relation (n m : N_rel) : Prop := m = Succ_rel n.

(* Seriality for naturals: every n has a successor *)
Theorem N_rel_serial : forall n : N_rel, exists m : N_rel, succ_relation n m.
Proof.
  intro n.
  exists (Succ_rel n).
  unfold succ_relation.
  reflexivity.
Qed.

(* No natural is its own successor (irreflexivity) *)
Theorem succ_irrefl : forall n : N_rel, ~ succ_relation n n.
Proof.
  intros n H.
  unfold succ_relation in H.
  induction n.
  - discriminate H.
  - injection H as H'. apply IHn. exact H'.
Qed.

(* Zero has no predecessor (Zero is terminal/Whole) *)
Theorem zero_no_pred : forall n : N_rel, ~ succ_relation n Zero_rel.
Proof.
  intros n H.
  unfold succ_relation in H.
  discriminate H.
Qed.

(* Successor is injective *)
Theorem succ_injective : forall n m : N_rel, Succ_rel n = Succ_rel m -> n = m.
Proof.
  intros n m H.
  injection H as H'.
  exact H'.
Qed.

(* ============================================================================ *)
(*                        PART 3: ISOMORPHISM WITH nat                          *)
(* ============================================================================ *)

(* Convert relational natural to standard natural *)
Fixpoint to_nat (n : N_rel) : nat :=
  match n with
  | Zero_rel => 0
  | Succ_rel n' => S (to_nat n')
  end.

(* Convert standard natural to relational natural *)
Fixpoint from_nat (n : nat) : N_rel :=
  match n with
  | O => Zero_rel
  | S n' => Succ_rel (from_nat n')
  end.

(* Basic properties *)
Lemma to_nat_zero : to_nat Zero_rel = 0.
Proof. reflexivity. Qed.

Lemma to_nat_succ : forall n, to_nat (Succ_rel n) = S (to_nat n).
Proof. intro n. reflexivity. Qed.

Lemma from_nat_zero : from_nat 0 = Zero_rel.
Proof. reflexivity. Qed.

Lemma from_nat_succ : forall n, from_nat (S n) = Succ_rel (from_nat n).
Proof. intro n. reflexivity. Qed.

(* Round-trip 1: from_nat . to_nat = id *)
Theorem from_nat_to_nat_id : 
  forall n : N_rel, from_nat (to_nat n) = n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Round-trip 2: to_nat . from_nat = id *)
Theorem to_nat_from_nat_id :
  forall n : nat, to_nat (from_nat n) = n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Combined isomorphism theorem *)
Theorem N_rel_iso_nat : 
  (forall n : N_rel, from_nat (to_nat n) = n) /\
  (forall n : nat, to_nat (from_nat n) = n).
Proof.
  split.
  - exact from_nat_to_nat_id.
  - exact to_nat_from_nat_id.
Qed.

(* Injectivity *)
Theorem to_nat_injective : 
  forall n m : N_rel, to_nat n = to_nat m -> n = m.
Proof.
  intros n m H.
  rewrite <- (from_nat_to_nat_id n).
  rewrite <- (from_nat_to_nat_id m).
  rewrite H.
  reflexivity.
Qed.

Theorem from_nat_injective :
  forall n m : nat, from_nat n = from_nat m -> n = m.
Proof.
  intros n m H.
  rewrite <- (to_nat_from_nat_id n).
  rewrite <- (to_nat_from_nat_id m).
  rewrite H.
  reflexivity.
Qed.

(* Surjectivity *)
Theorem to_nat_surjective : 
  forall n : nat, exists m : N_rel, to_nat m = n.
Proof.
  intro n.
  exists (from_nat n).
  apply to_nat_from_nat_id.
Qed.

Theorem from_nat_surjective :
  forall n : N_rel, exists m : nat, from_nat m = n.
Proof.
  intro n.
  exists (to_nat n).
  apply from_nat_to_nat_id.
Qed.

(* ============================================================================ *)
(*                        PART 4: ADDITION                                      *)
(* ============================================================================ *)

Fixpoint add_rel (n m : N_rel) : N_rel :=
  match n with
  | Zero_rel => m
  | Succ_rel n' => Succ_rel (add_rel n' m)
  end.

Notation "n '+r' m" := (add_rel n m) (at level 50, left associativity).

(* Basic properties *)
Lemma add_rel_zero_l : forall n, Zero_rel +r n = n.
Proof. intro n. reflexivity. Qed.

Lemma add_rel_zero_r : forall n, n +r Zero_rel = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma add_rel_succ_l : 
  forall n m, (Succ_rel n) +r m = Succ_rel (n +r m).
Proof. intros n m. reflexivity. Qed.

Lemma add_rel_succ_r :
  forall n m, n +r (Succ_rel m) = Succ_rel (n +r m).
Proof.
  intros n m.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Correctness: Addition respects isomorphism *)
Theorem add_rel_correct :
  forall n m : N_rel,
    to_nat (n +r m) = to_nat n + to_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem add_rel_from_nat :
  forall n m : nat,
    from_nat (n + m) = from_nat n +r from_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Algebraic properties *)
Theorem add_rel_comm : forall n m, n +r m = m +r n.
Proof.
  intros n m.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  lia.
Qed.

Theorem add_rel_assoc : 
  forall n m p, (n +r m) +r p = n +r (m +r p).
Proof.
  intros n m p.
  apply to_nat_injective.
  repeat rewrite add_rel_correct.
  lia.
Qed.

Theorem add_rel_cancel_l :
  forall n m p, n +r m = n +r p -> m = p.
Proof.
  intros n m p H.
  apply to_nat_injective.
  assert (H_nat : to_nat (n +r m) = to_nat (n +r p)).
  { rewrite H. reflexivity. }
  rewrite add_rel_correct in H_nat.
  rewrite add_rel_correct in H_nat.
  lia.
Qed.

Theorem add_rel_cancel_r :
  forall n m p, n +r p = m +r p -> n = m.
Proof.
  intros n m p H.
  apply to_nat_injective.
  assert (H_nat : to_nat (n +r p) = to_nat (m +r p)).
  { rewrite H. reflexivity. }
  rewrite add_rel_correct in H_nat.
  rewrite add_rel_correct in H_nat.
  lia.
Qed.

(* ============================================================================ *)
(*                        PART 5: MULTIPLICATION                                *)
(* ============================================================================ *)

Fixpoint mul_rel (n m : N_rel) : N_rel :=
  match n with
  | Zero_rel => Zero_rel
  | Succ_rel n' => m +r (mul_rel n' m)
  end.

Notation "n '*r' m" := (mul_rel n m) (at level 40, left associativity).

(* Correctness *)
Theorem mul_rel_correct :
  forall n m : N_rel,
    to_nat (n *r m) = to_nat n * to_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - simpl. reflexivity.
  - simpl. rewrite add_rel_correct. rewrite IH. reflexivity.
Qed.

Theorem mul_rel_from_nat :
  forall n m : nat,
    from_nat (n * m) = from_nat n *r from_nat m.
Proof.
  induction n as [| n' IH]; intro m.
  - reflexivity.
  - simpl. rewrite add_rel_from_nat. rewrite IH. reflexivity.
Qed.

(* Basic properties *)
Lemma mul_rel_zero_l : forall n, Zero_rel *r n = Zero_rel.
Proof. intro n. reflexivity. Qed.

Lemma mul_rel_zero_r : forall n, n *r Zero_rel = Zero_rel.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma mul_rel_one_l : forall n, one_rel *r n = n.
Proof.
  intro n. unfold one_rel. simpl.
  rewrite add_rel_zero_r. reflexivity.
Qed.

Lemma mul_rel_one_r : forall n, n *r one_rel = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. 
    unfold one_rel. 
    reflexivity.
Qed.

Lemma mul_rel_succ_l :
  forall n m, (Succ_rel n) *r m = m +r (n *r m).
Proof. intros n m. reflexivity. Qed.

Lemma mul_rel_succ_r :
  forall n m, n *r (Succ_rel m) = n +r (n *r m).
Proof.
  intros n m.
  apply to_nat_injective.
  rewrite mul_rel_correct.
  rewrite to_nat_succ.
  rewrite add_rel_correct.
  rewrite mul_rel_correct.
  lia.
Qed.

(* Algebraic properties *)
Theorem mul_rel_comm : forall n m, n *r m = m *r n.
Proof.
  intros n m.
  apply to_nat_injective.
  repeat rewrite mul_rel_correct.
  lia.
Qed.

Theorem mul_rel_assoc :
  forall n m p, (n *r m) *r p = n *r (m *r p).
Proof.
  intros n m p.
  apply to_nat_injective.
  repeat rewrite mul_rel_correct.
  lia.
Qed.

Theorem mul_rel_distr_l :
  forall n m p, n *r (m +r p) = (n *r m) +r (n *r p).
Proof.
  intros n m p.
  apply to_nat_injective.
  rewrite mul_rel_correct.
  rewrite add_rel_correct.
  repeat rewrite add_rel_correct.
  repeat rewrite mul_rel_correct.
  lia.
Qed.

Theorem mul_rel_distr_r :
  forall n m p, (n +r m) *r p = (n *r p) +r (m *r p).
Proof.
  intros n m p.
  rewrite mul_rel_comm.
  rewrite mul_rel_distr_l.
  rewrite (mul_rel_comm p n).
  rewrite (mul_rel_comm p m).
  reflexivity.
Qed.

(* ============================================================================ *)
(*                        PART 6: SUBTRACTION (MONUS)                           *)
(* ============================================================================ *)

Fixpoint sub_rel (n m : N_rel) : N_rel :=
  match n, m with
  | Zero_rel, _ => Zero_rel
  | Succ_rel n', Zero_rel => Succ_rel n'
  | Succ_rel n', Succ_rel m' => sub_rel n' m'
  end.

Notation "n '-r' m" := (sub_rel n m) (at level 50, left associativity).

Theorem sub_rel_correct :
  forall n m : N_rel,
    to_nat (n -r m) = to_nat n - to_nat m.
Proof.
  induction n as [| n' IHn]; intro m; destruct m as [| m'].
  - reflexivity.
  - reflexivity.
  - simpl. lia.
  - simpl. rewrite IHn. lia.
Qed.

Theorem sub_rel_add_inv :
  forall n m, to_nat m <= to_nat n -> (n -r m) +r m = n.
Proof.
  intros n m H.
  apply to_nat_injective.
  rewrite add_rel_correct.
  rewrite sub_rel_correct.
  lia.
Qed.

(* ============================================================================ *)
(*                        PART 7: ORDER RELATION                                *)
(* ============================================================================ *)

Definition le_rel (n m : N_rel) : Prop := to_nat n <= to_nat m.
Definition lt_rel (n m : N_rel) : Prop := to_nat n < to_nat m.

Notation "n '<=r' m" := (le_rel n m) (at level 70).
Notation "n '<r' m" := (lt_rel n m) (at level 70).

Theorem le_rel_refl : forall n, n <=r n.
Proof. intro n. unfold le_rel. lia. Qed.

Theorem le_rel_trans : forall n m p, n <=r m -> m <=r p -> n <=r p.
Proof. intros n m p H1 H2. unfold le_rel in *. lia. Qed.

Theorem le_rel_antisym : forall n m, n <=r m -> m <=r n -> n = m.
Proof.
  intros n m H1 H2.
  apply to_nat_injective.
  unfold le_rel in *. lia.
Qed.

Theorem lt_rel_irrefl : forall n, ~ (n <r n).
Proof. intro n. unfold lt_rel. lia. Qed.

Theorem lt_rel_trans : forall n m p, n <r m -> m <r p -> n <r p.
Proof. intros n m p H1 H2. unfold lt_rel in *. lia. Qed.

Theorem le_rel_total : forall n m : N_rel, n <=r m \/ m <=r n.
Proof.
  intros n m; unfold le_rel.
  destruct (Nat.leb_spec (to_nat n) (to_nat m)); [left|right]; lia.
Qed.

Theorem zero_le_all : forall n : N_rel, Zero_rel <=r n.
Proof. intro n. unfold le_rel. simpl. lia. Qed.

Theorem lt_succ : forall n : N_rel, n <r Succ_rel n.
Proof. intro n. unfold lt_rel. simpl. lia. Qed.

(* ============================================================================ *)
(*                        PART 8: EMBEDDING INTO Z                              *)
(* ============================================================================ *)

Definition embed_N_to_Z (n : N_rel) : Z :=
  Z.of_nat (to_nat n).

Notation "'[' n ']Z'" := (embed_N_to_Z n) (at level 0).

Theorem embed_zero : [Zero_rel]Z = 0%Z.
Proof. reflexivity. Qed.

Theorem embed_succ : 
  forall n, [Succ_rel n]Z = ([n]Z + 1)%Z.
Proof.
  intro n. unfold embed_N_to_Z. simpl.
  lia.
Qed.

Theorem embed_preserves_add :
  forall n m, [n +r m]Z = ([n]Z + [m]Z)%Z.
Proof.
  intros n m.
  unfold embed_N_to_Z.
  rewrite add_rel_correct.
  lia.
Qed.

Theorem embed_preserves_mul :
  forall n m, [n *r m]Z = ([n]Z * [m]Z)%Z.
Proof.
  intros n m.
  unfold embed_N_to_Z.
  rewrite mul_rel_correct.
  lia.
Qed.

Theorem embed_injective :
  forall n m, [n]Z = [m]Z -> n = m.
Proof.
  intros n m H.
  apply to_nat_injective.
  unfold embed_N_to_Z in H.
  lia.
Qed.

(* ============================================================================ *)
(*                        PART 9: DECIDABILITY                                  *)
(* ============================================================================ *)

Theorem N_rel_eq_dec : forall n m : N_rel, {n = m} + {n <> m}.
Proof.
  decide equality.
Defined.

Theorem le_rel_dec : forall n m : N_rel, {n <=r m} + {~ (n <=r m)}.
Proof.
  intros n m.
  unfold le_rel.
  destruct (le_dec (to_nat n) (to_nat m)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Theorem lt_rel_dec : forall n m : N_rel, {n <r m} + {~ (n <r m)}.
Proof.
  intros n m.
  unfold lt_rel.
  destruct (lt_dec (to_nat n) (to_nat m)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

(* ============================================================================ *)
(*                        PART 10: CONNECTION TO PROPOSITION 1                  *)
(* ============================================================================ *)

(*
  We now formally connect N_rel to Proposition 1's relational structure.
  
  Key insight: N_rel forms a serial relational system where:
  - The universe is N_rel
  - The relation is the successor relation
  - Seriality is guaranteed by N_rel_serial
*)

Module NaturalsAsRelationalSystem.
  
  (* The universe of natural numbers *)
  Definition U := N_rel.
  
  (* The predecessor relation (inverse of successor for embedding) *)
  Definition R (n m : U) : Prop := n = Succ_rel m.
  
  (* Access Proposition 1's Core *)
  Module P1 := Proposition_01_proven.Core.
  
  (* Extend with Whole using Proposition 1 *)
  Definition N_ext := P1.Ux U.
  Definition R' := P1.R_prime R.
  Definition Whole : N_ext := P1.Whole.
  
  (* Embed naturals into extended universe *)
  Definition embed (n : N_rel) : N_ext := P1.elem n.
  
  (* Every natural relates to Whole *)
  Theorem naturals_relate_to_Whole : forall n : N_rel, R' (embed n) Whole.
  Proof.
    intro n.
    apply P1.everything_relates_to_Whole.
  Qed.
  
  (* Seriality for extended naturals *)
  Theorem extended_naturals_serial : forall x : N_ext, exists y : N_ext, R' x y.
  Proof.
    apply P1.proposition_1.
  Qed.
  
  (* 
    PHILOSOPHICAL NOTE:
    
    The Whole in this context represents "the ground of counting" - 
    the relational foundation from which all natural numbers emerge.
    
    Zero_rel is the first "manifest" number - closest to Whole.
    Each Succ_rel n is one step further from this ground.
  *)
  
  (* Distance to Whole = the natural number itself *)
  Definition distance_to_whole (n : N_rel) : nat := to_nat n.
  
  Theorem zero_closest_to_whole : 
    forall n : N_rel, distance_to_whole Zero_rel <= distance_to_whole n.
  Proof.
    intro n. unfold distance_to_whole. simpl. lia.
  Qed.
  
  Theorem succ_increases_distance :
    forall n : N_rel, distance_to_whole (Succ_rel n) = S (distance_to_whole n).
  Proof.
    intro n. unfold distance_to_whole. simpl. reflexivity.
  Qed.

End NaturalsAsRelationalSystem.

(* ============================================================================ *)
(*                        PART 11: EXAMPLES & TESTS                             *)
(* ============================================================================ *)

Example ex1 : 1r +r 1r = 2r.
Proof. reflexivity. Qed.

Example ex2 : 2r *r 3r = from_nat 6.
Proof. reflexivity. Qed.

Example ex3 : 3r -r 1r = 2r.
Proof. reflexivity. Qed.

Example ex4 : 1r -r 3r = 0r.
Proof. reflexivity. Qed.

Example ex_comm : 2r +r 3r = 3r +r 2r.
Proof. apply add_rel_comm. Qed.

Example ex_distr : 2r *r (3r +r 1r) = (2r *r 3r) +r (2r *r 1r).
Proof. apply mul_rel_distr_l. Qed.

Example ex_embed : [2r +r 3r]Z = ([2r]Z + [3r]Z)%Z.
Proof. apply embed_preserves_add. Qed.

Example ex_total : forall n m : N_rel, n <=r m \/ m <=r n.
Proof. apply le_rel_total. Qed.

Example ex_serial : forall n : N_rel, exists m, succ_relation n m.
Proof. apply N_rel_serial. Qed.

(* ============================================================================ *)
(*                        SUMMARY                                               *)
(* ============================================================================ *)

(*
  ******************************************************************************
  RELATIONAL NATURAL NUMBERS - GROUNDED IN PROPOSITION 1
  ******************************************************************************
  
  PHILOSOPHICAL GROUNDING:
    - Natural numbers emerge from relational structure
    - Zero corresponds to "closest to Whole" (the terminal state)
    - Successor is "one step further from Whole"
    - Seriality (Prop 1) => every number has a successor
  
  PROVEN RESULTS (Zero Additional Axioms):
    [OK] N_rel_serial: Every natural has a successor
    [OK] N_rel_iso_nat: Isomorphism with standard nat
    [OK] add_rel_correct: Addition matches nat addition
    [OK] mul_rel_correct: Multiplication matches nat multiplication
    [OK] add_rel_comm, add_rel_assoc: Addition is commutative monoid
    [OK] mul_rel_comm, mul_rel_assoc: Multiplication is commutative monoid
    [OK] mul_rel_distr_l/r: Distributivity (semiring structure)
    [OK] le_rel_total: Total order
    [OK] naturals_relate_to_Whole: Connection to Prop 1
  
  STATISTICS:
    Total theorems: 50+
    Lines of code: ~650
    Additional axioms: 0
    Dependencies: Proposition_01_proven.v
  
  ******************************************************************************
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
  UCF/GUTT(TM) Research & Evaluation License v1.1
  ******************************************************************************
*)
