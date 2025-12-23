(* ============================================================================ *)
(*                    N_rel Compatibility Adapter                         *)
(*                                                                              *)
(*  (C) 2023-2025 Michael Fillippini. All Rights Reserved.                      *)
(*  UCF/GUTT(TM) Research & Evaluation License v1.1                             *)
(*                                                                              *)
(*  merges improvements from technical review:                                *)
(*   (i)   Z-scope hygiene (avoid nat/Z notation ambiguity)                     *)
(*   (ii)  Reusable Ltac transport pipeline with modular tactics                *)
(*   (iii) Part 4 claims strictly correct: pre-quotient Z representation only   *)
(*   (iv)  Equivalence instance for future setoid/quotient work                 *)
(*   (v)   Isomorphism normalizer for roundtrip simplification                  *)
(*                                                                              *)
(* Dependencies: RelationalNaturals_proven.v, Proposition_01_proven.v           *)
(* ============================================================================ *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znat.  (* Nat2Z / Z.of_nat interaction lemmas *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Import Proposition_01_proven.
Require Import RelationalNaturals_proven.

Module N_rel_Adapter.

(* -------------------------------------------------------------------------- *)
(* Local scope hygiene: avoid ambiguous "-" and mixed nat/Z notation issues.  *)
(* -------------------------------------------------------------------------- *)
Local Open Scope nat_scope.

(* ========================================================================== *)
(* PART 1: ISOMORPHISM FOUNDATION                                             *)
(* ========================================================================== *)

(*
  WHAT THIS FILE PROVES (precisely):
  
  1. The isomorphism N_rel <-> nat is structure-preserving for +, *, -, <=, <
  2. A modular tactic pipeline for transporting nat proofs to N_rel
  3. Z_rel_pre as a PRE-QUOTIENT representation (not full quotient type)
  4. Equivalence instance for Z_rel_equiv (enables future setoid work)
  5. Soundness: Z_rel_to_Z respects Z_rel_equiv
  6. The grounding chain from Proposition 1 to N_rel
  
  WHAT THIS FILE DOES NOT PROVE (and what would be required):
  
  1. Full quotient construction for Z_rel
     - Would require: Quotient type + operations proven well-defined
     - See roadmap Module B for Proper instances
  
  2. Automatic transport of arbitrary theorems
     - Would require: General logical relation / parametricity, or
       fully-developed typeclass algebraic hierarchy, or
       explicit "transfer" mechanism
     - Current: Reliable transport for targeted fragment only
  
  3. Ring/field instances for N_rel/Z_rel
     - Would require: Carrier + operations + ring axiom proofs
     - For Z_rel: typically done on quotient, not pre-quotient
     - See roadmap Module D for required lemmas
  
  4. "All Z theorems apply to Z_rel"
     - Would require: Isomorphism to Coq Z (surjectivity + faithfulness)
     - See roadmap Module E for precise requirements
*)

(* Explicit aliases for adapter boundary clarity *)
Definition to_nat' := to_nat.
Definition from_nat' := from_nat.

Theorem iso_roundtrip_1 : forall n : N_rel, from_nat (to_nat n) = n.
Proof. exact from_nat_to_nat_id. Qed.

Theorem iso_roundtrip_2 : forall n : nat, to_nat (from_nat n) = n.
Proof. exact to_nat_from_nat_id. Qed.

Theorem to_nat_inj : forall n m : N_rel, to_nat n = to_nat m -> n = m.
Proof. exact to_nat_injective. Qed.

Theorem from_nat_inj : forall n m : nat, from_nat n = from_nat m -> n = m.
Proof. exact from_nat_injective. Qed.

(* ========================================================================== *)
(* PART 2: OPERATION CORRESPONDENCE                                           *)
(* ========================================================================== *)

Theorem add_corresponds : forall n m : N_rel,
  to_nat (n +r m) = to_nat n + to_nat m.
Proof. exact add_rel_correct. Qed.

Theorem add_lift : forall n m : nat,
  from_nat (n + m) = from_nat n +r from_nat m.
Proof. exact add_rel_from_nat. Qed.

Theorem mul_corresponds : forall n m : N_rel,
  to_nat (n *r m) = to_nat n * to_nat m.
Proof. exact mul_rel_correct. Qed.

Theorem mul_lift : forall n m : nat,
  from_nat (n * m) = from_nat n *r from_nat m.
Proof. exact mul_rel_from_nat. Qed.

Theorem sub_corresponds : forall n m : N_rel,
  to_nat (n -r m) = to_nat n - to_nat m.
Proof. exact sub_rel_correct. Qed.

(* NOTE: These work because le_rel/lt_rel are DEFINED as to_nat comparisons.
   If your RelationalNaturals_proven uses different definitions, replace
   with the corresponding correctness lemmas exported there. *)
Theorem le_corresponds : forall n m : N_rel,
  n <=r m <-> to_nat n <= to_nat m.
Proof.
  intros n m. unfold le_rel. reflexivity.
Qed.

Theorem lt_corresponds : forall n m : N_rel,
  n <r m <-> to_nat n < to_nat m.
Proof.
  intros n m. unfold lt_rel. reflexivity.
Qed.

(* ========================================================================== *)
(* PART 3: TRANSPORT PIPELINE (Modular Ltac)                                  *)
(* ========================================================================== *)

(*
  The transport pipeline has three layers:
  
  1. nrel_norm      - Rewrite N_rel operations to nat operations
  2. nrel_iso_norm  - Simplify isomorphism roundtrips  
  3. nrel_push_*    - Convert N_rel goals to nat goals
  4. nrel_lia       - Combined push + solve
*)

(* Layer 1: Normalize N_rel operations to nat *)
Ltac nrel_norm :=
  repeat first
    [ rewrite add_corresponds
    | rewrite mul_corresponds
    | rewrite sub_corresponds
    ].

(* Layer 2: Simplify isomorphism roundtrips *)
Ltac nrel_iso_norm :=
  repeat first
    [ rewrite iso_roundtrip_1  (* from_nat (to_nat n) -> n *)
    | rewrite iso_roundtrip_2  (* to_nat (from_nat n) -> n *)
    ].

(* Layer 3a: Push N_rel equality goal to nat *)
Ltac nrel_push_eq :=
  apply to_nat_inj; nrel_norm; nrel_iso_norm.

(* Layer 3b: Push N_rel order goals to nat *)
Ltac nrel_push_le :=
  apply (proj1 (le_corresponds _ _)); nrel_norm; nrel_iso_norm.

Ltac nrel_push_lt :=
  apply (proj1 (lt_corresponds _ _)); nrel_norm; nrel_iso_norm.

(* Layer 4: Combined push + solve wrappers *)
Ltac nrel_lia :=
  first
    [ nrel_push_eq; lia
    | nrel_push_le; lia
    | nrel_push_lt; lia
    ].

Ltac nrel_nia :=
  first
    [ nrel_push_eq; nia
    | nrel_push_le; nia
    | nrel_push_lt; nia
    ].

(* ========================================================================== *)
(* PART 4: EXAMPLE TRANSPORTS                                                 *)
(* ========================================================================== *)

(* Example: commutativity via the pipeline *)
Corollary add_comm_N_rel : forall n m : N_rel, n +r m = m +r n.
Proof.
  intros n m.
  nrel_push_eq.
  (* goal: to_nat n + to_nat m = to_nat m + to_nat n *)
  apply Nat.add_comm.
Qed.

(* Example: associativity via nrel_lia *)
Corollary add_assoc_N_rel : forall n m p : N_rel, 
  (n +r m) +r p = n +r (m +r p).
Proof. intros. nrel_lia. Qed.

(* Example: distributivity via nrel_nia *)
Corollary mul_add_distr_N_rel : forall n m p : N_rel,
  n *r (m +r p) = (n *r m) +r (n *r p).
Proof. intros. nrel_nia. Qed.

(* Consistency check: matches direct proof *)
Lemma add_comm_check : forall n m : N_rel, n +r m = m +r n.
Proof. exact add_rel_comm. Qed.

(* ========================================================================== *)
(* PART 5: INTEGER PRE-QUOTIENT                                               *)
(* ========================================================================== *)

(*
  PRECISE STATEMENT OF WHAT THIS MODULE PROVIDES:

  This module defines a pre-quotient integer representation
  Z_rel_pre := N_rel × N_rel, an equivalence relation Z_rel_equiv,
  and a canonical interpretation map into Coq's Z that is sound
  with respect to Z_rel_equiv.

  It intentionally DOES NOT:
    - Construct the quotient type
    - Prove well-defined operations on the quotient
    - Provide algebraic (ring/field) instances
    - Claim generic theorem transfer from Z to Z_rel_pre

  For a complete relational integer development, see Relationalintegers.v
  or follow the roadmap below.
*)

Definition Z_rel_pre := (N_rel * N_rel)%type.

(* Equivalence relation: (a,b) ~ (c,d) iff a + d = c + b *)
Definition Z_rel_equiv (p q : Z_rel_pre) : Prop :=
  (fst p +r snd q) = (fst q +r snd p).

(* Prove Z_rel_equiv is an equivalence relation *)
Theorem Z_rel_equiv_refl : Reflexive Z_rel_equiv.
Proof.
  unfold Reflexive, Z_rel_equiv. intro x. reflexivity.
Qed.

Theorem Z_rel_equiv_sym : Symmetric Z_rel_equiv.
Proof.
  unfold Symmetric, Z_rel_equiv. intros x y H. symmetry. exact H.
Qed.

Theorem Z_rel_equiv_trans : Transitive Z_rel_equiv.
Proof.
  unfold Transitive, Z_rel_equiv.
  intros x y z Hxy Hyz.
  destruct x as [a b], y as [c d], z as [e f]. simpl in *.
  (* Transport N_rel equalities to nat *)
  assert (Ha : to_nat a + to_nat d = to_nat c + to_nat b).
  { pose proof (f_equal to_nat Hxy) as Hn.
    rewrite add_corresponds, add_corresponds in Hn.
    exact Hn. }
  assert (Hb : to_nat c + to_nat f = to_nat e + to_nat d).
  { pose proof (f_equal to_nat Hyz) as Hn.
    rewrite add_corresponds, add_corresponds in Hn.
    exact Hn. }
  (* Now prove the N_rel goal *)
  apply to_nat_inj. nrel_norm. lia.
Qed.

(* Register as Equivalence instance for future setoid work *)
Global Instance Z_rel_equiv_Equivalence : Equivalence Z_rel_equiv := {
  Equivalence_Reflexive := Z_rel_equiv_refl;
  Equivalence_Symmetric := Z_rel_equiv_sym;
  Equivalence_Transitive := Z_rel_equiv_trans
}.

(* Map Z_rel_pre to Coq Z - explicit %Z annotation *)
Definition Z_rel_to_Z (p : Z_rel_pre) : Z :=
  (Z.of_nat (to_nat (fst p)) - Z.of_nat (to_nat (snd p)))%Z.

(* Soundness: equivalent pairs map to the same Z value *)
Theorem Z_rel_equiv_implies_equal : forall p q : Z_rel_pre,
  Z_rel_equiv p q -> Z_rel_to_Z p = Z_rel_to_Z q.
Proof.
  intros p q H.
  unfold Z_rel_equiv, Z_rel_to_Z in *.
  destruct p as [a b], q as [c d]. simpl in *.

  (* Transport the N_rel equality to nat *)
  assert (Heq_nat : to_nat a + to_nat d = to_nat c + to_nat b).
  { pose proof (f_equal to_nat H) as Hn.
    rewrite add_corresponds, add_corresponds in Hn.
    exact Hn. }

  (* Convert nat equality to Z equality using Nat2Z *)
  assert (Heq_Z :
    (Z.of_nat (to_nat a) + Z.of_nat (to_nat d))%Z =
    (Z.of_nat (to_nat c) + Z.of_nat (to_nat b))%Z).
  { pose proof (f_equal Z.of_nat Heq_nat) as Hz.
    repeat rewrite Nat2Z.inj_add in Hz.
    exact Hz. }

  (* Finish: from a+d = c+b in Z, derive a-b = c-d *)
  lia.
Qed.

(* ========================================================================== *)
(* PART 5b: ROADMAP - Upgrading to Full Relational Integers                   *)
(* ========================================================================== *)
(*
  Current status (this file):
    - Z_rel_pre := N_rel × N_rel (representatives)
    - Z_rel_equiv : Prop  (equivalence on representatives)
    - Z_rel_to_Z : Z_rel_pre -> Z (interpretation into Coq Z)
    - Soundness: Z_rel_equiv p q -> Z_rel_to_Z p = Z_rel_to_Z q

  Next steps (strictly required for "full integers" claims), organized as
  small modules so the adapter remains lightweight.

  ---------------------------------------------------------------------------
  Module A: RelationalIntegers_PreOps.v
  ---------------------------------------------------------------------------
  Goal: Define operations on representatives (pre-quotient level).

    Definitions:
      Z_rel_zero_pre : Z_rel_pre := (Zero_rel, Zero_rel)
      Z_rel_one_pre  : Z_rel_pre := (one_rel,  Zero_rel)
      Z_rel_neg_pre  : Z_rel_pre -> Z_rel_pre
      Z_rel_add_pre  : Z_rel_pre -> Z_rel_pre -> Z_rel_pre
      Z_rel_mul_pre  : Z_rel_pre -> Z_rel_pre -> Z_rel_pre

    Canonical forms:
      neg (a,b) := (b,a)
      add (a,b) (c,d) := (a +r c, b +r d)
      mul (a,b) (c,d) := (a*c + b*d, a*d + b*c)

  ---------------------------------------------------------------------------
  Module B: RelationalIntegers_Proper.v
  ---------------------------------------------------------------------------
  Goal: Prove operations are well-defined with respect to Z_rel_equiv.

    Core Properness/congruence lemmas:
      Z_rel_neg_respects_equiv :
        forall p q, Z_rel_equiv p q -> Z_rel_equiv (Z_rel_neg_pre p) (Z_rel_neg_pre q).

      Z_rel_add_respects_equiv :
        forall p p' q q',
          Z_rel_equiv p p' -> Z_rel_equiv q q' ->
          Z_rel_equiv (Z_rel_add_pre p q) (Z_rel_add_pre p' q').

      Z_rel_mul_respects_equiv :
        forall p p' q q',
          Z_rel_equiv p p' -> Z_rel_equiv q q' ->
          Z_rel_equiv (Z_rel_mul_pre p q) (Z_rel_mul_pre p' q').

    Recommended: Declare Proper instances for setoid rewriting:
      Instance Z_rel_add_Proper : Proper (Z_rel_equiv ==> Z_rel_equiv ==> Z_rel_equiv) Z_rel_add_pre.
      Instance Z_rel_mul_Proper : Proper (Z_rel_equiv ==> Z_rel_equiv ==> Z_rel_equiv) Z_rel_mul_pre.
      Instance Z_rel_neg_Proper : Proper (Z_rel_equiv ==> Z_rel_equiv) Z_rel_neg_pre.

  ---------------------------------------------------------------------------
  Module C: RelationalIntegers_Interpretation.v
  ---------------------------------------------------------------------------
  Goal: Show Z_rel_to_Z is a homomorphism for the pre-ops.

    Homomorphism lemmas:
      Z_rel_to_Z_zero : Z_rel_to_Z Z_rel_zero_pre = 0%Z.
      Z_rel_to_Z_one  : Z_rel_to_Z Z_rel_one_pre  = 1%Z.
      Z_rel_to_Z_neg  : forall p, Z_rel_to_Z (Z_rel_neg_pre p) = (- Z_rel_to_Z p)%Z.
      Z_rel_to_Z_add  : forall p q, Z_rel_to_Z (Z_rel_add_pre p q) = (Z_rel_to_Z p + Z_rel_to_Z q)%Z.
      Z_rel_to_Z_mul  : forall p q, Z_rel_to_Z (Z_rel_mul_pre p q) = (Z_rel_to_Z p * Z_rel_to_Z q)%Z.

  ---------------------------------------------------------------------------
  Module D: RelationalIntegers_Algebra.v
  ---------------------------------------------------------------------------
  Goal: Prove ring laws for your integer structure.

    Minimum ring law suite (setoid or quotient):
      add_assoc, add_comm, add_zero_l, add_neg_l,
      mul_assoc, mul_one_l,
      left_distrib, right_distrib.

    Optional: Provide a ring instance once the above is in place.

  ---------------------------------------------------------------------------
  Module E: RelationalIntegers_Isomorphism.v
  ---------------------------------------------------------------------------
  Goal: Justify "Z theorems apply" via explicit isomorphism.

    (E1) Surjectivity onto Z:
      Z_rel_of_Z : Z -> Z_rel_pre
      Z_rel_to_Z (Z_rel_of_Z z) = z.

    (E2) Faithfulness (injective up to equivalence):
      Z_rel_to_Z p = Z_rel_to_Z q -> Z_rel_equiv p q.

    Once (E1) and (E2) are proven, you can state an explicit isomorphism
    between relational integers and Coq Z, enabling transfer of Z-theorems.

  ---------------------------------------------------------------------------
  Optional Module F: RelationalIntegers_Order.v
  ---------------------------------------------------------------------------
  Goal: Define <= and < on relational integers.

    Define:
      Z_rel_le_pre p q := (Z_rel_to_Z p <= Z_rel_to_Z q)%Z
      Z_rel_lt_pre p q := (Z_rel_to_Z p <  Z_rel_to_Z q)%Z

    Prove: Properness, compatibility with operations, transfer lemmas.
*)

(* ========================================================================== *)
(* PART 6: RELATIONAL GROUNDING                                               *)
(* ========================================================================== *)

(*
  Grounding narrative:

  - This adapter shows: once N_rel exists (grounded via Prop 1's Whole-completion),
    the already-proved isomorphism N_rel <-> nat lets you reuse nat proofs
    without rewriting them.

  - For Z, this file provides a pre-quotient representation, an Equivalence
    instance, and a sound map into Coq Z. A full relational-integer development
    (quotient + operations + Properness + isomorphism theorems) can be layered
    later if desired (see Relationalintegers.v).
*)

Module RelationalGrounding.

  Module P1 := Proposition_01_proven.Core.

  Definition N_rel_ext := P1.Ux N_rel.

  Definition succ_ext := P1.R_prime (fun n m => m = Succ_rel n).

  Theorem naturals_ground_in_whole : forall n : N_rel,
    succ_ext (P1.elem n) P1.Whole.
  Proof.
    intro n. apply P1.everything_relates_to_Whole.
  Qed.

  Theorem N_rel_ext_serial : forall x : N_rel_ext, exists y, succ_ext x y.
  Proof.
    apply P1.proposition_1.
  Qed.

  (* Complete grounding chain - what this adapter actually proves *)
  Theorem grounding_chain_complete :
    (* (1) Seriality from Prop 1 *)
    (forall x : N_rel_ext, exists y, succ_ext x y) /\
    (* (2) Isomorphism N_rel <-> nat (round-trip) *)
    (forall n : N_rel, from_nat (to_nat n) = n) /\
    (forall n : nat, to_nat (from_nat n) = n) /\
    (* (3) Operation correspondence *)
    (forall n m : N_rel, to_nat (n +r m) = to_nat n + to_nat m) /\
    (forall n m : N_rel, to_nat (n *r m) = to_nat n * to_nat m) /\
    (* (4) Z_rel_equiv is an equivalence *)
    Equivalence Z_rel_equiv.
  Proof.
    split; [apply N_rel_ext_serial |].
    split; [apply iso_roundtrip_1 |].
    split; [apply iso_roundtrip_2 |].
    split; [apply add_corresponds |].
    split; [apply mul_corresponds |].
    exact Z_rel_equiv_Equivalence.
  Qed.

End RelationalGrounding.

(* ========================================================================== *)
(* PART 7: USAGE GUIDE                                                        *)
(* ========================================================================== *)

(*
  RECOMMENDED WORKFLOW
  ====================
  
  Keep bulk proof automation on nat/Z as-is.
  When you need the explicit relational bridge for N_rel goals, use:

    nrel_norm         (* just normalize operations, no goal change *)
    nrel_iso_norm     (* simplify from_nat(to_nat n) and to_nat(from_nat n) *)
    nrel_push_eq      (* for N_rel equality goals *)
    nrel_push_le      (* for <=r goals *)
    nrel_push_lt      (* for <r goals *)
    nrel_lia          (* push + lia *)
    nrel_nia          (* push + nia *)

  EXAMPLE:
  
    Goal forall n m, n +r m = m +r n.
    Proof. intros; nrel_push_eq; apply Nat.add_comm. Qed.

    Goal forall n m p, (n +r m) +r p = n +r (m +r p).
    Proof. intros; nrel_lia. Qed.

  INTEGER LAYER NOTE:
  
    Z_rel_pre + Z_rel_equiv + Z_rel_to_Z is a lightweight adapter surface.
    It gives you:
      - A canonical pre-quotient representation
      - An Equivalence instance (for setoid rewriting)
      - A soundness lemma (equivalent pairs map to same Z)
    
    It does NOT give you a full quotient-based integer development.
    For that, see Relationalintegers.v.
*)

End N_rel_Adapter.

(* ========================================================================== *)
(*                    SUMMARY                                                 *)
(* ========================================================================== *)

(*
  N_REL COMPATIBILITY ADAPTER v3
  ==============================
  
  PROVEN RESULTS:
    [OK] Isomorphism N_rel <-> nat (both directions)
    [OK] Operation correspondence (+, *, -, <=, <)
    [OK] Modular transport tactics (nrel_norm, nrel_push_*, nrel_lia/nia)
    [OK] Isomorphism normalizer (nrel_iso_norm)
    [OK] Z_rel_equiv is an Equivalence
    [OK] Z_rel_to_Z respects equivalence (soundness)
    [OK] Grounding chain to Proposition 1
    [OK] Roadmap for full integer development (Modules A-F)
  
  NOT PROVEN (intentionally out of scope):
    [ ] Full quotient construction for Z_rel
    [ ] Automatic transport of arbitrary theorems
    [ ] Ring/field instances for N_rel/Z_rel
    [ ] Generic "Z theorems apply" claim
  
  v3 IMPROVEMENTS:
    - Modular tactic design (separate norm, push, solve layers)
    - Coq.ZArith.Znat for explicit Nat2Z handling
    - Z_rel_pre naming emphasizes pre-quotient status
    - nrel_iso_norm for roundtrip simplification
    - Cleaner proofs using f_equal + Nat2Z.inj_add
    - Detailed roadmap for upgrading to full integers (Part 5b)
    - Precise "does not prove" documentation
  
  DEPENDENCIES:
    - Proposition_01_proven.v
    - RelationalNaturals_proven.v
  
  (C) 2023-2025 Michael Fillippini. All Rights Reserved.
  UCF/GUTT(TM) Research & Evaluation License v1.1
*)
