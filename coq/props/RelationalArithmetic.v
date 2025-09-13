(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

Require Import ZArith.
Open Scope Z_scope.

Module RelationalArithmetic.

(* In our relational view, we model "relational numbers" as integers. *)
Definition RNum := Z.

(* Define relational addition and multiplication as the standard integer operations *)
Definition radd := Z.add.
Definition rmul := Z.mul.

(* Commutativity of addition: a ⊕ b = b ⊕ a *)
Theorem radd_comm : forall a b : RNum, radd a b = radd b a.
Proof.
  intros a b. unfold radd. apply Z.add_comm.
Qed.

(* Associativity of addition: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) *)
Theorem radd_assoc : forall a b c : RNum, radd (radd a b) c = radd a (radd b c).
Proof.
  intros a b c. unfold radd. rewrite <- Z.add_assoc. reflexivity.
Qed.

(* Commutativity of multiplication: a ⊗ b = b ⊗ a *)
Theorem rmul_comm : forall a b : RNum, rmul a b = rmul b a.
Proof.
  intros a b. unfold rmul. apply Z.mul_comm.
Qed.

(* Associativity of multiplication: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c) *)
Theorem rmul_assoc : forall a b c : RNum, rmul (rmul a b) c = rmul a (rmul b c).
Proof.
  intros a b c. unfold rmul. rewrite <- Z.mul_assoc. reflexivity.
Qed.

(* Distributivity of multiplication over addition:
   a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c) *)
Theorem rmul_distr : forall a b c : RNum, rmul a (radd b c) = radd (rmul a b) (rmul a c).
Proof.
  intros a b c. unfold radd, rmul. apply Z.mul_add_distr_l.
Qed.

(* For local exploration, uncomment:
   Print RelationalArithmetic.radd_assoc.
*)

End RelationalArithmetic.
