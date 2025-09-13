(*
  UCF/GUTT™ Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)
  © 2023–2025 Michael Fillippini. All Rights Reserved.
*)

theory Scratch_UCF
  imports Main
begin

  (* Define a type for the universe U *)
  typedecl U

  (* Define the relation R on U *)
  consts R :: "U ⇒ U ⇒ bool"

  (* Axiom: ∀x ∈ U, ∃y ∈ U : R(x, y) *)
  axiomatization where
    R_relation: "∀x::U. ∃y::U. R x y"

  (* A simple lemma that uses the axiom *)
  lemma exists_related_entity: "∀x::U. ∃y::U. R x y"
  proof -
    from R_relation show ?thesis by simp
  qed

end
