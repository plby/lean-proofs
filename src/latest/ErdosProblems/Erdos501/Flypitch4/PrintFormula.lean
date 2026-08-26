/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Andrew Tindall, Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/print_formula.lean (70 lines) — Task 23 -/

import ErdosProblems.Erdos501.Flypitch4.Zfc

set_option relaxedAutoImplicit true

open Fol ZFC_rel ZFC_func

-- ugly but working (str_formula says it's not well-founded recursion, but it evaluates anyways)

/-- Convert a bounded preterm of L_ZFC to a string, given a variable counter z. -/
partial def str_preterm : ∀ {n m : ℕ}, ℕ → bounded_preterm L_ZFC n m → String
  | _, _, z, bd_var k       => "x" ++ toString (z - k.val)
  | _, _, _, bd_func ZFC_func.emptyset => "∅"
  | _, _, _, bd_func ZFC_func.pr      => "pair"
  | _, _, _, bd_func ZFC_func.ω       => "ω"
  | _, _, _, bd_func ZFC_func.P       => "𝒫"
  | _, _, _, bd_func ZFC_func.Union   => "⋃"
  | _, _, z, bd_app t₁ t₂  =>
      str_preterm z t₁ ++ "(" ++ str_preterm z t₂ ++ ")"

/-- Convert a bounded term of L_ZFC to a string. -/
partial def str_term {n : ℕ} (z : ℕ) (t : bounded_term L_ZFC n) : String :=
  str_preterm z t

/-- Convert a bounded preformula of L_ZFC to a string, given a variable counter z. -/
partial def str_preformula : ∀ {n m : ℕ}, ℕ → bounded_preformula L_ZFC n m → String
  | _, _, _, bd_falsum          => "⊥"
  | _, _, z, bd_equal a b       =>
      str_preterm z a ++ " = " ++ str_preterm z b
  | _, _, z, bd_imp a b         =>
      str_preformula z a ++ " ⟹ " ++ str_preformula z b
  | _, _, _, bd_rel _           => "∈"
  | _, _, z, bd_apprel a b      =>
      str_preformula z a ++ "(" ++ str_term z b ++ ")"
  | _, _, z, bd_all t           =>
      "(∀x" ++ toString (z + 1) ++ "," ++ str_preformula (z + 1) t ++ ")"

/-- Pretty-print a bounded formula of L_ZFC, given a variable counter m. -/
partial def str_formula : ∀ {n : ℕ}, bounded_formula L_ZFC n → ℕ → String
  -- conjunction: (f₁ ∧ f₂) is encoded as ¬(f₁ ⟹ ¬f₂) = (f₁ ⟹ (f₂ ⟹ ⊥)) ⟹ ⊥
  | _, bd_imp (bd_imp f₁ (bd_imp f₂ bd_falsum)) bd_falsum, m =>
      "(" ++ str_formula f₁ m ++ " ∧ " ++ str_formula f₂ m ++ ")"
  -- disjunction: ¬f₁ ⟹ f₂
  | _, bd_imp (bd_imp f₁ bd_falsum) f₂, m =>
      "(" ++ str_formula f₁ m ++ " ∨ " ++ str_formula f₂ m ++ ")"
  -- equality
  | _, bd_equal s1 s2, m =>
      "(" ++ str_term m s1 ++ " = " ++ str_term m s2 ++ ")"
  -- existential: ∃x, f is encoded as ¬(∀x, ¬f) = (∀x, f ⟹ ⊥) ⟹ ⊥
  | _, bd_imp (bd_all (bd_imp f bd_falsum)) bd_falsum, m =>
      "∃x" ++ toString (m + 1) ++ "," ++ str_formula f (m + 1)
  -- universal
  | _, bd_all f, m =>
      "(∀x" ++ toString (m + 1) ++ "," ++ str_formula f (m + 1) ++ ")"
  -- falsum
  | _, bd_falsum, _ => "⊥"
  -- negation
  | _, bd_imp f bd_falsum, m => "¬ " ++ str_formula f m
  -- membership: t₁ ∈ t₂
  | _, bd_apprel (bd_apprel (bd_rel (ZFC_rel.ε)) a) b, m =>
      str_preterm m a ++ " ∈ " ++ str_preterm m b
  -- generic apprel
  | _, bd_apprel f₁ f₂, m =>
      str_preformula 1 f₁ ++ "(" ++ str_term m f₂ ++ ")"
  -- implication (catch-all)
  | _, bd_imp a b, m =>
      "(" ++ str_formula a m ++ " ⟹ " ++ str_formula b m ++ ")"

/-- Print a sentence (n=0 bounded formula) of L_ZFC. -/
partial def print_formula {n : ℕ} (f : bounded_formula L_ZFC n) : String :=
  str_formula f 0

instance formula_to_string {n : ℕ} : ToString (bounded_formula L_ZFC n) :=
  ⟨print_formula⟩

/-- Trace-print a list of bounded formulas (useful in tactic mode). -/
def print_formula_list {n : ℕ} (axms : List (bounded_formula L_ZFC n)) : IO Unit :=
  axms.forM (fun ax => IO.println (toString ax ++ "\n"))

section test

/-- ∀ x, ∀ y, x = y → ∀ z, z = x → z = y -/
def testsentence : sentence L_ZFC :=
  bd_all (bd_all (bd_imp (bd_equal (&ᵇ⟨1, by omega⟩) (&ᵇ⟨0, by omega⟩))
    (bd_all (bd_imp (bd_equal (&ᵇ⟨0, by omega⟩) (&ᵇ⟨2, by omega⟩))
      (bd_equal (&ᵇ⟨0, by omega⟩) (&ᵇ⟨1, by omega⟩))))))

end test
