/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The strong collection scheme: semantics on both sides

* `realize_collectionAxiom` — the two-valued meaning of the Mathlib-side collection axiom
  `collectionAxiom n ψ` (Challenge / `Erdos501.FOL.Statement`) in any `L`-structure;
* `realize_axiom_of_collection` — the two-valued meaning of Flypitch's `axiom_of_collection ϕ`;
* `toM_realize_collectionAxiom` — a Flypitch structure satisfying Flypitch's scheme (for the
  translated formula `tr ψ`) satisfies the Mathlib-side instance for `ψ`.
-/
import ErdosProblems.Erdos501.FOL.Translate
import ErdosProblems.Erdos501.FOL.FolLemmas

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol

namespace Erdos501.FOL

/-! ### `Fin.snoc` by value -/

section snoc

variable {M : Type*}

lemma snoc_of_lt {n : ℕ} (p : Fin n → M) (x : M) (i : Fin (n + 1)) (h : (i : ℕ) < n) :
    (Fin.snoc p x : Fin (n + 1) → M) i = p ⟨i, h⟩ := by
  simp only [Fin.snoc, h, dite_true, cast_eq]
  rfl

lemma snoc_of_eq {n : ℕ} (p : Fin n → M) (x : M) (i : Fin (n + 1)) (h : (i : ℕ) = n) :
    (Fin.snoc p x : Fin (n + 1) → M) i = x := by
  simp only [Fin.snoc, h, lt_self_iff_false, dite_false, cast_eq]

/-- The variable map of `liftAt n' m`. -/
abbrev liftFun (n' m k : ℕ) : Fin k → Fin (k + n') :=
  fun i => if (i : ℕ) < m then Fin.castAdd n' i else Fin.addNat i n'

set_option linter.unusedSimpArgs false in
lemma comp_liftFun₁ {n : ℕ} (xs : Fin (n + 1) → M) (x y : M) :
    (Fin.snoc (Fin.snoc xs x) y ∘ liftFun 1 n (n + 2)) = Fin.snoc (Fin.snoc (Fin.init xs) x) y := by
  funext i
  simp only [Function.comp, liftFun]
  by_cases hi : (i : ℕ) < n
  · simp only [hi, ite_true]
    rw [snoc_of_lt _ _ _ (by simp only [Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by omega), snoc_of_lt _ _ _ (by omega)]
    rfl
  · simp only [hi, ite_false]
    rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi' | hi'
    · have hi'' : (i : ℕ) = n := by omega
      rw [snoc_of_lt _ _ _ (by simp only [Fin.val_addNat]; omega),
        snoc_of_eq _ _ _ (by simp only [Fin.val_mk, Fin.val_addNat]; omega),
        snoc_of_lt _ _ _ (by omega), snoc_of_eq _ _ _ (by omega)]
    · have hi'' : (i : ℕ) = n + 1 := by omega
      rw [snoc_of_eq _ _ _ (by simp only [Fin.val_addNat]; omega), snoc_of_eq _ _ _ (by omega)]

set_option linter.unusedSimpArgs false in
lemma comp_liftFun₂ {n : ℕ} (xs : Fin (n + 1) → M) (v x y : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs v) x) y ∘ liftFun 2 n (n + 2)) =
      Fin.snoc (Fin.snoc (Fin.init xs) x) y := by
  funext i
  simp only [Function.comp, liftFun]
  by_cases hi : (i : ℕ) < n
  · simp only [hi, ite_true]
    rw [snoc_of_lt _ _ _ (by simp only [Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by omega), snoc_of_lt _ _ _ (by omega)]
    rfl
  · simp only [hi, ite_false]
    rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi' | hi'
    · have hi'' : (i : ℕ) = n := by omega
      rw [snoc_of_lt _ _ _ (by simp only [Fin.val_addNat]; omega),
        snoc_of_eq _ _ _ (by simp only [Fin.val_mk, Fin.val_addNat]; omega),
        snoc_of_lt _ _ _ (by omega), snoc_of_eq _ _ _ (by omega)]
    · have hi'' : (i : ℕ) = n + 1 := by omega
      rw [snoc_of_eq _ _ _ (by simp only [Fin.val_addNat]; omega), snoc_of_eq _ _ _ (by omega)]

set_option linter.unusedSimpArgs false in
lemma comp_liftFun₃ {n : ℕ} (xs : Fin (n + 1) → M) (v y x y' : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs v) y) x) y' ∘ liftFun 3 n (n + 2)) =
      Fin.snoc (Fin.snoc (Fin.init xs) x) y' := by
  funext i
  simp only [Function.comp, liftFun]
  by_cases hi : (i : ℕ) < n
  · simp only [hi, ite_true]
    rw [snoc_of_lt _ _ _ (by simp only [Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by simp only [Fin.val_mk, Fin.val_castAdd]; omega),
      snoc_of_lt _ _ _ (by omega), snoc_of_lt _ _ _ (by omega)]
    rfl
  · simp only [hi, ite_false]
    rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi' | hi'
    · have hi'' : (i : ℕ) = n := by omega
      rw [snoc_of_lt _ _ _ (by simp only [Fin.val_addNat]; omega),
        snoc_of_eq _ _ _ (by simp only [Fin.val_mk, Fin.val_addNat]; omega),
        snoc_of_lt _ _ _ (by omega), snoc_of_eq _ _ _ (by omega)]
    · have hi'' : (i : ℕ) = n + 1 := by omega
      rw [snoc_of_eq _ _ _ (by simp only [Fin.val_addNat]; omega), snoc_of_eq _ _ _ (by omega)]

end snoc

/-! ### The Mathlib side -/

section mathlib

variable {M : Type*} [L.Structure M]

/-- `a ∈ b` in an `L`-structure. -/
def memM (a b : M) : Prop := Structure.RelMap (L := L) Rel.mem ![a, b]

/-- The meaning of `collectionAxiom n ψ`: for all parameters `p` and all `u`, if every `x ∈ u`
has a `y` with `ψ p x y`, then there is `v` with `∀ x ∈ u, ∃ y ∈ v, ψ p x y` and
`∀ y ∈ v, ∃ x ∈ u, ψ p x y`.  (The parameters and `u` are packed as `xs : Fin (n + 1) → M`.) -/
theorem realize_collectionAxiom (n : ℕ) (ψ : L.BoundedFormula Empty (n + 2)) :
    (M ⊨ collectionAxiom n ψ) ↔
      ∀ xs : Fin (n + 1) → M,
        (∀ x, memM x (xs (Fin.last n)) →
          ∃ y, ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) →
        ∃ v, (∀ x, memM x (xs (Fin.last n)) →
                ∃ y, memM y v ∧ ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) ∧
             (∀ y, memM y v →
                ∃ x, memM x (xs (Fin.last n)) ∧
                  ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y)) := by
  unfold collectionAxiom memM
  simp only [Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_rel₂, BoundedFormula.realize_bdEqual,
    Term.realize_var, Sum.elim_inr]
  simp only [BoundedFormula.realize_liftAt (show n ≤ n + 2 by omega)]
  simp only [comp_liftFun₁, comp_liftFun₂, comp_liftFun₃]
  simp (disch := simp +arith [Fin.val_mk]) only [snoc_of_lt, snoc_of_eq]
  simp only [exists_eq_left]
  rfl

end mathlib

/-! ### The Flypitch side -/

section flypitch

variable (S : Fol.Structure L_ZFC)

/-- `a ∈ b` in a Flypitch structure for `L_ZFC`. -/
def memS (a b : S.carrier) : Prop := S.rel_map ZFC_rel.ε (DVec.cons a (DVec.cons b DVec.nil))

variable {S}

@[simp] lemma realize_mem' {n : ℕ} (v : DVec S n) (t₁ t₂ : bounded_term L_ZFC n) :
    realize_bounded_formula v (mem' t₁ t₂) DVec.nil ↔
      memS S (realize_bounded_term v t₁ DVec.nil) (realize_bounded_term v t₂ DVec.nil) :=
  Iff.rfl

/-- The meaning of Flypitch's `axiom_of_collection ϕ`, `ϕ : bounded_formula L_ZFC (n + 2)` with
`&0 = y`, `&1 = x` and `&2, …` the parameters. -/
theorem realize_axiom_of_collection [Nonempty S] {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2)) :
    (S ⊨ₘ axiom_of_collection ϕ) ↔
      ∀ (u : S) (xs : DVec S n),
        (∀ x, memS S x u →
          ∃ y, realize_bounded_formula (DVec.cons y (DVec.cons x xs)) ϕ DVec.nil) →
        ∃ v, (∀ x, memS S x u → ∃ y, memS S y v ∧
                realize_bounded_formula (DVec.cons y (DVec.cons x xs)) ϕ DVec.nil) ∧
             (∀ y, memS S y v → ∃ x, memS S x u ∧
                realize_bounded_formula (DVec.cons y (DVec.cons x xs)) ϕ DVec.nil) := by
  simp only [axiom_of_collection, realize_sentence_bd_alls]
  constructor
  · intro h u xs
    have := h (DVec.cons u xs)
    simpa only [realize_bounded_formula_imp, realize_bounded_formula, realize_bounded_formula_ex,
      realize_bounded_formula_and, realize_mem', realize_bounded_term, DVec.nth,
      realize_formula_insert_lift2, realize_lift2_at2, realize_lift3_at2,
      realize_subst_formula0] using this
  · intro h xs
    cases xs with
    | cons u xs =>
      simpa only [realize_bounded_formula_imp, realize_bounded_formula, realize_bounded_formula_ex,
        realize_bounded_formula_and, realize_mem', realize_bounded_term, DVec.nth,
        realize_formula_insert_lift2, realize_lift2_at2, realize_lift3_at2,
        realize_subst_formula0] using h u xs

end flypitch

/-! ### Transfer -/

section transfer

variable (S : Fol.Structure L_ZFC)

attribute [local instance] toM

lemma memM_toM (a b : S.carrier) : memM (M := S.carrier) a b ↔ memS S a b := Iff.rfl

/-- If `S` satisfies Flypitch's collection axiom for `tr ψ`, then `toM S` satisfies the Mathlib-side
collection axiom for `ψ`. -/
theorem toM_realize_collectionAxiom [Nonempty S] {n : ℕ} (ψ : L.BoundedFormula Empty (n + 2))
    (h : S ⊨ₘ axiom_of_collection (tr ψ)) : S.carrier ⊨ collectionAxiom n ψ := by
  rw [realize_collectionAxiom]
  rw [realize_axiom_of_collection] at h
  intro xs
  have key : ∀ x y : S.carrier,
      ψ.Realize default (Fin.snoc (Fin.snoc (Fin.init xs) x) y) ↔
        realize_bounded_formula (DVec.cons y (DVec.cons x (dvecOfCtx (Fin.init xs)))) (tr ψ)
          DVec.nil := by
    intro x y
    rw [realize_tr S default ψ, dvecOfCtx_snoc, dvecOfCtx_snoc]
  simp only [key, memM_toM]
  exact h (xs (Fin.last n)) (dvecOfCtx (Fin.init xs))

end transfer

end Erdos501.FOL
