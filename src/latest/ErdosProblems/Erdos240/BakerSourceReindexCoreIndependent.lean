/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.RationalPrimeBaker

/-!
# Dependency-light source reindexing identities

These are the finite-product and finite-sum identities behind transport from
an arbitrary old-prime index type to its canonical `Fin` enumeration.  This
core deliberately does not import the source assembly, so it remains usable
while downstream analytic modules are being rebuilt.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceReindexCoreIndependent

open RationalPrimeBaker

universe u v

/-- An indexed rational logarithmic form is invariant under a bijective
change of its old-prime coordinates. -/
theorem indexedRationalLogForm_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) (p : ℕ) (c : ι → ℤ) (d : ℤ) :
    indexedRationalLogForm (old ∘ e) p (c ∘ e) d =
      indexedRationalLogForm old p c d := by
  unfold indexedRationalLogForm
  have hsum : (∑ j : κ,
      ((c ∘ e) j : ℝ) * Real.log ((old ∘ e) j : ℝ)) =
        ∑ i : ι, (c i : ℝ) * Real.log (old i : ℝ) := by
    simpa only [Function.comp_apply] using
      e.sum_comp (fun i : ι ↦ (c i : ℝ) * Real.log (old i : ℝ))
  exact congrArg (fun x : ℝ ↦ x + (d : ℝ) * Real.log (p : ℝ)) hsum

/-- The old normalized-height product is invariant under a finite
equivalence. -/
theorem normalizedOldHeight_prod_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) :
    (∏ j : κ,
        max (Real.exp (Real.exp 1)) ((old (e j) : ℝ) + 1)) =
      ∏ i : ι,
        max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1) := by
  exact e.prod_comp
    (fun i : ι ↦ max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1))

/-- The product of the logarithms of the old normalized heights is likewise
invariant. -/
theorem log_normalizedOldHeight_prod_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) :
    (∏ j : κ, Real.log
        (max (Real.exp (Real.exp 1)) ((old (e j) : ℝ) + 1))) =
      ∏ i : ι, Real.log
        (max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1)) := by
  exact e.prod_comp
    (fun i : ι ↦ Real.log
      (max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1)))

end Erdos240.BakerSourceReindexCoreIndependent

#print axioms Erdos240.BakerSourceReindexCoreIndependent.indexedRationalLogForm_comp_equiv
#print axioms Erdos240.BakerSourceReindexCoreIndependent.normalizedOldHeight_prod_comp_equiv
#print axioms Erdos240.BakerSourceReindexCoreIndependent.log_normalizedOldHeight_prod_comp_equiv
