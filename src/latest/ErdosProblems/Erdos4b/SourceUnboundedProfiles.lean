/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceGridVariational
import ErdosProblems.Erdos4b.SourceRescaledRectangles

/-!
# Smooth compact source profiles with unbounded variational quotient

The theorem constructs all regularity, support and positivity data. Its
only input is the requested real lower bound for the actual source ratio.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_sourceProfile_ratio_gt (L : ℝ) :
    ∃ K : ℕ, ∃ I : Type, ∃ S : Finset I, ∃ F : I → Fin K → ℝ → ℝ,
      SourceProfileConditions S F sourceCompanionProfile ∧
        L < sourceProfileRatio S F sourceCompanionProfile := by
  obtain ⟨K, A, n, hK, hA, hI, hJ, hL⟩ := exists_sourceGrid_ratio_gt (10 * sourceCompanionEnergy * L)
  let S := sourceSimplexGrid K n
  let a := fun (j : Fin K → Fin (n + 1)) (i : Fin K) ↦ sourceGridLower n (j i)
  let b := fun (j : Fin K → Fin (n + 1)) (i : Fin K) ↦ sourceGridUpper n (j i)
  let c := fun (j : Fin K → Fin (n + 1)) (i : Fin K) ↦
    VariableMaynard.factor A ((K : ℝ) * sourceGridUpper n (j i))
  have hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i := by
    intro j hj i
    exact (sourceGridLower_nonneg n (j i)).trans (sourceGridLower_lt_upper n (j i)).le
  have hbudget : ∀ j ∈ S, (∑ i, b j i) ≤ (1 : ℝ) :=
    fun j hj ↦ mem_sourceSimplexGrid.mp hj
  obtain ⟨F, hF, hratio⟩ := exists_sourceProfile_of_unitRectangles hK S a b c hb hbudget hI hJ hL
  exact ⟨K, Fin K → Fin (n + 1), S, F, hF, hratio⟩

end

end Erdos4b
