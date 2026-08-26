import ErdosProblems.Erdos796.Baseline
import ErdosProblems.Erdos796.GammaFinite
import ErdosProblems.Erdos796.Statement

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact excess decomposition of the finite cofactor model

Subtracting the prime baseline from a model score leaves the bucket-weighted
cofactor excess exactly.  This identity is the algebraic entry point for the
cofactor-model limit.
-/

namespace Erdos796

open scoped BigOperators

/-- Real bucket-weighted excess of one cofactor family. -/
noncomputable def modelExcessSum (n : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt,
    (bucketCount n j : ℝ) * excess U j

theorem excess_eq_card_sub_prime (U : ℕ → Finset ℕ) (j : ℕ) :
    excess U j =
      ((U j).card : ℝ) - 1 - (Nat.primeCounting j : ℝ) := by
  simp [excess, excessInt, Int.cast_sub, Int.cast_natCast]

/-- Exact finite identity `modelScore - baseline = Σ N_j e_j`. -/
theorem modelScore_sub_baseline_eq_modelExcessSum
    (n : ℕ) (U : ℕ → Finset ℕ) :
    (modelScore n U : ℝ) - (baseline n : ℝ) = modelExcessSum n U := by
  rw [modelScore, baseline, modelExcessSum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [excess_eq_card_sub_prime]
  ring

theorem normalized_modelScore_sub_baseline_eq
    (n : ℕ) (U : ℕ → Finset ℕ) :
    ((modelScore n U : ℝ) - (baseline n : ℝ)) / secondOrderScale n =
      modelExcessSum n U / secondOrderScale n := by
  rw [modelScore_sub_baseline_eq_modelExcessSum]

end Erdos796
