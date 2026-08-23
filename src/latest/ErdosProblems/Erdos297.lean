/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 297.
https://www.erdosproblems.com/forum/thread/297

Informal authors:
- Yang P. Liu
- Mehtaab Sawhney

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos297.md
-/
import ErdosProblems.Erdos297.Constant
import ErdosProblems.Erdos297.LimitAssembly
import ErdosProblems.Erdos297.Lower
import ErdosProblems.Erdos297.Subunit
import ErdosProblems.Erdos297.Upper

/-!
# Erdős Problem 297

Let `count N` be the number of subsets `A ⊆ {1, ..., N}` whose reciprocal
sum is exactly one in `ℚ`.  The theorem below proves the sharp asymptotic

`count N = exp ((gamma lam + o(1)) * N)`

where `lam` is the unique positive solution of the integral moment equation.
The equivalent base-two exponent is `binaryExponent lam`, and it is strictly
less than one.
-/

namespace Erdos297

noncomputable section

/-- Resolution of Erdős Problem 297 in natural-logarithm form.  The count is
the exact rational reciprocal-sum count from `Basic.lean`. -/
theorem erdos_297 : NaturalLogResolution := by
  obtain ⟨lam, hlam⟩ := exists_unique_criticalParameter
  refine ⟨lam, hlam, ?_⟩
  exact tendsto_logGrowth_of_eventual_bounds lam
    (fun _epsilon hepsilon ↦
      eventually_gamma_sub_le_logGrowth hlam hepsilon)
    (fun _epsilon hepsilon ↦
      eventually_logGrowth_le_gamma_add hlam.1.1 hepsilon)

/-- The customary `2^((c + o(1))N)` formulation, with
`c = binaryExponent lam`. -/
theorem erdos_297_binary : BinaryLogResolution :=
  binaryLogResolution_iff_naturalLogResolution.mpr erdos_297

/-- The sharp base-two exponent in the resolution is strictly below one. -/
theorem erdos_297_exponent_lt_one :
    ∃ lam : ℝ, IsUniqueCriticalParameter lam ∧ binaryExponent lam < 1 := by
  obtain ⟨lam, hlam⟩ := exists_unique_criticalParameter
  exact ⟨lam, hlam, binaryExponent_lt_one_of_isUniqueCriticalParameter hlam⟩

end

end Erdos297

#print axioms Erdos297.erdos_297
#print axioms Erdos297.erdos_297_binary
#print axioms Erdos297.erdos_297_exponent_lt_one
