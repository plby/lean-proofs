/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The unconditional Bernoulli strong law for distinct roots in [-1,1].
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PositiveDyadicStrongLaw
import ErdosProblems.Erdos521.DyadicInterpolation

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem ae_interiorRootCount_dyadic_div_log_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦ (interiorRootCount ε (2 ^ j) : ℝ) /
      Real.log ((2 ^ j : ℕ) : ℝ)) atTop (𝓝 (1 / Real.pi)) := by
  have hsym := measurePreserving_alternateSigns.quasiMeasurePreserving.ae
    ae_positiveRootCount_dyadic_div_log_limit
  filter_upwards [ae_positiveRootCount_dyadic_div_log_limit, hsym, ae_sequence_signs]
    with ε hpos hneg hsign
  have hε₀ : ε 0 ≠ 0 := by rcases hsign 0 with h | h <;> simp [h]
  convert hpos.add hneg using 1
  · funext j
    rw [interiorRootCount_eq_positive_add_alternate ε _ hε₀, Nat.cast_add, add_div]
  · congr 1
    field_simp
    ring

theorem ae_interiorRootCount_div_log_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun n : ℕ ↦ (interiorRootCount ε n : ℝ) / Real.log n)
      atTop (𝓝 (1 / Real.pi)) := by
  filter_upwards [ae_interiorRootCount_dyadic_div_log_limit, ae_interiorRootCount_dyadic_error]
    with ε hdyadic herror
  exact tendsto_of_dyadic_normalized_error (fun n ↦ (interiorRootCount ε n : ℝ))
    (1 / Real.pi) herror hdyadic

end Erdos521
