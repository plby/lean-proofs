/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The actual and capped natural-valued central statistics.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CappedCentralNat
import ErdosProblems.Erdos521.DyadicFineGrid
import ErdosProblems.Erdos521.CentralIntervalMean
import ErdosProblems.Erdos521.CentralIntervalMoments

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

noncomputable def centralRootCount (ε : ℕ → ℝ) (j : ℕ) : ℕ :=
  intervalRootCount ε (2 ^ j) (dyadicPoint (Nat.sqrt j)) (dyadicPoint (j - Nat.sqrt j))

noncomputable def centralCappedCount (ε : ℕ → ℝ) (j : ℕ) : ℕ :=
  cappedCentralNatSum ε j (dyadicFineGrid j) (fun _ ↦ fineGridLength j)

theorem centralRootCount_aemeasurable (j : ℕ) : AEMeasurable (fun ε ↦ centralRootCount ε j) sequenceLaw :=
  intervalRootCount_aemeasurable _ _ _

theorem centralCappedCount_measurable (j : ℕ) : Measurable (fun ε ↦ centralCappedCount ε j) :=
  measurable_cappedCentralNatSum _ _ _

theorem centralRootCount_le (ε : ℕ → ℝ) (j : ℕ) : centralRootCount ε j ≤ 2 ^ j :=
  intervalRootCount_le _ _ _ _

theorem centralCappedCount_le (ε : ℕ → ℝ) (j : ℕ) : centralCappedCount ε j ≤ j * windowCapScale j :=
  cappedCentralNatSum_le _ _ _ _

theorem centralRootCount_pow_integrable (j p : ℕ) :
    Integrable (fun ε ↦ (centralRootCount ε j : ℝ) ^ p) sequenceLaw := intervalRootCount_pow_integrable _ _ _ _

theorem centralCappedCount_pow_integrable (j p : ℕ) :
    Integrable (fun ε ↦ (centralCappedCount ε j : ℝ) ^ p) sequenceLaw := cappedCentralNatSum_pow_integrable _ _ _ _

theorem centralRootCount_mean_div_index_limit :
    Tendsto (fun j : ℕ ↦ (∫ ε, (centralRootCount ε j : ℝ) ∂sequenceLaw) / j)
      atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := central_interval_mean_div_index_limit

theorem centralRootCount_moments (p : ℕ) (hp : 1 ≤ p) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop,
      (∫ ε, (centralRootCount ε j : ℝ) ^ p ∂sequenceLaw) ≤ (j : ℝ) ^ p * B :=
  eventually_central_interval_moments p hp

end Erdos521
