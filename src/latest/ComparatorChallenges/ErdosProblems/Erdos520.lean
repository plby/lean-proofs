/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Erdos.Problem520

abbrev Omega := ℕ → Bool

noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true

noncomputable def μ : Measure Omega :=
  Measure.infinitePi fun _ : ℕ => coin

def ε (omega : Omega) (p : ℕ) : ℝ :=
  if omega p then 1 else -1

noncomputable def f (omega : Omega) (n : ℕ) : ℝ :=
  if Squarefree n then
    ∏ p ∈ n.primeFactors, ε omega p
  else
    0

noncomputable def partialSum (omega : Omega) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f omega (k + 1)

theorem normalized_tendsto_zero :
    ∀ᵐ omega ∂μ, Tendsto (fun N : ℕ =>
      |partialSum omega N| / Real.sqrt ((N : ℝ) * Real.log (Real.log N)))
      atTop (𝓝 0) :=
  by sorry

theorem not_erdos_520 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᵐ omega ∂μ,
      limsup (fun N : ℕ =>
        partialSum omega N / Real.sqrt ((N : ℝ) * Real.log (Real.log N))) atTop = c := by
  sorry

end Erdos.Problem520
