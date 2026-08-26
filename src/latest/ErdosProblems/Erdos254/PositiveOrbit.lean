/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.InvariantMeasure

namespace Erdos254

open Filter MeasureTheory Set
open scoped Topology BigOperators

lemma birkhoffAverage_unit_bounds {X : Type*} (T : X → X) (g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (N : ℕ) (x : X) :
    0 ≤ birkhoffAverage ℝ T g (N + 1) x ∧ birkhoffAverage ℝ T g (N + 1) x ≤ 1 := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun k _ ↦ (hg _).1))
  · have hs : ∑ k ∈ Finset.range (N + 1), g (T^[k] x) ≤ (N + 1 : ℝ) := by
      simpa using Finset.sum_le_sum (s := Finset.range (N + 1)) (g := fun _ ↦ (1 : ℝ))
        (fun k _ ↦ (hg (T^[k] x)).2)
    calc
      _ ≤ (N + 1 : ℝ)⁻¹ * (N + 1) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)

/-- A positive integral of a bounded nonnegative observable produces an orbit
with positive upper average. This elementary dominated-convergence argument
does not require a pointwise ergodic theorem. -/
theorem exists_positive_orbit {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hTc : Continuous T) (hT : MeasurePreserving T μ μ)
    (g : C(X, ℝ)) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hpos : 0 < ∫ x, g x ∂μ) :
    ∃ x : X, ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in atTop,
      δ ≤ birkhoffAverage ℝ T g (N + 1) x := by
  have hc (N : ℕ) : Continuous (birkhoffAverage ℝ T g (N + 1)) := by
    change Continuous (fun x ↦ ((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ k ∈ Finset.range (N + 1), g (T^[k] x))
    apply continuous_const.mul
    exact continuous_finsetSum _ (fun k _ ↦ g.continuous.comp (hTc.iterate k))
  have hint (N : ℕ) : (∫ x, birkhoffAverage ℝ T g (N + 1) x ∂μ) = ∫ x, g x ∂μ := by
    simp only [birkhoffAverage, birkhoffSum]
    rw [integral_smul, integral_finsetSum]
    · have hiter (k : ℕ) : (∫ x, g (T^[k] x) ∂μ) = ∫ x, g x ∂μ := by
        rw [← integral_map_of_stronglyMeasurable (hT.iterate k).measurable
          g.continuous.stronglyMeasurable, (hT.iterate k).map_eq]
      simp_rw [hiter]
      have hN : (N + 1 : ℝ) ≠ 0 := by positivity
      simp [smul_eq_mul, hN]
    · intro k _
      exact (g.continuous.comp (hTc.iterate k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  by_contra! h
  have hlim (x : X) : Tendsto (fun N ↦ birkhoffAverage ℝ T g (N + 1) x) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun N ↦
        ha.trans_le (birkhoffAverage_unit_bounds T g hg N x).1
    · intro b hb
      exact h x b hb
  have hzero := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X ↦ (1 : ℝ))
    (fun N ↦ (hc N).aestronglyMeasurable) (integrable_const 1)
    (fun N ↦ Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (birkhoffAverage_unit_bounds T g hg N x).1]
      exact (birkhoffAverage_unit_bounds T g hg N x).2)
    (Filter.Eventually.of_forall hlim)
  have hconst : Tendsto (fun _ : ℕ ↦ ∫ x, g x ∂μ) atTop (𝓝 0) := by
    simpa only [hint, integral_zero] using hzero
  exact hpos.ne' (tendsto_nhds_unique tendsto_const_nhds hconst)

end Erdos254
