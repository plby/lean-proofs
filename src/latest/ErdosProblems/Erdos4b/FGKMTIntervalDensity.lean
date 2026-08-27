/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueDensityLower
import ErdosProblems.Erdos851.LocalEulerProducts

/-! # Two-sided density of a prime interval from weak Mertens estimates -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem residueSieveDensity_primeInterval_eq {v z : ℕ} (hvz : v ≤ z) :
    residueSieveDensity (commonPinnedPrimeSet v z) =
      partial_euler_product v / partial_euler_product z := by
  have hinv : (residueSieveDensity (commonPinnedPrimeSet v z))⁻¹ =
      partial_euler_product z / partial_euler_product v := by
    rw [residueSieveDensity, ← Finset.prod_inv_distrib]
    simpa only [commonPinnedPrimeSet, Erdos851.inverseLocalEulerProduct,
      Erdos851.oneShiftDensity, Erdos851.sievePrimes, one_div] using
      Erdos851.oneShift_inverseLocalEulerProduct_eq hvz
  simpa only [inv_inv, inv_div] using congrArg (fun t : ℝ => t⁻¹) hinv

theorem exists_primeInterval_density_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ v z : ℝ, 2 ≤ v → v ≤ z →
      A * (Real.log v / Real.log z) ≤
          residueSieveDensity (commonPinnedPrimeSet ⌊v⌋₊ ⌊z⌋₊) ∧
      residueSieveDensity (commonPinnedPrimeSet ⌊v⌋₊ ⌊z⌋₊) ≤
          B * (Real.log v / Real.log z) := by
  obtain ⟨M, hM, hupper⟩ := weak_mertens_third_upper_all
  obtain ⟨m, hm, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨m / M, M / m, div_pos hm hM, div_pos hM hm, ?_⟩
  intro v z hv hvz
  have hz : 2 ≤ z := hv.trans hvz
  have hvlog : 0 < Real.log v := Real.log_pos (by linarith)
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hvE : 0 < partial_euler_product ⌊v⌋₊ :=
    zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hzE : 0 < partial_euler_product ⌊z⌋₊ :=
    zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hvlower : m * Real.log v ≤ partial_euler_product ⌊v⌋₊ := by
    simpa only [Real.norm_of_nonneg hvlog.le, Real.norm_of_nonneg hvE.le] using
      hlower v (by linarith)
  have hvupper : partial_euler_product ⌊v⌋₊ ≤ M * Real.log v := by
    simpa only [Real.norm_of_nonneg hvlog.le, Real.norm_of_nonneg hvE.le] using hupper v hv
  have hzlower : m * Real.log z ≤ partial_euler_product ⌊z⌋₊ := by
    simpa only [Real.norm_of_nonneg hzlog.le, Real.norm_of_nonneg hzE.le] using
      hlower z (by linarith)
  have hzupper : partial_euler_product ⌊z⌋₊ ≤ M * Real.log z := by
    simpa only [Real.norm_of_nonneg hzlog.le, Real.norm_of_nonneg hzE.le] using hupper z hz
  rw [residueSieveDensity_primeInterval_eq (Nat.floor_mono hvz)]
  constructor
  · calc
      _ = (m * Real.log v) / (M * Real.log z) := by ring
      _ ≤ _ := div_le_div₀ (by positivity) hvlower hzE hzupper
  · calc
      _ ≤ (M * Real.log v) / (m * Real.log z) :=
        div_le_div₀ (by positivity) hvupper (mul_pos hm hzlog) hzlower
      _ = _ := by ring

end

end Erdos4b.FGKMT
