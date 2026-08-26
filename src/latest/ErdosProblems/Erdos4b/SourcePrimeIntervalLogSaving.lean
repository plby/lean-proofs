/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourcePrimeIntervalCount
import BoundedGaps.BombieriVinogradov.Analytic.WeightedPntPrefix

/-!
# Arbitrary logarithmic saving for natural Chebyshev endpoints

The strong modulus-one Chebyshev estimate supplies the psi error.
The prime-power remainder is bounded by a fixed multiple of the square
root, which is absorbed into any inverse logarithmic power.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

theorem exists_chebyshevPsi_nat_logSaving (L : ℕ) :
    ∃ C ≥ 0, ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ x : ℕ, X₀ ≤ x →
      |Chebyshev.psi (x : ℝ) - (x : ℝ)| ≤ C * (x : ℝ) / Real.log x ^ L := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ :=
    BoundedGaps.BombieriVinogradov.exists_maxWeightedProgressionDiscrepancyUpTo_one_le_logSaving
      (L : ℝ) (Nat.cast_nonneg L)
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := by omega
  have hpoint : |Chebyshev.psi (x : ℝ) - (x : ℝ)| ≤
      BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo x 1 := by
    rw [BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo_one hx2]
    exact Finset.le_sup' (fun y : ℕ ↦ |Chebyshev.psi (y : ℝ) - (y : ℝ)|)
      (Finset.mem_Icc.mpr ⟨hx2, le_rfl⟩)
  have hpow : Real.rpow (Real.log x) (L : ℝ) = Real.log x ^ L := Real.rpow_natCast _ _
  simpa only [hpow] using hpoint.trans (hbound x hx)

theorem eventually_sqrt_nat_le_div_log_pow (L : ℕ) :
    ∀ᶠ x : ℕ in atTop, Real.sqrt (x : ℝ) ≤ (x : ℝ) / Real.log x ^ L := by
  have hdom := ((isLittleO_log_rpow_rpow_atTop (L : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto tendsto_natCast_atTop_atTop).eventuallyLE
  filter_upwards [hdom, eventually_ge_atTop 2] with x hpoly hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hpoly' : Real.log (x : ℝ) ^ (L : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog.le (L : ℝ)),
      abs_of_nonneg (Real.rpow_nonneg hxpos.le (1 / 2 : ℝ))] using hpoly
  rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow] at hpoly'
  apply (le_div_iff₀ (pow_pos hlog L)).mpr
  calc
    Real.sqrt (x : ℝ) * Real.log x ^ L ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
      mul_le_mul_of_nonneg_left hpoly' (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt hxpos.le

theorem exists_chebyshevTheta_nat_logSaving (L : ℕ) :
    ∃ C ≥ 0, ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ x : ℕ, X₀ ≤ x →
      |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤ C * (x : ℝ) / Real.log x ^ L := by
  obtain ⟨C, hC, X₀, hX₀, hpsi⟩ := exists_chebyshevPsi_nat_logSaving L
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (eventually_sqrt_nat_le_div_log_pow L)
  refine ⟨C + max K 0, by positivity, max X₀ X₁, hX₀.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hpsix := hpsi x ((le_max_left _ _).trans hx)
  have hsqrt := hX₁ x ((le_max_right _ _).trans hx)
  have hdiff : Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
      max K 0 * Real.sqrt (x : ℝ) :=
    (hK (x : ℝ)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have htri := abs_sub_le (Chebyshev.theta (x : ℝ)) (Chebyshev.psi (x : ℝ)) (x : ℝ)
  rw [abs_of_nonpos (sub_nonpos.mpr (Chebyshev.theta_le_psi _))] at htri
  calc
    _ ≤ |Chebyshev.psi (x : ℝ) - (x : ℝ)| + max K 0 * Real.sqrt (x : ℝ) := by linarith
    _ ≤ C * (x : ℝ) / Real.log x ^ L + max K 0 * ((x : ℝ) / Real.log x ^ L) :=
      add_le_add hpsix (mul_le_mul_of_nonneg_left hsqrt (le_max_right _ _))
    _ = _ := by ring

end

end Erdos4b
