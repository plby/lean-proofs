import ErdosProblems.Erdos4.FGKMTExponentialDistribution
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeAbel

/-! Uniform prime-counting distribution after one prime is omitted. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

noncomputable def primeDiscrepancyUpTo (x q : ℕ) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y => maxProgressionDiscrepancy y q)
  else 0

noncomputable def excisedPrimeSum (x Q B : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B), primeDiscrepancyUpTo x q

theorem maxProgressionDiscrepancy_le_primeDiscrepancyUpTo
    {x y q : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    maxProgressionDiscrepancy y q ≤ primeDiscrepancyUpTo x q := by
  rw [primeDiscrepancyUpTo, dif_pos (hy.trans hyx)]
  exact Finset.le_sup' (fun z => maxProgressionDiscrepancy z q)
    (Finset.mem_Icc.mpr ⟨hy, hyx⟩)

theorem thetaMaximum_mono {x y q : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    maxCenteredThetaProgressionDiscrepancyUpTo y q ≤
      maxCenteredThetaProgressionDiscrepancyUpTo x q := by
  rw [maxCenteredThetaProgressionDiscrepancyUpTo, dif_pos hy,
    maxCenteredThetaProgressionDiscrepancyUpTo, dif_pos (hy.trans hyx)]
  apply Finset.sup'_le
  intro z hz
  exact Finset.le_sup' (fun z => maxCenteredThetaProgressionDiscrepancy z q)
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hz).1, (Finset.mem_Icc.mp hz).2.trans hyx⟩)

theorem primeDiscrepancyUpTo_le {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    primeDiscrepancyUpTo x q ≤ (Real.log 2)⁻¹ *
      (maxCenteredProgressionDiscrepancyUpTo x q +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  have hlog : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos (by norm_num))).le
  rw [primeDiscrepancyUpTo, dif_pos hx]
  apply Finset.sup'_le
  intro y hy
  have hyy := Finset.mem_Icc.mp hy
  exact (maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo hyy.1 hq).trans
    (mul_le_mul_of_nonneg_left
      ((thetaMaximum_mono hyy.1 hyy.2).trans (maxCenteredThetaProgressionDiscrepancyUpTo_le hq)) hlog)

theorem excisedPrimeSum_le {x Q B : ℕ} (hx : 2 ≤ x) :
    excisedPrimeSum x Q B ≤ (Real.log 2)⁻¹ *
      (excisedCenteredSum x Q B + (Q : ℝ) *
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  have hlog : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos (by norm_num))).le
  have hrem : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  unfold excisedPrimeSum
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B), (Real.log 2)⁻¹ *
        (maxCenteredProgressionDiscrepancyUpTo x q +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact primeDiscrepancyUpTo_le hx (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    _ = (Real.log 2)⁻¹ * (excisedCenteredSum x Q B +
        ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => q.Coprime B),
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hlog
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ _q ∈ Finset.Icc 1 Q, (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hrem)
        _ = _ := by simp [nsmul_eq_mul]; ring

theorem primePowerRemainder_power_level {x Q : ℕ} (hx : 1 ≤ x)
    (hQ : (Q : ℝ) ≤ vaughanCubeRoot x) :
    (Q : ℝ) * (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
      2 * ((x : ℝ) ^ (5 / 6 : ℝ) * Real.sqrt (Real.log (x : ℝ)) ^ 2) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog := Real.log_natCast_nonneg x
  calc
    _ ≤ (Q : ℝ) * (2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le hx1) (Nat.cast_nonneg Q)
    _ ≤ vaughanCubeRoot x * (2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by
      rw [Real.sq_sqrt hlog]
      calc
        _ = 2 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) * Real.log (x : ℝ) := by ring
        _ = _ := by rw [sqrt_mul_cubeRoot_eq_five_sixths hx]; ring

theorem exists_exponential_prime_distribution :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
          excisedPrimeSum x (powerDistributionLevel x) B ≤
            C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨a, C, ha, ha1, hC, hdist⟩ := exists_exponential_centered_distribution
  have hlog : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨a, (Real.log 2)⁻¹ * (C + 2), ha, ha1, by positivity, ?_⟩
  have hcut := eventually_distribution_cutoffs ha ha1
  have hrem := eventually_rpow_sqrtLog_pow_le_decay
    (α := (5 / 6 : ℝ)) (β := 1) (c := a / 2) (by norm_num) 2
  filter_upwards [hdist, hcut, hrem, eventually_ge_atTop 2] with x hdist hcut hrem hx
  obtain ⟨B, hBR, hB, hbound⟩ := hdist
  refine ⟨B, hBR, hB, ?_⟩
  have hprime := primePowerRemainder_power_level (by omega : 1 ≤ x) hcut.2.2.2.2.2.2.2
  have hrem' : (powerDistributionLevel x : ℝ) *
      (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
      2 * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
    exact hprime.trans (by simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ (Real.log 2)⁻¹ * (excisedCenteredSum x (powerDistributionLevel x) B +
        (powerDistributionLevel x : ℝ) * (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) :=
      excisedPrimeSum_le hx
    _ ≤ (Real.log 2)⁻¹ * (C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) +
        2 * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))))) :=
      mul_le_mul_of_nonneg_left (add_le_add hbound hrem') hlog.le
    _ = _ := by ring

end Erdos4.FGKMT
