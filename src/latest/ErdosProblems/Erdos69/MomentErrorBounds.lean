import ErdosProblems.Erdos69.ConstructionModel

/-! # Vanishing error in the concrete finite-moment comparison -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem construction_moment_ratio_le (m : ℕ) :
    (smallPrimeCutoff m : ℝ) ^ momentOrder m / progressionLength m ≤
      (1 : ℝ) / 2 ^ fluctuationScale m := by
  have hy : (0 : ℝ) < smallPrimeCutoff m := by exact_mod_cast smallPrimeCutoff_pos m
  have hp : (2 : ℝ) ^ fluctuationScale m ≤
      (smallPrimeCutoff m : ℝ) ^ (38 * fluctuationScale m) := by
    calc
      _ ≤ (smallPrimeCutoff m : ℝ) ^ fluctuationScale m :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast smallPrimeCutoff_ge_two m) _
      _ ≤ _ := pow_le_pow_right₀ (by have h := smallPrimeCutoff_ge_two m
                                     exact_mod_cast (show 1 ≤ smallPrimeCutoff m by omega)) (by omega)
  calc
    _ = (1 : ℝ) / (smallPrimeCutoff m : ℝ) ^ (38 * fluctuationScale m) := by
      rw [smallPrimeCutoff_moment_ratio, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      field_simp
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hp

noncomputable def modelComparisonError (m : ℕ) : ℝ :=
  (2 * Real.exp (2 * Real.pi) + 8) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m

theorem tendsto_modelComparisonError : Tendsto modelComparisonError atTop (𝓝 0) := by
  have h := tendsto_scale_tail.const_mul (2 * Real.exp (2 * Real.pi) + 8)
  change Tendsto (fun m ↦ (2 * Real.exp (2 * Real.pi) + 8) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using h

theorem construction_mgf_exp_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (q : ℝ) (m : ℕ)
    (hε : (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 * (Real.log 2 + C + 1) ≤ Real.log 2) :
    Real.exp ((4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 *
      ∑ p : ConstructionPrime m, (1 : ℝ) / p.val) ≤ (2 : ℝ) ^ fluctuationScale m := by
  have hmass := (constructionPrime_reciprocal_le m).trans (smallPrime_reciprocal_upper hC0 hC m)
  have h₁ := mul_le_mul_of_nonneg_left hmass
    (by positivity : 0 ≤ (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2)
  have h₂ := mul_le_mul_of_nonneg_right hε
    (by positivity : (0 : ℝ) ≤ fluctuationScale m)
  have he : Real.exp ((fluctuationScale m : ℝ) * Real.log 2) = (2 : ℝ) ^ fluctuationScale m := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [← he]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem construction_fourier_transfer_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) (q : ℝ) (hε : coefficientMassBound q m ≤ 1)
    (hsmall : 4 * Real.pi * coefficientMassBound q m ≤ 1)
    (hmgf : (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 * (Real.log 2 + C + 1) ≤ Real.log 2) :
    ‖smallCharacteristic q m - modelCharacteristic q m‖ ≤ modelComparisonError m := by
  have h := construction_fourier_transfer_raw hm q hε hsmall
  have he := construction_mgf_exp_le hC0 hC q m hmgf
  have hr := construction_moment_ratio_le m
  apply h.trans
  calc
    _ ≤ ((1 : ℝ) / 2 ^ fluctuationScale m) * (1 + momentOrder m) * Real.exp (2 * Real.pi) +
        4 * momentOrder m * (2 : ℝ) ^ fluctuationScale m * (1 / 2 : ℝ) ^ momentOrder m := by
      gcongr
    _ = ((1 + 2 * fluctuationScale m) * Real.exp (2 * Real.pi) + 8 * fluctuationScale m) /
        (2 : ℝ) ^ fluctuationScale m := by
      simp only [momentOrder, Nat.cast_mul, Nat.cast_ofNat, pow_mul, div_pow, one_pow]
      rw [pow_right_comm (2 : ℝ) 2 (fluctuationScale m)]
      field_simp
      ring
    _ ≤ modelComparisonError m := by
      unfold modelComparisonError
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [Real.exp_pos (2 * Real.pi)]

theorem tendsto_small_sub_model_norm (q : ℝ) :
    Tendsto (fun m ↦ ‖smallCharacteristic q m - modelCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := tendsto_coefficientMassBound q
  have hsmall := hε.const_mul (4 * Real.pi)
  have hmgf := ((hε.pow 2).const_mul ((4 * Real.pi) ^ 2)).mul_const (Real.log 2 + C + 1)
  simp only [mul_zero, zero_pow (by omega : 2 ≠ 0), zero_mul] at hsmall hmgf
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ tendsto_modelComparisonError
  filter_upwards [eventually_ge_atTop (1 : ℕ), hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hmgf.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
    with m hm he hs hg
  exact construction_fourier_transfer_le hC0 hC (by omega) q he.le hs.le hg.le

end Erdos69.Elementary
