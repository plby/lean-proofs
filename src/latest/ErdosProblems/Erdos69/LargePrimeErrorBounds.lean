import ErdosProblems.Erdos69.CharacteristicLimits

/-! # Removing the large-prime contribution in the concrete construction -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem smallPrimeCutoff_le_intermediate (m : ℕ) :
    smallPrimeCutoff m ≤ intermediatePrimeCutoff m := by
  have hB := fluctuationScale_pos m
  simpa only [intermediatePrimeCutoff, pow_one] using Nat.pow_le_pow_right (smallPrimeCutoff_pos m)
    (show 1 ≤ 20 * fluctuationScale m by omega)

theorem intermediatePrimeCutoff_ge_two (m : ℕ) : 2 ≤ intermediatePrimeCutoff m :=
  (smallPrimeCutoff_ge_two m).trans (smallPrimeCutoff_le_intermediate m)

theorem primeWindow_card_le (y R : ℕ) : (primeWindow y R).card ≤ R := by
  have hsubset : primeWindow y R ⊆ Finset.Icc 1 R := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsubset

theorem primeWindow_frequency_le_one (m : ℕ) :
    ((primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card : ℝ) /
      progressionLength m ≤ 1 := by
  have hR := intermediatePrimeCutoff_ge_two m
  have hcard := primeWindow_card_le (smallPrimeCutoff m) (intermediatePrimeCutoff m)
  have hle : (primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card ≤
      progressionLength m := by
    rw [← intermediatePrimeCutoff_square]
    nlinarith
  exact (div_le_one (by exact_mod_cast progressionLength_pos m : (0 : ℝ) < progressionLength m)).mpr
    (by exact_mod_cast hle)

theorem upper_log_ratio_le_three {m : ℕ} (hm : 0 < m) :
    Real.log (constructionUpperBound m : ℝ) / Real.log (intermediatePrimeCutoff m : ℝ) ≤ 3 := by
  have hpos : 0 < Real.log (intermediatePrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast intermediatePrimeCutoff_ge_two m)
  apply (div_le_iff₀ hpos).mpr
  have hX := log_constructionUpperBound_le hm
  have hE : (2 : ℝ) * excludedPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast twice_excluded_le_two_pow_scale hm
  have hB : (1 : ℝ) ≤ fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  have hpow : 0 ≤ (2 : ℝ) ^ fluctuationScale m := by positivity
  have hlower := mul_le_mul_of_nonneg_right half_le_log_two hpow
  have hmul := mul_le_mul_of_nonneg_right hB hpow
  rw [log_progressionLength] at hX
  rw [log_intermediatePrimeCutoff]
  nlinarith [mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ (20 : ℝ) * fluctuationScale m)]

theorem largePrime_parameter_error_le {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) :
    primeReciprocalSum (intermediatePrimeCutoff m) - primeReciprocalSum (smallPrimeCutoff m) +
      ((primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card : ℝ) / progressionLength m +
      Real.log (constructionUpperBound m : ℝ) / Real.log (intermediatePrimeCutoff m : ℝ) ≤
        Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4 := by
  have hR := primeReciprocalSum_upper hC _ (intermediatePrimeCutoff_ge_two m)
  have hy := primeReciprocalSum_lower hC _ (smallPrimeCutoff_ge_two m)
  have hlog := log_log_intermediate_sub_small m
  linarith [primeWindow_frequency_le_one m, upper_log_ratio_le_three hm]

noncomputable def constructionRetainedValue (q : ℝ) (m t : ℕ) : ℝ :=
  ∑ r : ConstructionShift m, constructionCoefficient m q r * omegaCount (constructionPoint m t + r.val)

noncomputable def retainedCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase (constructionRetainedValue q m t.val))

theorem construction_retained_compare_small {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) (q : ℝ) :
    ‖retainedCharacteristic q m‖ ≤ ‖smallCharacteristic q m‖ +
      2 * Real.pi * coefficientMassBound q m * (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4) := by
  have h := FiniteLaw.affine_omega_fourier_compare_small
    (progressionLength m) (constructionModulus m) (constructionBase m)
    (smallPrimeCutoff m) (intermediatePrimeCutoff m) (constructionUpperBound m)
    (progressionLength_pos m) (constructionModulus_pos m) (constructionModulus_le_smallPrimeCutoff hm)
    (smallPrimeCutoff_le_intermediate m) (by have h := intermediatePrimeCutoff_ge_two m; omega)
    (fun r : ConstructionShift m ↦ r.val) (constructionCoefficient m q)
    (fun t r ↦ by have hp := constructionPoint_pos m t.val; change 0 < constructionPoint m t.val + r.val; omega)
    (sampled_shift_le_upper m)
  have heq (t : Fin (progressionLength m)) :
      (∑ p ∈ freePrimes (constructionModulus m) (smallPrimeCutoff m),
        ∑ r : ConstructionShift m, constructionCoefficient m q r *
          (if p ∣ constructionBase m + constructionModulus m * t.val + r.val then (1 : ℝ) else 0)) =
        constructionSmallValue q m t.val := by
    exact (Finset.sum_coe_sort _ _).symm
  simp_rw [heq] at h
  apply h.trans
  apply add_le_add le_rfl
  have hnonneg : 0 ≤ Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4 := by positivity
  calc
    _ ≤ 2 * Real.pi * (∑ r : ConstructionShift m, |constructionCoefficient m q r|) *
        (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4) := by
      exact mul_le_mul_of_nonneg_left (largePrime_parameter_error_le hC hm) (by positivity)
    _ ≤ _ := by
      gcongr
      exact constructionCoefficient_mass_le m q

theorem tendsto_retainedCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖retainedCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := tendsto_coefficientMassBound_affine q (4 * Real.log 36) (Real.log 20 + 2 * C + 4)
  have he : Tendsto (fun m : ℕ ↦ 2 * Real.pi * coefficientMassBound q m *
      (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4)) atTop (𝓝 0) := by
    convert! hε.const_mul (2 * Real.pi) using 1
    · funext m
      ring
    · ring
  have hlim := (tendsto_smallCharacteristic_norm hq).add he
  simp only [add_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact construction_retained_compare_small hC0 hC (by omega) q

end Erdos69.Elementary
