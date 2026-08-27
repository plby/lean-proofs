import ErdosProblems.Erdos587.HooleySmoothQuadratic
import ErdosProblems.Erdos587.HooleyNonzeroLattice

/-! # Small primitive denominators and the retained zero mode -/

open scoped FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_small_denominator_centered_norm_bound {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ q : ℕ, 0 < q →
      ∀ a : ℤ, IsUnit (a : ZMod q) → ∀ K : ℝ, 0 < K → (q : ℝ) ≤ K →
      ‖deltaSmoothCenteredQuadratic f K q a‖ ≤ C * Real.sqrt (2 * K) := by
  obtain ⟨C, hC, hdecay⟩ := exists_delta_family_fourier_decay hW
  refine ⟨20 * C, by positivity, ?_⟩
  intro f hf q hq a ha K hK hqK
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let w := dilateSchwartz f K⁻¹ (inv_ne_zero hK.ne')
  let σ := K / (q : ℝ)
  let E := Real.sqrt (2 * (q : ℝ)) * K * C
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨hkernel, hkernelBound⟩ := delta_nonzero_lattice_decay_bound (div_pos hK hqR)
  change Summable (fun n : ℤ => if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2)
    at hkernel
  let F := fun n : ℤ => if n = 0 then (0 : ℂ) else
    completeQuadraticGaussSum q a n * 𝓕 w ((n : ℝ) / q)
  have hpoint (n : ℤ) : ‖F n‖ ≤
      E * (if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2) := by
    by_cases hn : n = 0
    · simp only [F, if_pos hn, norm_zero, mul_zero, le_refl]
    · simp only [F, if_neg hn]
      have harg : |K * ((n : ℝ) / q)| = σ * |(n : ℝ)| := by
        rw [abs_mul, abs_div, abs_of_pos hK, abs_of_pos hqR]
        dsimp only [σ]
        ring
      have hb := hdecay f hf (K * ((n : ℝ) / q))
      rw [harg] at hb
      rw [norm_mul, delta_fourier_dilate_inverse f hK, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hK.le]
      calc
        _ ≤ Real.sqrt (2 * (q : ℝ)) * (K * (C / (1 + σ * |(n : ℝ)|) ^ 2)) :=
          mul_le_mul (norm_completeQuadraticGaussSum_le_sqrt hq a n ha)
            (mul_le_mul_of_nonneg_left hb hK.le) (by positivity) (by positivity)
        _ = _ := by dsimp only [E]; ring
  have hsum : Summable F := Summable.of_norm_bounded (hkernel.mul_left E) hpoint
  have hnormsum : (∑' n : ℤ, ‖F n‖) ≤ E * (20 / σ ^ 2) := by
    calc
      _ ≤ ∑' n : ℤ, E *
          (if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2) :=
        hsum.norm.tsum_le_tsum hpoint (hkernel.mul_left E)
      _ = E * ∑' n : ℤ,
          if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2 := tsum_mul_left
      _ ≤ E * (20 / σ ^ 2) := mul_le_mul_of_nonneg_left hkernelBound hE
  calc
    _ = ‖(q : ℂ)⁻¹ * ∑' n : ℤ, F n‖ := by rw [delta_smooth_centered_poisson f hK hq a]
    _ ≤ (q : ℝ)⁻¹ * (E * (20 / σ ^ 2)) := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        ((norm_tsum_le_tsum_norm hsum.norm).trans hnormsum) (by positivity)
    _ = (20 * C) * Real.sqrt (2 * (q : ℝ)) * ((q : ℝ) / K) := by
      dsimp only [E, σ]
      field_simp
    _ ≤ (20 * C) * Real.sqrt (2 * (q : ℝ)) :=
      mul_le_of_le_one_right (by positivity) ((div_le_one hK).mpr hqK)
    _ ≤ (20 * C) * Real.sqrt (2 * K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.sqrt_le_sqrt (by linarith)

theorem exists_delta_small_denominator_centered_sq_bound {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ q : ℕ, 0 < q →
      ∀ a : ℤ, IsUnit (a : ZMod q) → ∀ K : ℝ, 0 < K → (q : ℝ) ≤ K →
      ‖deltaSmoothCenteredQuadratic f K q a‖ ^ 2 ≤ C * K := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_small_denominator_centered_norm_bound hW
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro f hf q hq a ha K hK hqK
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hbound f hf q hq a ha K hK hqK)
  apply h.trans_eq
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * K)]
  ring

theorem exists_delta_large_denominator_zero_mode_sq_bound {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ q : ℕ, 0 < q →
      ∀ a : ℤ, IsUnit (a : ZMod q) → ∀ K : ℝ, 0 < K → K ≤ (q : ℝ) →
      ‖deltaSmoothQuadraticMean f K q a‖ ^ 2 ≤ C * K := by
  obtain ⟨C, hC, hdecay⟩ := exists_delta_family_fourier_decay hW
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro f hf q hq a ha K hK hKq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hzero : ‖𝓕 f 0‖ ≤ C := by
    simpa only [abs_zero, add_zero, one_pow, div_one] using hdecay f hf 0
  have hnorm : ‖deltaSmoothQuadraticMean f K q a‖ ≤
      (K / q) * Real.sqrt (2 * (q : ℝ)) * C := by
    rw [deltaSmoothQuadraticMean, norm_mul, norm_mul, norm_div,
      Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hK.le]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_completeQuadraticGaussSum_le_sqrt hq a 0 ha) (by positivity))
      hzero (norm_nonneg _) (by positivity)
  calc
    _ ≤ ((K / q) * Real.sqrt (2 * (q : ℝ)) * C) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
    _ = (2 * C ^ 2) * (K ^ 2 / q) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (q : ℝ))]
      field_simp
    _ ≤ (2 * C ^ 2) * K := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ hqR).mpr
      nlinarith

end Erdos587
