import ErdosProblems.Erdos964.ScalarKernelPolynomialError

/-!
# Normalized transform error in the second scalar kernel

After division by the fourth power of the logarithm, the transform error
vanishes with the radius. The omitted prime-divisor mass is bounded by a
constant divided by the distinguished prime.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_scalarTransformErrorEnvelope_div_log (M : ℕ) (K C : ℝ) :
    Tendsto (fun R : ℕ => scalarTransformErrorEnvelope M R K C / Real.log R)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hconst := hlog.const_div_atTop (K + primeLogDivisorMass M + C + 2 + Real.log 2)
  have h := (hsmall.add hconst).const_mul (81 * coprimeHarmonicDensity M)
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  exact Eventually.of_forall (fun R => by
    simp only [Function.comp_apply, id_eq, scalarTransformErrorEnvelope]
    ring)

noncomputable def scalarKernelTransformTail (M R : ℕ) (K C D : ℝ) : ℝ :=
  4 * D * (2 * scalarTransformErrorEnvelope M R K C / Real.log R) *
    (2 * scalarTransformErrorEnvelope M R K C / Real.log R +
      16 * coprimeHarmonicDensity M)

theorem tendsto_scalarKernelTransformTail (M : ℕ) (K C D : ℝ) :
    Tendsto (fun R : ℕ => scalarKernelTransformTail M R K C D) atTop (𝓝 0) := by
  have h := (tendsto_scalarTransformErrorEnvelope_div_log M K C).const_mul 2
  have h' := (h.const_mul (4 * D)).mul (h.add_const (16 * coprimeHarmonicDensity M))
  simp only [mul_zero, zero_add, zero_mul] at h'
  simpa only [scalarKernelTransformTail, mul_div_assoc] using h'

theorem exists_scalar_prime_kernel_normalized_polynomial_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    ∃ K C D : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ D ∧ ∀ R p : ℕ,
      2 ≤ Real.log R → p.Prime → p.Coprime M →
      |scalarCandidatePrimeKernel M R p / (Real.log R) ^ 4 -
        scalarPolynomialPrimeKernel M R p / (Real.log R) ^ 4| ≤
        scalarKernelTransformTail M R K C D +
          (2048 * D * coprimeHarmonicDensity M ^ 2) / p := by
  obtain ⟨K, C, D, hK, hC, hD, herror⟩ :=
    exists_scalar_prime_kernel_polynomial_error M hM h2M h3M
  refine ⟨K, C, D, hK, hC, hD, ?_⟩
  intro R p hR hp hpM
  let L := Real.log R
  let e := scalarTransformErrorEnvelope M R K C
  let δ := coprimeHarmonicDensity M
  let B := (2 * e / L) * (2 * e / L + 16 * δ) + (512 / (p : ℝ)) * δ ^ 2
  have hL : 0 < L := by dsimp only [L]; linarith
  have he : 0 ≤ e := scalarTransformErrorEnvelope_nonneg M R K C hK.le hC hR
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hr0 : 0 ≤ (1 + L) / L := by positivity
  have hr2 : (1 + L) / L ≤ 2 := (div_le_iff₀ hL).mpr (by dsimp only [L]; linarith)
  have hrsq : ((1 + L) / L) ^ 2 ≤ 4 := by nlinarith
  calc
    _ = |scalarCandidatePrimeKernel M R p - scalarPolynomialPrimeKernel M R p| / L ^ 4 := by
      rw [← sub_div, abs_div, abs_of_pos (pow_pos hL 4)]
    _ ≤ (D * (1 + L) ^ 2 *
        ((2 * e) * (2 * e + 16 * (δ * L)) + (512 / (p : ℝ)) * δ ^ 2 * L ^ 2)) /
          L ^ 4 := div_le_div_of_nonneg_right (herror R p hR hp hpM) (by positivity)
    _ = D * ((1 + L) / L) ^ 2 * B := by dsimp only [B]; field_simp
    _ ≤ D * 4 * B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrsq hD) hB
    _ = _ := by dsimp only [scalarKernelTransformTail, B, e, δ, L]; ring

end Erdos964
