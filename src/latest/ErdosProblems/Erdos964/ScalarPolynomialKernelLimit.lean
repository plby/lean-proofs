import ErdosProblems.Erdos964.ScalarPolynomialKernelFaceError

/-!
# Uniform normalized face approximation for the polynomial kernel
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem exists_scalar_polynomial_kernel_uniform_face_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, 2 ≤ R₀ ∧ ∀ R p : ℕ, R₀ ≤ R → 0 < p →
      |scalarPolynomialPrimeKernel M R p / (Real.log R) ^ 4 -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          scalarSieveFace (Real.log p / Real.log R)| < ε := by
  let a := 1296 * coprimeHarmonicDensity M ^ 2
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4
  let η := ε / (2 * (a + 1))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have haη : a * η < ε / 2 := by
    dsimp only [η]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hid : a * (ε / (2 * (a + 1))) * 2 = ε * (a / (a + 1)) := by
      field_simp
    rw [hid]
    exact (mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).mpr (by linarith)) hε).trans_eq
      (mul_one ε)
  obtain ⟨C, hC, herror⟩ := exists_scalar_polynomial_kernel_face_error M hM h2M h3M η hη
  have hlog : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail : Tendsto (fun R : ℕ => a * C / (Real.log R) ^ 2 +
      (132 * A * Real.log 2) / Real.log R) atTop (𝓝 0) := by
    have h₁ := ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hlog).const_div_atTop (a * C)
    have h₂ := hlog.const_div_atTop (132 * A * Real.log 2)
    simpa only [add_zero, Function.comp_apply] using h₁.add h₂
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp ((tendsto_order.mp htail).2 (ε / 2) (by linarith))
  refine ⟨max R₁ 2, le_max_right _ _, ?_⟩
  intro R p hR hp
  have hRtwo : 2 ≤ R := (le_max_right R₁ 2).trans hR
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hbound : |scalarPolynomialPrimeKernel M R p / (Real.log R) ^ 4 -
      A * scalarSieveFace (Real.log p / Real.log R)| ≤
      a * η + a * C / (Real.log R) ^ 2 + (132 * A * Real.log 2) / Real.log R := by
    have hid : scalarPolynomialPrimeKernel M R p / (Real.log R) ^ 4 -
        A * scalarSieveFace (Real.log p / Real.log R) =
        (scalarPolynomialPrimeKernel M R p - A * (Real.log R) ^ 4 *
          scalarSieveFace (Real.log p / Real.log R)) / (Real.log R) ^ 4 := by field_simp
    rw [hid, abs_div, abs_of_pos (pow_pos hL 4)]
    calc
      _ ≤ (1296 * coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 *
          (η * (Real.log R) ^ 2 + C) + 132 * A * (Real.log R) ^ 4 *
            (Real.log 2 / Real.log R)) / (Real.log R) ^ 4 :=
        div_le_div_of_nonneg_right (herror R p hRtwo hp) (by positivity)
      _ = _ := by dsimp only [a]; field_simp
  have hsmall := hR₁ R ((le_max_left R₁ 2).trans hR)
  change _ < ε
  linarith

end Erdos964
