import ErdosProblems.Erdos4.FGKMTPrimeExcision

/-! A uniform zero-free region after removing one prime. -/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem reciprocal_log_scale_mono {a b x y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 < x) (hxy : x ≤ y) :
    1 / (b ^ 2 * Real.log y) ≤ 1 / (a ^ 2 * Real.log x) := by
  have hlog := Real.log_pos hx
  apply one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos ha) hlog)
  exact mul_le_mul (pow_le_pow_left₀ ha.le hab 2)
    (Real.log_le_log (by linarith) hxy) hlog.le (sq_nonneg b)

noncomputable def uniformZeroWidth (M Q : ℕ) (t : ℝ) : ℝ :=
  1 / ((M : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * (|t| + 2)))

theorem uniformZeroWidth_zero (M Q : ℕ) : uniformZeroWidth M Q 0 = exceptionalWidth M Q := by
  simp only [uniformZeroWidth, exceptionalWidth, abs_zero, zero_add, mul_comm]

theorem exceptionalWidth_mono {U M Q : ℕ} (hU : 2 ≤ U) (hUM : U ≤ M) (hQ : 2 ≤ Q) :
    exceptionalWidth M Q ≤ exceptionalWidth U Q := by
  have hUr : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  exact reciprocal_log_scale_mono hUr (by exact_mod_cast hUM) (by nlinarith) le_rfl

theorem uniformZeroWidth_le_local {S M Q q : ℕ}
    (hS : 2 ≤ S) (hSM : S ≤ M) (hq : 1 < q) (hqQ : q ≤ Q) (t : ℝ) :
    uniformZeroWidth M Q t ≤
      1 / ((S : ℝ) ^ 2 * Real.log ((q : ℝ) * (|t| + 2))) := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqQsq : (q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  apply reciprocal_log_scale_mono hSr (by exact_mod_cast hSM)
  · nlinarith [abs_nonneg t]
  · exact mul_le_mul_of_nonneg_right hqQsq (by positivity)

/-- A single absolute scale works for all bounded primitive moduli.
The omitted integer is one or a prime; no Siegel lower bound is assumed. -/
theorem exists_uniform_zero_free_prime_excision :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ B : ℕ, B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ χ : PrimitiveCharacter, χ.modulus ≤ Q → χ.modulus.Coprime B →
          ∀ ρ : ℂ, IsNonprincipalNontrivialLFunctionZero χ.character ρ →
            ρ.re < 1 - uniformZeroWidth M Q ρ.im := by
  obtain ⟨U, hU, hexc⟩ := exists_uniform_prime_excision
  obtain ⟨S, hS, hshape⟩ := exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  let M := S + U
  have hSM : S ≤ M := Nat.le_add_right _ _
  have hUM : U ≤ M := Nat.le_add_left _ _
  refine ⟨M, hS.trans hSM, ?_⟩
  intro Q hQ
  obtain ⟨B, hBQ, hB, hfree⟩ := hexc Q hQ
  refine ⟨B, hBQ, hB, ?_⟩
  intro χ hχQ hcop ρ hρ
  by_contra hnear
  have hnear' : 1 - uniformZeroWidth M Q ρ.im ≤ ρ.re := le_of_not_gt hnear
  have hlocal := uniformZeroWidth_le_local hS hSM χ.modulus_gt_one hχQ ρ.im
  have hρshape := hshape χ.modulus χ.character ρ hρ (by linarith)
  have him : ρ.im = 0 := hρshape.2.1
  have hwidth : uniformZeroWidth M Q ρ.im = exceptionalWidth M Q := by
    rw [him, uniformZeroWidth_zero]
  have hwidthle := exceptionalWidth_mono hU hUM hQ
  have hordinary := (isNonprincipalNontrivialLFunctionZero_iff χ.character ρ).mp hρ
  have hreal : (ρ.re : ℂ) = ρ := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him.symm
  apply hfree χ hcop
  refine ⟨hχQ, ρ.re, hordinary.2.2.1, hordinary.2.2.2, ?_, ?_⟩
  · rw [hreal]
    exact hordinary.2.1
  · rw [hwidth] at hnear'
    linarith

end Erdos4.FGKMT
