/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTExceptionalPrime
import ErdosProblems.Erdos4b.FGKMTZeroKernelBound
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormula

/-!
# An effective explicit-formula bound after excluding one prime

The exceptional prime is chosen once for the whole conductor range, before
either endpoint or truncation height. The complete zero sum is bounded using
the common zero-free region; no Siegel constant is introduced.
-/

namespace Erdos4b.FGKMT

noncomputable section

open BoundedGaps.Maynard

theorem zeroFreeExponent_mono_height {A Q : ℕ} (hA : 2 ≤ A) (hQ : 2 ≤ Q)
    {t T : ℝ} (ht : |t| ≤ T) :
    1 - 1 / ((A : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * (|t| + 2))) ≤
      1 - 1 / ((A : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * (T + 2))) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hscale : 1 < (Q : ℝ) ^ 2 * (|t| + 2) := by
    nlinarith [sq_nonneg ((Q : ℝ) - 1), abs_nonneg t,
      mul_nonneg (sq_nonneg (Q : ℝ)) (abs_nonneg t)]
  have hlog := Real.log_le_log (zero_lt_one.trans hscale)
    (mul_le_mul_of_nonneg_left (show |t| + 2 ≤ T + 2 by linarith)
      (sq_nonneg (Q : ℝ)))
  have hden := mul_pos (sq_pos_of_pos hApos) (Real.log_pos hscale)
  have hinv := one_div_le_one_div_of_le hden
    (mul_le_mul_of_nonneg_left hlog (sq_nonneg (A : ℝ)))
  linarith

theorem exists_exceptionalPrime_twistedSum_formula_bound :
    ∃ A K N : ℕ, 2 ≤ A ∧ 1 ≤ K ∧ 37 ≤ N ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ Q →
          ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → q.Coprime B →
            ∀ (x : ℕ) (T : ℝ), 4 ≤ x → 1 ≤ Real.log (x : ℝ) →
              2 ≤ T → T ≤ (x : ℝ) →
              ‖twistedChebyshevSum x q chi‖ ≤
                (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
                  32 * (N : ℝ) *
                    (x : ℝ) ^ (1 - 1 / ((A : ℝ) ^ 2 *
                      Real.log ((Q : ℝ) ^ 2 * (T + 2)))) * Real.log (x : ℝ) *
                      Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  obtain ⟨A, hA, hremove⟩ := exists_exceptionalPrime_primitiveZeroFree
  obtain ⟨K, hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  obtain ⟨N, hN, hsum⟩ := exists_completeZeroKernelSum_bound
  refine ⟨A, K, N, hA, hK, hN, ?_⟩
  intro Q hQ
  obtain ⟨B, hBpos, hBQ, hB, hzeroFree⟩ := hremove Q hQ
  refine ⟨B, hBpos, hBQ, hB, ?_⟩
  intro q _ hq hqQ chi hprimitive hcop x T hx hlog hT hTx
  have hchi : chi ≠ 1 := by
    intro heq
    have hc := (DirichletCharacter.isPrimitive_def chi).mp hprimitive
    rw [heq, DirichletCharacter.conductor_one] at hc
    omega
  let alpha : ℝ := 1 - 1 / ((A : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * (T + 2)))
  have hzeros (rho : ℂ) (hrho : rho ∈ dirichletNontrivialLFunctionZerosFinset chi T) :
      rho.re ≤ alpha := by
    obtain ⟨hzero, hheight⟩ := mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho
    have hnonprincipal : IsNonprincipalNontrivialLFunctionZero chi rho :=
      (isNonprincipalNontrivialLFunctionZero_iff chi rho).mpr ⟨hchi, hzero⟩
    have hfar := hzeroFree q hq hqQ chi hprimitive hcop rho hnonprincipal
    have hheight' : |rho.im| ≤ T := by
      simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using hheight
    exact hfar.le.trans (zeroFreeExponent_mono_height hA hQ hheight')
  have hsumBound := hsum q chi (x : ℝ) T alpha
    (by exact_mod_cast (by omega : 1 ≤ x)) hlog hT hzeros
  have hmain : dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T =
      -dirichletNontrivialZeroKernelSum chi (x : ℝ) T := by
    simp only [dirichletExplicitFormulaMainZeroTerms, if_neg hchi, zero_sub]
  have hformulaBound := hformula q chi T hT x hx hTx
  calc
    _ ≤ ‖twistedChebyshevSum x q chi -
        dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ +
        ‖dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
        (32 * (N : ℝ) * (x : ℝ) ^ alpha * Real.log (x : ℝ) *
          Real.log ((q : ℝ) * (T + 2)) ^ 2) := by
      apply add_le_add hformulaBound
      simpa only [hmain, norm_neg] using hsumBound
    _ = _ := rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_twistedSum_formula_bound
