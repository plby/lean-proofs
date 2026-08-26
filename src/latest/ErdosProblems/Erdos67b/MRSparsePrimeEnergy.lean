import ErdosProblems.Erdos67b.MRSparsePrimeGram
import ErdosProblems.Erdos67b.MRSparsePositiveMajorant
import ErdosProblems.Erdos67b.MRAppendixLargeValues

/-! # Sparse prime energy from the actual positive majorant and Gram rows -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSmoothPrimeSieveWeight (D : ℕ) (hD : 1 ≤ D) (P : ℝ) (n : ℕ) : ℝ :=
  mrPrimeSelbergMajorant D hD n * mrPrimeWeightPolynomial ((n : ℝ) / P)

theorem mrPrimeMellinMonomial_eq_logarithmicPhase {n : ℕ} (hn : 0 < n) (t : ℝ) :
    mrPrimeMellinMonomial 0 t n = logarithmicPhase n t := by
  rw [logarithmicPhase_eq_archimedeanTwist hn]
  simp [mrPrimeMellinMonomial, mrPrimeMellinCoefficient, archimedeanTwist, mul_comm]

theorem mrSmoothPrimeSelbergKernel_eq_weightedPolynomial (D : ℕ) (hD : 1 ≤ D)
    {P : ℝ} (hP : 0 < P) (t : ℝ) :
    mrSmoothPrimeSelbergKernel D hD P t =
      logarithmicDirichletPolynomial (mrSmoothPrimeKernelSupport P)
        (fun n ↦ (mrSmoothPrimeSieveWeight D hD P n : ℂ)) t := by
  unfold mrSmoothPrimeSelbergKernel logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n :=
    (Erdos1149.AnalyticParameters.natCeil_pos (by linarith : 0 < P / 2)).trans_le
      (Finset.mem_Icc.1 hn).1
  rw [mrSmoothPrimeKernelIntegrand, mrPrimeMellinMonomial_eq_logarithmicPhase hnpos]
  simp only [mrSmoothPrimeSieveWeight, Complex.ofReal_mul]
  ring

theorem mrExists_sparsePrime_energy_bound (R : ℕ) (hR : 2 ≤ R)
    {h : ℝ} (hhR : 2 * h ≤ (R : ℝ)) :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, (p : ℝ) ∈ Set.Icc P (2 * P)) →
      ∀ S : Finset ℝ,
        (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
        (∀ s ∈ S, ∀ t ∈ S, |t - s| ≤ P ^ h) →
      ∀ a : ℕ → ℂ,
        (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
          mrSparsePrimeGramBudget R P S.card * ∑ p ∈ A, ‖a p‖ ^ 2 := by
  obtain ⟨P₀, hP₀one, hP₀⟩ := mrExists_sparsePrime_gram_row_bound R hR hhR
  refine ⟨P₀, hP₀one, ?_⟩
  intro P hP A hprime hblock S hsep hdiam a
  have hPone : 1 < P := hP₀one.trans_le hP
  have hPpos : 0 < P := by linarith
  obtain ⟨hDtwo, hrows⟩ := hP₀ P hP
  let D := mrPrimePowerCutoff R P
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hcutoff := mrPrimePowerCutoff_lt_scale hR hPone
  apply mrSparse_logarithmic_energy_le_of_majorant_rows A (mrSmoothPrimeKernelSupport P)
    S (mrSmoothPrimeSieveWeight D hD P)
    (fun p hp ↦ mrMem_smoothPrimeKernelSupport hPpos (hblock p hp))
    (fun n _ ↦ mrSmoothPrimeSelbergWeight_nonneg D hD P n)
    (fun p hp ↦ mrSmoothPrimeSelbergWeight_ge_one D hD hPpos (hprime p hp)
      (by exact_mod_cast hcutoff.trans_le (hblock p hp).1) (hblock p hp))
    (mrSparsePrimeGramBudget_nonneg R hPone.le S.card)
  intro s hs
  simp_rw [← mrSmoothPrimeSelbergKernel_eq_weightedPolynomial D hD hPpos]
  exact hrows hD S hsep hdiam s hs

end

end Erdos67b
