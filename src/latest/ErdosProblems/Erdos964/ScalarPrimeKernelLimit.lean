import ErdosProblems.Erdos964.ScalarKernelNormalizedError
import ErdosProblems.Erdos964.ScalarPolynomialKernelLimit

/-!
# Uniform face approximation for the actual scalar prime kernel

The radius and the distinguished prime have independent lower thresholds.
This permits the approximation to be summed over a growing range of primes.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem exists_scalar_prime_kernel_uniform_face_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ P₀ : ℕ, 2 ≤ R₀ ∧ 2 ≤ P₀ ∧ ∀ R p : ℕ,
      R₀ ≤ R → P₀ ≤ p → p.Prime → p.Coprime M →
      |scalarCandidatePrimeKernel M R p / (Real.log R) ^ 4 -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          scalarSieveFace (Real.log p / Real.log R)| < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨R₂, hR₂, hpoly⟩ :=
    exists_scalar_polynomial_kernel_uniform_face_error M hM h2M h3M (ε / 3) hthird
  obtain ⟨K, C, D, hK, hC, hD, herror⟩ :=
    exists_scalar_prime_kernel_normalized_polynomial_error M hM h2M h3M
  have htail := (tendsto_order.mp (tendsto_scalarKernelTransformTail M K C D)).2
    (ε / 3) hthird
  have hlog : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp
    (htail.and (hlog.eventually (eventually_ge_atTop 2)))
  have hprime : Tendsto (fun p : ℕ =>
      (2048 * D * coprimeHarmonicDensity M ^ 2) / p) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  obtain ⟨P₁, hP₁⟩ := eventually_atTop.mp ((tendsto_order.mp hprime).2 (ε / 3) hthird)
  refine ⟨max R₁ R₂, max P₁ 2, hR₂.trans (le_max_right _ _), le_max_right _ _, ?_⟩
  intro R p hR hp hpp hpM
  have hR₁' := hR₁ R ((le_max_left R₁ R₂).trans hR)
  have hP₁' := hP₁ p ((le_max_left P₁ 2).trans hp)
  have he := herror R p hR₁'.2 hpp hpM
  have hf := hpoly R p ((le_max_right R₁ R₂).trans hR) hpp.pos
  have htriangle := abs_sub_le
    (scalarCandidatePrimeKernel M R p / (Real.log R) ^ 4)
    (scalarPolynomialPrimeKernel M R p / (Real.log R) ^ 4)
    ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
      scalarSieveFace (Real.log p / Real.log R))
  linarith

theorem exists_scalar_second_main_uniform_face_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ P₀ : ℕ, 2 ≤ R₀ ∧ 2 ≤ P₀ ∧ ∀ (R x z : ℕ) (P Q : Finset ℕ),
      R₀ ≤ R → (∀ p ∈ P, P₀ ≤ p ∧ p.Prime ∧ p.Coprime M) →
      |scalarCandidateSecondMain M R P Q x z / (Real.log R) ^ 4 -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          ∑ p ∈ P, (primeSlice Q p x z).card *
            scalarSieveFace (Real.log p / Real.log R)| ≤
        ε * ∑ p ∈ P, ((primeSlice Q p x z).card : ℝ) := by
  obtain ⟨R₀, P₀, hR₀, hP₀, herror⟩ :=
    exists_scalar_prime_kernel_uniform_face_error M hM h2M h3M ε hε
  refine ⟨R₀, P₀, hR₀, hP₀, ?_⟩
  intro R x z P Q hR hP
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4
  have hid : scalarCandidateSecondMain M R P Q x z / (Real.log R) ^ 4 -
      A * (∑ p ∈ P, (primeSlice Q p x z).card *
        scalarSieveFace (Real.log p / Real.log R)) =
      ∑ p ∈ P, (primeSlice Q p x z).card *
        (scalarCandidatePrimeKernel M R p / (Real.log R) ^ 4 -
          A * scalarSieveFace (Real.log p / Real.log R)) := by
    simp only [scalarCandidateSecondMain, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hid]
  calc
    _ ≤ ∑ p ∈ P, |(primeSlice Q p x z).card *
        (scalarCandidatePrimeKernel M R p / (Real.log R) ^ 4 -
          A * scalarSieveFace (Real.log p / Real.log R))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, (primeSlice Q p x z).card * ε := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (herror R p hR (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2).le (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end Erdos964
