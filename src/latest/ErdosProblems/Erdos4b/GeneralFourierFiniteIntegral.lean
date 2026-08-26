/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTensorIdentity
import ErdosProblems.Erdos4b.GeneralFourierFiniteEuler

/-!
# The finite Selberg coefficient sum as a Fourier Euler integral

This is an exact equality of the original divisor-profile sum and the
finite Euler-product integral. All finite sum/integral interchanges are
justified by the proved integrability of each divisor tensor.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance finiteIntegralDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open MeasureTheory
open scoped BigOperators

def cutoffSelbergProfileTensorSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d then
      doubledSelbergProfileTensor F L d /
        ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)
    else 0

theorem finiteEulerProduct_mul_tensor_eq_divisor_sum
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    (∏ p ∈ P, doubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p) *
        doubledFourierTensor f ξ =
      ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if DoubledDivisorPrimeCompatible P edges companion d then
          doubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) *
            doubledFourierTensor f ξ
        else 0 := by
  have h := sum_doubledDivisorFourierWeight_eq_finiteEulerProduct P hP edges companion hedges
    (doubledFourierTensorExponents L ξ)
  have hm := congrArg (fun z : ℂ ↦ z * doubledFourierTensor f ξ) h.symm
  simpa only [Finset.sum_mul, ite_mul, zero_mul] using! hm

theorem integrable_compatible_divisorFourierTensor
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : d ∈ doubledCutoffDivisorTuples ι P) :
    Integrable (fun ξ ↦ if DoubledDivisorPrimeCompatible P edges companion d then
      doubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) * doubledFourierTensor f ξ
      else 0) := by
  by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
  · simp only [if_pos hc]
    apply integrable_doubledDivisorFourierWeight_mul_tensor f L hL d
    intro i b
    have hdiv := ((mem_doubledCutoffDivisorTuples P hP d).mp hd).1 i b
    exact Nat.pos_of_dvd_of_pos hdiv (primeFinsetProduct_pos P hP)
  · simp only [if_neg hc]
    exact integrable_zero _ _ _

theorem cutoffSelbergProfileTensorSum_eq_integral_finiteEulerProduct
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    cutoffSelbergProfileTensorSum P edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏ p ∈ P,
        doubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p) *
          doubledFourierTensor f ξ := by
  simp_rw [finiteEulerProduct_mul_tensor_eq_divisor_sum P hP edges companion hedges f L]
  rw [integral_finsetSum]
  · unfold cutoffSelbergProfileTensorSum
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
    · simp only [if_pos hc]
      exact (integral_doubledDivisorFourierWeight_mul_tensor f L d).symm
    · simp [hc]
  · exact fun d hd ↦ integrable_compatible_divisorFourierTensor P hP edges companion f L hL d hd

end

end Erdos4b
