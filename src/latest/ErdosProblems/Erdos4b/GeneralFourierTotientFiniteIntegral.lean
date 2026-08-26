/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientEuler
import ErdosProblems.Erdos4b.GeneralFourierFiniteIntegral

/-!
# The finite totient Selberg sum as an exact Fourier integral

The existing coordinate Fubini identity applies unchanged. Only a
constant arithmetic denominator is replaced, and every finite
sum/integral interchange has an integrability proof.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance totientFiniteIntegralDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open MeasureTheory
open scoped BigOperators

theorem complex_div_nat_mul_nat_div_totient (z : ℂ) (n : ℕ) :
    z / (n : ℂ) * ((n : ℂ) / (Nat.totient n : ℂ)) = z / (Nat.totient n : ℂ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact div_mul_div_cancel₀ (by exact_mod_cast hn)

theorem totientDoubledDivisorFourierWeight_eq_mul
    {ι : Type*} [Fintype ι] (d : (ι ⊕ ι) → Bool → ℕ) (s : (ι ⊕ ι) → Bool → ℂ) :
    totientDoubledDivisorFourierWeight d s = doubledDivisorFourierWeight d s *
      ((((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) : ℂ) /
        (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) : ℂ)) :=
  (complex_div_nat_mul_nat_div_totient _ _).symm

theorem integrable_totientDoubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : ∀ i b, 0 < d i b) :
    Integrable (fun ξ ↦ totientDoubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) *
      doubledFourierTensor f ξ) := by
  have h := (integrable_doubledDivisorFourierWeight_mul_tensor f L hL d hd).mul_const
    ((((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) : ℂ) /
      (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) : ℂ))
  apply h.congr (ae_of_all _ fun ξ ↦ ?_)
  rw [totientDoubledDivisorFourierWeight_eq_mul]
  ring

theorem integral_totientDoubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (d : (ι ⊕ ι) → Bool → ℕ) :
    (∫ ξ, totientDoubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) *
      doubledFourierTensor f ξ) =
      doubledSelbergProfileTensor (fun ib ↦ laplaceFourierProfile (f ib)) L d /
        (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) : ℂ) := by
  simp_rw [totientDoubledDivisorFourierWeight_eq_mul, mul_right_comm _ _ (doubledFourierTensor f _)]
  rw [integral_mul_const, integral_doubledDivisorFourierWeight_mul_tensor,
    complex_div_nat_mul_nat_div_totient]

def cutoffTotientSelbergProfileTensorSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d then
      doubledSelbergProfileTensor F L d /
        (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) : ℂ)
    else 0

theorem cutoffTotientSelbergProfileTensorSum_eq_integral_finiteEulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    cutoffTotientSelbergProfileTensorSum P edges companion
      (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏ p ∈ P,
        totientDoubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p) *
          doubledFourierTensor f ξ := by
  have hid (ξ : ((ι ⊕ ι) × Bool) → ℝ) :=
    sum_totientDoubledDivisorFourierWeight_eq_finiteEulerProduct P hP edges companion hedges
      (doubledFourierTensorExponents L ξ)
  simp_rw [← hid, Finset.sum_mul, ite_mul, zero_mul]
  rw [integral_finsetSum]
  · unfold cutoffTotientSelbergProfileTensorSum
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
    · simp only [if_pos hc]
      exact (integral_totientDoubledDivisorFourierWeight_mul_tensor f L d).symm
    · simp [hc]
  · intro d hd
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
    · simp only [if_pos hc]
      apply integrable_totientDoubledDivisorFourierWeight_mul_tensor f L hL d
      intro i b
      exact Nat.pos_of_dvd_of_pos (((mem_doubledCutoffDivisorTuples P hP d).mp hd).1 i b)
        (primeFinsetProduct_pos P hP)
    · simp only [if_neg hc]
      exact integrable_zero _ _ _

end

end Erdos4b
