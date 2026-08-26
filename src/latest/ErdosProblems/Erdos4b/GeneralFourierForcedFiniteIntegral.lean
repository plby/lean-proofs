/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedEuler
import ErdosProblems.Erdos4b.GeneralFourierFiniteIntegral

/-!
# Exact Fourier integral with one forced prime

The finite profile sum retains the prescribed local condition and the
actual enlarged totient denominator. Every summand is integrable.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem complex_div_nat_mul_nat_div_totient_lcm (z : ℂ) (n p : ℕ) :
    z / (n : ℂ) * ((n : ℂ) / (Nat.totient (Nat.lcm n p) : ℂ)) =
      z / (Nat.totient (Nat.lcm n p) : ℂ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact div_mul_div_cancel₀ (by exact_mod_cast hn)

theorem forcedDoubledDivisorFourierWeight_eq_mul
    {ι : Type*} [Fintype ι] (p : ℕ) (d : (ι ⊕ ι) → Bool → ℕ)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    forcedDoubledDivisorFourierWeight p d s = doubledDivisorFourierWeight d s *
      ((((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) : ℂ) /
        (Nat.totient (Nat.lcm
          ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)) :=
  (complex_div_nat_mul_nat_div_totient_lcm _ _ p).symm

theorem integrable_forcedDoubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (p : ℕ) (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : ∀ i b, 0 < d i b) :
    Integrable (fun ξ ↦ forcedDoubledDivisorFourierWeight p d
      (doubledFourierTensorExponents L ξ) * doubledFourierTensor f ξ) := by
  have h := (integrable_doubledDivisorFourierWeight_mul_tensor f L hL d hd).mul_const
    ((((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) : ℂ) /
      (Nat.totient (Nat.lcm
        ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ))
  apply h.congr (ae_of_all _ fun ξ ↦ ?_)
  rw [forcedDoubledDivisorFourierWeight_eq_mul]
  ring

theorem integral_forcedDoubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (p : ℕ) (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (d : (ι ⊕ ι) → Bool → ℕ) :
    (∫ ξ, forcedDoubledDivisorFourierWeight p d (doubledFourierTensorExponents L ξ) *
      doubledFourierTensor f ξ) =
      doubledSelbergProfileTensor (fun ib ↦ laplaceFourierProfile (f ib)) L d /
        (Nat.totient (Nat.lcm
          ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ) := by
  simp_rw [forcedDoubledDivisorFourierWeight_eq_mul,
    mul_right_comm _ _ (doubledFourierTensor f _)]
  rw [integral_mul_const, integral_doubledDivisorFourierWeight_mul_tensor,
    complex_div_nat_mul_nat_div_totient_lcm]

open Classical in
def cutoffForcedSelbergProfileTensorSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d ∧ R d then
      doubledSelbergProfileTensor F L d /
        (Nat.totient (Nat.lcm
          ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
    else 0

open Classical in
theorem cutoffForcedSelbergProfileTensorSum_eq_integral_finiteEulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ r ∈ P, ∀ ij ∈ edges r, companion r = true)
    (p : P) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop) (force : DoubledPrimeChoice ι → Prop)
    (hR : ∀ c : P → DoubledPrimeChoice ι, R (doubledPrimeChoiceDivisor P c) ↔ force (c p))
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    cutoffForcedSelbergProfileTensorSum P edges companion p R
      (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏ r : P, if r = p then
        forcedTotientFourierPrimeFactor
          (fun c ↦ DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c)
          (doubledFourierTensorExponents L ξ) p
        else totientDoubledFourierPrimeFactor edges companion
          (doubledFourierTensorExponents L ξ) r) *
          doubledFourierTensor f ξ := by
  simp_rw [← sum_forcedDivisorFourierWeight_eq_finiteEulerProduct
    P hP edges companion hedges p R force hR, Finset.sum_mul, ite_mul, zero_mul]
  rw [integral_finsetSum]
  · unfold cutoffForcedSelbergProfileTensorSum
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d ∧ R d
    · simp only [if_pos hc]
      exact (integral_forcedDoubledDivisorFourierWeight_mul_tensor p f L d).symm
    · simp [hc]
  · intro d hd
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d ∧ R d
    · simp only [if_pos hc]
      apply integrable_forcedDoubledDivisorFourierWeight_mul_tensor p f L hL d
      intro i b
      exact Nat.pos_of_dvd_of_pos (((mem_doubledCutoffDivisorTuples P hP d).mp hd).1 i b)
        (primeFinsetProduct_pos P hP)
    · simp only [if_neg hc]
      exact integrable_zero _ _ _

end

end Erdos4b
