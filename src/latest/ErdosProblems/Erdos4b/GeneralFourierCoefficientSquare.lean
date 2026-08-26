/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFiniteIntegral

/-!
# Finite tensor combinations and the Selberg coefficient square

These identities expand the actual product of two finite sums of
Möbius--profile tensors. All cross terms are retained; the source
coefficient square is the case when the two finite sums agree.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance coefficientSquareDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

def selbergTensorCoefficient {ι : Type*} [Fintype ι]
    (F : (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) (d : (ι ⊕ ι) → ℕ) : ℂ :=
  ∏ i, (ArithmeticFunction.moebius (d i) : ℂ) * F i (Real.log (d i) / L i)

def pairedSelbergProfiles {ι : Type*}
    (F G : (ι ⊕ ι) → ℝ → ℂ) (ib : (ι ⊕ ι) × Bool) : ℝ → ℂ :=
  if ib.2 then G ib.1 else F ib.1

theorem doubledSelbergProfileTensor_eq_coefficient_mul
    {ι : Type*} [Fintype ι] (F G : (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ)
    (d : (ι ⊕ ι) → Bool → ℕ) :
    doubledSelbergProfileTensor (pairedSelbergProfiles F G) (fun i _ ↦ L i) d =
      selbergTensorCoefficient F L (fun i ↦ d i false) *
        selbergTensorCoefficient G L (fun i ↦ d i true) := by
  unfold doubledSelbergProfileTensor selbergTensorCoefficient
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Fintype.prod_bool, pairedSelbergProfiles, Bool.false_eq_true,
    if_false, if_true]
  exact mul_comm _ _

def cutoffSelbergBilinearSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d then
      a (fun i ↦ d i false) * b (fun i ↦ d i true) /
        ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)
    else 0

theorem cutoffSelbergBilinearSum_tensors
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F G : (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffSelbergBilinearSum P edges companion
        (selbergTensorCoefficient F L) (selbergTensorCoefficient G L) =
      cutoffSelbergProfileTensorSum P edges companion
        (pairedSelbergProfiles F G) (fun i _ ↦ L i) := by
  unfold cutoffSelbergBilinearSum cutoffSelbergProfileTensorSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [doubledSelbergProfileTensor_eq_coefficient_mul]

theorem cutoffSelbergBilinearSum_sum
    {ι J J' : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (T : Finset J')
    (a : J → ((ι ⊕ ι) → ℕ) → ℂ) (b : J' → ((ι ⊕ ι) → ℕ) → ℂ) :
    cutoffSelbergBilinearSum P edges companion
        (fun d ↦ ∑ j ∈ S, a j d) (fun d ↦ ∑ j ∈ T, b j d) =
      ∑ j ∈ S, ∑ k ∈ T, cutoffSelbergBilinearSum P edges companion (a j) (b k) := by
  unfold cutoffSelbergBilinearSum
  have hpoint (d : (ι ⊕ ι) → Bool → ℕ) :
      (if DoubledDivisorPrimeCompatible P edges companion d then
        (∑ j ∈ S, a j (fun i ↦ d i false)) * (∑ k ∈ T, b k (fun i ↦ d i true)) /
          ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)
      else 0) =
      ∑ j ∈ S, ∑ k ∈ T,
        if DoubledDivisorPrimeCompatible P edges companion d then
          a j (fun i ↦ d i false) * b k (fun i ↦ d i true) /
            ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)
        else 0 := by
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d
    · simp only [if_pos hc, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_comm
    · simp only [if_neg hc, Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

theorem cutoffSelbergBilinearSum_tensor_sum_square
    {ι J : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffSelbergBilinearSum P edges companion
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) =
      ∑ j ∈ S, ∑ k ∈ S, cutoffSelbergProfileTensorSum P edges companion
        (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  rw [cutoffSelbergBilinearSum_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact cutoffSelbergBilinearSum_tensors P edges companion (F j) (F k) L

end

end Erdos4b
