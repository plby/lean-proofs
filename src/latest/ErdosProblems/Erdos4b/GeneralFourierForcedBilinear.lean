/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedPrimeCount

/-!
# The forced bilinear kernel and every profile cross term

The congruence restriction and the actual enlarged totient denominator
are retained when expanding the square of a finite tensor combination.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

open Classical in
def cutoffForcedSelbergBilinearSum {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) : ℂ :=
  ∑ d ∈ doubledCutoffDivisorTuples ι P,
    if DoubledDivisorPrimeCompatible P edges companion d ∧ R d then
      a (fun i ↦ d i false) * b (fun i ↦ d i true) /
        (Nat.totient (Nat.lcm
          ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
    else 0

open Classical in
theorem cutoffForcedSelbergBilinearSum_eq_raw_supported
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (a b : ((ι ⊕ ι) → ℕ) → ℂ) :
    cutoffForcedSelbergBilinearSum P edges companion p R a b =
      ∑ d ∈ rawDoubledCutoffDivisorTuples ι P,
        if (d ∈ doubledCutoffDivisorTuples ι P ∧
          DoubledDivisorPrimeCompatible P edges companion d) ∧ R d then
          a (fun i ↦ d i false) * b (fun i ↦ d i true) /
            (Nat.totient (Nat.lcm
              ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
        else 0 := by
  classical
  have hsubset : doubledCutoffDivisorTuples ι P ⊆ rawDoubledCutoffDivisorTuples ι P := by
    intro d hd
    exact (mem_rawDoubledCutoffDivisorTuples P hP d).mpr
      ((mem_doubledCutoffDivisorTuples P hP d).mp hd).1
  unfold cutoffForcedSelbergBilinearSum
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if (d ∈ doubledCutoffDivisorTuples ι P ∧
          DoubledDivisorPrimeCompatible P edges companion d) ∧ R d then
          a (fun i ↦ d i false) * b (fun i ↦ d i true) /
            (Nat.totient (Nat.lcm
              ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [hd, true_and]
    _ = _ := Finset.sum_subset hsubset
      (fun d hd hn ↦ by simp only [hn, false_and, if_false])

theorem cutoffForcedSelbergBilinearSum_weighted_tensors
    {ι J : Type*} [Fintype ι]
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (S : Finset J) (c : J → ℂ) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) :
    cutoffForcedSelbergBilinearSum P edges companion p R
        (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v)
        (fun v ↦ ∑ j ∈ S, c j * selbergTensorCoefficient (F j) L v) =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * cutoffForcedSelbergProfileTensorSum
        P edges companion p R (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) := by
  classical
  unfold cutoffForcedSelbergBilinearSum cutoffForcedSelbergProfileTensorSum
  have hpoint (d : (ι ⊕ ι) → Bool → ℕ) :
      (if DoubledDivisorPrimeCompatible P edges companion d ∧ R d then
        (∑ j ∈ S, c j * selbergTensorCoefficient (F j) L (fun i ↦ d i false)) *
          (∑ k ∈ S, c k * selbergTensorCoefficient (F k) L (fun i ↦ d i true)) /
            (Nat.totient (Nat.lcm
              ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
      else 0) =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) *
        (if DoubledDivisorPrimeCompatible P edges companion d ∧ R d then
          doubledSelbergProfileTensor (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) d /
            (Nat.totient (Nat.lcm
              ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
        else 0) := by
    simp_rw [doubledSelbergProfileTensor_eq_coefficient_mul]
    by_cases hc : DoubledDivisorPrimeCompatible P edges companion d ∧ R d
    · simp only [if_pos hc, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  simp_rw [hpoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

end

end Erdos4b
