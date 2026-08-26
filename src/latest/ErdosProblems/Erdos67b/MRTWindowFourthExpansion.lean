import ErdosProblems.Erdos67b.MRTProductWindows

/-! # Exact fourth moment of the actual dual-window prime rows -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

def mrtWindowWeight (Z H Y p m : ℕ) (θ : ℕ → ℂ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Ioc Y (2 * Y), if mrtProductWindow Z H n p m then θ n else 0

def mrtWindowPrimeRow (P : Finset ℕ) (Z H Y : ℕ) (c θ : ℕ → ℂ) (α : ℝ) (m : ℕ) : ℂ :=
  ∑ p ∈ P, (c p * additivePhase α (m * p)) * mrtWindowWeight Z H Y p m θ

def mrtCofactorPhaseSum (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ)) (α : ℝ) : ℂ :=
  ∑ m ∈ mrtQuadCofactors Z H M p n,
    additivePhase (α * (primeQuadrupleDifference p : ℝ)) m

theorem mrtFourthMomentCoefficient_mul (a b : ℕ → ℂ) (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourthMomentCoefficient (fun p ↦ a p * b p) x =
      fourthMomentCoefficient a x * fourthMomentCoefficient b x := by
  unfold fourthMomentCoefficient
  simp only [map_mul]
  ring

theorem mrtFourthMomentCoefficient_sum (S : Finset ℕ) (b : ℕ → ℕ → ℂ)
    (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourthMomentCoefficient (fun p ↦ ∑ n ∈ S, b p n) x =
      ∑ n ∈ primeQuadrupleSet S,
        b x.2.2 n.2.2 * conj (b x.2.1 n.2.1) *
          b x.1.2 n.1.2 * conj (b x.1.1 n.1.1) := by
  unfold fourthMomentCoefficient
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  simp only [primeQuadrupleSet, Finset.sum_product]

theorem mrtFourthMoment_windowWeight (Z H Y m : ℕ) (θ : ℕ → ℂ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourthMomentCoefficient (fun r ↦ mrtWindowWeight Z H Y r m θ) p =
      ∑ n ∈ primeQuadrupleSet (Finset.Ioc Y (2 * Y)),
        if mrtProductWindow Z H n.1.1 p.1.1 m ∧ mrtProductWindow Z H n.1.2 p.1.2 m ∧
            mrtProductWindow Z H n.2.1 p.2.1 m ∧ mrtProductWindow Z H n.2.2 p.2.2 m
          then fourthMomentCoefficient θ n else 0 := by
  classical
  unfold mrtWindowWeight
  rw [mrtFourthMomentCoefficient_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h₁₁ : mrtProductWindow Z H n.1.1 p.1.1 m <;>
    by_cases h₁₂ : mrtProductWindow Z H n.1.2 p.1.2 m <;>
      by_cases h₂₁ : mrtProductWindow Z H n.2.1 p.2.1 m <;>
        by_cases h₂₂ : mrtProductWindow Z H n.2.2 p.2.2 m <;>
          simp [h₁₁, h₁₂, h₂₁, h₂₂, fourthMomentCoefficient]

theorem mrtWindowPrimeRow_fourthMoment_eq (P : Finset ℕ) (Z H M Y : ℕ)
    (c θ : ℕ → ℂ) (α : ℝ) :
    ((∑ m ∈ Finset.Icc 1 M, ‖mrtWindowPrimeRow P Z H Y c θ α m‖ ^ 4 : ℝ) : ℂ) =
      ∑ p ∈ primeQuadrupleSet P, fourthMomentCoefficient c p *
        ∑ n ∈ primeQuadrupleSet (Finset.Ioc Y (2 * Y)),
          fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α := by
  classical
  unfold mrtWindowPrimeRow
  rw [fourthMoment_eq_sum_primeQuadruples]
  apply Finset.sum_congr rfl
  intro p _
  have hrow (m : ℕ) :
      fourthMomentCoefficient
          (fun r ↦ (c r * additivePhase α (m * r)) * mrtWindowWeight Z H Y r m θ) p =
        (fourthMomentCoefficient c p *
          additivePhase (α * (primeQuadrupleDifference p : ℝ)) m) *
        ∑ n ∈ primeQuadrupleSet (Finset.Ioc Y (2 * Y)),
          if mrtProductWindow Z H n.1.1 p.1.1 m ∧ mrtProductWindow Z H n.1.2 p.1.2 m ∧
              mrtProductWindow Z H n.2.1 p.2.1 m ∧ mrtProductWindow Z H n.2.2 p.2.2 m
            then fourthMomentCoefficient θ n else 0 := by
    rw [mrtFourthMomentCoefficient_mul, fourthMomentCoefficient_phase_factorization,
      mrtFourthMoment_windowWeight]
  simp_rw [hrow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [mrtCofactorPhaseSum, mrtQuadCofactors, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> ring

end

end Erdos67b
