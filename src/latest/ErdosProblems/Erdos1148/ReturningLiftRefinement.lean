import ErdosProblems.Erdos1148.ReturningGaussLiftCover
import ErdosProblems.Erdos1148.ReturningVectors
import ErdosProblems.Erdos1148.CompactCoreLifts
import ErdosProblems.Erdos1148.LiftCoverRefinement

/-! # Refining a coherent lift piece over a returning-vector segment -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_returning_lift_refinement (H : ℝ) {c η : ℝ}
    (hc : 0 < c) (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {S T : ℝ}, 0 ≤ S → 0 ≤ T → 96 * Real.exp (-T) ≤ c →
      ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ modularCompactCore H) →
      (∀ g ∈ E, HasReturningVector T c (g * diagonalFlow S)) →
      ∃ (N : ℕ) (C : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ K * Real.exp (T / 2) ∧ (⋃ i, C i) = E ∧
        ∀ i, LiftForwardClose η (S + T) (C i) := by
  obtain ⟨A, hA, hlift⟩ := exists_compactCore_integral_bounded_lifts H
  obtain ⟨K, hK, hcover⟩ := exists_returningGauss_lift_cover hA.le hc
    (div_pos hηpos (by norm_num : (0 : ℝ) < 8))
  refine ⟨K, hK, ?_⟩
  intro S T hS hT hsmall E hE hcore hreturn
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨γ, hγ⟩ := hlift (g₀ * diagonalFlow S) (hcore g₀ hg₀)
    let a : SL(2, ℝ) := γ
    let base := a * (g₀ * diagonalFlow S)
    obtain ⟨N, B, hN, _, hcov, hB⟩ := hcover base hγ T hT hsmall
    have hB' : ∀ i, LiftForwardClose η T (B i) := by
      have hscale : 8 * (η / 8) = η := by ring
      simpa only [hscale] using hB
    have hcov' : (fun g => a * (g * diagonalFlow S)) '' E ⊆ ⋃ i, B i := by
      rintro _ ⟨g, hg, rfl⟩
      apply hcov
      have hclose : EntryCloseOne η (base⁻¹ * (a * (g * diagonalFlow S))) := by
        have heq : base⁻¹ * (a * (g * diagonalFlow S)) =
            (g₀ * diagonalFlow S)⁻¹ * (g * diagonalFlow S) := by dsimp [base]; group
        rw [heq]
        exact hE g₀ hg₀ g hg S ⟨hS, le_rfl⟩
      exact exists_returningGaussParameters_of_close hη base _ hclose
        ((hreturn g hg).integral_mul γ)
    obtain ⟨C, hC, hclose⟩ := exists_lift_cover_refinement hE a B hcov' hB'
    exact ⟨N, C, hN, hC, hclose⟩
  · have hEempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEempty]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
