import ErdosProblems.Erdos1148.GaussLiftCover
import ErdosProblems.Erdos1148.NearbyGaussParameters
import ErdosProblems.Erdos1148.LiftCoverRefinement

/-! # Refining a coherent lift piece over an ordinary orbit segment -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_ordinary_lift_refinement {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {S T : ℝ}, 0 ≤ S → 0 ≤ T → ∀ E : Set SL(2, ℝ),
      LiftForwardClose η S E →
      ∃ (N : ℕ) (C : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ K * Real.exp T ∧ (⋃ i, C i) = E ∧
        ∀ i, LiftForwardClose η (S + T) (C i) := by
  obtain ⟨K, hK, hcover⟩ := exists_gauss_lift_cover (div_pos hηpos (by norm_num : (0 : ℝ) < 8))
  refine ⟨K, hK, ?_⟩
  intro S T hS hT E hE
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨N, B, hN, _, hcov, hB⟩ := hcover (g₀ * diagonalFlow S) T hT
    have hB' : ∀ i, LiftForwardClose η T (B i) := by
      have hscale : 8 * (η / 8) = η := by ring
      simpa only [hscale] using hB
    have hcov' : (fun g => (1 : SL(2, ℝ)) * (g * diagonalFlow S)) '' E ⊆ ⋃ i, B i := by
      rintro _ ⟨g, hg, rfl⟩
      dsimp only
      rw [one_mul]
      apply hcov
      exact exists_boundedGaussParameters_of_close hη _ _ (hE g₀ hg₀ g hg S ⟨hS, le_rfl⟩)
    obtain ⟨C, hC, hclose⟩ := exists_lift_cover_refinement hE 1 B hcov' hB'
    exact ⟨N, C, hN, hC, hclose⟩
  · have hEempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEempty]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
