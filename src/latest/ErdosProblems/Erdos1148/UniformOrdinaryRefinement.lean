import ErdosProblems.Erdos1148.SmallGaussLiftCover
import ErdosProblems.Erdos1148.NearbyGaussParameters
import ErdosProblems.Erdos1148.LiftCoverRefinement

/-! # Forward refinement with a constant independent of the neighborhood radius -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_uniform_ordinary_lift_refinement {η S T : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (E : Set SL(2, ℝ)) (hE : LiftForwardClose η S E) :
    ∃ (N : ℕ) (C : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ 33 ^ 3 * Real.exp T ∧ (⋃ i, C i) = E ∧
      ∀ i, LiftForwardClose η (S + T) (C i) := by
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨N, B, hN, _, hcov, hB⟩ := exists_small_gauss_lift_cover hηpos
      (g₀ * diagonalFlow S) hT
    have hcov' : (fun g => (1 : SL(2, ℝ)) * (g * diagonalFlow S)) '' E ⊆ ⋃ i, B i := by
      rintro _ ⟨g, hg, rfl⟩
      dsimp only
      rw [one_mul]
      apply hcov
      have hc := hE g₀ hg₀ g hg S ⟨hS, le_rfl⟩
      obtain ⟨p, hp, hr, hx, ha⟩ := exists_boundedGaussParameters_of_forward_tube hη
        (g₀ * diagonalFlow S) (g * diagonalFlow S) ⟨hc, hc.2.2.1⟩
      exact ⟨p, ⟨hr, hx, ha⟩, hp⟩
    obtain ⟨C, hC, hclose⟩ := exists_lift_cover_refinement hE 1 B hcov' hB
    exact ⟨N, C, hN, hC, hclose⟩
  · have hEempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEempty]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
