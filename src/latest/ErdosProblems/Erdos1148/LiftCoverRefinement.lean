import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Refining coherent lift pieces while preserving their past orbit history -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_lift_cover_refinement {η S T : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (a : SL(2, ℝ)) {N : ℕ}
    (B : Fin N → Set SL(2, ℝ))
    (hcov : (fun g => a * (g * diagonalFlow S)) '' E ⊆ ⋃ i, B i)
    (hB : ∀ i, LiftForwardClose η T (B i)) :
    ∃ C : Fin N → Set SL(2, ℝ), (⋃ i, C i) = E ∧
      ∀ i, LiftForwardClose η (S + T) (C i) := by
  let C : Fin N → Set SL(2, ℝ) := fun i =>
    E ∩ (fun g => a * (g * diagonalFlow S)) ⁻¹' B i
  refine ⟨C, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
      exact hi.1
    · intro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨g, hg, rfl⟩)
      exact Set.mem_iUnion.mpr ⟨i, hg, hi⟩
  · intro i
    apply (hE.mono (show C i ⊆ E from Set.inter_subset_left)).append
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ t ht
    have hc := hB i (a * (g * diagonalFlow S)) hg.2
      (a * (h * diagonalFlow S)) hh.2 t ht
    have heq : ((a * (g * diagonalFlow S)) * diagonalFlow t)⁻¹ *
        ((a * (h * diagonalFlow S)) * diagonalFlow t) =
        ((g * diagonalFlow S) * diagonalFlow t)⁻¹ *
          ((h * diagonalFlow S) * diagonalFlow t) := by group
    rwa [heq] at hc

end Erdos1148.DukeArithmetic
