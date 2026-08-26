import ErdosProblems.Erdos1148.LatticeVectorCandidateCount
import ErdosProblems.Erdos1148.ReturningGaussParameters

/-! # An explicit polynomial bound on returning-vector candidates in Gauss boxes -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_uniform_returningGauss_candidates_card_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ V : Finset (ℤ × ℤ), (V.card : ℝ) ≤ (64 * A + 3) ^ 2 ∧
      ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ (S c : ℝ) (p : BoundedGaussParameters) (q : ℤ × ℤ),
        GaussVectorReturns g S c q p → q ∈ V := by
  obtain ⟨V, hV, hcover⟩ := exists_lattice_vector_candidates_card_bound
    (A := 8 * A) (by positivity) (R := 1) (by norm_num)
  refine ⟨V, ?_, ?_⟩
  · have heq : 4 * (8 * A) * ((1 : ℝ) + 1) + 3 = 64 * A + 3 := by ring
    simpa only [heq] using hV
  · intro g hg S c p q hp
    exact hcover (gaussParameterFrame g p)
      (translated_gaussFrame_abs_entries_le g hA hg p.property.1 p.property.2.1
        p.property.2.2.1 p.property.2.2.2) q.1 q.2 hp.2.1

end Erdos1148.DukeArithmetic
