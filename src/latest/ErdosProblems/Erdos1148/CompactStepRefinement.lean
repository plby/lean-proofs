import ErdosProblems.Erdos1148.CompactCoreLiftRadius
import ErdosProblems.Erdos1148.LiftEndpointCloseness

/-! # A fine compact atom extends a coherent lift without adding pieces -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftForwardClose.extend_over_compact_atom {η S : ℝ} {K : Set ModularOrbitSpace}
    (hS : 0 ≤ S)
    (hradius : ∀ g h : SL(2, ℝ), modularMk g ∈ K →
      EntryCloseOne (η * Real.exp 1) (g⁻¹ * h) →
      (modularMk g, modularMk h) ∈ modularClosePairs η → EntryCloseOne η (g⁻¹ * h))
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E)
    (hcore : ∀ g ∈ E, modularMk (g * diagonalFlow (S + 1)) ∈ K)
    (hpairs : ∀ g ∈ E, ∀ h ∈ E,
      (modularMk (g * diagonalFlow (S + 1)), modularMk (h * diagonalFlow (S + 1))) ∈
        modularClosePairs η) : LiftForwardClose η (S + 1) E := by
  apply liftForwardClose_of_endpoints (by linarith : 0 ≤ S + 1)
  · intro g hg h hh
    have hc := hE g hg h hh 0 ⟨le_rfl, hS⟩
    simpa only [diagonalFlow_zero, mul_one] using hc
  · intro g hg h hh
    apply hradius _ _ (hcore g hg) _ (hpairs g hg h hh)
    have hc := entryCloseOne_conjugate_exp_bound (by norm_num : (0 : ℝ) ≤ 1)
      (hE g hg h hh S ⟨hS, le_rfl⟩)
    have heq : (g * diagonalFlow (S + 1))⁻¹ * (h * diagonalFlow (S + 1)) =
        diagonalFlow (-1) * ((g * diagonalFlow S)⁻¹ * (h * diagonalFlow S)) *
          diagonalFlow 1 := by
      rw [diagonalFlow_add, diagonalFlow_neg]
      group
    rwa [heq]

end Erdos1148.DukeArithmetic
