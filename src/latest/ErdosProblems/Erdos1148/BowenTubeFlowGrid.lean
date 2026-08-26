import ErdosProblems.Erdos1148.BowenTubeNormalization
import ErdosProblems.Erdos1148.RealIntervalGrid

/-! # Covering a Bowen tube by finitely many translates of a small ball -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_bowenTube_flow_grid {η δ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N : ℕ) (s : Fin N → ℝ), (N : ℝ) ≤ 2 / δ ∧
      ∀ g : SL(2, ℝ), EntryBowenTube η δ g →
        ∃ i : Fin N, EntryCloseOne (3 * δ) (g * diagonalFlow (s i)) := by
  obtain ⟨N, c, hN, hcmin, hcover⟩ := exists_real_interval_grid
    (show 1 - η ≤ 1 + η by linarith) hδ
  refine ⟨N, fun i => -(2 * Real.log (c i)), hN.trans ?_, ?_⟩
  · apply (le_div_iff₀ hδ).mpr
    calc
      ((1 + η - (1 - η)) / δ + 1) * δ = 2 * η + δ := by field_simp; ring
      _ ≤ 2 := by linarith
  · intro g hg
    have ha := abs_le.mp hg.1
    obtain ⟨i, hi⟩ := hcover (g 0 0) ⟨by linarith [ha.1], by linarith [ha.2]⟩
    exact ⟨i, entryCloseOne_of_bowenTube_grid hη hδ.le hδ1 hg (hcmin i) hi⟩

end Erdos1148.DukeArithmetic
