import ErdosProblems.Erdos1148.RealIntervalGrid

/-! # A set of bounded diameter has an explicitly bounded interval cover -/

namespace Erdos1148.DukeArithmetic

theorem exists_diameter_interval_grid {E : Set ℝ} {D w : ℝ} (hD : 0 ≤ D) (hw : 0 < w)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x - y| ≤ D) :
    ∃ (N : ℕ) (c : Fin N → ℝ), (N : ℝ) ≤ 2 * D / w + 1 ∧
      ∀ x ∈ E, ∃ i : Fin N, x ∈ Set.Icc (c i) (c i + w) := by
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨a, ha⟩ := hE
    obtain ⟨N, c, hN, _, hcover⟩ := exists_real_interval_grid
      (show a - D ≤ a + D by linarith) hw
    refine ⟨N, c, ?_, ?_⟩
    · convert hN using 1 <;> ring
    · intro x hx
      have h := abs_le.mp (hdiam x hx a ha)
      exact hcover x ⟨by linarith [h.1], by linarith [h.2]⟩
  · refine ⟨0, Fin.elim0, ?_, ?_⟩
    · rw [Nat.cast_zero]
      exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) hD) hw.le) zero_le_one
    · intro x hx
      exact (hE ⟨x, hx⟩).elim

end Erdos1148.DukeArithmetic
