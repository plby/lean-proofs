import ErdosProblems.Erdos444.Basic

/-!
# Regular tail points for Erdős Problem 444

The analytic argument needs a point whose future normalized reciprocal mass
does not jump by more than a fixed factor.  This file isolates the underlying
order lemma: a positive, bounded real sequence has a point on every relevant
tail whose value is within a factor two of every later value.
-/

open Set

namespace Erdos444

/-- A factor-two regular point which controls the entire tail on which it
is selected.  In particular, its value is at least half the value at any
previously chosen seed point in that tail. -/
theorem exists_tail_two_regular_strong
    (q : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (hpos : ∃ n, N ≤ n ∧ 0 < q n)
    (hB : ∀ n, N ≤ n → q n ≤ B) :
    ∃ x, N ≤ x ∧ 0 < q x ∧ ∀ y, N ≤ y → q y ≤ 2 * q x := by
  let S : Set ℝ := q '' Ici N
  have hSne : S.Nonempty := by
    obtain ⟨n, hnN, hnpos⟩ := hpos
    exact ⟨q n, ⟨n, hnN, rfl⟩⟩
  have hSbdd : BddAbove S := by
    refine ⟨B, ?_⟩
    rintro z ⟨n, hnN, rfl⟩
    exact hB n hnN
  have hsup_pos : 0 < sSup S := by
    obtain ⟨n, hnN, hnpos⟩ := hpos
    exact hnpos.trans_le (le_csSup hSbdd ⟨n, hnN, rfl⟩)
  have hhalf : sSup S / 2 < sSup S := by linarith
  obtain ⟨z, hzS, hhz⟩ := exists_lt_of_lt_csSup hSne hhalf
  obtain ⟨x, hxN, rfl⟩ := hzS
  refine ⟨x, hxN, by linarith, ?_⟩
  intro y hyN
  have hy_le : q y ≤ sSup S := le_csSup hSbdd ⟨y, hyN, rfl⟩
  linarith

/-- A bounded real sequence which is positive somewhere on a tail has a
factor-two regular point on that tail. -/
theorem exists_tail_two_regular
    (q : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (hpos : ∃ n, N ≤ n ∧ 0 < q n)
    (hB : ∀ n, N ≤ n → q n ≤ B) :
    ∃ x, N ≤ x ∧ 0 < q x ∧ ∀ y, x ≤ y → q y ≤ 2 * q x := by
  obtain ⟨x, hxN, hxpos, hx⟩ :=
    exists_tail_two_regular_strong q N B hpos hB
  exact ⟨x, hxN, hxpos, fun y hxy ↦ hx y (hxN.trans hxy)⟩

end Erdos444
