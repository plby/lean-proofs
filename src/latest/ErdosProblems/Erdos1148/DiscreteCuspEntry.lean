import ErdosProblems.Erdos1148.BufferedCuspEntry
import ErdosProblems.Erdos1148.CuspRunGeometry

/-! # Every noninitial cusp run has the uniform entry-side excursion property -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem bufferedCuspEntry_of_integer_run (g : SL(2, ℝ)) {H : ℝ}
    (hH : 0 < H) (hwindow : Real.exp 1 ≤ H ^ 4) {a b : ℕ}
    (hvisits : ∀ k ∈ Finset.Icc a b, modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow ((a : ℝ) - 1)) ∉ modularCusp H) :
    BufferedCuspEntry H ((b : ℝ) - a)
      (g * diagonalFlow ((a : ℝ) - 2 * Real.log H)) := by
  have hentry : (g * diagonalFlow ((a : ℝ) - 2 * Real.log H)) *
      diagonalFlow (2 * Real.log H) = g * diagonalFlow (a : ℝ) := by
    rw [mul_assoc, ← diagonalFlow_add, sub_add_cancel]
  dsimp only [BufferedCuspEntry]
  rw [hentry]
  constructor
  · intro t ht
    rw [mul_assoc, ← diagonalFlow_add]
    apply cusp_on_real_interval_of_integer_visits g hH hwindow hvisits
    constructor <;> linarith [ht.1, ht.2]
  · simpa only [mul_assoc, ← diagonalFlow_add, sub_eq_add_neg] using hbefore

theorem maximal_cusp_run_bufferedEntry (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hwindow : Real.exp 1 ≤ H ^ 4) {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g))) (ha0 : p.1 ≠ 0) :
    BufferedCuspEntry H ((p.2 : ℝ) - p.1)
      (g * diagonalFlow ((p.1 : ℝ) - 2 * Real.log H)) := by
  let V := modularCuspVisitTimes H n (modularMk g)
  have hr := (mem_maximalNatRuns_iff V p).mp hp
  have hmem (k : ℕ) (hk : k ∈ Finset.Icc p.1 p.2) : k < n ∧
      modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H :=
    (mem_modularCuspVisitTimes_iff H n (modularMk g) k).mp (hr.2.1 hk)
  have ha := hmem p.1 (Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩)
  have hbefore : modularMk (g * diagonalFlow ((p.1 : ℝ) - 1)) ∉ modularCusp H := by
    intro hcusp
    apply hr.2.2.1.resolve_left ha0
    apply (mem_modularCuspVisitTimes_iff H n (modularMk g) (p.1 - 1)).mpr
    refine ⟨by omega, ?_⟩
    simpa only [Nat.cast_sub (show 1 ≤ p.1 by omega), Nat.cast_one,
      modularRightTranslate_mk] using hcusp
  exact bufferedCuspEntry_of_integer_run g hH hwindow (fun k hk => (hmem k hk).2) hbefore

end Erdos1148.DukeArithmetic
