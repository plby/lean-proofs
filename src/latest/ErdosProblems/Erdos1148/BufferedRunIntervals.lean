import ErdosProblems.Erdos1148.DiscreteCuspEntry
import ErdosProblems.Erdos1148.LongRunDuration
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Buffered real intervals attached to maximal integer cusp runs -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def bufferedRunInterval (H : ℝ) (p : ℕ × ℕ) : ℝ × ℝ :=
  ((p.1 : ℝ), (p.2 : ℝ) + 4 * Real.log H)

lemma bufferedRunInterval_duration (H : ℝ) (p : ℕ × ℕ) :
    (bufferedRunInterval H p).2 - (bufferedRunInterval H p).1 =
      ((p.2 : ℝ) - p.1) + 4 * Real.log H := by dsimp only [bufferedRunInterval]; ring

theorem bufferedRunInterval_bounds (g₀ : SL(2, ℝ)) {H : ℝ} (hH : 1 ≤ H)
    {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g₀))) :
    0 ≤ (bufferedRunInterval H p).1 ∧
      (bufferedRunInterval H p).1 ≤ (bufferedRunInterval H p).2 ∧
      (bufferedRunInterval H p).2 ≤ (n : ℝ) + 4 * Real.log H := by
  have hr := (mem_maximalNatRuns_iff _ p).mp hp
  have hpV := hr.2.1 (Finset.mem_Icc.mpr ⟨hr.1, le_rfl⟩)
  have hpn := ((mem_modularCuspVisitTimes_iff H n (modularMk g₀) p.2).mp hpV).1
  have hple : (p.1 : ℝ) ≤ p.2 := by exact_mod_cast hr.1
  have hpn' : (p.2 : ℝ) < n := by exact_mod_cast hpn
  dsimp only [bufferedRunInterval]
  exact ⟨Nat.cast_nonneg _, by linarith [Real.log_nonneg hH], by linarith⟩

theorem bufferedRunIntervals_pairwise (g₀ : SL(2, ℝ)) {H : ℝ} (hH : 0 < H) {n : ℕ}
    (l : List (ℕ × ℕ))
    (hmem : ∀ p ∈ l, p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g₀)))
    (hpair : l.Pairwise (fun p q => p.2 < q.1)) :
    (l.map (bufferedRunInterval H)).Pairwise (fun p q => p.2 ≤ q.1) := by
  rw [List.pairwise_map]
  apply hpair.imp_of_mem
  intro p q hp hq hpq
  have hp' := hmem p hp
  have hq' := hmem q hq
  have hpstart := ((mem_maximalNatRuns_iff _ p).mp hp').1
  have hstart : p.1 < q.1 := by omega
  have hgap := maximal_cusp_runs_buffered_order g₀ hH hp' hq' hstart
  dsimp only [bufferedRunInterval]
  linarith

theorem bufferedRunInterval_entry_of_pattern (g₀ g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hwindow : Real.exp 1 ≤ H ^ 4) {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g₀))) (ha0 : p.1 ≠ 0)
    (htimes : modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H))) =
      modularCuspVisitTimes H n (modularMk g₀)) :
    BufferedCuspEntry H ((p.2 : ℝ) - p.1) (g * diagonalFlow (bufferedRunInterval H p).1) := by
  have hp' : p ∈ maximalNatRuns
      (modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H)))) := by
    rw [htimes]
    exact hp
  have h := maximal_cusp_run_bufferedEntry (g * diagonalFlow (2 * Real.log H)) hH hwindow hp' ha0
  have heq : (g * diagonalFlow (2 * Real.log H)) * diagonalFlow ((p.1 : ℝ) - 2 * Real.log H) =
      g * diagonalFlow (p.1 : ℝ) := by
    rw [mul_assoc, ← diagonalFlow_add]
    congr 1
    congr 1
    ring
  simpa only [heq, bufferedRunInterval] using h

theorem bufferedRunInterval_initial_cusp_of_pattern (g₀ g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hwindow : Real.exp 1 ≤ H ^ 4) {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g₀))) (ha0 : p.1 = 0)
    (htimes : modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H))) =
      modularCuspVisitTimes H n (modularMk g₀)) :
    ∀ t ∈ Set.Icc 0 (p.2 : ℝ),
      modularMk ((g * diagonalFlow (2 * Real.log H)) * diagonalFlow t) ∈ modularCusp H := by
  have hr := (mem_maximalNatRuns_iff _ p).mp hp
  have hvisits : ∀ k ∈ Finset.Icc 0 p.2,
      modularMk ((g * diagonalFlow (2 * Real.log H)) * diagonalFlow (k : ℝ)) ∈ modularCusp H := by
    intro k hk
    have hmem := hr.2.1 (by simpa only [ha0] using hk)
    rw [← htimes] at hmem
    exact ((mem_modularCuspVisitTimes_iff H n _ k).mp hmem).2
  simpa only [Nat.cast_zero] using
    cusp_on_real_interval_of_integer_visits (g * diagonalFlow (2 * Real.log H)) hH hwindow hvisits

end Erdos1148.DukeArithmetic
