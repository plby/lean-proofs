import ErdosProblems.Erdos1148.LongRunDuration
import ErdosProblems.Erdos1148.BufferedExcursionScale
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Ordered buffered excursion data for a fixed cusp visit pattern -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_fixed_pattern_excursion_data (g₀ : SL(2, ℝ)) {H : ℝ} (hH : 1 ≤ H)
    (hwindow : Real.exp 1 ≤ H ^ 4) (hlarge : 96 / cuspEndpointLengthSqLower ≤ H)
    (n : ℕ) (E : Set SL(2, ℝ))
    (hE : ∀ g ∈ E, let entry := g * diagonalFlow (2 * Real.log H)
      modularMk entry ∉ modularCusp H ∧
      modularMk (entry * diagonalFlow (n : ℝ)) ∉ modularCusp H ∧
      modularCuspVisitTimes H n (modularMk entry) = modularCuspVisitTimes H n (modularMk g₀)) :
    let V := modularCuspVisitTimes H n (modularMk g₀)
    ∃ l : List (ℝ × ℝ), l.Pairwise (fun p q => p.2 ≤ q.1) ∧
      (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ (n : ℝ) + 4 * Real.log H) ∧
      l.length ≤ (maximalNatRuns V).card ∧
      (V.card : ℝ) - (maximalNatRuns V).card ≤ (l.map (fun p => p.2 - p.1)).sum ∧
      ∀ p ∈ l, ∃ L : ℝ, 1 ≤ L ∧ p.2 - p.1 = L + 4 * Real.log H ∧
        96 * Real.exp (-(p.2 - p.1)) ≤ cuspEndpointLengthSqLower ∧
        ∀ g ∈ E, BufferedCuspExcursion H L (g * diagonalFlow p.1) := by
  classical
  let V := modularCuspVisitTimes H n (modularMk g₀)
  obtain ⟨l, hfin, hnodup, hpair, hlen, hsum⟩ := exists_ordered_long_nat_runs V
  let f : (ℕ × ℕ) → ℝ × ℝ := fun p => ((p.1 : ℝ), (p.2 : ℝ) + 4 * Real.log H)
  have hrun (p : ℕ × ℕ) (hp : p ∈ l) : p ∈ maximalNatRuns V ∧ p.1 < p.2 := by
    have hmem : p ∈ l.toFinset := List.mem_toFinset.mpr hp
    rw [hfin] at hmem
    exact Finset.mem_filter.mp hmem
  have hHpos : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  refine ⟨l.map f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    apply hpair.imp_of_mem
    intro p q hp hq hpq
    have hpr := hrun p hp
    have hqr := hrun q hq
    have hstart : p.1 < q.1 := by omega
    have hgap := maximal_cusp_runs_buffered_order g₀ hHpos hpr.1 hqr.1 hstart
    change (p.2 : ℝ) + 4 * Real.log H ≤ (q.1 : ℝ)
    linarith
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqr := (mem_maximalNatRuns_iff V q).mp (hrun q hq).1
    have hqmem : q.2 ∈ V := hqr.2.1 (Finset.mem_Icc.mpr ⟨hqr.1, le_rfl⟩)
    have hqn := ((mem_modularCuspVisitTimes_iff H n (modularMk g₀) q.2).mp hqmem).1
    have hqle : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hqr.1
    have hqn' : (q.2 : ℝ) < n := by exact_mod_cast hqn
    change 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ (q.2 : ℝ) + 4 * Real.log H ∧ _
    exact ⟨Nat.cast_nonneg _, by linarith, by dsimp [f]; linarith⟩
  · simpa only [List.length_map] using hlen
  · rw [List.map_map, ← hsum]
    apply List.sum_le_sum
    intro p _
    dsimp only [Function.comp_apply, f]
    linarith
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqr := hrun q hq
    have hL : (1 : ℝ) ≤ (q.2 : ℝ) - q.1 := by
      have hstep : (q.1 : ℝ) + 1 ≤ q.2 := by
        exact_mod_cast (show q.1 + 1 ≤ q.2 from hqr.2)
      linarith
    refine ⟨(q.2 : ℝ) - q.1, hL, by dsimp [f]; ring, ?_, ?_⟩
    · change 96 * Real.exp (-(((q.2 : ℝ) + 4 * Real.log H) - q.1)) ≤ _
      rw [show ((q.2 : ℝ) + 4 * Real.log H) - q.1 =
        ((q.2 : ℝ) - q.1) + 4 * Real.log H by ring]
      exact exp_neg_buffered_duration_small cuspEndpointLengthSqLower_pos hH (by linarith) hlarge
    · intro g hg
      obtain ⟨hstart, hend, htimes⟩ := hE g hg
      have hqr' : q ∈ maximalNatRuns
          (modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H)))) := by
        rw [htimes]
        exact hqr.1
      have h := maximal_cusp_run_buffered (g * diagonalFlow (2 * Real.log H)) hHpos
        hwindow hqr' hstart hend
      have heq : (g * diagonalFlow (2 * Real.log H)) *
          diagonalFlow ((q.1 : ℝ) - 2 * Real.log H) = g * diagonalFlow (q.1 : ℝ) := by
        rw [mul_assoc, ← diagonalFlow_add]
        congr 1
        congr 1
        ring
      simpa only [heq] using h

end Erdos1148.DukeArithmetic
