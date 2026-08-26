import ErdosProblems.Erdos1148.CuspExcursionSeparation
import ErdosProblems.Erdos1148.BufferedExcursionRefinement
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Continuous cusp excursions arising from discrete visit runs -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem cusp_on_real_interval_of_integer_visits (g : SL(2, ℝ)) {H : ℝ}
    (hH : 0 < H) (hwindow : Real.exp 1 ≤ H ^ 4) {a b : ℕ}
    (hvisits : ∀ k ∈ Finset.Icc a b, modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H) :
    ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), modularMk (g * diagonalFlow t) ∈ modularCusp H := by
  intro t ht
  have ht0 : 0 ≤ t := (Nat.cast_nonneg a).trans ht.1
  have hab : a ≤ b := by exact_mod_cast ht.1.trans ht.2
  by_cases htb : t = (b : ℝ)
  · rw [htb]
    exact hvisits b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
  · have htb' : t < (b : ℝ) := lt_of_le_of_ne ht.2 htb
    let k := ⌊t⌋₊
    have hak : a ≤ k := Nat.le_floor ht.1
    have hkb : k < b := (Nat.floor_lt ht0).mpr htb'
    have hk : modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H :=
      hvisits k (Finset.mem_Icc.mpr ⟨hak, hkb.le⟩)
    have hk1 : modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)) ∈ modularCusp H :=
      hvisits (k + 1) (Finset.mem_Icc.mpr ⟨by omega, hkb⟩)
    have hgap : Real.exp (((k + 1 : ℕ) : ℝ) - (k : ℝ)) ≤ H ^ 4 := by
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left] using hwindow
    exact cusp_between_of_short_time_gap g hH (by exact_mod_cast Nat.le_succ k)
      hgap hk hk1 t ⟨Nat.floor_le ht0, by exact_mod_cast (Nat.lt_floor_add_one t).le⟩

theorem cusp_time_gap_gt_of_intermediate_exit (g : SL(2, ℝ)) {H a b t : ℝ}
    (hH : 0 < H) (ht : t ∈ Set.Icc a b)
    (ha : modularMk (g * diagonalFlow a) ∈ modularCusp H)
    (hb : modularMk (g * diagonalFlow b) ∈ modularCusp H)
    (hexit : modularMk (g * diagonalFlow t) ∉ modularCusp H) :
    4 * Real.log H < b - a := by
  by_contra h
  exact hexit (cusp_between_of_log_time_gap g hH (ht.1.trans ht.2) (le_of_not_gt h) ha hb t ht)

theorem buffered_cusp_intervals_disjoint_of_exit (g : SL(2, ℝ)) {H a b t : ℝ}
    (hH : 0 < H) (ht : t ∈ Set.Icc a b)
    (ha : modularMk (g * diagonalFlow a) ∈ modularCusp H)
    (hb : modularMk (g * diagonalFlow b) ∈ modularCusp H)
    (hexit : modularMk (g * diagonalFlow t) ∉ modularCusp H) :
    a + 2 * Real.log H < b - 2 * Real.log H := by
  linarith [cusp_time_gap_gt_of_intermediate_exit g hH ht ha hb hexit]

theorem bufferedCuspExcursion_of_integer_run (g : SL(2, ℝ)) {H : ℝ}
    (hH : 0 < H) (hwindow : Real.exp 1 ≤ H ^ 4) {a b : ℕ}
    (hvisits : ∀ k ∈ Finset.Icc a b, modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow ((a : ℝ) - 1)) ∉ modularCusp H)
    (hafter : modularMk (g * diagonalFlow ((b : ℝ) + 1)) ∉ modularCusp H) :
    BufferedCuspExcursion H ((b : ℝ) - a)
      (g * diagonalFlow ((a : ℝ) - 2 * Real.log H)) := by
  have hentry : (g * diagonalFlow ((a : ℝ) - 2 * Real.log H)) *
      diagonalFlow (2 * Real.log H) = g * diagonalFlow (a : ℝ) := by
    rw [mul_assoc, ← diagonalFlow_add, sub_add_cancel]
  dsimp only [BufferedCuspExcursion]
  rw [hentry]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [mul_assoc, ← diagonalFlow_add]
    apply cusp_on_real_interval_of_integer_visits g hH hwindow hvisits
    constructor <;> linarith [ht.1, ht.2]
  · simpa only [mul_assoc, ← diagonalFlow_add, sub_eq_add_neg] using hbefore
  · rw [mul_assoc, ← diagonalFlow_add,
      show (a : ℝ) + ((b : ℝ) - a + 1) = b + 1 by ring]
    exact hafter

end Erdos1148.DukeArithmetic
