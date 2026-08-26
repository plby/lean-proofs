import ErdosProblems.Erdos1148.RelativeFlow

/-!
# Accounting for the two lifts from the projective group

Negation fixes every binary quadratic form. Both signs of the relative
matrix must therefore be included when using chosen special-linear lifts.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

def signedCloseDiagonalFlowTimes (g : SL(2, ℝ)) (η : ℝ) : Set (Fin 2 → ℝ) :=
  closeDiagonalFlowTimes g η ∪ closeDiagonalFlowTimes (-g) η

theorem volume_signedCloseDiagonalFlowTimes_le {d ℓ : ℤ}
    (hd : 0 < d) (hℓ : ℓ ≠ 2 * d) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (g : SL(2, ℝ)) (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * g 0 1 * g 1 0)) :
    volume (signedCloseDiagonalFlowTimes g η) ≤
      ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by
  have hpneg : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * (-g) 0 1 * (-g) 1 0) := by
    change (ℓ : ℝ) = (d : ℝ) * (2 + 4 * (-g 0 1) * (-g 1 0))
    nlinarith [hpair]
  have hlog : 0 ≤ Real.log (4 * (d : ℝ)) := by
    apply Real.log_nonneg
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
    linarith
  have hbound := volume_closeDiagonalFlowTimes_le hd hℓ hη0 hη g hpair
  have hboundneg := volume_closeDiagonalFlowTimes_le hd hℓ hη0 hη (-g) hpneg
  calc
    volume (signedCloseDiagonalFlowTimes g η) ≤
        volume (closeDiagonalFlowTimes g η) + volume (closeDiagonalFlowTimes (-g) η) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (8 * η * Real.log (4 * (d : ℝ))) +
        ENNReal.ofReal (8 * η * Real.log (4 * (d : ℝ))) := add_le_add hbound hboundneg
    _ = ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma close_pairing_mem_noncentralMultiples {d ℓ : ℤ} (hd : 0 < d)
    (hℓ : ℓ ≠ 2 * d) {η : ℝ} {g : SL(2, ℝ)} (hg : EntryCloseOne η g)
    (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * g 0 1 * g 1 0)) :
    ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1 := by
  have habs : |ℓ - 2 * d| ≤ ⌊4 * (d : ℝ) * η ^ 2⌋ := by
    apply Int.le_floor.mpr
    exact_mod_cast entryCloseOne_pairing_bound hd hg hpair
  have hi := abs_le.mp habs
  simp only [noncentralMultiples, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, one_dvd _, hℓ⟩

lemma close_pairing_cutoff_bounds {d : ℤ} (hd : 0 < d)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    0 ≤ ⌊4 * (d : ℝ) * η ^ 2⌋ ∧ ⌊4 * (d : ℝ) * η ^ 2⌋ ≤ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Int.floor_nonneg.mpr (by positivity), ?_⟩
  have hηsq : 4 * η ^ 2 ≤ 1 := by nlinarith
  have hbound : 4 * (d : ℝ) * η ^ 2 ≤ d := by nlinarith
  have hf := (Int.floor_le (4 * (d : ℝ) * η ^ 2)).trans hbound
  exact_mod_cast hf

end Erdos1148.DukeArithmetic
