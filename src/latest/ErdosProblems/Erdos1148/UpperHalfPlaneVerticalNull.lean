import ErdosProblems.Erdos1148.UpperHalfPlaneAffine
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! # Invariant measures give zero mass to each vertical geodesic -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Function
open scoped MatrixGroups

theorem invariant_upperHalfPlane_vertical_eq_zero (ν : Measure UpperHalfPlane) [SFinite ν]
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (c : ℝ) : ν {z | z.re = c} = 0 := by
  have hmeas (r : ℝ) : MeasurableSet {z : UpperHalfPlane | z.re = r} :=
    (isClosed_eq UpperHalfPlane.continuous_re continuous_const).measurableSet
  have hdisj : Pairwise (Disjoint on fun r : ℝ => {z : UpperHalfPlane | z.re = r}) := by
    intro r s hrs
    exact Set.disjoint_left.mpr (fun _ hr hs => hrs (hr.symm.trans hs))
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := ν) hmeas hdisj
  have hne : {r : ℝ | 0 < ν {z : UpperHalfPlane | z.re = r}} ≠ Set.univ := by
    intro h
    rw [h] at hcount
    exact Set.not_countable_univ hcount
  obtain ⟨r, hr⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hzero : ν {z : UpperHalfPlane | z.re = r} = 0 := by
    exact le_antisymm (not_lt.mp hr) bot_le
  have heq : (fun z : UpperHalfPlane => stableHorocycle (c - r) • z) ⁻¹'
      {z : UpperHalfPlane | z.re = c} = {z : UpperHalfPlane | z.re = r} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, stableHorocycle_smul_re]
    constructor <;> intro h <;> linarith
  have hmeasure := measure_preimage_smul ν (stableHorocycle (c - r)) {z : UpperHalfPlane | z.re = c}
  rw [heq, hzero] at hmeasure
  exact hmeasure.symm

end Erdos1148.DukeArithmetic
