import ErdosProblems.Erdos1148.UpperHalfPlaneRectangles
import ErdosProblems.Erdos1148.UpperHalfPlaneAffine

/-! # A finite packing bound for invariant upper half-plane measures -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Function
open scoped MatrixGroups ENNReal

theorem invariant_upper_rectangle_translation (ν : Measure UpperHalfPlane)
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (a b c d r : ℝ) :
    ν (upperHalfOpenRectangle (a + r) (b + r) c d) =
      ν (upperHalfOpenRectangle a b c d) := by
  have heq : (fun z : UpperHalfPlane => stableHorocycle r • z) ⁻¹'
      upperHalfOpenRectangle (a + r) (b + r) c d =
      upperHalfOpenRectangle a b c d := by
    ext z
    simp only [Set.mem_preimage, upperHalfOpenRectangle, Set.mem_setOf_eq,
      Set.mem_Ico, Set.mem_Icc, stableHorocycle_smul_re, stableHorocycle_smul_im]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, h₃⟩
  exact (measure_preimage_smul ν (stableHorocycle r) _).symm.trans (congrArg ν heq)

theorem invariant_upper_thin_rectangle_packing (ν : Measure UpperHalfPlane)
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (N : ℕ) (hN : 0 < N) :
    (N : ℝ≥0∞) * ν (upperHalfOpenRectangle 0 (1 / N) 1 2) ≤
      ν (upperClosedRectangle 0 1 1 2) := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let R (k : Fin N) := upperHalfOpenRectangle (k / (N : ℝ)) ((k + 1) / (N : ℝ)) 1 2
  have hmeas (k : Fin N) : MeasurableSet (R k) := measurableSet_upperHalfOpenRectangle _ _ _ _
  have hmass (k : Fin N) : ν (R k) = ν (upperHalfOpenRectangle 0 (1 / N) 1 2) := by
    have h := invariant_upper_rectangle_translation ν 0 (1 / N) 1 2 (k / (N : ℝ))
    simpa only [R, zero_add, add_zero, add_div, add_comm] using h
  have hdisj : Pairwise (Disjoint on R) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z hi hj
    have hi' : (i : ℝ) / N ≤ z.re ∧ z.re < ((i : ℝ) + 1) / N := hi.1
    have hj' : (j : ℝ) / N ≤ z.re ∧ z.re < ((j : ℝ) + 1) / N := hj.1
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with hlt | hlt
    · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      have := div_le_div_of_nonneg_right hle hNR.le
      linarith
    · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      have := div_le_div_of_nonneg_right hle hNR.le
      linarith
  have hsub : (⋃ k, R k) ⊆ upperClosedRectangle 0 1 1 2 := by
    intro z hz
    obtain ⟨k, hz⟩ := Set.mem_iUnion.mp hz
    have h₀ : (0 : ℝ) ≤ k / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) hNR.le
    have hk : (k : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
    have h₁ : ((k : ℝ) + 1) / N ≤ 1 := (div_le_one hNR).mpr hk
    exact ⟨⟨h₀.trans hz.1.1, hz.1.2.le.trans h₁⟩, hz.2⟩
  calc
    (N : ℝ≥0∞) * ν (upperHalfOpenRectangle 0 (1 / N) 1 2) = ∑ k : Fin N, ν (R k) := by
      simp [hmass]
    _ = ν (⋃ k, R k) := by simpa only [tsum_fintype] using (measure_iUnion hdisj hmeas).symm
    _ ≤ ν (upperClosedRectangle 0 1 1 2) := measure_mono hsub

end Erdos1148.DukeArithmetic
