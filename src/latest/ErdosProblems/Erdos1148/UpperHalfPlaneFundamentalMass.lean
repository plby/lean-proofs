import ErdosProblems.Erdos1148.UpperHalfPlaneStripMass
import ErdosProblems.Erdos1148.UpperHalfPlaneHaarImage
import Mathlib.NumberTheory.Modular

/-! # The modular fundamental domain has finite invariant mass -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

theorem invariant_upper_shifted_siegel_strip_finite (ν : Measure UpperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (r : ℝ) :
    ν {z : UpperHalfPlane | z.re ∈ Set.Ico r (1 + r) ∧ 1 ≤ z.im} < ∞ := by
  have heq : (fun z : UpperHalfPlane => stableHorocycle r • z) ⁻¹'
      {z : UpperHalfPlane | z.re ∈ Set.Ico r (1 + r) ∧ 1 ≤ z.im} =
      {z : UpperHalfPlane | z.re ∈ Set.Ico 0 1 ∧ 1 ≤ z.im} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ico,
      stableHorocycle_smul_re, stableHorocycle_smul_im]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, h₃⟩
  have hmass := measure_preimage_smul ν (stableHorocycle r)
    {z : UpperHalfPlane | z.re ∈ Set.Ico r (1 + r) ∧ 1 ≤ z.im}
  rw [heq] at hmass
  rw [← hmass]
  exact invariant_upper_siegel_strip_finite ν

theorem invariant_upper_fundamental_domain_finite (ν : Measure UpperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] :
    ν ModularGroup.fd < ∞ := by
  let K := upperClosedRectangle (-1) 1 (1 / 2) 1
  let S₀ := {z : UpperHalfPlane | z.re ∈ Set.Ico (-1) (1 + -1) ∧ 1 ≤ z.im}
  let S₁ := {z : UpperHalfPlane | z.re ∈ Set.Ico 0 1 ∧ 1 ≤ z.im}
  have hsub : ModularGroup.fd ⊆ K ∪ (S₀ ∪ S₁) := by
    intro z hz
    have hx := abs_le.mp hz.2
    by_cases hy : z.im ≤ 1
    · left
      have hlow := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, hy⟩⟩
    · right
      by_cases hx' : z.re < 0
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, (lt_of_not_ge hy).le⟩
      · exact Or.inr ⟨⟨le_of_not_gt hx', by linarith⟩, (lt_of_not_ge hy).le⟩
  apply lt_of_le_of_lt (measure_mono hsub)
  apply lt_of_le_of_lt (measure_union_le K (S₀ ∪ S₁))
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact (isCompact_upperClosedRectangle (-1) 1 (1 / 2) 1 (by norm_num)).measure_lt_top
  · apply lt_of_le_of_lt (measure_union_le S₀ S₁)
    exact ENNReal.add_lt_top.mpr ⟨invariant_upper_shifted_siegel_strip_finite ν (-1),
      invariant_upper_siegel_strip_finite ν⟩

theorem specialLinear_haar_fd_preimage_finite :
    (Measure.haar (G := SL(2, ℝ)))
      ((fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹' ModularGroup.fd) < ∞ := by
  have h := invariant_upper_fundamental_domain_finite upperHalfPlaneHaarImage
  rwa [upperHalfPlaneHaarImage, Measure.map_apply measurable_smul_I
    ModularGroup.isClosed_fd.measurableSet] at h

end Erdos1148.DukeArithmetic
