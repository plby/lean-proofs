import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! # Compact rectangles in the upper half-plane -/

namespace Erdos1148.DukeArithmetic

def upperClosedRectangle (a b c d : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d}

theorem isCompact_upperClosedRectangle (a b c d : ℝ) (hc : 0 < c) :
    IsCompact (upperClosedRectangle a b c d) := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  have heq : UpperHalfPlane.coe '' upperClosedRectangle a b c d =
      {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hc.trans_le hz.2.1⟩, hz, rfl⟩
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def upperHalfOpenRectangle (a b c d : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Set.Ico a b ∧ z.im ∈ Set.Icc c d}

lemma measurableSet_upperHalfOpenRectangle (a b c d : ℝ) :
    MeasurableSet (upperHalfOpenRectangle a b c d) :=
  (measurableSet_Ico.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Icc.preimage UpperHalfPlane.continuous_im.measurable)

lemma upperHalfOpenRectangle_subset_closed (a b c d : ℝ) :
    upperHalfOpenRectangle a b c d ⊆ upperClosedRectangle a b c d := by
  rintro z ⟨hre, him⟩
  exact ⟨⟨hre.1, hre.2.le⟩, him⟩

end Erdos1148.DukeArithmetic
