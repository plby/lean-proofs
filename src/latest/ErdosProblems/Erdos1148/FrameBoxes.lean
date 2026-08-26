import ErdosProblems.Erdos1148.FrameBoxCloseness
import ErdosProblems.Erdos1148.PacketClosePairs

/-! # Compact boxes in modular frame coordinates -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

def frameBoxParameters (x h θ wx wh wθ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Icc x (x + wx) ×ˢ (Set.Icc h (h + wh) ×ˢ Set.Icc θ (θ + wθ))

noncomputable def frameBoxMap (x h θ wx wh wθ : ℝ) (hh : 0 < h)
    (p : frameBoxParameters x h θ wx wh wθ) : ModularOrbitSpace :=
  modularMk (cuspFrame p.val.1 p.val.2.1 p.val.2.2 (hh.trans_le p.prop.2.1.1).ne')

noncomputable def frameBox (x h θ wx wh wθ : ℝ) (hh : 0 < h) : Set ModularOrbitSpace :=
  Set.range (frameBoxMap x h θ wx wh wθ hh)

lemma continuous_frameBoxMap (x h θ wx wh wθ : ℝ) (hh : 0 < h) :
    Continuous (frameBoxMap x h θ wx wh wθ hh) := by
  apply continuous_modularMk.comp
  apply Continuous.mul
  · apply Continuous.subtype_mk
    change Continuous (fun p : frameBoxParameters x h θ wx wh wθ =>
      !![p.val.2.1, p.val.1 / p.val.2.1; 0, (p.val.2.1)⁻¹])
    have hc : Continuous (fun p : frameBoxParameters x h θ wx wh wθ => p.val.2.1) := by fun_prop
    have hne (p : frameBoxParameters x h θ wx wh wθ) : p.val.2.1 ≠ 0 :=
      (hh.trans_le p.prop.2.1.1).ne'
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j
    · exact hc
    · exact (show Continuous (fun p : frameBoxParameters x h θ wx wh wθ => p.val.1) by
        fun_prop).div hc hne
    · exact continuous_const
    · exact hc.inv₀ hne
  · apply Continuous.subtype_mk
    change Continuous (fun p : frameBoxParameters x h θ wx wh wθ =>
      !![Real.cos p.val.2.2, -Real.sin p.val.2.2; Real.sin p.val.2.2, Real.cos p.val.2.2])
    fun_prop

theorem isCompact_frameBox (x h θ wx wh wθ : ℝ) (hh : 0 < h) :
    IsCompact (frameBox x h θ wx wh wθ hh) := by
  have hparams : IsCompact (frameBoxParameters x h θ wx wh wθ) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let : CompactSpace (frameBoxParameters x h θ wx wh wθ) := isCompact_iff_compactSpace.mp hparams
  exact isCompact_range (continuous_frameBoxMap x h θ wx wh wθ hh)

lemma measurableSet_frameBox (x h θ wx wh wθ : ℝ) (hh : 0 < h) :
    MeasurableSet (frameBox x h θ wx wh wθ hh) :=
  (isCompact_frameBox x h θ wx wh wθ hh).measurableSet

theorem frameBox_prod_subset_close {x h θ H δ : ℝ} (hH : 0 < H) (hh : H ≤ h) (hδ : 0 ≤ δ) :
    let B := frameBox x h θ (δ * H ^ 2) (δ * H) δ (hH.trans_le hh)
    B ×ˢ B ⊆ modularClosePairs (5 * δ) := by
  dsimp only
  rintro ⟨a, b⟩ ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
  refine ⟨cuspFrame p.val.1 p.val.2.1 p.val.2.2 _, cuspFrame q.val.1 q.val.2.1 q.val.2.2 _, rfl, ?_⟩
  exact cuspFrame_relative_close hH (hh.trans p.prop.2.1.1) (hh.trans q.prop.2.1.1) hδ
    (abs_sub_le_of_mem_same_interval q.prop.2.1 p.prop.2.1)
    (abs_sub_le_of_mem_same_interval q.prop.1 p.prop.1)
    (abs_sub_le_of_mem_same_interval q.prop.2.2 p.prop.2.2)

end Erdos1148.DukeArithmetic
