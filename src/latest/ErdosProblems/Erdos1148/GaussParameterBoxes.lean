import ErdosProblems.Erdos1148.ReturningGaussParameters
import ErdosProblems.Erdos1148.GaussForwardCloseness
import ErdosProblems.Erdos1148.ModularForwardBowenPairs
import ErdosProblems.Erdos1148.RealIntervalGrid

/-! # Compact measurable Gauss parameter boxes and forward Bowen closeness -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

instance : TopologicalSpace BoundedGaussParameters :=
  inferInstanceAs (TopologicalSpace
    {p : ℝ × ℝ × ℝ // |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ 1 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2})

instance : CompactSpace BoundedGaussParameters := by
  have heq : {p : ℝ × ℝ × ℝ | |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ 1 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2} =
      Set.Icc (-1) 1 ×ˢ (Set.Icc (-1) 1 ×ˢ Set.Icc (1 / 2) 2) := by
    ext p
    simp only [Set.mem_ofPred_eq, abs_le, Set.mem_prod, Set.mem_Icc]
  have hcompact : IsCompact
      {p : ℝ × ℝ × ℝ | |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ 1 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2} := by
    rw [heq]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  exact isCompact_iff_compactSpace.mp hcompact

lemma continuous_gaussParameterFrame (g : SL(2, ℝ)) : Continuous (gaussParameterFrame g) := by
  apply Continuous.mul
  · apply Continuous.mul continuous_const
    apply Continuous.subtype_mk
    change Continuous (fun p : BoundedGaussParameters => !![1, 0; p.val.1, 1])
    fun_prop
  · apply Continuous.subtype_mk
    change Continuous (fun p : BoundedGaussParameters =>
      !![p.val.2.2, p.val.2.1 / p.val.2.2; 0, p.val.2.2⁻¹])
    have hc : Continuous (fun p : BoundedGaussParameters => p.val.2.2) := by fun_prop
    have hne (p : BoundedGaussParameters) : p.val.2.2 ≠ 0 := by
      have := p.property.2.2.1
      linarith
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j
    · exact hc
    · exact (show Continuous (fun p : BoundedGaussParameters => p.val.2.1) by fun_prop).div hc hne
    · exact continuous_const
    · exact hc.inv₀ hne

def gaussParameterCell (a b c wr wx wh : ℝ) : Set BoundedGaussParameters :=
  {p | p.val.1 ∈ Set.Icc a (a + wr) ∧ p.val.2.1 ∈ Set.Icc b (b + wx) ∧
    p.val.2.2 ∈ Set.Icc c (c + wh)}

lemma isClosed_gaussParameterCell (a b c wr wx wh : ℝ) :
    IsClosed (gaussParameterCell a b c wr wx wh) :=
  (isClosed_Icc.preimage (by fun_prop : Continuous (fun p : BoundedGaussParameters => p.val.1))).inter
    ((isClosed_Icc.preimage (by fun_prop : Continuous (fun p : BoundedGaussParameters => p.val.2.1))).inter
      (isClosed_Icc.preimage (by fun_prop : Continuous (fun p : BoundedGaussParameters => p.val.2.2))))

noncomputable def gaussParameterBox (g : SL(2, ℝ)) (a b c wr wx wh : ℝ) : Set ModularOrbitSpace :=
  (fun p : BoundedGaussParameters => modularMk (gaussParameterFrame g p)) ''
    gaussParameterCell a b c wr wx wh

theorem isCompact_gaussParameterBox (g : SL(2, ℝ)) (a b c wr wx wh : ℝ) :
    IsCompact (gaussParameterBox g a b c wr wx wh) :=
  (isClosed_gaussParameterCell a b c wr wx wh).isCompact.image
    (continuous_modularMk.comp (continuous_gaussParameterFrame g))

lemma measurableSet_gaussParameterBox (g : SL(2, ℝ)) (a b c wr wx wh : ℝ) :
    MeasurableSet (gaussParameterBox g a b c wr wx wh) :=
  (isCompact_gaussParameterBox g a b c wr wx wh).measurableSet

theorem gaussParameterBox_prod_subset_forward (g : SL(2, ℝ)) (a b c : ℝ) {δ S : ℝ}
    (hδ : 0 ≤ δ) (hS : 0 ≤ S) :
    let B := gaussParameterBox g a b c (δ * Real.exp (-S)) δ δ
    B ×ˢ B ⊆ modularForwardBowenPairs (8 * δ) S := by
  dsimp only
  rintro ⟨u, v⟩ ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩
  apply mem_modularForwardBowenPairs_of_lifts hS
  exact gaussFrame_forward_close g p.property.2.1 q.property.2.1
    p.property.2.2.1 q.property.2.2.1 p.property.2.2.2 q.property.2.2.2 hδ hS
    (abs_sub_le_of_mem_same_interval hq.2.2 hp.2.2)
    (abs_sub_le_of_mem_same_interval hq.2.1 hp.2.1)
    (abs_sub_le_of_mem_same_interval hq.1 hp.1)

end Erdos1148.DukeArithmetic
