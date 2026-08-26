import ErdosProblems.Erdos1002.MarkedResonances

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Positive and negative marked windows

The state space deletes the singular coordinate `x = 0`.  This file proves
that an arbitrary marked set avoiding that hyperplane splits exactly into
disjoint positive and negative parts, and that the literal finite marked
count is additive across the split.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance signedMarkedWindowsPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

theorem markedResonanceCount_union_of_disjoint
    (N P : ℕ) {B C : Set (ℝ × ℝ × ℝ)} (hBC : Disjoint B C) (α : ℝ) :
    markedResonanceCount N P (B ∪ C) α =
      markedResonanceCount N P B α + markedResonanceCount N P C α := by
  classical
  unfold markedResonanceCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hprim : IsPrimitiveResonance p α
  · by_cases hB : markedResonancePoint N p α ∈ B
    · have hC : markedResonancePoint N p α ∉ C := by
        exact fun hz ↦ Set.disjoint_left.1 hBC hB hz
      simp [hprim, hB, hC]
    · by_cases hC : markedResonancePoint N p α ∈ C
      · simp [hprim, hB, hC]
      · simp [hprim, hB, hC]
  · simp [hprim]

/-- Part of a marked set with positive singular coordinate. -/
def positiveMarkedPart (B : Set (ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  B ∩ {z | 0 < z.2.1}

/-- Part of a marked set with negative singular coordinate. -/
def negativeMarkedPart (B : Set (ℝ × ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  B ∩ {z | z.2.1 < 0}

theorem measurableSet_positiveMarkedPart {B : Set (ℝ × ℝ × ℝ)}
    (hB : MeasurableSet B) : MeasurableSet (positiveMarkedPart B) := by
  exact hB.inter (measurableSet_lt measurable_const
    (measurable_fst.comp measurable_snd))

theorem measurableSet_negativeMarkedPart {B : Set (ℝ × ℝ × ℝ)}
    (hB : MeasurableSet B) : MeasurableSet (negativeMarkedPart B) := by
  exact hB.inter (measurableSet_lt
    (measurable_fst.comp measurable_snd) measurable_const)

theorem disjoint_positiveMarkedPart_negativeMarkedPart
    (B : Set (ℝ × ℝ × ℝ)) :
    Disjoint (positiveMarkedPart B) (negativeMarkedPart B) := by
  rw [Set.disjoint_left]
  intro z hzpos hzneg
  have hp : 0 < z.2.1 := hzpos.2
  have hn : z.2.1 < 0 := hzneg.2
  linarith

theorem positiveMarkedPart_union_negativeMarkedPart
    {B : Set (ℝ × ℝ × ℝ)}
    (hzero : ∀ z ∈ B, z.2.1 ≠ 0) :
    positiveMarkedPart B ∪ negativeMarkedPart B = B := by
  ext z
  constructor
  · rintro (hz | hz) <;> exact hz.1
  · intro hz
    rcases lt_or_gt_of_ne (hzero z hz) with hx | hx
    · exact Or.inr ⟨hz, hx⟩
    · exact Or.inl ⟨hz, hx⟩

/-- Exact count decomposition for any signed window avoiding zero. -/
theorem markedResonanceCount_eq_positive_add_negative
    (N P : ℕ) {B : Set (ℝ × ℝ × ℝ)}
    (hzero : ∀ z ∈ B, z.2.1 ≠ 0) (α : ℝ) :
    markedResonanceCount N P B α =
      markedResonanceCount N P (positiveMarkedPart B) α +
        markedResonanceCount N P (negativeMarkedPart B) α := by
  rw [← markedResonanceCount_union_of_disjoint N P
    (disjoint_positiveMarkedPart_negativeMarkedPart B) α,
    positiveMarkedPart_union_negativeMarkedPart hzero]

end

end Erdos1002
