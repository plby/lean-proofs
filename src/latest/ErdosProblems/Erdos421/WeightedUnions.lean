import Mathlib

/-! # Nonnegative weights on finite coverings -/

namespace Erdos421

theorem sum_union_weight_le {α : Type*} [DecidableEq α] (S T : Finset α)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ a ∈ S ∪ T, w a) ≤ (∑ a ∈ S, w a) + ∑ a ∈ T, w a := by
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := w)
  have hpos : 0 ≤ ∑ a ∈ S ∩ T, w a := Finset.sum_nonneg (fun a _ ↦ hw a)
  linarith

theorem sum_biUnion_weight_le {α β : Type*} [DecidableEq β] (S : Finset α)
    (T : α → Finset β) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b ∈ S.biUnion T, w b) ≤ ∑ a ∈ S, ∑ b ∈ T a, w b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_weight_le (T a) (S.biUnion T) w hw).trans (add_le_add le_rfl ih)

end Erdos421
