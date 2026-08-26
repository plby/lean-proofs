import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Removing both endpoints from a finite set in `[L,U]` loses at most two
points. -/
theorem interval_interior_card_add_two
    (S : Finset ℕ) (L U : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    S.card ≤ (S.filter fun n => L < n ∧ n < U).card + 2 := by
  let I := S.filter fun n => L < n ∧ n < U
  let E := S.filter fun n => ¬(L < n ∧ n < U)
  have hEsub : E ⊆ {L, U} := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hnnot := (Finset.mem_filter.mp hn).2
    have hnI := hinterval n hnS
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hEcard : E.card ≤ 2 := by
    calc
      E.card ≤ ({L, U} : Finset ℕ).card := Finset.card_le_card hEsub
      _ ≤ 2 := by
        simpa using Finset.card_insert_le L ({U} : Finset ℕ)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := S) (fun n => L < n ∧ n < U)
  change (S.filter fun n => L < n ∧ n < U).card + E.card = S.card at hpart
  omega

/-- Real-valued rearrangement used with density bounds. -/
theorem interval_interior_card_cast_lower
    (S : Finset ℕ) (L U : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ U)
    (D : ℝ) (hdense : D ≤ (S.card : ℝ)) :
    D - 2 ≤ ((S.filter fun n => L < n ∧ n < U).card : ℝ) := by
  have hnat := interval_interior_card_add_two S L U hinterval
  have hcast : (S.card : ℝ) ≤
      ((S.filter fun n => L < n ∧ n < U).card : ℝ) + 2 := by
    exact_mod_cast hnat
  linarith

end Erdos489
