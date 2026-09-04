/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord

/-!
# Packaging a finite chronological scan as a radial word

This file exposes the small list-to-word constructor needed by walk-facing
parsers.  Geometry is deliberately absent: the caller proves that the
observed label list starts at one, has adjacent successive labels, has no
zero before its last entry, and ends at zero.  The resulting word renders
back to the original list definitionally up to the length cast.
-/

namespace Erdos1165.AnnularRadialWordOfList

open AnnularRadialLabelWord

noncomputable section

/-- Package a nonempty first-zero adjacent label list as a literal radial
word.  Its transition length is `labels.length - 1`. -/
noncomputable def radialLabelWordOfList
    {n : ℕ} (labels : List (Fin (n + 2))) (hne : labels ≠ [])
    (hstart : labels.head? = some ⟨1, by omega⟩)
    (hadjacent : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1))
    (hbefore : ∀ i (hi : i < labels.length),
      i + 1 < labels.length → (labels[i]'hi : ℕ) ≠ 0)
    (hend : labels.getLast? = some ⟨0, by omega⟩) :
    RadialLabelWord n (labels.length - 1) := by
  have hlength : labels.length - 1 + 1 = labels.length :=
    Nat.sub_add_cancel (List.length_pos_iff.mpr hne)
  let index : Fin (labels.length - 1 + 1) → Fin labels.length :=
    fun j ↦ Fin.cast hlength j
  refine
    { level := fun j ↦ labels.get (index j)
      startsAtOne := ?_
      adjacent := ?_
      beforeFinal_ne_zero := ?_
      endsAtZero := ?_ }
  · have hzero : (index ⟨0, by omega⟩ : ℕ) = 0 := rfl
    have hhead : labels[0] = (⟨1, by omega⟩ : Fin (n + 2)) := by
      rw [List.head?_eq_getElem?] at hstart
      rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr hne)] at hstart
      exact Option.some.inj hstart
    simpa only [index, List.get_eq_getElem, hzero] using hhead
  · intro j
    have hj : (j : ℕ) + 1 < labels.length := by omega
    have hstep := List.isChain_iff_getElem.mp hadjacent (j : ℕ) hj
    simpa [index, List.get_eq_getElem] using hstep
  · intro j
    have hj : (j : ℕ) + 1 < labels.length := by omega
    simpa [index, List.get_eq_getElem] using
      hbefore (j : ℕ) (by omega) hj
  · have hlast : labels[labels.length - 1] =
        (⟨0, by omega⟩ : Fin (n + 2)) := by
      rw [← List.getLast_eq_getElem hne]
      rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
      exact hend
    simpa [index, List.get_eq_getElem] using hlast

/-- Rendering the packaged word recovers the input label list exactly. -/
theorem radialLabelWordOfList_toList
    {n : ℕ} (labels : List (Fin (n + 2))) (hne : labels ≠ [])
    (hstart hadjacent hbefore hend) :
    (radialLabelWordOfList labels hne hstart hadjacent hbefore hend).toList =
      labels := by
  apply List.ext_get
  · simp only [RadialLabelWord.length_toList]
    exact Nat.sub_add_cancel (List.length_pos_iff.mpr hne)
  · intro i hi₁ hi₂
    cases i with
    | zero => simp [radialLabelWordOfList, RadialLabelWord.toList]
    | succ i => simp [radialLabelWordOfList, RadialLabelWord.toList]

/-- The same packaging as a bounded word once the transition-count bound is
known. -/
noncomputable def boundedRadialLabelWordOfList
    {n maxTransitions : ℕ}
    (labels : List (Fin (n + 2))) (hne : labels ≠ [])
    (hstart : labels.head? = some ⟨1, by omega⟩)
    (hadjacent : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1))
    (hbefore : ∀ i (hi : i < labels.length),
      i + 1 < labels.length → (labels[i]'hi : ℕ) ≠ 0)
    (hend : labels.getLast? = some ⟨0, by omega⟩)
    (hbound : labels.length - 1 ≤ maxTransitions) :
    BoundedRadialLabelWord n maxTransitions :=
  ⟨⟨labels.length - 1, by omega⟩,
    radialLabelWordOfList labels hne hstart hadjacent hbefore hend⟩

/-- Rendering the bounded packaging also recovers the input list. -/
theorem boundedRadialLabelWordOfList_toList
    {n maxTransitions : ℕ}
    (labels : List (Fin (n + 2))) (hne : labels ≠ [])
    (hstart hadjacent hbefore hend)
    (hbound : labels.length - 1 ≤ maxTransitions) :
    (boundedRadialLabelWordOfList labels hne hstart hadjacent hbefore hend
      hbound).2.toList = labels := by
  exact radialLabelWordOfList_toList labels hne hstart hadjacent hbefore hend

end

end Erdos1165.AnnularRadialWordOfList
