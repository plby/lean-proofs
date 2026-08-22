/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialUpperCover
import ErdosProblems.Erdos1165.AnnularChronologicalFirstZero

/-!
# Walk-facing classifier for the radial upper cover

A fresh path which starts on radial level one and first reaches radial level
zero at its terminal time has exactly the chronological word shape expected
by the fixed-profile upper family.  This file combines the separate head,
last, adjacency, and no-early-zero lemmas into the single membership theorem
needed by source-cover constructions.
-/

open Set

namespace Erdos1165.AnnularRadialUpperClassifier

open AnnularChronologicalFirstZero AnnularFixedProfileTraceParser
open AnnularProfileLiteralAtoms AnnularRadialLabelWord
open AnnularRadialProfileWords AnnularRadialUpperCover
open AppendixFirstMoment PlanarPotential TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- The sound restart form: after retaining the approach through level one,
the fresh first-zero segment need only carry the internal and terminal
profile coordinates.  Its level-one count is deliberately not constrained,
because the retained approach contains that forced first transition. -/
theorem mem_fixedProfileRadialWordFamilyAtom_of_firstLevelZero_profileCoordinates
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : delta ≤ 1)
    {center start : Point} {omega : StepPath} {m : Profile n}
    (hm : IsConstrainedProfile delta m)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hinternal : ∀ i : Fin (n - 1),
      excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨scaleIndex i, by unfold scaleIndex; omega⟩ =
        m i)
    (hterminalLower : terminalLower n delta ≤
      (excursionProfile (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ : ℝ))
    (hterminalUpper : excursionProfile
        (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ ≤ n ^ 3) :
    omega ∈ fixedProfileRadialWordFamilyAtom n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  have hhead : labels.head? = some ⟨1, by omega⟩ :=
    chronologicalRadialLabels_head?_eq_of_start_mem hn hstart
  have hnonempty : labels ≠ [] := by
    intro hempty
    rw [hempty] at hhead
    simp at hhead
  have hbefore : ∀ i (hi : i < labels.length),
      i + 1 < labels.length → (labels[i]'hi : ℕ) ≠ 0 :=
    chronologicalRadialLabels_beforeFinal_ne_zero_of_firstZero
      hn center start omega hfirst
  have hadjacent : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1) :=
    chronologicalRadialLabels_isChain_adjacent hn hstart hbefore hhead
  have hend : labels.getLast? = some ⟨0, by omega⟩ :=
    chronologicalRadialLabels_getLast?_eq_of_first hn hfirst
  exact mem_fixedProfileRadialWordFamilyAtom_of_profileCoordinates
    hn hdelta hm hfirst hinternal hterminalLower hterminalUpper
      hnonempty hhead hadjacent hbefore hend

/-- First-level restart classifier with the profile-dependent cutoff.  The
internal profile is arbitrary. -/
theorem mem_exactFixedProfileRadialWordFamilyAtom_of_firstLevelZero_profileCoordinates
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} {center start : Point} {omega : StepPath} {m : Profile n}
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hinternal : ∀ i : Fin (n - 1),
      excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨scaleIndex i, by unfold scaleIndex; omega⟩ =
        m i)
    (hterminalLower : terminalLower n delta ≤
      (excursionProfile (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ : ℝ))
    (hterminalUpper : excursionProfile
        (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ ≤ n ^ 3) :
    omega ∈ exactFixedProfileRadialWordFamilyAtom
      n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  have hhead : labels.head? = some ⟨1, by omega⟩ :=
    chronologicalRadialLabels_head?_eq_of_start_mem hn hstart
  have hnonempty : labels ≠ [] := by
    intro hempty
    rw [hempty] at hhead
    simp at hhead
  have hbefore : ∀ i (hi : i < labels.length),
      i + 1 < labels.length → (labels[i]'hi : ℕ) ≠ 0 :=
    chronologicalRadialLabels_beforeFinal_ne_zero_of_firstZero
      hn center start omega hfirst
  have hadjacent : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1) :=
    chronologicalRadialLabels_isChain_adjacent hn hstart hbefore hhead
  have hend : labels.getLast? = some ⟨0, by omega⟩ :=
    chronologicalRadialLabels_getLast?_eq_of_first hn hfirst
  exact mem_exactFixedProfileRadialWordFamilyAtom_of_profileCoordinates
    hn hfirst hinternal hterminalLower hterminalUpper
      hnonempty hhead hadjacent hbefore hend

/-- A literal fixed-profile fresh excursion from level one until its first
level-zero hit belongs to the bounded fixed-profile radial-word family. -/
theorem mem_fixedProfileRadialWordFamilyAtom_of_firstLevelZero
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : delta ≤ 1)
    {center start : Point} {omega : StepPath} {m : Profile n}
    (hm : IsConstrainedProfile delta m)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile
        (fun q ↦ trajectoryFrom start omega q) n horizon center)) :
    omega ∈ fixedProfileRadialWordFamilyAtom n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  have hhead : labels.head? = some ⟨1, by omega⟩ := by
    exact chronologicalRadialLabels_head?_eq_of_start_mem hn hstart
  have hnonempty : labels ≠ [] := by
    intro hempty
    rw [hempty] at hhead
    simp at hhead
  have hbefore : ∀ i (hi : i < labels.length),
      i + 1 < labels.length → (labels[i]'hi : ℕ) ≠ 0 := by
    exact chronologicalRadialLabels_beforeFinal_ne_zero_of_firstZero
      hn center start omega hfirst
  have hadjacent : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1) := by
    exact chronologicalRadialLabels_isChain_adjacent
      hn hstart hbefore hhead
  have hend : labels.getLast? = some ⟨0, by omega⟩ := by
    exact chronologicalRadialLabels_getLast?_eq_of_first hn hfirst
  exact mem_fixedProfileRadialWordFamilyAtom_of_chronological_shape
    hn hdelta hm hfirst hfixed hnonempty hhead hadjacent hbefore hend

end

end Erdos1165.AnnularRadialUpperClassifier
