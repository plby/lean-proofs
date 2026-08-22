/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialWordLength
import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms

/-!
# Packaging a successful first-zero trace into the fixed-profile word family

The walk-facing geometry only has to show that the chronological scan begins
at one, moves through adjacent labels, has no zero before its final label,
and ends at zero.  This module performs all remaining bookkeeping: it builds
the radial word, reads its upcrossing counts from the literal excursion
profile, proves the finite transition cutoff, and inserts the path into the
fixed-profile radial-word family.
-/

open Set

namespace Erdos1165.AnnularFixedProfileTraceParser

open AppendixFirstMoment AnnularProfileLiteralAtoms
open AnnularRadialLabelWord AnnularRadialProfileWords
open AnnularRadialWordLength AnnularRadialWordOfList
open PlanarPotential TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- A successful literal profile together with the elementary shape facts
about its chronological first-zero scan belongs to the bounded fixed-profile
word family. -/
theorem mem_fixedProfileRadialWordFamilyAtom_of_chronological_shape
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : delta ≤ 1)
    {center start : Point} {omega : StepPath} {m : Profile n}
    (hm : IsConstrainedProfile delta m)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile
        (fun q ↦ trajectoryFrom start omega q) n horizon center))
    (hnonempty : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon ≠ [])
    (hstart : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).head? =
        some ⟨1, by omega⟩)
    (hadjacent : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).IsChain
        (fun left right ↦ Nat.dist left.val right.val = 1))
    (hbefore : ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0)
    (hend : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).getLast? =
        some ⟨0, by omega⟩) :
    omega ∈ fixedProfileRadialWordFamilyAtom
      n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  let word := radialLabelWordOfList labels hnonempty hstart hadjacent hbefore hend
  have htrace : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon = word.toList := by
    exact (radialLabelWordOfList_toList
      labels hnonempty hstart hadjacent hbefore hend).symm
  have hinternal : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i := by
    intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k, scaleIndex]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k, scaleIndex])
    exact hup.symm.trans (hcompleted.trans (hfixed.2.1 i))
  have hterminalCount :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ =
        excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨n + 1, by omega⟩ := by
    let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k]; omega)
    exact hup.symm.trans hcompleted
  have hterminalLower : terminalLower n delta ≤
      (radialUpcrossingCount word ⟨n + 1, by omega⟩ : ℝ) := by
    rw [hterminalCount]
    exact hfixed.2.2.1
  have hterminalUpper :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
    rw [hterminalCount]
    exact hfixed.2.2.2
  have hbound : labels.length - 1 ≤ profileRadialWordMaxTransitions n := by
    exact radialLabelWord_transitionLength_le_profileRadialWordMaxTransitions
      hn hdelta hm word hinternal hterminalUpper
  let bounded : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) :=
    ⟨⟨labels.length - 1, by omega⟩, word⟩
  have hboundedFixed : IsFixedProfileRadialWord n delta m bounded := by
    exact ⟨hinternal, hterminalLower, hterminalUpper⟩
  apply (mem_radialLabelWordFamilyAtom_iff n
    (profileRadialWordMaxTransitions n) center start
      (IsFixedProfileRadialWord n delta m) omega).2
  refine ⟨bounded, hboundedFixed, ?_⟩
  apply (mem_radialLabelWordAtom_iff n bounded.1 center start bounded.2 omega).2
  exact ⟨horizon, hfirst, htrace⟩

/-- Fresh level-one suffixes have no completed level-one excursion of their
own, so they need not satisfy the redundant first component of
`FixedSuccessfulProfile`.  The radial word family only records the internal
profile coordinates (levels two through `n`) and the terminal window.  This
variant takes precisely those literal coordinate facts. -/
theorem mem_fixedProfileRadialWordFamilyAtom_of_profileCoordinates
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : delta ≤ 1)
    {center start : Point} {omega : StepPath} {m : Profile n}
    (hm : IsConstrainedProfile delta m)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hinternalProfile : ∀ i : Fin (n - 1),
      excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨scaleIndex i, by unfold scaleIndex; omega⟩ =
        m i)
    (hterminalLower : terminalLower n delta ≤
      (excursionProfile (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ : ℝ))
    (hterminalUpper : excursionProfile
        (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ ≤ n ^ 3)
    (hnonempty : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon ≠ [])
    (hstart : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).head? =
        some ⟨1, by omega⟩)
    (hadjacent : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).IsChain
        (fun left right ↦ Nat.dist left.val right.val = 1))
    (hbefore : ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0)
    (hend : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).getLast? =
        some ⟨0, by omega⟩) :
    omega ∈ fixedProfileRadialWordFamilyAtom
      n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  let word := radialLabelWordOfList labels hnonempty hstart hadjacent hbefore hend
  have htrace : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon = word.toList := by
    exact (radialLabelWordOfList_toList
      labels hnonempty hstart hadjacent hbefore hend).symm
  have hinternal : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i := by
    intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k, scaleIndex]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k, scaleIndex])
    exact hup.symm.trans (hcompleted.trans (hinternalProfile i))
  have hterminalCount :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ =
        excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨n + 1, by omega⟩ := by
    let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k]; omega)
    exact hup.symm.trans hcompleted
  have hterminalLower' : terminalLower n delta ≤
      (radialUpcrossingCount word ⟨n + 1, by omega⟩ : ℝ) := by
    rw [hterminalCount]
    exact hterminalLower
  have hterminalUpper' :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
    rw [hterminalCount]
    exact hterminalUpper
  have hbound : labels.length - 1 ≤ profileRadialWordMaxTransitions n := by
    exact radialLabelWord_transitionLength_le_profileRadialWordMaxTransitions
      hn hdelta hm word hinternal hterminalUpper'
  let bounded : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n) :=
    ⟨⟨labels.length - 1, by omega⟩, word⟩
  have hboundedFixed : IsFixedProfileRadialWord n delta m bounded := by
    exact ⟨hinternal, hterminalLower', hterminalUpper'⟩
  apply (mem_radialLabelWordFamilyAtom_iff n
    (profileRadialWordMaxTransitions n) center start
      (IsFixedProfileRadialWord n delta m) omega).2
  refine ⟨bounded, hboundedFixed, ?_⟩
  apply (mem_radialLabelWordAtom_iff n bounded.1 center start bounded.2 omega).2
  exact ⟨horizon, hfirst, htrace⟩

/-- The profile-dependent-cutoff version of the coordinate parser.  It is
valid for an arbitrary exact internal profile; only the successful terminal
window is required. -/
theorem mem_exactFixedProfileRadialWordFamilyAtom_of_profileCoordinates
    {n horizon : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} {center start : Point} {omega : StepPath} {m : Profile n}
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon)
    (hinternalProfile : ∀ i : Fin (n - 1),
      excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨scaleIndex i, by unfold scaleIndex; omega⟩ =
        m i)
    (hterminalLower : terminalLower n delta ≤
      (excursionProfile (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ : ℝ))
    (hterminalUpper : excursionProfile
        (fun q ↦ trajectoryFrom start omega q)
        n horizon center ⟨n + 1, by omega⟩ ≤ n ^ 3)
    (hnonempty : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon ≠ [])
    (hstart : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).head? =
        some ⟨1, by omega⟩)
    (hadjacent : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).IsChain
        (fun left right ↦ Nat.dist left.val right.val = 1))
    (hbefore : ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0)
    (hend : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).getLast? =
        some ⟨0, by omega⟩) :
    omega ∈ exactFixedProfileRadialWordFamilyAtom
      n delta center start m := by
  let labels := chronologicalRadialLabels n center
    (fun q ↦ trajectoryFrom start omega q) horizon
  let word := radialLabelWordOfList labels hnonempty hstart hadjacent hbefore hend
  have htrace : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon = word.toList := by
    exact (radialLabelWordOfList_toList
      labels hnonempty hstart hadjacent hbefore hend).symm
  have hinternal : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i := by
    intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k, scaleIndex]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k, scaleIndex])
    exact hup.symm.trans (hcompleted.trans (hinternalProfile i))
  have hterminalCount :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ =
        excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨n + 1, by omega⟩ := by
    let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by simp [k]) k.2 center _ word htrace
    have hup := radialWordCompletedCount_eq_radialUpcrossingCount word k
      (by simp [k]; omega)
    exact hup.symm.trans hcompleted
  have hterminalLower' : terminalLower n delta ≤
      (radialUpcrossingCount word ⟨n + 1, by omega⟩ : ℝ) := by
    rw [hterminalCount]
    exact hterminalLower
  have hterminalUpper' :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
    rw [hterminalCount]
    exact hterminalUpper
  have hbound : labels.length - 1 ≤
      exactProfileRadialWordMaxTransitions m := by
    exact
      radialLabelWord_transitionLength_le_exactProfileRadialWordMaxTransitions
        hn word hinternal hterminalUpper'
  let bounded : BoundedRadialLabelWord n
      (exactProfileRadialWordMaxTransitions m) :=
    ⟨⟨labels.length - 1, by omega⟩, word⟩
  have hboundedFixed : IsFixedProfileRadialWordWithCutoff n
      (exactProfileRadialWordMaxTransitions m) delta m bounded := by
    exact ⟨hinternal, hterminalLower', hterminalUpper'⟩
  apply (mem_radialLabelWordFamilyAtom_iff n
    (exactProfileRadialWordMaxTransitions m) center start
      (IsFixedProfileRadialWordWithCutoff n
        (exactProfileRadialWordMaxTransitions m) delta m) omega).2
  refine ⟨bounded, hboundedFixed, ?_⟩
  apply (mem_radialLabelWordAtom_iff n bounded.1 center start bounded.2 omega).2
  exact ⟨horizon, hfirst, htrace⟩

end

end Erdos1165.AnnularFixedProfileTraceParser
