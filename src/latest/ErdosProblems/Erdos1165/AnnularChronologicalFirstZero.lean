/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord

/-!
# The first level-zero label is final in the chronological scan

A literal first-hit certificate at radial level zero implies that the raw
observed-label list contains level zero exactly once, at its last position.
Consecutive-repeat compression preserves the last label and never increases
the multiplicity of any label.  Hence level zero cannot occur before the
last entry of the compressed chronological list.
-/

namespace Erdos1165.AnnularChronologicalFirstZero

open AnnularRadialLabelWord PlanarPotential TerminalSequentialVisitLaw

noncomputable section

private theorem getLast?_cons_compressLabelsFrom
    {Label : Type*} [DecidableEq Label] :
    ∀ (previous : Label) (labels : List Label),
      (previous :: compressLabelsFrom (some previous) labels).getLast? =
        (previous :: labels).getLast?
  | previous, [] => by rfl
  | previous, label :: tail => by
      by_cases heq : some previous = some label
      · have hvalue : previous = label := Option.some.inj heq
        subst label
        simpa [compressLabelsFrom] using
          getLast?_cons_compressLabelsFrom previous tail
      · simpa [compressLabelsFrom, heq] using
          getLast?_cons_compressLabelsFrom label tail

private theorem getLast?_compressLabels
    {Label : Type*} [DecidableEq Label] (labels : List Label) :
    (compressLabels labels).getLast? = labels.getLast? := by
  cases labels with
  | nil => rfl
  | cons head tail =>
      simpa [compressLabels, compressLabelsFrom] using
        getLast?_cons_compressLabelsFrom head tail

private theorem count_compressLabelsFrom_le
    {Label : Type*} [DecidableEq Label] (target : Label) :
    ∀ (previous : Option Label) (labels : List Label),
      (compressLabelsFrom previous labels).count target ≤ labels.count target
  | _, [] => by simp [compressLabelsFrom]
  | previous, label :: tail => by
      by_cases heq : previous = some label
      · rw [compressLabelsFrom, if_pos heq]
        have ih := count_compressLabelsFrom_le target previous tail
        simp only [List.count_cons]
        split <;> omega
      · rw [compressLabelsFrom, if_neg heq]
        have ih := count_compressLabelsFrom_le target (some label) tail
        simp only [List.count_cons]
        split <;> omega

private theorem count_compressLabels_le
    {Label : Type*} [DecidableEq Label]
    (target : Label) (labels : List Label) :
    (compressLabels labels).count target ≤ labels.count target := by
  exact count_compressLabelsFrom_le target none labels

/-- Under a literal first level-zero hit, every indexed chronological label
strictly before the final label is nonzero. -/
theorem chronologicalRadialLabels_beforeFinal_ne_zero_of_firstZero
    {n horizon : ℕ} (hn : 2 ≤ n) (center start : Point)
    (omega : StepPath)
    (hfirst : AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon) :
    ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0 := by
  let zero : Fin (n + 2) := ⟨0, by omega⟩
  let s : WalkPath := fun q ↦ trajectoryFrom start omega q
  let raw := observedRadialLabels n center s horizon
  let labels := chronologicalRadialLabels n center s horizon
  have hfinalLabels : radialLabelsAt n center (s horizon) = [zero] := by
    apply radialLabelsAt_eq_singleton_of_mem hn
    exact hfirst.1
  let observedPrefix := (List.range horizon).flatMap
    (fun t ↦ radialLabelsAt n center (s t))
  have hzeroNotPrefix : zero ∉ observedPrefix := by
    intro hmem
    simp only [observedPrefix, List.mem_flatMap, List.mem_range] at hmem
    obtain ⟨t, ht, hzero⟩ := hmem
    exact hfirst.2 t ht (mem_radialLabelsAt.mp hzero)
  have hraw : raw = observedPrefix ++ [zero] := by
    unfold raw observedRadialLabels
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_singleton, hfinalLabels, observedPrefix]
  have hrawCount : raw.count zero = 1 := by
    rw [hraw, List.count_append]
    rw [List.count_eq_zero_of_not_mem hzeroNotPrefix]
    simp
  have hlabelsDef : labels = compressLabels raw := by
    rfl
  have hcount : labels.count zero ≤ 1 := by
    rw [hlabelsDef]
    exact (count_compressLabels_le zero raw).trans_eq hrawCount
  have hlastOption : labels.getLast? = some zero := by
    rw [hlabelsDef, getLast?_compressLabels, hraw]
    simp
  intro i hi hiLast hzeroVal
  change i < labels.length at hi
  change i + 1 < labels.length at hiLast
  change (labels[i]'hi : ℕ) = 0 at hzeroVal
  have hlabelsNe : labels ≠ [] := by
    intro hnil
    rw [hnil] at hi
    simp at hi
  have hlast : labels.getLast hlabelsNe = zero := by
    exact Option.some.inj ((List.getLast?_eq_some_getLast hlabelsNe).symm.trans
      hlastOption)
  have hiDrop : i < labels.dropLast.length := by
    rw [List.length_dropLast]
    omega
  have hzeroElem : labels[i] = zero := by
    apply Fin.ext
    simpa [zero] using hzeroVal
  have hzeroDrop : zero ∈ labels.dropLast := by
    have hget : labels.dropLast[i] = zero := by
      rw [List.getElem_dropLast hiDrop]
      exact hzeroElem
    rw [← hget]
    exact List.getElem_mem hiDrop
  have hcountDrop : 0 < labels.dropLast.count zero :=
    List.count_pos_iff.mpr hzeroDrop
  have hdecompose := List.dropLast_append_getLast hlabelsNe
  have hcountExact : labels.count zero = labels.dropLast.count zero + 1 := by
    conv_lhs => rw [← hdecompose]
    simp [hlast]
  omega

end

end Erdos1165.AnnularChronologicalFirstZero
