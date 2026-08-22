/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyFilteredTransitions
import ErdosProblems.Erdos1165.HLOZGapFixedPair
import ErdosProblems.Erdos1165.HLOZSpatialAdapter
import ErdosProblems.Erdos1165.TilingDistinguishedTraceInvariant

/-!
# Stopped observability for the candidate-local filtered past

This module contains the fixed pair/triple creation-prefix machinery needed
by the atomwise high and low factors.  It derives observability of the
no-lazy filtered past from observability of only the staged candidate on the
same fixed atom.  No lazy predicate or legacy lazy-filtered transition module
is imported.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZNoLazyFilteredPastObservability

open HLOZFilteredTransitionAssembly HLOZGapPointReturn HLOZPathEvents
open HLOZNoLazyFilteredTransitions HLOZSpatialAdapter StoppedInsertion
open TilingDistinguishedTraceInvariant

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## Fixed creation atoms -/

/-- A path predicate determined through time `n` is measurable in the
first-`n` increment filtration. -/
theorem measurableSet_incrementFiltration_of_pathPrefix_dependent
    (n : ℕ) (P : WalkPath → Prop)
    (hP : ∀ s s' : WalkPath, pathPrefix s n = pathPrefix s' n →
      (P s ↔ P s')) :
    MeasurableSet[incrementFiltration n]
      {omega : StepPath | P (trajectory omega)} := by
  rw [incrementFiltration_apply]
  let A : Set (Fin n → Direction) :=
    {u | P (trajectory (StoppedInsertion.extendPrefix u))}
  refine ⟨A, (Set.to_countable A).measurableSet, ?_⟩
  ext omega
  change P (trajectory (StoppedInsertion.extendPrefix (stepPrefix n omega))) ↔
    P (trajectory omega)
  apply hP
  rw [← trajectoryPrefix_stepPrefix omega n,
    ← trajectoryPrefix_stepPrefix
      (StoppedInsertion.extendPrefix (stepPrefix n omega)) n,
    PreStoppingFiber.stepPrefix_extendPrefix]

theorem pairCreationAtom_iff_of_pathPrefix_eq
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) (hz : z.1 ≤ z.2)
    {s s' : WalkPath} (hp : pathPrefix s z.2 = pathPrefix s' z.2) :
    s ∈ pairCreationAtom t m a z ↔ s' ∈ pairCreationAtom t m a z := by
  have hcreation₁ := thresholdCreation_iff_of_pathPrefix_eq
    (N := z.2) (n := z.1) (m := m) (rank := 1) hp hz
  have hcreation₂ := thresholdCreation_iff_of_pathPrefix_eq
    (N := z.2) (n := z.2) (m := m) (rank := 2) hp le_rfl
  have hcount := thresholdCount_eq_of_pathPrefix_eq
    (N := z.2) (n := z.2) (m := m + 1) hp le_rfl
  have hpoint₁ := walkPoint_eq_of_pathPrefix_eq hp hz
  have hpoint₂ := walkPoint_eq_of_pathPrefix_eq hp le_rfl
  change
    (ThresholdCreation s m 1 z.1 ∧ ThresholdCreation s m 2 z.2 ∧
      thresholdCount s z.2 (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (s z.1) (s z.2) ∧
      gapScaleOf m (s z.1) (s z.2) = a.1.1) ↔
    (ThresholdCreation s' m 1 z.1 ∧ ThresholdCreation s' m 2 z.2 ∧
      thresholdCount s' z.2 (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (s' z.1) (s' z.2) ∧
      gapScaleOf m (s' z.1) (s' z.2) = a.1.1)
  simp only [hcreation₁, hcreation₂, hcount, hpoint₁, hpoint₂]

theorem pairCreationAtom_observable_at_second
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' pairCreationAtom t m a z) := by
  by_cases hz : z.1 ≤ z.2
  · apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact measurableSet_incrementFiltration_of_pathPrefix_dependent z.2
      (fun s ↦ s ∈ pairCreationAtom t m a z)
      (fun s s' hp ↦ pairCreationAtom_iff_of_pathPrefix_eq
        t m a z hz hp)
  · have hempty : trajectory ⁻¹' pairCreationAtom t m a z = ∅ := by
      ext omega
      constructor
      · intro homega
        have hlt : z.1 < z.2 := creation_time_lt (by omega) (by omega)
          (by omega) homega.1 homega.2.1
        exact (hz hlt.le).elim
      · exact False.elim
    rw [hempty]
    apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact (incrementFiltration z.2).measurableSet_empty

theorem tripleCreationAtom_iff_of_pathPrefix_eq
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) (hz₁ : z.1.1 ≤ z.2) (hz₂ : z.1.2 ≤ z.2)
    {s s' : WalkPath} (hp : pathPrefix s z.2 = pathPrefix s' z.2) :
    s ∈ tripleCreationAtom t m a z ↔ s' ∈ tripleCreationAtom t m a z := by
  have hcreation₁ := thresholdCreation_iff_of_pathPrefix_eq
    (N := z.2) (n := z.1.1) (m := m) (rank := 1) hp hz₁
  have hcreation₂ := thresholdCreation_iff_of_pathPrefix_eq
    (N := z.2) (n := z.1.2) (m := m) (rank := 2) hp hz₂
  have hcreation₃ := thresholdCreation_iff_of_pathPrefix_eq
    (N := z.2) (n := z.2) (m := m) (rank := 3) hp le_rfl
  have hcount := thresholdCount_eq_of_pathPrefix_eq
    (N := z.2) (n := z.2) (m := m + 1) hp le_rfl
  have hpoint₁ := walkPoint_eq_of_pathPrefix_eq hp hz₁
  have hpoint₂ := walkPoint_eq_of_pathPrefix_eq hp hz₂
  have hpoint₃ := walkPoint_eq_of_pathPrefix_eq hp le_rfl
  change
    (ThresholdCreation s m 1 z.1.1 ∧
      ThresholdCreation s m 2 z.1.2 ∧
      ThresholdCreation s m 3 z.2 ∧
      thresholdCount s z.2 (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (s z.1.1) (s z.1.2) ∧
      ¬Tilings.sameDomino t (s z.1.1) (s z.2) ∧
      ¬Tilings.sameDomino t (s z.1.2) (s z.2) ∧
      gapScaleOf m (s z.1.1) (s z.1.2) = a.1.1 ∧
      gapScaleOf m (s z.1.2) (s z.2) = a.1.2) ↔
    (ThresholdCreation s' m 1 z.1.1 ∧
      ThresholdCreation s' m 2 z.1.2 ∧
      ThresholdCreation s' m 3 z.2 ∧
      thresholdCount s' z.2 (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (s' z.1.1) (s' z.1.2) ∧
      ¬Tilings.sameDomino t (s' z.1.1) (s' z.2) ∧
      ¬Tilings.sameDomino t (s' z.1.2) (s' z.2) ∧
      gapScaleOf m (s' z.1.1) (s' z.1.2) = a.1.1 ∧
      gapScaleOf m (s' z.1.2) (s' z.2) = a.1.2)
  simp only [hcreation₁, hcreation₂, hcreation₃, hcount,
    hpoint₁, hpoint₂, hpoint₃]

theorem tripleCreationAtom_observable_at_third
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' tripleCreationAtom t m a z) := by
  by_cases hz₁ : z.1.1 ≤ z.2
  · by_cases hz₂ : z.1.2 ≤ z.2
    · apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
      exact measurableSet_incrementFiltration_of_pathPrefix_dependent z.2
        (fun s ↦ s ∈ tripleCreationAtom t m a z)
        (fun s s' hp ↦ tripleCreationAtom_iff_of_pathPrefix_eq
          t m a z hz₁ hz₂ hp)
    · have hempty : trajectory ⁻¹' tripleCreationAtom t m a z = ∅ := by
        ext omega
        constructor
        · intro homega
          have hlt : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
            (by omega) homega.2.1 homega.2.2.1
          exact (hz₂ hlt.le).elim
        · exact False.elim
      rw [hempty]
      apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
      exact (incrementFiltration z.2).measurableSet_empty
  · have hempty : trajectory ⁻¹' tripleCreationAtom t m a z = ∅ := by
      ext omega
      constructor
      · intro homega
        have hlt₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
          (by omega) homega.1 homega.2.1
        have hlt₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
          (by omega) homega.2.1 homega.2.2.1
        exact (hz₁ (hlt₁₂.trans hlt₂₃).le).elim
      · exact False.elim
    rw [hempty]
    apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact (incrementFiltration z.2).measurableSet_empty

/-! ## Prefix-dependent predicates on fixed atoms -/

theorem pairCreationAtom_inter_observable_of_prefix
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) (event : Set WalkPath)
    (hevent : ∀ s s' : WalkPath,
      pathPrefix s z.2 = pathPrefix s' z.2 →
      s ∈ pairCreationAtom t m a z →
      s' ∈ pairCreationAtom t m a z →
      (s ∈ event ↔ s' ∈ event)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩ event)) := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_pathPrefix_dependent z.2
    (fun s ↦ s ∈ pairCreationAtom t m a z ∩ event)
  intro s s' hp
  by_cases hz : z.1 ≤ z.2
  · have hpair := pairCreationAtom_iff_of_pathPrefix_eq t m a z hz hp
    constructor
    · rintro ⟨hsPair, hsEvent⟩
      have hsPair' := hpair.mp hsPair
      exact ⟨hsPair', (hevent s s' hp hsPair hsPair').mp hsEvent⟩
    · rintro ⟨hsPair', hsEvent'⟩
      have hsPair := hpair.mpr hsPair'
      exact ⟨hsPair, (hevent s s' hp hsPair hsPair').mpr hsEvent'⟩
  · have hempty : ∀ u : WalkPath,
        u ∉ pairCreationAtom t m a z := by
      intro u hu
      have hlt : z.1 < z.2 := creation_time_lt (by omega) (by omega)
        (by omega) hu.1 hu.2.1
      exact hz hlt.le
    simp only [Set.mem_inter_iff, hempty, false_and]

theorem tripleCreationAtom_inter_observable_of_prefix
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) (event : Set WalkPath)
    (hevent : ∀ s s' : WalkPath,
      pathPrefix s z.2 = pathPrefix s' z.2 →
      s ∈ tripleCreationAtom t m a z →
      s' ∈ tripleCreationAtom t m a z →
      (s ∈ event ↔ s' ∈ event)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩ event)) := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_pathPrefix_dependent z.2
    (fun s ↦ s ∈ tripleCreationAtom t m a z ∩ event)
  intro s s' hp
  by_cases hz₁ : z.1.1 ≤ z.2
  · by_cases hz₂ : z.1.2 ≤ z.2
    · have htriple := tripleCreationAtom_iff_of_pathPrefix_eq
        t m a z hz₁ hz₂ hp
      constructor
      · rintro ⟨hsTriple, hsEvent⟩
        have hsTriple' := htriple.mp hsTriple
        exact ⟨hsTriple', (hevent s s' hp hsTriple hsTriple').mp hsEvent⟩
      · rintro ⟨hsTriple', hsEvent'⟩
        have hsTriple := htriple.mpr hsTriple'
        exact ⟨hsTriple, (hevent s s' hp hsTriple hsTriple').mpr hsEvent'⟩
    · have hempty : ∀ u : WalkPath,
          u ∉ tripleCreationAtom t m a z := by
        intro u hu
        have hlt : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
          (by omega) hu.2.1 hu.2.2.1
        exact hz₂ hlt.le
      simp only [Set.mem_inter_iff, hempty, false_and]
  · have hempty : ∀ u : WalkPath,
        u ∉ tripleCreationAtom t m a z := by
      intro u hu
      have hlt₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
        (by omega) hu.1 hu.2.1
      have hlt₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
        (by omega) hu.2.1 hu.2.2.1
      exact hz₁ (hlt₁₂.trans hlt₂₃).le
    simp only [Set.mem_inter_iff, hempty, false_and]

theorem pathPrefix_eq_of_pathPrefix_eq_of_le
    {s s' : WalkPath} {N n : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) (hn : n ≤ N) :
    pathPrefix s n = pathPrefix s' n := by
  funext i
  exact walkPoint_eq_of_pathPrefix_eq hp
    ((Nat.lt_succ_iff.mp i.isLt).trans hn)

theorem lowGapDeficitFailure_iff_of_pathPrefix_eq
    {s s' : WalkPath} {N nOld nNew m : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N)
    (hOld : nOld ≤ N) (hNew : nNew ≤ N) :
    lowGapDeficitFailure s m nOld nNew ↔
      lowGapDeficitFailure s' m nOld nNew := by
  have hpOld := pathPrefix_eq_of_pathPrefix_eq_of_le hp hOld
  have hpointOld := walkPoint_eq_of_pathPrefix_eq hp hOld
  have hpointNew := walkPoint_eq_of_pathPrefix_eq hp hNew
  unfold lowGapDeficitFailure localTime
  rw [hpOld, hpointOld, hpointNew]

theorem pairCreationAtom_mem_pairConfiguration
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : PairCreationIndex} {s : WalkPath}
    (hs : s ∈ pairCreationAtom t m a z) :
    s ∈ pairConfiguration t m a.1.1 z.1 z.2 := hs

theorem tripleCreationAtom_mem_pairConfiguration
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : TripleCreationIndex} {s : WalkPath}
    (hs : s ∈ tripleCreationAtom t m a z) :
    s ∈ pairConfiguration t m a.1.1 z.1.1 z.1.2 := by
  have hsecond : s ∈ secondTransitionEvent t m a :=
    Set.mem_iUnion.mpr ⟨z.1.1, Set.mem_iUnion.mpr ⟨z.1.2,
      Set.mem_iUnion.mpr ⟨z.2, hs⟩⟩⟩
  have hfirst := secondTransitionEvent_subset_first t m a hsecond
  rcases Set.mem_iUnion.mp hfirst with ⟨q₁, hq₁⟩
  rcases Set.mem_iUnion.mp hq₁ with ⟨q₂, hq⟩
  have hq₁eq : q₁ = z.1.1 :=
    thresholdCreation_time_unique hq.1 hs.1
  have hq₂eq : q₂ = z.1.2 :=
    thresholdCreation_time_unique hq.2.1 hs.2.1
  simpa only [hq₁eq, hq₂eq] using hq

theorem mem_firstLowGapFailureEvent_iff_of_pairCreationAtom
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : PairCreationIndex} {s : WalkPath}
    (hs : s ∈ pairCreationAtom t m a z) :
    s ∈ firstLowGapFailureEvent t m a ↔
      lowGapDeficitFailure s m z.1 z.2 := by
  constructor
  · intro hfail
    rcases Set.mem_iUnion.mp hfail with ⟨q₁, hq₁⟩
    rcases Set.mem_iUnion.mp hq₁ with ⟨q₂, hq, hlocal⟩
    have hq₁eq : q₁ = z.1 := thresholdCreation_time_unique hq.1 hs.1
    have hq₂eq : q₂ = z.2 := thresholdCreation_time_unique hq.2.1 hs.2.1
    subst q₁
    subst q₂
    exact hlocal
  · intro hlocal
    exact Set.mem_iUnion.mpr ⟨z.1, Set.mem_iUnion.mpr
      ⟨z.2, pairCreationAtom_mem_pairConfiguration hs, hlocal⟩⟩

theorem mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : TripleCreationIndex} {s : WalkPath}
    (hs : s ∈ tripleCreationAtom t m a z) :
    s ∈ firstLowGapFailureEvent t m a ↔
      lowGapDeficitFailure s m z.1.1 z.1.2 := by
  have hpair := tripleCreationAtom_mem_pairConfiguration hs
  constructor
  · intro hfail
    rcases Set.mem_iUnion.mp hfail with ⟨q₁, hq₁⟩
    rcases Set.mem_iUnion.mp hq₁ with ⟨q₂, hq, hlocal⟩
    have hq₁eq : q₁ = z.1.1 := thresholdCreation_time_unique hq.1 hs.1
    have hq₂eq : q₂ = z.1.2 := thresholdCreation_time_unique hq.2.1 hs.2.1
    subst q₁
    subst q₂
    exact hlocal
  · intro hlocal
    exact Set.mem_iUnion.mpr ⟨z.1.1,
      Set.mem_iUnion.mpr ⟨z.1.2, hpair, hlocal⟩⟩

theorem mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : TripleCreationIndex} {s : WalkPath}
    (hs : s ∈ tripleCreationAtom t m a z) :
    s ∈ secondLowGapFailureEvent t m a ↔
      lowGapDeficitFailure s m z.1.2 z.2 := by
  constructor
  · intro hfail
    rcases Set.mem_iUnion.mp hfail with ⟨q₁, hq₁⟩
    rcases Set.mem_iUnion.mp hq₁ with ⟨q₂, hq₂⟩
    rcases Set.mem_iUnion.mp hq₂ with ⟨q₃, hq, hlocal⟩
    have hq₂eq : q₂ = z.1.2 := thresholdCreation_time_unique hq.2.1 hs.2.1
    have hq₃eq : q₃ = z.2 := thresholdCreation_time_unique hq.2.2.1 hs.2.2.1
    subst q₂
    subst q₃
    exact hlocal
  · intro hlocal
    exact Set.mem_iUnion.mpr ⟨z.1.1, Set.mem_iUnion.mpr ⟨z.1.2,
      Set.mem_iUnion.mpr ⟨z.2, hs, hlocal⟩⟩⟩

theorem isMeasurableAtStopping_union
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A B : Set StepPath}
    (hA : IsMeasurableAtStopping τ A)
    (hB : IsMeasurableAtStopping τ B) :
    IsMeasurableAtStopping τ (A ∪ B) := by
  rw [show A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ by ext omega; simp only
    [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]; tauto]
  exact isMeasurableAtStopping_compl hτ
    (isMeasurableAtStopping_inter
      (isMeasurableAtStopping_compl hτ hA)
      (isMeasurableAtStopping_compl hτ hB))

theorem pairCreationAtom_firstLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) := by
  apply pairCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1).le
  exact (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz le_rfl).trans
      (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs').symm)

theorem tripleCreationAtom_firstLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1
  have hz₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1
  exact (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp
      (hz₁₂.trans hz₂₃).le hz₂₃.le).trans
        (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)

theorem tripleCreationAtom_secondLowGapFailure_observable
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondLowGapFailureEvent t m a)) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1.2 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1).le
  exact (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
    ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz le_rfl).trans
      (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)

/-! ## No-lazy filtered-past adapters -/

/-- The rank-two high/low factor past is observable from only the staged
candidate intersection on the fixed pair atom. -/
theorem pairCreationAtom_inter_filteredFirstTransitionEvent_observable
    (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex)
    (hcandidate : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        stagedCandidate₁ t m a))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        filteredFirstTransitionEvent stagedCandidate₁ t m a)) := by
  have hbad : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstFactorBadHistory stagedCandidate₁ t m a)) := by
    rw [show trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstFactorBadHistory stagedCandidate₁ t m a) =
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) ∪
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        stagedCandidate₁ t m a)) by
      ext omega
      simp only [firstFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (pairCreationAtom_firstLowGapFailure_observable t m a z) hcandidate
  have heq : pairCreationAtom t m a z ∩
      filteredFirstTransitionEvent stagedCandidate₁ t m a =
      pairCreationAtom t m a z \ firstFactorBadHistory stagedCandidate₁ t m a := by
    ext s
    constructor
    · rintro ⟨hpair, hfiltered⟩
      exact ⟨hpair, hfiltered.2⟩
    · rintro ⟨hpair, hgood⟩
      exact ⟨hpair, ⟨Set.mem_iUnion.mpr ⟨z.1,
        Set.mem_iUnion.mpr ⟨z.2, hpair⟩⟩, hgood⟩⟩
  rw [heq]
  rw [show trajectory ⁻¹' (pairCreationAtom t m a z \
      firstFactorBadHistory stagedCandidate₁ t m a) =
      (trajectory ⁻¹' pairCreationAtom t m a z) ∩
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          firstFactorBadHistory stagedCandidate₁ t m a))ᶜ by
    ext omega
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_compl_iff]
    tauto]
  exact isMeasurableAtStopping_inter
    (pairCreationAtom_observable_at_second t m a z)
    (isMeasurableAtStopping_compl (isFiniteStoppingTime_const z.2) hbad)

/-- The same rank-two past in the intersection order used by the countable
high-factor atom. -/
theorem filteredFirstTransitionEvent_inter_pairCreationAtom_observable
    (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex)
    (hcandidate : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        stagedCandidate₁ t m a))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (filteredFirstTransitionEvent stagedCandidate₁
        t m a ∩ pairCreationAtom t m a z)) := by
  simpa only [inter_comm] using
    pairCreationAtom_inter_filteredFirstTransitionEvent_observable
      stagedCandidate₁ t m a z hcandidate

/-- Rank-three filtered past from the two exact staged-candidate atom
observability inputs. -/
theorem tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex)
    (hcandidate₁ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₁ t m a)))
    (hcandidate₂ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₂ t m a))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)) := by
  have hbad₁ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstFactorBadHistory stagedCandidate₁ t m a)) := by
    rw [show trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstFactorBadHistory stagedCandidate₁ t m a) =
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstLowGapFailureEvent t m a)) ∪
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₁ t m a)) by
      ext omega
      simp only [firstFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (tripleCreationAtom_firstLowGapFailure_observable t m a z) hcandidate₁
  have hbad₂ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondFactorBadHistory stagedCandidate₂ t m a)) := by
    rw [show trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondFactorBadHistory stagedCandidate₂ t m a) =
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondLowGapFailureEvent t m a)) ∪
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₂ t m a)) by
      ext omega
      simp only [secondFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (tripleCreationAtom_secondLowGapFailure_observable t m a z) hcandidate₂
  have heq : tripleCreationAtom t m a z ∩
      filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a =
      tripleCreationAtom t m a z \
        (firstFactorBadHistory stagedCandidate₁ t m a ∪
          secondFactorBadHistory stagedCandidate₂ t m a) := by
    ext s
    constructor
    · rintro ⟨htriple, hfiltered⟩
      exact ⟨htriple, hfiltered.2⟩
    · rintro ⟨htriple, hgood⟩
      exact ⟨htriple, ⟨Set.mem_iUnion.mpr ⟨z.1.1,
        Set.mem_iUnion.mpr ⟨z.1.2,
          Set.mem_iUnion.mpr ⟨z.2, htriple⟩⟩⟩, hgood⟩⟩
  rw [heq]
  rw [show trajectory ⁻¹' (tripleCreationAtom t m a z \
      (firstFactorBadHistory stagedCandidate₁ t m a ∪
        secondFactorBadHistory stagedCandidate₂ t m a)) =
      (trajectory ⁻¹' tripleCreationAtom t m a z) ∩
        ((trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          firstFactorBadHistory stagedCandidate₁ t m a)) ∪
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          secondFactorBadHistory stagedCandidate₂ t m a)))ᶜ by
    ext omega
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_compl_iff]
    tauto]
  have hunion : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      ((trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          firstFactorBadHistory stagedCandidate₁ t m a)) ∪
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          secondFactorBadHistory stagedCandidate₂ t m a))) :=
    isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2) hbad₁ hbad₂
  exact isMeasurableAtStopping_inter
    (tripleCreationAtom_observable_at_third t m a z)
    (isMeasurableAtStopping_compl (isFiniteStoppingTime_const z.2) hunion)

/-- Intersection-order adapter for the rank-three countable high factor. -/
theorem filteredSecondTransitionEvent_inter_tripleCreationAtom_observable
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex)
    (hcandidate₁ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₁ t m a)))
    (hcandidate₂ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₂ t m a))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (filteredSecondTransitionEvent stagedCandidate₁
        stagedCandidate₂ t m a ∩ tripleCreationAtom t m a z)) := by
  simpa only [inter_comm] using
    tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
      stagedCandidate₁ stagedCandidate₂ t m a z hcandidate₁ hcandidate₂

end

end Erdos1165.HLOZNoLazyFilteredPastObservability
