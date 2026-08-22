/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZHighSpatialTransitionFactor
import ErdosProblems.Erdos1165.TilingDistinguishedTraceInvariant

/-!
# Stopped observability of filtered high-transition pasts

The rank-two and rank-three high-spatial factors condition at a fixed old
creation time.  This module proves that the fixed pair/triple creation atoms
are observable at that time.  It derives the low-gap and lazy-cap parts of
the filters from deterministic-prefix invariance, leaving only the literal
fixed-atom intersection with each staged candidate as an input.  No
transition measure estimate or event-probability premise occurs here.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZFilteredPastObservability

open HLOZFilteredTransitionAssembly HLOZGapPointReturn HLOZPathEvents
open HLOZHighSpatialTransitionFactor HLOZSourceCorrectFilteredTransitions
open HLOZSpatialAdapter StoppedInsertion
open HLOZTilingGapRandomClockScreen
open TilingDistinguishedTraceInvariant TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-! ## Deterministic-prefix measurability -/

/-- A path predicate determined by the physical trajectory through time `n`
is measurable in the first-`n` increment filtration. -/
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

/-- A fixed pair-creation configuration depends only on the trajectory
prefix through its second creation time. -/
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

/-- The fixed pair atom is observable at its second creation clock. -/
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

/-- A fixed triple-creation configuration depends only on the trajectory
prefix through its third creation time. -/
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

/-- The fixed triple atom is observable at its third creation clock. -/
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
        have hlt : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
          (by omega) homega.1 homega.2.1
        have hlt' : z.1.1 < z.2 := hlt.trans (creation_time_lt
          (by omega) (by omega) (by omega) homega.2.1 homega.2.2.1)
        exact (hz₁ hlt'.le).elim
      · exact False.elim
    rw [hempty]
    apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact (incrementFiltration z.2).measurableSet_empty

/-! ## Fixed-atom predicate adapters -/

/-- A predicate which is prefix-invariant on one fixed pair atom gives a
stopped-past observable intersection.  No behavior is required away from
the atom, where the predicate may involve later creations. -/
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

/-- Triple-atom version of `pairCreationAtom_inter_observable_of_prefix`. -/
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
        exact ⟨hsTriple',
          (hevent s s' hp hsTriple hsTriple').mp hsEvent⟩
      · rintro ⟨hsTriple', hsEvent'⟩
        have hsTriple := htriple.mpr hsTriple'
        exact ⟨hsTriple,
          (hevent s s' hp hsTriple hsTriple').mpr hsEvent'⟩
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

/-! ## Structural bad histories on fixed creation atoms -/

/-- Equality of a later path prefix implies equality of every earlier path
prefix. -/
theorem pathPrefix_eq_of_pathPrefix_eq_of_le
    {s s' : WalkPath} {N n : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) (hn : n ≤ N) :
    pathPrefix s n = pathPrefix s' n := by
  funext i
  exact walkPoint_eq_of_pathPrefix_eq hp
    ((Nat.lt_succ_iff.mp i.isLt).trans hn)

/-- A low-gap failure at fixed creation times is determined by the path
through the later creation. -/
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

/-- The tiling lazy-overflow predicate at a deterministic prefix is invariant
under equality of that prefix. -/
theorem tilingLazyOverflowAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    {s s' : WalkPath} {n cap : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    TilingLazyOverflowAt t o n cap s ↔
      TilingLazyOverflowAt t o n cap s' := by
  unfold TilingLazyOverflowAt pathPhasedBoundaryLocalTime
    pathPhasedLazyLocalTime
  rw [hp]

/-- On a fixed creation atom, stopped lazy overflow is exactly overflow at
the displayed creation time. -/
theorem mem_tilingStoppedLazyOverflowEvent_iff_of_creation
    {t : DominoTiling} {o : LazyDecomposition.Orientation}
    {s : WalkPath} {m rank n cap : ℕ}
    (hcreation : ThresholdCreation s m rank n) :
    s ∈ tilingStoppedLazyOverflowEvent t o m rank cap ↔
      TilingLazyOverflowAt t o n cap s := by
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨q, hqCreation, hqOverflow⟩
    have hqn := thresholdCreation_time_unique hqCreation hcreation
    subst q
    exact hqOverflow
  · intro hs
    exact Set.mem_iUnion.mpr ⟨n, hcreation, hs⟩

/-- The pair atom supplies its exact pair configuration. -/
theorem pairCreationAtom_mem_pairConfiguration
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    {z : PairCreationIndex} {s : WalkPath}
    (hs : s ∈ pairCreationAtom t m a z) :
    s ∈ pairConfiguration t m a.1.1 z.1 z.2 := hs

/-- The triple atom supplies the earlier pair configuration, including the
absence of level `m+1` sites at its second creation time. -/
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

/-- On a fixed pair atom, the global rank-one low-gap family reduces to the
displayed creation pair. -/
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

/-- Triple-atom version of the preceding rank-one reduction. -/
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
    exact Set.mem_iUnion.mpr ⟨z.1.1, Set.mem_iUnion.mpr
      ⟨z.1.2, hpair, hlocal⟩⟩

/-- On a fixed triple atom, the global rank-two low-gap family reduces to
the second and third creation times. -/
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
    have hq₂eq : q₂ = z.1.2 :=
      thresholdCreation_time_unique hq.2.1 hs.2.1
    have hq₃eq : q₃ = z.2 :=
      thresholdCreation_time_unique hq.2.2.1 hs.2.2.1
    subst q₂
    subst q₃
    exact hlocal
  · intro hlocal
    exact Set.mem_iUnion.mpr ⟨z.1.1, Set.mem_iUnion.mpr ⟨z.1.2,
      Set.mem_iUnion.mpr ⟨z.2, hs, hlocal⟩⟩⟩

/-- Union closure for stopped-past observable events. -/
theorem isMeasurableAtStopping_union
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A B : Set StepPath}
    (hA : IsMeasurableAtStopping τ A)
    (hB : IsMeasurableAtStopping τ B) :
    IsMeasurableAtStopping τ (A ∪ B) := by
  rw [show A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ by
    ext omega
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto]
  exact isMeasurableAtStopping_compl hτ
    (isMeasurableAtStopping_inter
      (isMeasurableAtStopping_compl hτ hA)
      (isMeasurableAtStopping_compl hτ hB))

/-- The low-gap and lazy-cap parts of the rank-one filter are observable on
a fixed pair atom. -/
theorem pairCreationAtom_firstStructuralBad_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        (firstLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 1))) := by
  apply pairCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz : z.1 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1).le
  have hlow : s ∈ firstLowGapFailureEvent t m a ↔
      s' ∈ firstLowGapFailureEvent t m a :=
    (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs).trans
      ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz le_rfl).trans
        (mem_firstLowGapFailureEvent_iff_of_pairCreationAtom hs').symm)
  have hp₁ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz
  have heven : s ∈ tilingStoppedLazyOverflowEvent t .even m 1 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .even m 1 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₁).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.1).symm)
  have hshifted :
      s ∈ tilingStoppedLazyOverflowEvent t .shifted m 1 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .shifted m 1 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₁).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.1).symm)
  simp only [rankLazyCapFailureEvent, Set.mem_union, hlow, heven, hshifted]

/-- Rank-one structural filter on a fixed triple atom. -/
theorem tripleCreationAtom_firstStructuralBad_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        (firstLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 1))) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₁₂ : z.1.1 < z.1.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.1 hs.2.1
  have hz₂₃ : z.1.2 < z.2 := creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1
  have hz₁ : z.1.1 ≤ z.2 := (hz₁₂.trans hz₂₃).le
  have hz₂ : z.1.2 ≤ z.2 := hz₂₃.le
  have hlow : s ∈ firstLowGapFailureEvent t m a ↔
      s' ∈ firstLowGapFailureEvent t m a :=
    (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
      ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz₁ hz₂).trans
        (mem_firstLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)
  have hp₁ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz₁
  have heven : s ∈ tilingStoppedLazyOverflowEvent t .even m 1 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .even m 1 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₁).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.1).symm)
  have hshifted :
      s ∈ tilingStoppedLazyOverflowEvent t .shifted m 1 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .shifted m 1 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₁).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.1).symm)
  simp only [rankLazyCapFailureEvent, Set.mem_union, hlow, heven, hshifted]

/-- Rank-two structural filter on a fixed triple atom. -/
theorem tripleCreationAtom_secondStructuralBad_observable
    (cap : ℕ → ℕ) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        (secondLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 2))) := by
  apply tripleCreationAtom_inter_observable_of_prefix
  intro s s' hp hs hs'
  have hz₂ : z.1.2 ≤ z.2 := (creation_time_lt (by omega) (by omega)
    (by omega) hs.2.1 hs.2.2.1).le
  have hlow : s ∈ secondLowGapFailureEvent t m a ↔
      s' ∈ secondLowGapFailureEvent t m a :=
    (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs).trans
      ((lowGapDeficitFailure_iff_of_pathPrefix_eq hp hz₂ le_rfl).trans
        (mem_secondLowGapFailureEvent_iff_of_tripleCreationAtom hs').symm)
  have hp₂ := pathPrefix_eq_of_pathPrefix_eq_of_le hp hz₂
  have heven : s ∈ tilingStoppedLazyOverflowEvent t .even m 2 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .even m 2 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.2.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .even hp₂).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.2.1).symm)
  have hshifted :
      s ∈ tilingStoppedLazyOverflowEvent t .shifted m 2 (cap m) ↔
      s' ∈ tilingStoppedLazyOverflowEvent t .shifted m 2 (cap m) :=
    (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs.2.1).trans
      ((tilingLazyOverflowAt_iff_of_pathPrefix_eq t .shifted hp₂).trans
        (mem_tilingStoppedLazyOverflowEvent_iff_of_creation hs'.2.1).symm)
  simp only [rankLazyCapFailureEvent, Set.mem_union, hlow, heven, hshifted]

/-! ## Filtered past adapters -/

/-- On a fixed pair atom, the filtered rank-one past is exactly the pair
atom with the rank-one bad-history filter removed. -/
theorem filteredFirstPairCreationAtom_eq_pair_diff_bad
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) :
    filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z =
      pairCreationAtom t m a z \
        firstFactorBadHistory cap stagedCandidate₁ t m a := by
  ext s
  constructor
  · rintro ⟨hfiltered, hpair⟩
    exact ⟨hpair, hfiltered.2⟩
  · rintro ⟨hpair, hgood⟩
    refine ⟨⟨?_, hgood⟩, hpair⟩
    rw [firstTransitionEvent]
    exact Set.mem_iUnion.mpr ⟨z.1,
      Set.mem_iUnion.mpr ⟨z.2, hpair⟩⟩

/-- On a fixed triple atom, the filtered rank-two past is exactly the triple
atom with the first two bad-history filters removed. -/
theorem filteredSecondTripleCreationAtom_eq_triple_diff_bad
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) :
    filteredSecondTripleCreationAtom cap stagedCandidate₁ stagedCandidate₂
        t m a z =
      tripleCreationAtom t m a z \
        (firstFactorBadHistory cap stagedCandidate₁ t m a ∪
          secondFactorBadHistory cap stagedCandidate₂ t m a) := by
  ext s
  constructor
  · rintro ⟨hfiltered, htriple⟩
    exact ⟨htriple, hfiltered.2⟩
  · rintro ⟨htriple, hgood⟩
    refine ⟨⟨?_, hgood⟩, htriple⟩
    rw [secondTransitionEvent]
    exact Set.mem_iUnion.mpr ⟨z.1.1,
      Set.mem_iUnion.mpr ⟨z.1.2,
        Set.mem_iUnion.mpr ⟨z.2, htriple⟩⟩⟩

/-- Derive the exact rank-two high-factor past observability.  Low-gap and
lazy-cap histories are handled internally; the only input is observability
of the actual staged candidate on this fixed pair atom. -/
theorem filteredFirstPairCreationAtom_observable
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex)
    (hcandidate : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        stagedCandidate₁ t m a))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹'
        filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z) := by
  have hbad : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstFactorBadHistory cap stagedCandidate₁ t m a)) := by
    rw [show trajectory ⁻¹' (pairCreationAtom t m a z ∩
        firstFactorBadHistory cap stagedCandidate₁ t m a) =
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        (firstLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 1))) ∪
      (trajectory ⁻¹' (pairCreationAtom t m a z ∩
        stagedCandidate₁ t m a)) by
      ext omega
      simp only [firstFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (pairCreationAtom_firstStructuralBad_observable cap t m a z)
      hcandidate
  rw [filteredFirstPairCreationAtom_eq_pair_diff_bad]
  rw [show trajectory ⁻¹' (pairCreationAtom t m a z \
      firstFactorBadHistory cap stagedCandidate₁ t m a) =
      (trajectory ⁻¹' pairCreationAtom t m a z) ∩
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          firstFactorBadHistory cap stagedCandidate₁ t m a))ᶜ by
    ext omega
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_compl_iff]
    tauto]
  exact isMeasurableAtStopping_inter
    (pairCreationAtom_observable_at_second t m a z)
    (isMeasurableAtStopping_compl (isFiniteStoppingTime_const z.2) hbad)

/-- Rank-three adapter.  Again only the two staged candidate intersections
remain as inputs; both structural filters are derived internally. -/
theorem filteredSecondTripleCreationAtom_observable
    (cap : ℕ → ℕ)
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
      (trajectory ⁻¹' filteredSecondTripleCreationAtom cap
        stagedCandidate₁ stagedCandidate₂ t m a z) := by
  classical
  have hbad₁ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstFactorBadHistory cap stagedCandidate₁ t m a)) := by
    rw [show trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        firstFactorBadHistory cap stagedCandidate₁ t m a) =
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        (firstLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 1))) ∪
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₁ t m a)) by
      ext omega
      simp only [firstFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (tripleCreationAtom_firstStructuralBad_observable cap t m a z)
      hcandidate₁
  have hbad₂ : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondFactorBadHistory cap stagedCandidate₂ t m a)) := by
    rw [show trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        secondFactorBadHistory cap stagedCandidate₂ t m a) =
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        (secondLowGapFailureEvent t m a ∪
          rankLazyCapFailureEvent t m (cap m) 2))) ∪
      (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
        stagedCandidate₂ t m a)) by
      ext omega
      simp only [secondFactorBadHistory, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_union]
      tauto]
    exact isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2)
      (tripleCreationAtom_secondStructuralBad_observable cap t m a z)
      hcandidate₂
  rw [filteredSecondTripleCreationAtom_eq_triple_diff_bad]
  rw [show trajectory ⁻¹' (tripleCreationAtom t m a z \
      (firstFactorBadHistory cap stagedCandidate₁ t m a ∪
        secondFactorBadHistory cap stagedCandidate₂ t m a)) =
      (trajectory ⁻¹' tripleCreationAtom t m a z) ∩
        ((trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          firstFactorBadHistory cap stagedCandidate₁ t m a)) ∪
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          secondFactorBadHistory cap stagedCandidate₂ t m a)))ᶜ by
    ext omega
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_compl_iff]
    tauto]
  have hunion : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      ((trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          firstFactorBadHistory cap stagedCandidate₁ t m a)) ∪
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          secondFactorBadHistory cap stagedCandidate₂ t m a))) :=
    isMeasurableAtStopping_union (isFiniteStoppingTime_const z.2) hbad₁ hbad₂
  exact isMeasurableAtStopping_inter
    (tripleCreationAtom_observable_at_third t m a z)
    (isMeasurableAtStopping_compl (isFiniteStoppingTime_const z.2) hunion)

end

end Erdos1165.HLOZFilteredPastObservability
