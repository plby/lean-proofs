/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.EssentialWaveLift
import ErdosProblems.Erdos599.HalfwaySchedulerConstruction

/-!
# The initial state and the geometric payload for the half-way scheduler

This file supplies two pieces of Section 9 bookkeeping which are independent
of Assertions 9.30--9.34.

* `singletonSeed` is the literal singleton blueprint on the designated
  sources.  If the reference warp is a source--stopover linkage, its
  untouched members cover every source omitted from the singleton family.
* `SeparatingHeightData` is the lossless fieldwise form of a separating
  half-way stopover together with its height witness.  It exposes exactly
  the stopover and quotient-wave fields later stored in a fair-resolution
  certificate.

The canonical stable seed uses the slice `source ∪ C`, the closing set
`univ`, and persistent set `A₀`.  These choices are only for the initial
state: later 9.31 steps may replace them by the actual ladder data through
the more general constructor proved below.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The literal singleton blueprint on a set of designated sources. -/
def singletonSeed (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa : Cardinal.{u}) (A0 : Set V) :
    LinkageBlueprint Gamma Y kappa where
  paths := (imaginaryWeb Gamma Y kappa).trivialPath '' A0
  isWarp := (imaginaryWeb Gamma Y kappa).isWarp_trivialPaths A0

@[simp] theorem singletonSeed_paths (A0 : Set V) :
    (singletonSeed Gamma Y kappa A0).paths =
      (imaginaryWeb Gamma Y kappa).trivialPath '' A0 :=
  rfl

@[simp] theorem singletonSeed_vertexSet (A0 : Set V) :
    (singletonSeed Gamma Y kappa A0).vertexSet = A0 := by
  exact (imaginaryWeb Gamma Y kappa).vertexSet_trivialPaths A0

@[simp] theorem singletonSeed_initialSet (A0 : Set V) :
    (singletonSeed Gamma Y kappa A0).initialSet = A0 := by
  exact (imaginaryWeb Gamma Y kappa).initialSet_trivialPaths A0

@[simp] theorem singletonSeed_terminalSet (A0 : Set V) :
    (singletonSeed Gamma Y kappa A0).terminalSet = A0 := by
  exact (imaginaryWeb Gamma Y kappa).terminalFrontier_trivialPaths A0

theorem singletonSeed_card_paths_le (A0 : Set V) :
    #(singletonSeed Gamma Y kappa A0).paths ≤ #A0 := by
  exact Cardinal.mk_image_le

/-- A source omitted from the singleton seed is retained by the reference
linkage.  Endpoint purity is what rules out an accidental meeting with a
different designated source. -/
theorem source_subset_singletonSeed_initial_union_retained
    {A0 C T : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hCT : C ⊆ T) :
    Gamma.source ⊆
      (singletonSeed Gamma Y kappa A0).initialSet ∪
        (singletonSeed Gamma Y kappa A0).retainedReferenceInitials T := by
  intro a ha
  by_cases ha0 : a ∈ A0
  · exact Or.inl (by simpa using ha0)
  · right
    obtain ⟨p, hpY, hpinitial⟩ := hY.initialSet_eq.symm ▸ ha
    have hpmeetT : (p.support ∩ T).Nonempty := by
      obtain ⟨q, rfl, _hpends, _hpsource⟩ := hY.endpointPure p hpY
      have hqC : q.finish ∈ C :=
        hY.terminalFrontier_subset ⟨Sum.inl q, hpY, rfl⟩
      exact ⟨q.finish, q.finish_mem_support, hCT hqC⟩
    have hpavoid : ¬ (p.support ∩
        (singletonSeed Gamma Y kappa A0).vertexSet).Nonempty := by
      rintro ⟨x, hxp, hxseed⟩
      have hxA0 : x ∈ A0 := by simpa using hxseed
      obtain ⟨q, hpq, _hpends, hpsource⟩ := hY.endpointPure p hpY
      subst p
      have hxsource : x ∈ Gamma.source := hA0 hxA0
      have hxstart : x = q.start := by
        have : x ∈ ({q.start} : Set V) := hpsource ▸ ⟨hxp, hxsource⟩
        exact Set.mem_singleton_iff.1 this
      have hstarta : q.start = a := hpinitial
      exact ha0 (hxstart.trans hstarta ▸ hxA0)
    have hpnotMeet : p ∉ referencePathsMeeting Y
        (singletonSeed Gamma Y kappa A0).vertexSet := by
      intro hp
      exact hpavoid hp.2
    exact ⟨p, ⟨⟨hpY, hpmeetT⟩, hpnotMeet⟩, hpinitial⟩

/-- Fieldwise construction of a singleton linkage blueprint.  This form is
useful when the surrounding ladder has already fixed `T`, `Z`, and the
persistent frontier. -/
theorem singletonSeed_isLinkageBlueprint
    {A0 C T Z persistent : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hCT : C ⊆ T)
    (hroof : A0 ⊆ Gamma.roof T) (hclosed : A0 ⊆ Z)
    (hcard : #A0 ≤ kappa)
    (hpopular : A0 ⊆ {u | IsPopular Gamma Y persistent kappa u} ∪ T) :
    (singletonSeed Gamma Y kappa A0).IsLinkageBlueprint T Z persistent := by
  refine
    { vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := ?_
      infinitely_many_strong := ?_
      terminals_popular := ?_ }
  · simpa using hroof
  · exact source_subset_singletonSeed_initial_union_retained
      (kappa := kappa) hY hA0 hCT
  · simpa using hclosed
  · exact (singletonSeed_card_paths_le (Gamma := Gamma) (Y := Y)
      (kappa := kappa) A0).trans hcard
  · intro r hr
    obtain ⟨a, ha, hrat⟩ := hr
    cases hrat
  · simpa using hpopular

/-- The exact stability premise for a singleton seed is just stability of
its set of singleton terminals. -/
theorem singletonSeed_stable_iff {A0 T persistent : Set V} :
    (singletonSeed Gamma Y kappa A0).Stable T persistent ↔
      A0 ∩ T ⊆ persistent := by
  change (singletonSeed Gamma Y kappa A0).terminalSet ∩ T ⊆ persistent ↔ _
  rw [singletonSeed_terminalSet]

/-- Bundle the singleton blueprint as a scheduler state. -/
def initialSingletonState
    {A0 C T Z persistent B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hCT : C ⊆ T)
    (hroof : A0 ⊆ Gamma.roof T) (hclosed : A0 ⊆ Z)
    (hcard : #A0 ≤ kappa)
    (hpopular : A0 ⊆ {u | IsPopular Gamma Y persistent kappa u} ∪ T)
    (hstable : A0 ∩ T ⊆ persistent) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  TerminalResolutionState.initial (singletonSeed Gamma Y kappa A0)
    (singletonSeed_isLinkageBlueprint hY hA0 hCT hroof hclosed hcard hpopular)
    (singletonSeed_stable_iff.2 hstable)

@[simp] theorem initialSingletonState_blueprint
    {A0 C T Z persistent B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hCT : C ⊆ T)
    (hroof : A0 ⊆ Gamma.roof T) (hclosed : A0 ⊆ Z)
    (hcard : #A0 ≤ kappa)
    (hpopular : A0 ⊆ {u | IsPopular Gamma Y persistent kappa u} ∪ T)
    (hstable : A0 ∩ T ⊆ persistent) :
    (initialSingletonState hY hA0 hCT hroof hclosed hcard hpopular
      hstable (B := B)).blueprint = singletonSeed Gamma Y kappa A0 :=
  rfl

theorem designated_initial_initialSingletonState
    {A0 C T Z persistent B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hCT : C ⊆ T)
    (hroof : A0 ⊆ Gamma.roof T) (hclosed : A0 ⊆ Z)
    (hcard : #A0 ≤ kappa)
    (hpopular : A0 ⊆ {u | IsPopular Gamma Y persistent kappa u} ∪ T)
    (hstable : A0 ∩ T ⊆ persistent) :
    A0 ⊆ (initialSingletonState hY hA0 hCT hroof hclosed hcard
      hpopular hstable (B := B)).blueprint.initialSet := by
  simpa

/-- A canonical stable initial state.  Taking `persistent = A₀` makes
each singleton terminal popular, while `T = source ∪ C` makes both the
stability and roof conditions immediate. -/
def canonicalInitialSingletonState
    {A0 C B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hcard : #A0 ≤ kappa) :
    TerminalResolutionState Gamma Y kappa
      (Gamma.source ∪ C) Set.univ A0 B := by
  apply initialSingletonState hY hA0 Set.subset_union_right
  · exact hA0.trans (Set.subset_union_left.trans
      (Gamma.subset_roof (Gamma.source ∪ C)))
  · exact Set.subset_univ A0
  · exact hcard
  · intro a ha
    exact Or.inl (Or.inl ha)
  · intro a ha
    exact ha.1

@[simp] theorem canonicalInitialSingletonState_blueprint
    {A0 C B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hcard : #A0 ≤ kappa) :
    (canonicalInitialSingletonState hY hA0 hcard
      (B := B)).blueprint = singletonSeed Gamma Y kappa A0 := by
  rfl

theorem canonicalInitialSingletonState_persistent_subset
    {A0 C B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hcard : #A0 ≤ kappa) :
    A0 ⊆ Gamma.source ∪ C :=
  hA0.trans Set.subset_union_left

theorem canonicalInitialSingletonState_designated_initial
    {A0 C B : Set V}
    (hY : CardinalInduction.IsLinkageBetween Gamma Gamma.source C Y)
    (hA0 : A0 ⊆ Gamma.source) (hcard : #A0 ≤ kappa) :
    A0 ⊆ (canonicalInitialSingletonState hY hA0 hcard
      (B := B)).blueprint.initialSet := by
  simpa

end LinkageBlueprint
end Blueprint

namespace CardinalInduction

open Blueprint LinkageBlueprint

universe u

variable {V : Type u}

/-- The reference warp at the actual start of Section 9: the essential
part of the canonical forward-maximal wave. -/
def maximalWaveReference (Gamma : DWeb V) : Set Gamma.DPath :=
  Gamma.essentialWarpPart Gamma.chosenMaximalWave.1

/-- The trimmed frontier of the canonical maximal wave. -/
def maximalWaveStopover (Gamma : DWeb V) : Set V :=
  Gamma.essential (Gamma.terminalFrontier Gamma.chosenMaximalWave.1)

/-- The genuine maximal-wave start of the scheduler, before the later
ladder slice supplies a bounded height witness. -/
structure MaximalWaveInitialData (Gamma : DWeb V) (A0 : Set V)
    (kappa : Cardinal.{u}) (B : Set V) where
  seed : TerminalResolutionState Gamma (maximalWaveReference Gamma) kappa
    (Gamma.source ∪ maximalWaveStopover Gamma) Set.univ A0 B
  separating_stopover : IsSeparatingHalfwayStopover Gamma
    (maximalWaveReference Gamma) (maximalWaveStopover Gamma)
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ seed.blueprint.initialSet
  persistent_subset : A0 ⊆ Gamma.source ∪ maximalWaveStopover Gamma

/-- An unhindered web has the exact stable singleton start used in the
Section 9 recursion.  The reference and stopover are not arbitrary: both
are definitionally obtained from the same maximal wave. -/
noncomputable def maximalWaveInitialData
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}} {B : Set V}
    (hGamma : Gamma.IsUnhindered) (hA0 : A0 ⊆ Gamma.source)
    (hcard : #A0 ≤ kappa) :
    MaximalWaveInitialData Gamma A0 kappa B := by
  have hstop : IsSeparatingHalfwayStopover Gamma
      (maximalWaveReference Gamma) (maximalWaveStopover Gamma) := by
    exact essentialWarpPart_isSeparatingHalfwayStopover_of_isMax hGamma
      Gamma.chosenMaximalWave.property Gamma.chosenMaximalWave_isMax
  let seed := Blueprint.LinkageBlueprint.canonicalInitialSingletonState
    hstop.linkage hA0 hcard (B := B)
  exact
    { seed := seed
      separating_stopover := hstop
      designated_source := hA0
      designated_initial := by
        exact
          Blueprint.LinkageBlueprint.canonicalInitialSingletonState_designated_initial
            hstop.linkage hA0 hcard
      persistent_subset := hA0.trans Set.subset_union_left }

/-- The separator and height fields of a fair-resolution certificate,
independent of its final blueprint and reference slice. -/
structure SeparatingHeightData (Gamma : DWeb V)
    (kappa : Cardinal.{u}) where
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- A separating half-way stopover and an altitude witness contain exactly
the scheduler's geometric payload; no choice beyond unpacking the height
witness is involved. -/
theorem exists_separatingHeightData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {W : Set Gamma.DPath} {C : Set V}
    (hC : IsSeparatingHalfwayStopover Gamma W C)
    (hheight : HeightAtMost Gamma C kappa) :
    ∃ D : SeparatingHeightData Gamma kappa, D.stopover = C := by
  obtain ⟨X, hX, hXcard⟩ := hheight
  obtain ⟨hXsource, R, hR, hCroof⟩ := hX
  exact ⟨
    { stopover := C
      heightDelete := X
      heightWave := R
      stopover_separator := hC.separator
      stopover_trimmed := hC.stopover.minimal
      quotient_unhindered := hC.stopover.quotient_unhindered
      heightDelete_nonSource := hXsource
      heightWave_isWave := hR
      stopover_roofed := hCroof
      heightDelete_card := hXcard }, rfl⟩

/-- A ready-to-run stable singleton state together with the exact
separator/height payload of its reference stopover.  Keeping the seed and
the geometry in one record prevents the scheduler setup from silently
changing either the reference linkage or the stopover. -/
structure InitialSchedulerData (Gamma : DWeb V) (A0 : Set V)
    (kappa : Cardinal.{u}) (B : Set V) where
  reference : Set Gamma.DPath
  stopover : Set V
  seed : TerminalResolutionState Gamma reference kappa
    (Gamma.source ∪ stopover) Set.univ A0 B
  geometry : SeparatingHeightData Gamma kappa
  geometry_stopover : geometry.stopover = stopover
  reference_linkage :
    IsLinkageBetween Gamma Gamma.source stopover reference
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ seed.blueprint.initialSet
  persistent_subset : A0 ⊆ Gamma.source ∪ stopover

/-- Build the initial scheduler package from the two mathematical inputs
available at a ladder slice: a separating stopover and its bounded-height
witness. -/
noncomputable def initialSchedulerData_of_separatingHalfway
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}} {B : Set V}
    {W : Set Gamma.DPath} {C : Set V}
    (hA0 : A0 ⊆ Gamma.source) (hcard : #A0 ≤ kappa)
    (hC : IsSeparatingHalfwayStopover Gamma W C)
    (hheight : HeightAtMost Gamma C kappa) :
    InitialSchedulerData Gamma A0 kappa B := by
  let E := Classical.choose (exists_separatingHeightData hC hheight)
  have hEC : E.stopover = C :=
    Classical.choose_spec (exists_separatingHeightData hC hheight)
  let seed := Blueprint.LinkageBlueprint.canonicalInitialSingletonState
    hC.linkage hA0 hcard (B := B)
  exact
    { reference := W
      stopover := C
      seed := seed
      geometry := E
      geometry_stopover := hEC
      reference_linkage := hC.linkage
      designated_source := hA0
      designated_initial := by
        exact
          Blueprint.LinkageBlueprint.canonicalInitialSingletonState_designated_initial
            hC.linkage hA0 hcard
      persistent_subset := hA0.trans Set.subset_union_left }

end CardinalInduction
end Erdos599
