/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedCertifiedScheduler
import ErdosProblems.Erdos599.IndexedRelationLimit

/-!
# Proper and final relation limits for the indexed half-way scheduler

The ladder slice and closure set vary along the half-way recursion.  This
module combines the indexed scheduler with the slice-independent relation
limits.  The relation is constructed canonically from real extension and
predecessor refinement; only the honest moving-slice blueprint, stability,
and supremum-index boundary remains an input.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {persistent B : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

namespace ResolutionChain

variable {I : Type v} [LinearOrder I]

/-- Forget the moving slice data and retain exactly the relation-level
extension and refinement chain. -/
def toIndexedRealExtensionChain
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I) :
    IndexedRealExtensionChain I Gamma Y kappa B where
  stage := fun i ↦ (C.stage i).blueprint
  realExtends := fun {_ _} hij ↦ (C.refiningExtends hij).realExtends
  predecessorRefines := fun {_ _} hij ↦
    (C.refiningExtends hij).predecessorRefines

/-- The genuine residual geometry at a proper moving-slice limit.  The
eventual-full relation itself is already constructed by
`IndexedRelationLimit`; these are precisely the fields that know the
supremum ladder slice. -/
structure ProperRelationLimitBoundary
    [Nonempty I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I) where
  limitIndex : Stage
  isBlueprint : C.toIndexedRealExtensionChain.eventualRelationBlueprint
    |>.IsLinkageBlueprint (slice limitIndex) (closure limitIndex) persistent
  stable : C.toIndexedRealExtensionChain.eventualRelationBlueprint
    |>.Stable (slice limitIndex) persistent
  index_upper : ∀ i, (C.stage i).stageIndex ≤ limitIndex
  index_least : ∀ b : Stage,
    (∀ i, (C.stage i).stageIndex ≤ b) → limitIndex ≤ b

/-- The canonical scheduler state at a proper indexed relation limit. -/
noncomputable def properLimitState
    [Nonempty I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : ProperRelationLimitBoundary C) :
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure where
  stageIndex := D.limitIndex
  blueprint := C.toIndexedRealExtensionChain.eventualRelationBlueprint
  isBlueprint := D.isBlueprint
  stable := D.stable
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toIndexedRealExtensionChain
        |>.realPart_extends_eventualRelationBlueprint i)
      (by simpa [toIndexedRealExtensionChain] using (C.stage i).links x hxi)

@[simp] theorem properLimitState_blueprint
    [Nonempty I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : ProperRelationLimitBoundary C) :
    (properLimitState C D).blueprint =
      C.toIndexedRealExtensionChain.eventualRelationBlueprint := rfl

theorem refiningExtends_properLimitState
    [Nonempty I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : ProperRelationLimitBoundary C) (i : I) :
    (C.stage i).RefiningExtends (properLimitState C D) where
  realExtends :=
    by simpa [properLimitState, toIndexedRealExtensionChain] using
      C.toIndexedRealExtensionChain.realExtends_eventualRelationBlueprint i
  predecessorRefines :=
    by simpa [properLimitState, toIndexedRealExtensionChain] using
      C.toIndexedRealExtensionChain.predecessorRefines_eventualRelationBlueprint i
  stage_mono := D.index_upper i

theorem linked_subset_properLimitState
    [Nonempty I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : ProperRelationLimitBoundary C) (i : I) :
    (C.stage i).linked ⊆ (properLimitState C D).linked :=
  Set.subset_iUnion (fun j ↦ (C.stage j).linked) i

/-- Package a coherent proper history as a relation chain. -/
def ofPrior {o : Ordinal.{u}}
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (hcoherent : PriorCoherent prior) :
    ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) (Set.Iio o) where
  stage := prior
  refiningExtends := hcoherent

/-- Compile the honest relation boundary to the exact proper-limit value
used by the ordinal recursor. -/
noncomputable def properLimitConclusionOfBoundary
    {o : Ordinal.{u}} [Nonempty (Set.Iio o)]
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (hcoherent : PriorCoherent prior)
    (D : ProperRelationLimitBoundary (ofPrior prior hcoherent)) :
    ProperLimitConclusion prior where
  limit := properLimitState (ofPrior prior hcoherent) D
  extension := fun i ↦
    refiningExtends_properLimitState (ofPrior prior hcoherent) D i
  linked := fun i ↦
    linked_subset_properLimitState (ofPrior prior hcoherent) D i
  index_upper := D.index_upper
  index_least := D.index_least

end ResolutionChain

/-- The proper-limit boundary type with its nonemptiness witness obtained
from the fact that the ordinal is a nonzero limit. -/
noncomputable def properRelationLimitBoundaryType
    {o : Ordinal.{u}} (ho : IsSuccLimit o)
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (hcoherent : PriorCoherent prior) : Type w := by
  letI : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
  exact ResolutionChain.ProperRelationLimitBoundary
    (ResolutionChain.ofPrior prior hcoherent)

/-- Reachable-history moving-slice geometry required at every proper
ordinal below a bounded run. -/
def ProperRelationLimitBoundaryProvider
    (length : Ordinal.{u}) : Prop :=
  ∀ (o : Ordinal.{u}), o < length → (ho : IsSuccLimit o) →
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) →
    (hcoherent : PriorCoherent prior) →
      Nonempty (properRelationLimitBoundaryType ho prior hcoherent)

/-- Turn the honest indexed relation-limit boundary provider into the
proper-limit compiler consumed by the ordinal recursor. -/
noncomputable def properLimitCompilerOfBoundaryProvider
    {length : Ordinal.{u}}
    (P : ProperRelationLimitBoundaryProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) length) :
    ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure length := by
  intro o hoLength ho prior hcoherent
  letI : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
  let D : ResolutionChain.ProperRelationLimitBoundary
      (ResolutionChain.ofPrior prior hcoherent) := by
    simpa only [properRelationLimitBoundaryType] using
      (P o hoLength ho prior hcoherent).some
  exact ⟨ResolutionChain.properLimitConclusionOfBoundary
    prior hcoherent D⟩

/-! ## Final all-real relation and fairness -/

namespace ResolutionChain

variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- The moving-slice geometry still required at the final all-real
relation.  Relation construction, reverse-ray exclusion, accounting, and
fairness are not fields of this record. -/
structure FinalRelationLimitBoundary
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I) where
  limitIndex : Stage
  isBlueprint : C.toIndexedRealExtensionChain.realRelationBlueprint
    |>.IsLinkageBlueprint (slice limitIndex) (closure limitIndex) persistent
  stable : C.toIndexedRealExtensionChain.realRelationBlueprint
    |>.Stable (slice limitIndex) persistent
  index_upper : ∀ i, (C.stage i).stageIndex ≤ limitIndex
  index_least : ∀ b : Stage,
    (∀ i, (C.stage i).stageIndex ≤ b) → limitIndex ≤ b

/-- Successful enumeration turns each stage real terminal into a completed
real vertex at some later (not necessarily ordered) stage. -/
theorem successfulResolutionEnumeration_eventuallyCompleted
    {C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I}
    {seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure}
    (E : SuccessfulResolutionEnumeration C seed) :
    ∀ i x, x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, x ∈ (C.stage j).blueprint.completedRealVertices B := by
  intro i x hx
  obtain ⟨j, hj⟩ := E.covers_stage_realTerminals i x hx
  refine ⟨j, ?_⟩
  rw [← hj]
  exact ((C.stage j).links _ (E.scheduled_linked j)).start_mem_completedRealVertices

/-- The canonical final moving-slice scheduler state. -/
noncomputable def finalLimitState
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : FinalRelationLimitBoundary C) :
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure where
  stageIndex := D.limitIndex
  blueprint := C.toIndexedRealExtensionChain.realRelationBlueprint
  isBlueprint := D.isBlueprint
  stable := D.stable
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toIndexedRealExtensionChain
        |>.realPart_extends_realRelationBlueprint i)
      (by simpa [toIndexedRealExtensionChain] using (C.stage i).links x hxi)

@[simp] theorem finalLimitState_blueprint
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (D : FinalRelationLimitBoundary C) :
    (finalLimitState C D).blueprint =
      C.toIndexedRealExtensionChain.realRelationBlueprint := rfl

/-- A terminal of the all-real limit already occurred as a real terminal
at one scheduler stage. -/
theorem exists_stage_realTerminal_of_finalLimit_terminal
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    {x : V}
    (hx : x ∈
      C.toIndexedRealExtensionChain.realRelationBlueprint.realPart.terminals) :
    ∃ i, x ∈ (C.stage i).blueprint.realPart.terminals := by
  rcases hx with ⟨hxvertex, hxterminal⟩
  rw [realPart_vertices,
    C.toIndexedRealExtensionChain.realRelationBlueprint_vertexSet] at hxvertex
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxvertex
  refine ⟨i, hxi, ?_⟩
  rintro ⟨y, hxy⟩
  apply hxterminal
  refine ⟨y, ?_⟩
  rw [C.toIndexedRealExtensionChain.realRelationBlueprint_realPart_edges]
  exact C.toIndexedRealExtensionChain.stage_edges_subset_realEdgeLimit i hxy

/-- Complete fair output of the moving-slice indexed scheduler. -/
structure FairResolutionLimit
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) where
  scheduled : I → V
  seed_absorbed : ∀ i,
    seed.blueprint.RealExtends (C.stage i).blueprint B
  scheduled_linked : ∀ i, scheduled i ∈ (C.stage i).linked
  limit : IndexedTerminalResolutionState
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  relation_limit : limit.blueprint =
    C.toIndexedRealExtensionChain.realRelationBlueprint
  absorbed : ∀ i, (C.stage i).blueprint.RealExtends limit.blueprint B
  fair : ∀ x ∈ limit.blueprint.realPart.terminals, x ∉ B →
    ∃ i, scheduled i = x
  real_limit : limit.blueprint.familyGraph.edges ⊆
    {e | Gamma.graph.Adj e.1 e.2}

/-- The indexed relation limit plus successful repeated enumeration produce
the complete all-real fair limit. -/
noncomputable def FairResolutionLimit.ofSuccessfulEnumeration
    {C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I}
    {seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure}
    (D : FinalRelationLimitBoundary C)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairResolutionLimit C seed := by
  let hcompleted : ∀ i x,
      x ∈ (C.stage i).blueprint.realPart.terminals →
      x ∉ (C.stage i).blueprint.terminalSet →
        ∃ j, x ∈ (C.stage j).blueprint.completedRealVertices B :=
    fun i x hx _ ↦
      successfulResolutionEnumeration_eventuallyCompleted E i x hx
  exact {
    scheduled := E.scheduled
    seed_absorbed := E.seed_absorbed
    scheduled_linked := E.scheduled_linked
    limit := finalLimitState C D
    relation_limit := rfl
    absorbed := fun i ↦
      by
        apply C.toIndexedRealExtensionChain
          |>.realExtends_realRelationBlueprint_of_eventuallyCompleted
        intro j x hx hnot
        exact hcompleted j x (by
          simpa [toIndexedRealExtensionChain] using hx) (by
            simpa [toIndexedRealExtensionChain] using hnot)
    fair := by
      intro x hx _hxB
      obtain ⟨i, hxi⟩ :=
        C.exists_stage_realTerminal_of_finalLimit_terminal hx
      exact E.covers_stage_realTerminals i x hxi
    real_limit := by
      intro e he
      change e ∈ (finalLimitState C D).blueprint.edgeSet at he
      rw [finalLimitState_blueprint,
        C.toIndexedRealExtensionChain.realRelationBlueprint_edgeSet] at he
      obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
      exact hei.2 }

/-- Forget moving-slice transition provenance and retain the terminal
schedule consumed by the public half-way certificate. -/
def FairResolutionLimit.toTerminalScheduledChain
    {C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I}
    {seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure}
    (R : FairResolutionLimit C seed) :
    TerminalScheduledChain I (fun i ↦ (C.stage i).blueprint)
      R.limit.blueprint B where
  scheduled := R.scheduled
  absorbed := fun i ↦ (R.absorbed i).realPart_extends
  fair := R.fair
  resolved := fun i ↦ (C.stage i).links _ (R.scheduled_linked i)
  real_limit := R.real_limit

/-- Structural final geometry over an indexed fair resolution.  This is the
moving-slice analogue of `TerminalResolutionState.FairResolutionCertificate`;
unlike that older fixed-slice record it does not retain an uninstantiable
constant-`T` successor compiler. -/
structure FairResolutionCertificate
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target)
      (slice := slice) (closure := closure) I)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target) slice closure)
    (A0 : Set V) where
  resolution : FairResolutionLimit C seed
  remainderSlice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp Y
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ resolution.limit.blueprint.initialSet
  source_cover : resolution.limit.blueprint.initialSet ∪
    Gamma.initialSet
      (resolution.limit.blueprint.referenceRemainder remainderSlice) =
      Gamma.source
  terminal_frontier : resolution.limit.blueprint.terminalSet ∪
    Gamma.terminalFrontier
      (resolution.limit.blueprint.referenceRemainder remainderSlice) = stopover
  blueprint_endpointPure : ∀ p ∈ resolution.limit.blueprint.paths,
    resolution.limit.blueprint.IsPathBetween Gamma.source stopover p
  reference_endpointPure :
    ∀ p ∈ resolution.limit.blueprint.referenceRemainder remainderSlice,
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator :
    CardinalInduction.IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- The indexed fair certificate has exactly the public terminal-scheduled
payload; the varying ladder indices are erased only here, after the final
blueprint has been constructed. -/
def FairResolutionCertificate.toTerminalScheduledBlueprintCertificate
    {I : Type u} [LinearOrder I] [Nonempty I]
    {C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target)
      (slice := slice) (closure := closure) I}
    {seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target) slice closure}
    {A0 : Set V} (R : FairResolutionCertificate C seed A0) :
    CardinalInduction.TerminalScheduledBlueprintCertificate Gamma A0 kappa where
  reference := Y
  blueprint := R.resolution.limit.blueprint
  index := I
  stage := fun i ↦ (C.stage i).blueprint
  schedule := R.resolution.toTerminalScheduledChain
  slice := R.remainderSlice
  stopover := R.stopover
  heightDelete := R.heightDelete
  heightWave := R.heightWave
  reference_isWarp := R.reference_isWarp
  designated_source := R.designated_source
  designated_initial := R.designated_initial
  source_cover := R.source_cover
  terminal_frontier := R.terminal_frontier
  blueprint_endpointPure := R.blueprint_endpointPure
  reference_endpointPure := R.reference_endpointPure
  stopover_trimmed := R.stopover_trimmed
  quotient_unhindered := R.quotient_unhindered
  heightDelete_nonSource := R.heightDelete_nonSource
  heightWave_isWave := R.heightWave_isWave
  stopover_roofed := R.stopover_roofed
  heightDelete_card := R.heightDelete_card

/-- Preserve the separator witness needed by the strong half-way clause. -/
def FairResolutionCertificate.toSeparatingGloballyResolved
    {I : Type v} [LinearOrder I] [Nonempty I]
    {C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target)
      (slice := slice) (closure := closure) I}
    {seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target) slice closure}
    {A0 : Set V} (R : FairResolutionCertificate C seed A0) :
    CardinalInduction.SeparatingGloballyResolvedBlueprintCertificate
      Gamma A0 kappa where
  certificate := {
    reference := Y
    blueprint := R.resolution.limit.blueprint
    slice := R.remainderSlice
    stopover := R.stopover
    heightDelete := R.heightDelete
    heightWave := R.heightWave
    reference_isWarp := R.reference_isWarp
    edge_real := R.resolution.real_limit
    real_terminals_target :=
      R.resolution.toTerminalScheduledChain.final_terminals_subset
    designated_source := R.designated_source
    designated_initial := R.designated_initial
    source_cover := R.source_cover
    terminal_frontier := R.terminal_frontier
    blueprint_endpointPure := R.blueprint_endpointPure
    reference_endpointPure := R.reference_endpointPure
    stopover_trimmed := R.stopover_trimmed
    quotient_unhindered := R.quotient_unhindered
    heightDelete_nonSource := R.heightDelete_nonSource
    heightWave_isWave := R.heightWave_isWave
    stopover_roofed := R.stopover_roofed
    heightDelete_card := R.heightDelete_card }
  stopover_separator := R.stopover_separator

/-- The checked repeated-request run and an honest final moving-slice
boundary compile directly to a fair all-real relation limit. -/
noncomputable def fairRepeatedLimit
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    [Nonempty Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (hclosure : ∀ s, closure s ⊆ Request)
    (D : FinalRelationLimitBoundary
      (repeatedChain successor seed u₀ hu₀ limit)) :
    FairResolutionLimit (repeatedChain successor seed u₀ hu₀ limit) seed :=
  FairResolutionLimit.ofSuccessfulEnumeration D
    (successfulRepeatedEnumeration successor seed u₀ hu₀ limit hclosure)

end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
