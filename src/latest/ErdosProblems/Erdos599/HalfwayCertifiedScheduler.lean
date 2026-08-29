/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Section9Environment
import ErdosProblems.Erdos599.HalfwayIntermediateLimit

/-!
# Reachable-state transfinite scheduling for the half-way clause

This module contains the order-theoretic recursion used by the terminal
scheduler.  Its successor operation is only asked for states produced by the
recursion.  This is important: the Section 9 geometry certifies reachable
blueprints, not arbitrary values satisfying the six blueprint fields.

Proper limit stages are likewise part of the recursor.  The concrete
instance uses the eventual-full-edge limit from `IntermediateRelationLimit`;
the final fair sweep is compiled separately with the all-real relation limit.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

/-- The occurrence-aware successor geometry together with the two ambient
facts needed only by the genuine 9.33 limit compilers.  Keeping these facts
outside `OccurrenceSection9Environment` makes the 9.31 construction itself
independent of normalization and of any projected assignment. -/
structure Section9SchedulerEnvironment
    (T Z persistent B : Set V) : Prop extends
    OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B where
  normalized : Gamma.IsNormalized
  reference_warp : Gamma.IsWarp Y

/-- Add the limit-only ambient facts to the occurrence-aware successor
environment. -/
def OccurrenceSection9Environment.withLimitGeometry
    (E : OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hGamma : Gamma.IsNormalized) (hYwarp : Gamma.IsWarp Y) :
    Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B where
  toOccurrenceSection9Environment := E
  normalized := hGamma
  reference_warp := hYwarp

namespace TerminalResolutionState

/-- Reapply the occurrence-aware local construction to one scheduler state.
The two limit-only fields of `E` play no role in this successor. -/
theorem compiledSuccessor
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingStable934 S.blueprint U u
        T Z persistent B := by
  let E₀ := E.toOccurrenceSection9Environment
  obtain ⟨U, hU, _⟩ :=
    (E₀.certify S.blueprint S.isBlueprint S.stable).compiledSuccessor
      E₀ u hu
  exact ⟨U, hU⟩

/-- The two transition invariants which compose through both successor and
proper-limit stages. -/
structure FullyExtends
    (S U : TerminalResolutionState Gamma Y kappa T Z persistent B) : Prop where
  realExtends : S.blueprint.RealExtends U.blueprint B
  noNewPredecessors : S.blueprint.NoNewPredecessorsTo U.blueprint

@[refl] theorem FullyExtends.refl
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.FullyExtends S where
  realExtends := realExtends_refl S.blueprint B
  noNewPredecessors := NoNewPredecessorsTo.refl S.blueprint

@[trans] theorem FullyExtends.trans
    {S U R : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (hSU : S.FullyExtends U) (hUR : U.FullyExtends R) :
    S.FullyExtends R where
  realExtends := realExtends_trans hSU.realExtends hUR.realExtends
  noNewPredecessors := NoNewPredecessorsTo.trans hSU.noNewPredecessors
    hUR.noNewPredecessors hSU.realExtends.vertices_mono

/-- Under (9.32), an old real terminal either stays a real terminal or has
already acquired a real path to the completion set.  A retained old full
edge cannot become real later: right-uniqueness identifies it with any
putative new real outgoing edge, and realness is a property of that fixed
ordered pair. -/
theorem realTerminal_or_realLinksTo_of_realExtends
    {W U : LinkageBlueprint Gamma Y kappa} {x : V}
    (hWU : W.RealExtends U B)
    (hx : x ∈ W.realPart.terminals) :
    x ∈ U.realPart.terminals ∨ U.RealLinksTo x B := by
  have hxW : x ∈ W.vertexSet := by
    simpa only [realPart_vertices] using hx.1
  rcases hWU.2 hxW with (hterminal | hcommon) | hcompleted
  · left
    refine ⟨hWU.1.1 hx.1, ?_⟩
    rintro ⟨y, hxy⟩
    exact (mem_familyGraph_terminals_of_mem_terminalSet hterminal.1).2
      ⟨y, hxy.1⟩
  · rcases hcommon with ⟨y, hxyW, hxyU⟩
    left
    refine ⟨hWU.1.1 hx.1, ?_⟩
    rintro ⟨z, hxzU⟩
    have hyz : y = z :=
      Alternating.IsWarp.familyEdges_rightUnique U.isWarp hxyU hxzU.1
    apply hx.2
    refine ⟨y, hxyW, ?_⟩
    simpa [hyz] using hxzU.2
  · exact Or.inr (realLinksTo_of_mem_completedRealVertices hcompleted)

/-! ## Certified all-real-terminal successor -/

/-- The successor selected from the concrete transition stored by the
Section 9 environment. -/
noncomputable def certifiedAdvanceBlueprint
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    LinkageBlueprint Gamma Y kappa :=
  Classical.choose
    (compiledSuccessor E S u hu)

theorem certifiedAdvanceBlueprint_spec
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    FullyPredecessorPreservingStable934 S.blueprint
      (certifiedAdvanceBlueprint E S u hu) u T Z persistent B :=
  (Classical.choose_spec
    (compiledSuccessor E S u hu))

/-- Execute one certified source-faithful 9.34 transition. -/
noncomputable def certifiedAdvance
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := certifiedAdvanceBlueprint E S u hu
  isBlueprint := (certifiedAdvanceBlueprint_spec E S u hu).conclusion.1
  stable := (certifiedAdvanceBlueprint_spec E S u hu).conclusion.2.1
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (certifiedAdvanceBlueprint_spec E S u hu).conclusion.links
    · exact realLinksTo_mono
        (certifiedAdvanceBlueprint_spec E S u hu).conclusion.realExtends.1
        (S.links x hx)

/-- Record a request which was already completed by an earlier transition.
This is the bookkeeping case needed after a proper limit: (9.32) may turn
an old terminal into a completed real path before its next cofinal visit. -/
def recordLinked
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : S.blueprint.RealLinksTo u B) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := S.blueprint
  isBlueprint := S.isBlueprint
  stable := S.stable
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · simpa [hx] using hu
    · exact S.links x hx

/-- The total reachable-state successor: all real terminals are executed;
other requests mark time. -/
noncomputable def certifiedStep
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    TerminalResolutionState Gamma Y kappa T Z persistent B := by
  classical
  exact if hu : u ∈ S.blueprint.realPart.terminals then
    certifiedAdvance E S u hu
  else if hlinked : S.blueprint.RealLinksTo u B then
    recordLinked S u hlinked
  else S

theorem fullyExtends_certifiedStep
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    S.FullyExtends (certifiedStep E S u) := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simp only [certifiedStep, hu, dite_true]
    exact {
      realExtends := (certifiedAdvanceBlueprint_spec E S u hu).conclusion.realExtends
      noNewPredecessors :=
        (certifiedAdvanceBlueprint_spec E S u hu).no_new_predecessors }
  · simp only [certifiedStep, hu, dite_false]
    by_cases hlinked : S.blueprint.RealLinksTo u B
    · simp only [hlinked, dite_true]
      exact
        { realExtends := realExtends_refl S.blueprint B
          noNewPredecessors := NoNewPredecessorsTo.refl S.blueprint }
    · simp only [hlinked, dite_false]
      exact FullyExtends.refl S

theorem linked_subset_certifiedStep
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    S.linked ⊆ (certifiedStep E S u).linked := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simpa [certifiedStep, hu, certifiedAdvance] using
      Set.subset_insert u S.linked
  · by_cases hlinked : S.blueprint.RealLinksTo u B <;>
      simp [certifiedStep, hu, hlinked, recordLinked]

theorem request_mem_linked_certifiedStep
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V)
    (hu : u ∈ S.blueprint.realPart.terminals) :
    u ∈ (certifiedStep E S u).linked := by
  simp [certifiedStep, hu, certifiedAdvance]

/-- A request which is either currently terminal or already completed is
recorded by the total successor. -/
theorem terminal_or_completed_mem_linked_certifiedStep
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V)
    (hu : u ∈ S.blueprint.realPart.terminals ∨
      S.blueprint.RealLinksTo u B) :
    u ∈ (certifiedStep E S u).linked := by
  rcases hu with hu | hu
  · exact request_mem_linked_certifiedStep E S u hu
  · by_cases hterm : u ∈ S.blueprint.realPart.terminals
    · exact request_mem_linked_certifiedStep E S u hterm
    · simp [certifiedStep, hterm, hu, recordLinked]

/-- Compatibility compiler used only as the phantom compiler parameter of
`ResolutionChain`.  Successor execution itself continues to use the
reachable certified transition, on the larger all-real-terminal domain. -/
noncomputable def schedulerCompiler
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B := by
  intro W u hW _hpersistent hu _huT
  let C := (E.toOccurrenceSection9Environment.certifiedTransition hW hu).some
  obtain ⟨U, hU⟩ := C.compile E.lower_induction E.extension_induction
  exact ⟨U, hU.conclusion⟩

/-- Coherence of all states strictly before one ordinal. -/
def PriorCoherent (o : Ordinal.{u})
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) : Prop :=
  ∀ a b, a ≤ b → (prior a).FullyExtends (prior b)

/-- A reachable-state recursor.  `step` is total (an ineligible request may
mark time), while `properLimit` is called only with a coherent family of
previously produced states. -/
structure ReachableResolutionRecursor where
  /-- Only stages below this ordinal are part of the scheduler run.  The
  bound is essential: proper initial segments of this ordinal have the
  cardinality required by Assertion 9.33. -/
  length : Ordinal.{u}
  seed : TerminalResolutionState Gamma Y kappa T Z persistent B
  step : TerminalResolutionState Gamma Y kappa T Z persistent B → V →
    TerminalResolutionState Gamma Y kappa T Z persistent B
  step_extends : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, FullyExtends S (step S u)
  linked_mono_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, S.linked ⊆ (step S u).linked
  request_linked_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u,
    u ∈ S.blueprint.realPart.terminals → u ∈ (step S u).linked
  properLimit : ∀ (o : Ordinal.{u}), o < length → IsSuccLimit o →
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) →
    PriorCoherent o prior →
      TerminalResolutionState Gamma Y kappa T Z persistent B
  extends_properLimit : ∀ o (hoLength : o < length) (ho : IsSuccLimit o)
      (prior : Set.Iio o →
        TerminalResolutionState Gamma Y kappa T Z persistent B)
      (hcoherent : PriorCoherent o prior) (a : Set.Iio o),
    FullyExtends (prior a) (properLimit o hoLength ho prior hcoherent)
  linked_properLimit : ∀ o (hoLength : o < length) (ho : IsSuccLimit o)
      (prior : Set.Iio o →
        TerminalResolutionState Gamma Y kappa T Z persistent B)
      (hcoherent : PriorCoherent o prior) (a : Set.Iio o),
    (prior a).linked ⊆
      (properLimit o hoLength ho prior hcoherent).linked

namespace ReachableResolutionRecursor

/-- A coherent proper initial history, viewed as the real-extension chain
consumed by the intermediate 9.33 relation-limit compiler. -/
def priorRealExtensionChain
    {o : Ordinal.{u}}
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : PriorCoherent o prior) :
    RealExtensionChain o.ToType Gamma Y kappa T Z persistent B where
  stage := fun a ↦ (prior (Ordinal.ToType.toOrd a)).blueprint
  isBlueprint := fun a ↦ (prior (Ordinal.ToType.toOrd a)).isBlueprint
  stable := fun a ↦ (prior (Ordinal.ToType.toOrd a)).stable
  realExtends := by
    intro a b hab
    exact (hcoherent _ _ (Ordinal.ToType.mk.symm.monotone hab)).realExtends

/-- Full predecessor preservation of the chain extracted from a coherent
history. -/
def priorChainNoNewPredecessors
    {o : Ordinal.{u}}
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : PriorCoherent o prior) :
    (priorRealExtensionChain prior hcoherent).NoNewPredecessors where
  of_le := by
    intro a b hab
    exact (hcoherent _ _
      (Ordinal.ToType.mk.symm.monotone hab)).noNewPredecessors

/-- The genuine nonfinal 9.33 state for one coherent reachable history. -/
noncomputable def intermediateLimitOfPrior
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : PriorCoherent o prior) :
    TerminalResolutionState Gamma Y kappa T Z persistent B := by
  letI : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  let C := priorRealExtensionChain prior hcoherent
  let H := priorChainNoNewPredecessors prior hcoherent
  have hindex : #o.ToType ≤ kappa := by
    rw [Cardinal.mk_toType]
    exact (Ordinal.card_le_card hoLength.le).trans hlength
  let D : C.EventualRelationLimitBoundary :=
    C.eventualRelationLimitBoundary_of_normalized_index E.normalized
      hBtarget E.infinite_cardinal hindex
  exact
    { blueprint := C.eventualRelationLimit H
      isBlueprint := C.eventualRelationLimit_isLinkageBlueprint H
        E.reference_warp hterminalB D
      stable := C.eventualRelationLimit_stable H hstableB
      linked := ⋃ i : o.ToType, (prior (Ordinal.ToType.toOrd i)).linked
      links := by
        intro x hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
        exact realLinksTo_mono
          (C.realPart_extends_eventualRelationLimit H i)
          ((prior (Ordinal.ToType.toOrd i)).links x hxi) }

theorem fullyExtends_intermediateLimitOfPrior
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : PriorCoherent o prior) (a : Set.Iio o) :
    (prior a).FullyExtends
      (intermediateLimitOfPrior E length hlength hBtarget hterminalB hstableB
        o hoLength ho prior hcoherent) := by
  letI : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  let C := priorRealExtensionChain prior hcoherent
  let H := priorChainNoNewPredecessors prior hcoherent
  let i : o.ToType := Ordinal.ToType.mk a
  have hi : Ordinal.ToType.toOrd i = a := by simp [i]
  change (prior a).FullyExtends _
  rw [← hi]
  exact
    { realExtends := C.realExtends_eventualRelationLimit H i
      noNewPredecessors := C.noNewPredecessorsTo_eventualRelationLimit H
        i }

theorem linked_subset_intermediateLimitOfPrior
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : PriorCoherent o prior) (a : Set.Iio o) :
    (prior a).linked ⊆
      (intermediateLimitOfPrior E length hlength hBtarget hterminalB hstableB
        o hoLength ho prior hcoherent).linked := by
  intro x hx
  change x ∈ ⋃ i : o.ToType, (prior (Ordinal.ToType.toOrd i)).linked
  let i : o.ToType := Ordinal.ToType.mk a
  have hi : Ordinal.ToType.toOrd i = a := by simp [i]
  exact Set.mem_iUnion.2 ⟨i, hi ▸ hx⟩

/-- Assemble the bounded reachable scheduler from certified Section 9
successors and genuine eventual-full-edge limits. -/
noncomputable def ofSection9SchedulerEnvironment
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) where
  length := length
  seed := seed
  step := certifiedStep E
  step_extends := fullyExtends_certifiedStep E
  linked_mono_step := linked_subset_certifiedStep E
  request_linked_step := request_mem_linked_certifiedStep E
  properLimit := intermediateLimitOfPrior E length hlength hBtarget
    hterminalB hstableB
  extends_properLimit := fullyExtends_intermediateLimitOfPrior E length
    hlength hBtarget hterminalB hstableB
  linked_properLimit := linked_subset_intermediateLimitOfPrior E length
    hlength hBtarget hterminalB hstableB

/-- Use the proper-limit compiler when the supplied history is coherent.
The fallback makes ordinal recursion total; the coherence theorem below
shows that it is never selected for the actual history. -/
noncomputable def limitOrSeed
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (o : Ordinal.{u}) (ho : IsSuccLimit o)
    (prior : ∀ a : Ordinal.{u}, a < o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) :
    TerminalResolutionState Gamma Y kappa T Z persistent B := by
  classical
  let family : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B :=
    fun a ↦ prior a.1 a.2
  exact if hoLength : o < R.length then
    if h : PriorCoherent o family then
      R.properLimit o hoLength ho family h
    else R.seed
  else R.seed

/-- The honest transfinite run.  Stage `a + 1` executes request `a`; a
proper limit retains eventual full blueprint edges through `properLimit`. -/
noncomputable def state
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  Ordinal.limitRecOn o R.seed
    (fun a S ↦ R.step S (request a))
    (fun o ho prior ↦ R.limitOrSeed o ho prior)

@[simp] theorem state_zero
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) :
    R.state request 0 = R.seed := by
  simp [state]

@[simp] theorem state_add_one
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    R.state request (o + 1) = R.step (R.state request o) (request o) := by
  simp [state]

theorem state_limit
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) (ho : IsSuccLimit o) :
    R.state request o = R.limitOrSeed o ho
      (fun a ha ↦ R.state request a) := by
  simpa [state] using
    (Ordinal.limitRecOn_limit o R.seed
      (fun a S ↦ R.step S (request a))
      (fun o ho prior ↦ R.limitOrSeed o ho prior) ho)

/-- Every earlier recursively produced state fully extends to every later
stage of the bounded run.  In the limit case this theorem supplies exactly
the coherence premise which selects the genuine proper-limit branch of
`limitOrSeed`. -/
theorem state_fullyExtends_below
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) :
    ∀ b, b < R.length → ∀ a, a ≤ b →
      (R.state request a).FullyExtends (R.state request b) := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact FullyExtends.refl _
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).1 hab
        rw [R.state_add_one request b]
        have hb : b < b + 1 := (Order.lt_add_one_iff).2 le_rfl
        exact (ih (hb.trans hbLength) a hab').trans
          (R.step_extends _ _)
      · exact FullyExtends.refl _
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b →
            TerminalResolutionState Gamma Y kappa T Z persistent B :=
          fun c ↦ R.state request c.1
        have hcoherent : PriorCoherent b prior := by
          intro c d hcd
          exact ih d.1 d.2 (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).FullyExtends
          (if h : PriorCoherent b prior then
            R.properLimit b hbLength hb prior h else R.seed)
        rw [dif_pos hcoherent]
        exact R.extends_properLimit b hbLength hb prior hcoherent ⟨a, hab⟩
      · exact FullyExtends.refl _

/-- The bookkeeping set is monotone throughout the same bounded run,
including genuine proper limits. -/
theorem state_linked_mono_below
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) :
    ∀ b, b < R.length → ∀ a, a ≤ b →
      (R.state request a).linked ⊆ (R.state request b).linked := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact Set.Subset.rfl
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).1 hab
        rw [R.state_add_one request b]
        have hb : b < b + 1 := (Order.lt_add_one_iff).2 le_rfl
        exact (ih (hb.trans hbLength) a hab').trans
          (R.linked_mono_step _ _)
      · exact Set.Subset.rfl
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b →
            TerminalResolutionState Gamma Y kappa T Z persistent B :=
          fun c ↦ R.state request c.1
        have hcoherent : PriorCoherent b prior := by
          intro c d hcd
          exact R.state_fullyExtends_below request d.1
            (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).linked ⊆
          (if h : PriorCoherent b prior then
            R.properLimit b hbLength hb prior h else R.seed).linked
        rw [dif_pos hcoherent]
        exact R.linked_properLimit b hbLength hb prior hcoherent ⟨a, hab⟩
      · exact Set.Subset.rfl

/-- At a genuine limit the fallback branch is definitionally absent. -/
theorem state_limit_eq_properLimit
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u})
    (hoLength : o < R.length) (ho : IsSuccLimit o) :
    R.state request o = R.properLimit o hoLength ho
      (fun a ↦ R.state request a.1) (by
        intro a b hab
        exact R.state_fullyExtends_below request b.1
          (b.2.trans hoLength) a.1 hab) := by
  classical
  let hcoherent : PriorCoherent o
      (fun a ↦ R.state request a.1) := by
    intro a b hab
    exact R.state_fullyExtends_below request b.1
      (b.2.trans hoLength) a.1 hab
  rw [R.state_limit request o ho]
  rw [limitOrSeed, dif_pos hoLength]
  change (if h : PriorCoherent o (fun a : Set.Iio o ↦
    R.state request a.1) then R.properLimit o hoLength ho _ h else R.seed) = _
  rw [dif_pos hcoherent]

/-! ## The cofinal all-real-terminal sweep -/

/-- The next lexicographic block contains every request strictly after the
current index.  The strict form is what leaves room for the successor stage
which actually executes the request. -/
theorem exists_strictly_later_repeatedRequest
    {X : Type u} [LinearOrder X]
    (i : RepeatedRequestIndex X) (x : X) :
    ∃ j, i < j ∧ repeatedRequest j = x := by
  let j : RepeatedRequestIndex X := toLex ((ofLex i).1 + 1, x)
  exact ⟨j, Prod.Lex.left _ _ (Nat.lt_succ_self (ofLex i).1), rfl⟩

/-- The ordinal length of the repeated lexicographic request order. -/
abbrev repeatedRequestLength (X : Type u) [LinearOrder X]
    [WellFoundedLT X] : Ordinal.{u} :=
  Ordinal.type (fun i j : RepeatedRequestIndex X ↦ i < j)

/-- There is still a successor stage after the rank of every repeated
request.  This uses the next occurrence of the same request, and is the key
reason for repeating the well-order in countably many blocks. -/
theorem typein_add_one_lt_repeatedRequestLength
    {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (i : RepeatedRequestIndex X) :
    Ordinal.typein (fun a b : RepeatedRequestIndex X ↦ a < b) i + 1 <
      repeatedRequestLength X := by
  obtain ⟨j, hij, _⟩ := exists_strictly_later_repeatedRequest i
    (repeatedRequest i)
  have hrank :
      Ordinal.typein (fun a b : RepeatedRequestIndex X ↦ a < b) i <
        Ordinal.typein (fun a b : RepeatedRequestIndex X ↦ a < b) j :=
    (Ordinal.typein_lt_typein _).2 hij
  exact ((add_one_le_iff).2 hrank).trans_lt
    (Ordinal.typein_lt_type _ j)

/-- Read the repeated request at an ordinal rank below the request order.
The fallback is used only to make the transfinite recursion total outside
its bounded run. -/
noncomputable def repeatedOrdinalRequest
    [LinearOrder Z] [WellFoundedLT Z]
    (fallback : V) (o : Ordinal.{u}) : V :=
  if h : o < repeatedRequestLength Z then
    (repeatedRequest
      (Ordinal.enum
        (fun a b : RepeatedRequestIndex Z ↦ a < b) ⟨o, h⟩) : Z)
  else fallback

@[simp] theorem repeatedOrdinalRequest_typein
    [LinearOrder Z] [WellFoundedLT Z]
    (fallback : V) (i : RepeatedRequestIndex Z) :
    repeatedOrdinalRequest (Z := Z) fallback
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) i) =
      (repeatedRequest i : Z) := by
  rw [repeatedOrdinalRequest, dif_pos (Ordinal.typein_lt_type _ i),
    Ordinal.enum_typein]

/-- The bounded honest recursion whose initial bookkeeping state has already
executed one real terminal.  That permanent linked request is used only for
indices at which the named request is neither terminal nor already
completed. -/
noncomputable def repeatedResolutionRecursor
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) :=
  ofSection9SchedulerEnvironment E (certifiedStep E seed u₀)
    (repeatedRequestLength Z) (by
      simpa only [repeatedRequestLength, Ordinal.card_type] using
        mk_repeatedRequestIndex_le E.infinite_cardinal hZ)
    hBtarget hterminalB hstableB

/-- The state immediately after executing a repeated request. -/
noncomputable def repeatedResolutionStage
    [LinearOrder Z] [WellFoundedLT Z]
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (fallback : V) (i : RepeatedRequestIndex Z) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  R.state (repeatedOrdinalRequest (Z := Z) fallback)
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)

/-- The successor states form an honest real-extension chain. -/
noncomputable def repeatedResolutionChain
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    ResolutionChain (RepeatedRequestIndex Z) (schedulerCompiler E)
      E.persistent_subset_slice := by
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  exact {
    stage := repeatedResolutionStage R u₀
    realExtends := by
      intro i j hij
      have hordinal :
          Ordinal.typein
              (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1 ≤
            Ordinal.typein
              (fun a b : RepeatedRequestIndex Z ↦ a < b) j + 1 := by
        simpa using
          ((Ordinal.add_le_add_iff_right 1).2
            ((Ordinal.typein_le_typein
              (fun a b : RepeatedRequestIndex Z ↦ a < b)).2
                (not_lt_of_ge hij)))
      exact (R.state_fullyExtends_below
        (repeatedOrdinalRequest (Z := Z) u₀) _
        (typein_add_one_lt_repeatedRequestLength j) _
        hordinal).realExtends }

/-- Full predecessor preservation of the recursion supplies the exact real
predecessor invariant required by the final relation limit. -/
def repeatedResolutionChainNoNewRealPredecessors
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    (repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
      hstableB).toRealExtensionChain.NoNewRealPredecessors := by
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  let request := repeatedOrdinalRequest (Z := Z) u₀
  refine ⟨?_⟩
  intro i j hij
  have hordinal :
      Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1 ≤
        Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) j + 1 :=
    by
      simpa using
        ((Ordinal.add_le_add_iff_right 1).2
          ((Ordinal.typein_le_typein
            (fun a b : RepeatedRequestIndex Z ↦ a < b)).2
              (not_lt_of_ge hij)))
  change ∀ {x y : V},
    x ∈ (R.state request
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)).blueprint.realPart.vertices →
    (y, x) ∈ (R.state request
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) j + 1)).blueprint.realPart.edges →
    (y, x) ∈ (R.state request
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)).blueprint.realPart.edges
  exact NoNewPredecessorsTo.toReal
    (R.state_fullyExtends_below request _
      (typein_add_one_lt_repeatedRequestLength j) _ hordinal
        |>.noNewPredecessors)

/-- Name the actual request when the pre-successor state can execute or
record it; otherwise name the permanently linked bootstrap request. -/
noncomputable def repeatedScheduled
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (i : RepeatedRequestIndex Z) : V := by
  classical
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  let pre := R.state (repeatedOrdinalRequest (Z := Z) u₀)
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i)
  let u : V := (repeatedRequest i : Z)
  exact if u ∈ pre.blueprint.realPart.terminals ∨
      pre.blueprint.RealLinksTo u B then u else u₀

theorem repeatedScheduled_mem_linked
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (i : RepeatedRequestIndex Z) :
    repeatedScheduled E seed u₀ hu₀ hZ hBtarget hterminalB hstableB i ∈
      ((repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB).stage i).linked := by
  classical
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  let request := repeatedOrdinalRequest (Z := Z) u₀
  let rank := Ordinal.typein
    (fun a b : RepeatedRequestIndex Z ↦ a < b) i
  let u : V := (repeatedRequest i : Z)
  by_cases hready : u ∈ (R.state request rank).blueprint.realPart.terminals ∨
      (R.state request rank).blueprint.RealLinksTo u B
  · change (if _ then u else u₀) ∈ _
    rw [if_pos hready]
    change u ∈ (R.state request (rank + 1)).linked
    rw [R.state_add_one request rank]
    have hrequest : request rank = u := by
      simpa only [request, rank, u] using
        repeatedOrdinalRequest_typein (Z := Z) u₀ i
    rw [hrequest]
    exact terminal_or_completed_mem_linked_certifiedStep E _ u hready
  · change (if _ then u else u₀) ∈ _
    rw [if_neg hready]
    have hu₀linked : u₀ ∈ R.seed.linked := by
      exact request_mem_linked_certifiedStep E seed u₀ hu₀
    have hmono := R.state_linked_mono_below request (rank + 1)
      (typein_add_one_lt_repeatedRequestLength i) 0 (bot_le)
    exact hmono (by simpa only [R.state_zero request] using hu₀linked)

theorem repeatedResolutionChain_seed_absorbed
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (i : RepeatedRequestIndex Z) :
    seed.blueprint.RealExtends
      ((repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB).stage i).blueprint B := by
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  let request := repeatedOrdinalRequest (Z := Z) u₀
  change seed.blueprint.RealExtends
    (R.state request
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)).blueprint B
  have hseed : seed.FullyExtends R.seed :=
    fullyExtends_certifiedStep E seed u₀
  have hrun := R.state_fullyExtends_below request
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)
    (typein_add_one_lt_repeatedRequestLength i) 0 (bot_le)
  exact realExtends_trans hseed.realExtends
    (by simpa only [R.state_zero request] using hrun.realExtends)

/-- Every real terminal appearing at any stage is named by a later
successful successor stage. -/
theorem repeatedResolutionChain_covers_stage_realTerminals
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (i : RepeatedRequestIndex Z) (x : V)
    (hx : x ∈
      ((repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB).stage i).blueprint.realPart.terminals) :
    ∃ j, repeatedScheduled E seed u₀ hu₀ hZ hBtarget hterminalB
      hstableB j = x := by
  classical
  let R := repeatedResolutionRecursor E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB
  let request := repeatedOrdinalRequest (Z := Z) u₀
  have hxvertex : x ∈
      ((repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB).stage i).blueprint.vertexSet := by
    simpa only [realPart_vertices] using hx.1
  have hxZ : x ∈ Z :=
    ((repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
      hstableB).stage i).isBlueprint.vertices_closed hxvertex
  let xZ : Z := ⟨x, hxZ⟩
  obtain ⟨j, hij, hjrequest⟩ :=
    exists_strictly_later_repeatedRequest i xZ
  have hord :
      Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1 ≤
        Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) j :=
    (add_one_le_iff).2
      ((Ordinal.typein_lt_typein _).2 hij)
  have hextends := R.state_fullyExtends_below request
    (Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) j)
    (Ordinal.typein_lt_type _ j)
    (Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)
    hord
  have hready : x ∈
      (R.state request
        (Ordinal.typein
          (fun a b : RepeatedRequestIndex Z ↦ a < b) j)).blueprint.realPart.terminals ∨
      (R.state request
        (Ordinal.typein
          (fun a b : RepeatedRequestIndex Z ↦ a < b) j)).blueprint.RealLinksTo x B := by
    apply realTerminal_or_realLinksTo_of_realExtends hextends.realExtends
    simpa only [repeatedResolutionChain, repeatedResolutionStage, R, request]
      using hx
  refine ⟨j, ?_⟩
  have hjvalue : (repeatedRequest j : Z).1 = x := by
    exact congrArg Subtype.val hjrequest
  simp only [repeatedScheduled]
  change (if (repeatedRequest j : Z).1 ∈
      (R.state request
        (Ordinal.typein
          (fun a b : RepeatedRequestIndex Z ↦ a < b) j)).blueprint.realPart.terminals ∨
      (R.state request
        (Ordinal.typein
          (fun a b : RepeatedRequestIndex Z ↦ a < b) j)).blueprint.RealLinksTo
            (repeatedRequest j : Z).1 B
    then (repeatedRequest j : Z).1 else u₀) = x
  rw [hjvalue, if_pos hready]

/-- The repeated transfinite run is the execution-only certificate consumed
by the final all-real relation limit. -/
noncomputable def successfulRepeatedResolutionEnumeration
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    ResolutionChain.SuccessfulResolutionEnumeration
      (repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB) seed where
  scheduled := repeatedScheduled E seed u₀ hu₀ hZ hBtarget hterminalB
    hstableB
  seed_absorbed := repeatedResolutionChain_seed_absorbed E seed u₀ hu₀ hZ
    hBtarget hterminalB hstableB
  scheduled_linked := repeatedScheduled_mem_linked E seed u₀ hu₀ hZ
    hBtarget hterminalB hstableB
  covers_stage_realTerminals :=
    repeatedResolutionChain_covers_stage_realTerminals E seed u₀ hu₀ hZ
      hBtarget hterminalB hstableB

/-- Normalization closes the final ray boundary, so the repeated successful
enumeration compiles to an honest fair all-real relation schedule. -/
noncomputable def fairRepeatedResolutionSchedule
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    ResolutionChain.FairRelationSchedule
      (repeatedResolutionChain E seed u₀ hu₀ hZ hBtarget hterminalB
        hstableB) seed := by
  have hu₀vertex : u₀ ∈ seed.blueprint.vertexSet := by
    simpa only [realPart_vertices] using hu₀.1
  letI : Nonempty Z :=
    ⟨⟨u₀, seed.isBlueprint.vertices_closed hu₀vertex⟩⟩
  exact ResolutionChain.FairRelationSchedule.ofSuccessfulEnumeration_of_normalized
    (repeatedResolutionChainNoNewRealPredecessors E seed u₀ hu₀ hZ
      hBtarget hterminalB hstableB)
    E.reference_warp E.infinite_cardinal
    (mk_repeatedRequestIndex_le E.infinite_cardinal hZ)
    E.normalized hBtarget hterminalB hstableB
    (successfulRepeatedResolutionEnumeration E seed u₀ hu₀ hZ hBtarget
      hterminalB hstableB)

/-- Forget the explicit ordinal recursion while retaining its fair final
relation-limit certificate. -/
noncomputable def fairRepeatedResolutionLimit
    [LinearOrder Z] [WellFoundedLT Z]
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    FairResolutionLimit (schedulerCompiler E) E.persistent_subset_slice seed :=
  (fairRepeatedResolutionSchedule E seed u₀ hu₀ hZ hBtarget hterminalB
    hstableB).toFairResolutionLimit

/-- Canonically well-order the closed carrier and run the fair scheduler.
No order on `Z` is part of the source-facing interface. -/
noncomputable def fairRepeatedResolutionLimit_of_choice
    (E : Section9SchedulerEnvironment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    FairResolutionLimit (schedulerCompiler E) E.persistent_subset_slice seed := by
  letI : LinearOrder Z := WellOrderingRel.isWellOrder.linearOrder
  letI : WellFoundedLT Z := ⟨WellOrderingRel.isWellOrder.wf⟩
  exact fairRepeatedResolutionLimit E seed u₀ hu₀ hZ hBtarget
    hterminalB hstableB

end ReachableResolutionRecursor

end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
