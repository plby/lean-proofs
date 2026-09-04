/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCertifiedScheduler
import ErdosProblems.Erdos599.HalfwayCompatibleIntermediateLimit
import ErdosProblems.Erdos599.FairRelationLimitCompatibility
import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# Compatible fixed-slice transfinite half-way scheduler

The imaginary-successor branch of Assertion 9.30 may replace an old
imaginary edge by a real path entering its old head.  Hence neither full nor
real predecessor preservation is a valid invariant of the published
construction.  This file repeats the reachable-state ordinal scheduler using
only the exact relation in Assertion 9.32, `RealExtends`.

At a proper limit, `RealExtends` alone does not exclude a reverse ray in the
eventual full-edge relation.  The missing assertion is therefore exposed as
`ProperLimitCompatibilityProvider`, indexed only by coherent histories which
can actually occur in the bounded recursion.  The final all-real union
similarly consumes an explicit `RelationLimitCore`.  No predecessor premise
is hidden in either compiler.

This module still uses the existing fixed-parameter scheduler state: every
stage is a linkage blueprint for the same `T`, `Z`, and `persistent`.  The
printed Assertion 9.34 advances from an alpha-blueprint to a beta-blueprint
for some strictly larger beta, hence changes the ladder slice.  Consequently
the final constructors below are unconditional only *relative to* the
fixed-slice refining successor compiler.  They must not be advertised as the
unconditional public half-way theorem until either a heterogeneous
ladder-indexed scheduler is supplied or a valid fixed-slice transport theorem
is proved.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace TerminalResolutionState

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

/-- The source-faithful composable transition invariant: (9.32) real
extension together with finite predecessor refinement.  Unlike full
predecessor preservation, refinement permits an old imaginary edge to be
replaced by a finite real path with the same head. -/
structure RefiningExtends
    (S U : TerminalResolutionState Gamma Y kappa T Z persistent B) : Prop where
  realExtends : S.blueprint.RealExtends U.blueprint B
  predecessorRefines : S.blueprint.PredecessorRefines U.blueprint

@[refl] theorem RefiningExtends.refl
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.RefiningExtends S where
  realExtends := realExtends_refl S.blueprint B
  predecessorRefines := PredecessorRefines.refl S.blueprint

@[trans] theorem RefiningExtends.trans
    {S U R : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (hSU : S.RefiningExtends U) (hUR : U.RefiningExtends R) :
    S.RefiningExtends R where
  realExtends := realExtends_trans hSU.realExtends hUR.realExtends
  predecessorRefines := PredecessorRefines.trans
    hSU.predecessorRefines hUR.predecessorRefines
      hSU.realExtends.1.1 hUR.realExtends.1.2

/-- Fixed-slice local 9.34 compiler on every real terminal, carrying the
finite predecessor-refinement certificate needed by the transfinite run. -/
def AllRealTerminalRefiningStable934Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          StableExtensionConclusion W U u T Z persistent B ∧
            W.PredecessorRefines U

/-- Projection to the older scheduled-slice compiler.  The artificial
`u ∈ T` argument is deliberately unused. -/
def AllRealTerminalRefiningStable934Compiler.toStable934Compiler
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B := by
  intro W u hW hpersistent hu _huT
  obtain ⟨U, hU, _⟩ := C W u hW hpersistent hu
  exact ⟨U, hU⟩

namespace RefiningSuccessor

noncomputable def advanceBlueprint
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    LinkageBlueprint Gamma Y kappa :=
  Classical.choose (C S.blueprint u S.isBlueprint hpersistent hu)

theorem advanceBlueprint_spec
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    StableExtensionConclusion S.blueprint
        (advanceBlueprint C hpersistent S u hu) u T Z persistent B ∧
      S.blueprint.PredecessorRefines
        (advanceBlueprint C hpersistent S u hu) :=
  Classical.choose_spec (C S.blueprint u S.isBlueprint hpersistent hu)

noncomputable def advance
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := advanceBlueprint C hpersistent S u hu
  isBlueprint := (advanceBlueprint_spec C hpersistent S u hu).1.1
  stable := (advanceBlueprint_spec C hpersistent S u hu).1.2.1
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (advanceBlueprint_spec C hpersistent S u hu).1.2.2.2.1
    · exact realLinksTo_mono
        (advanceBlueprint_spec C hpersistent S u hu).1.2.2.1.1
        (S.links x hx)

/-- Execute current real terminals, record already completed requests, and
otherwise mark time. -/
noncomputable def step
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    TerminalResolutionState Gamma Y kappa T Z persistent B := by
  classical
  exact if hu : u ∈ S.blueprint.realPart.terminals then
    advance C hpersistent S u hu
  else if hlinked : S.blueprint.RealLinksTo u B then
    recordLinked S u hlinked
  else S

theorem refiningExtends_step
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    S.RefiningExtends (step C hpersistent S u) := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simp only [step, hu, dite_true]
    exact {
      realExtends := (advanceBlueprint_spec C hpersistent S u hu).1.2.2.1
      predecessorRefines :=
        (advanceBlueprint_spec C hpersistent S u hu).2 }
  · simp only [step, hu, dite_false]
    by_cases hlinked : S.blueprint.RealLinksTo u B
    · simp only [hlinked, dite_true]
      exact {
        realExtends := realExtends_refl S.blueprint B
        predecessorRefines := PredecessorRefines.refl S.blueprint }
    · simp only [hlinked, dite_false]
      exact RefiningExtends.refl S

theorem linked_subset_step
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V) :
    S.linked ⊆ (step C hpersistent S u).linked := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals
  · simpa [step, hu, advance] using Set.subset_insert u S.linked
  · by_cases hlinked : S.blueprint.RealLinksTo u B <;>
      simp [step, hu, hlinked, recordLinked]

theorem terminal_or_completed_mem_linked_step
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) (u : V)
    (hu : u ∈ S.blueprint.realPart.terminals ∨
      S.blueprint.RealLinksTo u B) :
    u ∈ (step C hpersistent S u).linked := by
  rcases hu with hu | hu
  · simp [step, hu, advance]
  · by_cases hterminal : u ∈ S.blueprint.realPart.terminals
    · simp [step, hterminal, advance]
    · simp [step, hterminal, hu, recordLinked]

end RefiningSuccessor

/-- The scheduler-facing part of the local Section 9 construction.  It is
deliberately stated only as a state transformer on certified states; a
concrete occurrence environment is adapted to it below. -/
structure CompatibleSchedulerSuccessor where
  compiler : Stable934Compiler
    (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B
  persistent_subset_slice : persistent ⊆ T
  step : TerminalResolutionState Gamma Y kappa T Z persistent B → V →
    TerminalResolutionState Gamma Y kappa T Z persistent B
  step_extends : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, S.RefiningExtends (step S u)
  linked_mono_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, S.linked ⊆ (step S u).linked
  request_linked_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u,
      u ∈ S.blueprint.realPart.terminals → u ∈ (step S u).linked
  terminal_or_completed_linked_step : ∀
      (S : TerminalResolutionState Gamma Y kappa T Z persistent B) u,
    (u ∈ S.blueprint.realPart.terminals ∨ S.blueprint.RealLinksTo u B) →
      u ∈ (step S u).linked

/-- Package a refining all-real-terminal compiler as the total state
successor consumed by the ordinal scheduler. -/
noncomputable def CompatibleSchedulerSuccessor.ofRefiningCompiler
    (C : AllRealTerminalRefiningStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hpersistent : persistent ⊆ T) :
    CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) where
  compiler := C.toStable934Compiler
  persistent_subset_slice := hpersistent
  step := RefiningSuccessor.step C hpersistent
  step_extends := RefiningSuccessor.refiningExtends_step C hpersistent
  linked_mono_step := RefiningSuccessor.linked_subset_step C hpersistent
  request_linked_step := by
    intro S u hu
    exact RefiningSuccessor.terminal_or_completed_mem_linked_step
      C hpersistent S u (Or.inl hu)
  terminal_or_completed_linked_step :=
    RefiningSuccessor.terminal_or_completed_mem_linked_step C hpersistent

/-- Coherence of a reachable history in precisely the source's (9.32)
extension relation. -/
def CompatiblePriorCoherent (o : Ordinal.{u})
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) : Prop :=
  ∀ a b, a ≤ b → (prior a).RefiningExtends (prior b)

/-- A coherent proper initial history, viewed as the real-extension chain
used by the source-faithful compatible limit compiler. -/
def compatiblePriorRealExtensionChain
    {o : Ordinal.{u}}
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : CompatiblePriorCoherent o prior) :
    RealExtensionChain o.ToType Gamma Y kappa T Z persistent B where
  stage := fun a ↦ (prior (Ordinal.ToType.toOrd a)).blueprint
  isBlueprint := fun a ↦ (prior (Ordinal.ToType.toOrd a)).isBlueprint
  stable := fun a ↦ (prior (Ordinal.ToType.toOrd a)).stable
  realExtends := by
    intro a b hab
    exact (hcoherent _ _ (Ordinal.ToType.mk.symm.monotone hab)).realExtends

/-- Refinement coherence of the chain extracted from a reachable history. -/
def compatiblePriorChainPredecessorRefinement
    {o : Ordinal.{u}}
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : CompatiblePriorCoherent o prior) :
    (compatiblePriorRealExtensionChain prior hcoherent)
      |>.PredecessorRefinement where
  of_le := by
    intro a b hab
    exact (hcoherent _ _
      (Ordinal.ToType.mk.symm.monotone hab)).predecessorRefines

/-- The exact extra datum needed at every nonfinal limit of a bounded run.
It is required only for coherent histories that the recursion can reach. -/
def ProperLimitCompatibilityProvider (length : Ordinal.{u}) : Prop :=
  ∀ (o : Ordinal.{u}), o < length → IsSuccLimit o →
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) →
    (hcoherent : CompatiblePriorCoherent o prior) →
      (compatiblePriorRealExtensionChain prior hcoherent)
        |>.EventualRelationLimitCompatibility

/-- Predecessor refinement canonically supplies compatibility at every
proper limit; no separate reverse-ray oracle remains in the scheduler. -/
def properLimitCompatibilityProvider_of_refinement
    (length : Ordinal.{u}) :
    ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) length := by
  intro o _hoLength ho prior hcoherent
  let : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  exact
    RealExtensionChain.EventualRelationLimitCompatibility.ofPredecessorRefinement
      (C := compatiblePriorRealExtensionChain prior hcoherent)
      (compatiblePriorChainPredecessorRefinement prior hcoherent)

/-- The genuine nonfinal 9.33 state for a coherent reachable history and
its direct reverse-ray compatibility certificate. -/
noncomputable def compatibleIntermediateLimitOfPrior
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) length)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : CompatiblePriorCoherent o prior) :
    TerminalResolutionState Gamma Y kappa T Z persistent B := by
  letI : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  let C := compatiblePriorRealExtensionChain prior hcoherent
  let H : C.EventualRelationLimitCompatibility :=
    K o hoLength ho prior hcoherent
  have hindex : #o.ToType ≤ kappa := by
    rw [Cardinal.mk_toType]
    exact (Ordinal.card_le_card hoLength.le).trans hlength
  let D : C.EventualRelationLimitBoundary :=
    C.eventualRelationLimitBoundary_of_normalized_index hGamma
      hBtarget hkappa hindex
  exact
    { blueprint := C.compatibleEventualRelationLimit H
      isBlueprint := C.compatibleEventualRelationLimit_isLinkageBlueprint H
        hYwarp hterminalB D
      stable := C.compatibleEventualRelationLimit_stable H hstableB
      linked := ⋃ i : o.ToType, (prior (Ordinal.ToType.toOrd i)).linked
      links := by
        intro x hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
        exact realLinksTo_mono
          (C.realPart_extends_compatibleEventualRelationLimit H i)
          ((prior (Ordinal.ToType.toOrd i)).links x hxi) }

theorem realExtends_compatibleIntermediateLimitOfPrior
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) length)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : CompatiblePriorCoherent o prior) (a : Set.Iio o) :
    (prior a).RefiningExtends
      (compatibleIntermediateLimitOfPrior hYwarp hGamma hkappa length hlength
        hBtarget hterminalB hstableB K o hoLength ho prior hcoherent) := by
  let : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  let C := compatiblePriorRealExtensionChain prior hcoherent
  let H : C.EventualRelationLimitCompatibility :=
    K o hoLength ho prior hcoherent
  let i : o.ToType := Ordinal.ToType.mk a
  have hi : Ordinal.ToType.toOrd i = a := by simp [i]
  change (prior a).RefiningExtends _
  rw [← hi]
  exact {
    realExtends := C.realExtends_compatibleEventualRelationLimit H i
    predecessorRefines :=
      C.predecessorRefines_compatibleEventualRelationLimit
        (compatiblePriorChainPredecessorRefinement prior hcoherent) H i }

theorem linked_subset_compatibleIntermediateLimitOfPrior
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) length)
    (o : Ordinal.{u}) (hoLength : o < length) (ho : IsSuccLimit o)
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hcoherent : CompatiblePriorCoherent o prior) (a : Set.Iio o) :
    (prior a).linked ⊆
      (compatibleIntermediateLimitOfPrior hYwarp hGamma hkappa length hlength
        hBtarget hterminalB hstableB K o hoLength ho prior hcoherent).linked := by
  intro x hx
  change x ∈ ⋃ i : o.ToType, (prior (Ordinal.ToType.toOrd i)).linked
  let i : o.ToType := Ordinal.ToType.mk a
  have hi : Ordinal.ToType.toOrd i = a := by simp [i]
  exact Set.mem_iUnion.2 ⟨i, hi ▸ hx⟩

/-- A bounded reachable-state recursor whose sole coherence relation is
`RealExtends`. -/
structure CompatibleReachableResolutionRecursor where
  length : Ordinal.{u}
  seed : TerminalResolutionState Gamma Y kappa T Z persistent B
  step : TerminalResolutionState Gamma Y kappa T Z persistent B → V →
    TerminalResolutionState Gamma Y kappa T Z persistent B
  step_extends : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, S.RefiningExtends (step S u)
  linked_mono_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u, S.linked ⊆ (step S u).linked
  request_linked_step : ∀ (S : TerminalResolutionState Gamma Y kappa
      T Z persistent B) u,
    u ∈ S.blueprint.realPart.terminals → u ∈ (step S u).linked
  properLimit : ∀ (o : Ordinal.{u}), o < length → IsSuccLimit o →
    (prior : Set.Iio o →
      TerminalResolutionState Gamma Y kappa T Z persistent B) →
    CompatiblePriorCoherent o prior →
      TerminalResolutionState Gamma Y kappa T Z persistent B
  extends_properLimit : ∀ o (hoLength : o < length) (ho : IsSuccLimit o)
      (prior : Set.Iio o →
        TerminalResolutionState Gamma Y kappa T Z persistent B)
      (hcoherent : CompatiblePriorCoherent o prior) (a : Set.Iio o),
    (prior a).RefiningExtends
      (properLimit o hoLength ho prior hcoherent)
  linked_properLimit : ∀ o (hoLength : o < length) (ho : IsSuccLimit o)
      (prior : Set.Iio o →
        TerminalResolutionState Gamma Y kappa T Z persistent B)
      (hcoherent : CompatiblePriorCoherent o prior) (a : Set.Iio o),
    (prior a).linked ⊆
      (properLimit o hoLength ho prior hcoherent).linked

namespace CompatibleReachableResolutionRecursor

/-- Assemble the bounded recursor from a reachable successor and the honest
proper-limit reverse-ray provider. -/
noncomputable def ofSuccessor
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa)
    (length : Ordinal.{u}) (hlength : length.card ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) length) :
    CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) where
  length := length
  seed := seed
  step := S.step
  step_extends := S.step_extends
  linked_mono_step := S.linked_mono_step
  request_linked_step := S.request_linked_step
  properLimit := compatibleIntermediateLimitOfPrior hYwarp hGamma hkappa
    length hlength hBtarget hterminalB hstableB K
  extends_properLimit :=
    realExtends_compatibleIntermediateLimitOfPrior hYwarp hGamma hkappa
      length hlength hBtarget hterminalB hstableB K
  linked_properLimit :=
    linked_subset_compatibleIntermediateLimitOfPrior hYwarp hGamma hkappa
      length hlength hBtarget hterminalB hstableB K

/-- Use the proper-limit compiler when the supplied history is coherent.
The fallback makes ordinal recursion total and is absent from the actual
bounded run. -/
noncomputable def limitOrSeed
    (R : CompatibleReachableResolutionRecursor
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
    if h : CompatiblePriorCoherent o family then
      R.properLimit o hoLength ho family h
    else R.seed
  else R.seed

/-- The honest transfinite run. -/
noncomputable def state
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  Ordinal.limitRecOn o R.seed
    (fun a state ↦ R.step state (request a))
    (fun o ho prior ↦ R.limitOrSeed o ho prior)

@[simp] theorem state_zero
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) :
    R.state request 0 = R.seed := by
  simp [state]

@[simp] theorem state_add_one
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    R.state request (o + 1) = R.step (R.state request o) (request o) := by
  simp [state]

theorem state_limit
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) (ho : IsSuccLimit o) :
    R.state request o = R.limitOrSeed o ho
      (fun a ha ↦ R.state request a) := by
  simpa [state] using
    (Ordinal.limitRecOn_limit o R.seed
      (fun a state ↦ R.step state (request a))
      (fun o ho prior ↦ R.limitOrSeed o ho prior) ho)

/-- Every earlier recursively produced state really extends to every later
state of the bounded run. -/
theorem state_realExtends_below
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (request : Ordinal.{u} → V) :
    ∀ b, b < R.length → ∀ a, a ≤ b →
      (R.state request a).RefiningExtends (R.state request b) := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact RefiningExtends.refl _
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).1 hab
        rw [R.state_add_one request b]
        have hb : b < b + 1 := (Order.lt_add_one_iff).2 le_rfl
        exact (ih (hb.trans hbLength) a hab').trans
          (R.step_extends _ _)
      · exact RefiningExtends.refl _
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b →
            TerminalResolutionState Gamma Y kappa T Z persistent B :=
          fun c ↦ R.state request c.1
        have hcoherent : CompatiblePriorCoherent b prior := by
          intro c d hcd
          exact ih d.1 d.2 (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).RefiningExtends
          (if h : CompatiblePriorCoherent b prior then
            R.properLimit b hbLength hb prior h else R.seed)
        rw [dif_pos hcoherent]
        exact R.extends_properLimit b hbLength hb prior hcoherent ⟨a, hab⟩
      · exact RefiningExtends.refl _

/-- The bookkeeping set is monotone through successors and proper limits. -/
theorem state_linked_mono_below
    (R : CompatibleReachableResolutionRecursor
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
        have hcoherent : CompatiblePriorCoherent b prior := by
          intro c d hcd
          exact R.state_realExtends_below request d.1
            (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).linked ⊆
          (if h : CompatiblePriorCoherent b prior then
            R.properLimit b hbLength hb prior h else R.seed).linked
        rw [dif_pos hcoherent]
        exact R.linked_properLimit b hbLength hb prior hcoherent ⟨a, hab⟩
      · exact Set.Subset.rfl

/-! ## Cofinal repeated-request sweep -/

/-- The bounded compatible recursion, bootstrapped by executing one real
terminal before the cofinal repeated-request sweep. -/
noncomputable def repeatedRecursor
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z)) :
    CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B) :=
  ofSuccessor S (S.step seed u₀) hYwarp hGamma hkappa
    (ReachableResolutionRecursor.repeatedRequestLength Z) (by
      simpa only [ReachableResolutionRecursor.repeatedRequestLength,
        Ordinal.card_type] using
        mk_repeatedRequestIndex_le hkappa hZ)
    hBtarget hterminalB hstableB K

/-- The successor state immediately after one repeated request. -/
noncomputable def repeatedStage
    [LinearOrder Z] [WellFoundedLT Z]
    (R : CompatibleReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (fallback : V) (i : RepeatedRequestIndex Z) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  R.state
    (ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Z) fallback)
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)

/-- The successor states form an honest real-extension chain. -/
noncomputable def repeatedChain
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z)) :
    ResolutionChain (RepeatedRequestIndex Z) S.compiler
      S.persistent_subset_slice := by
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  exact {
    stage := repeatedStage R u₀
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
      exact (R.state_realExtends_below
        (ReachableResolutionRecursor.repeatedOrdinalRequest
          (Z := Z) u₀) _
        (ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength j)
        _ hordinal).realExtends }

/-- The repeated successor chain inherits predecessor refinement from the
reachable-state recursion. -/
def repeatedChainPredecessorRefinement
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z)) :
    (repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K).toRealExtensionChain
        |>.PredecessorRefinement := by
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
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
  exact (R.state_realExtends_below
    (ReachableResolutionRecursor.repeatedOrdinalRequest (Z := Z) u₀) _
    (ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength j)
    _ hordinal).predecessorRefines

/-- Name the actual request when the pre-successor state can execute or
record it; otherwise name the permanently linked bootstrap request. -/
noncomputable def repeatedScheduled
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z))
    (i : RepeatedRequestIndex Z) : V := by
  classical
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  let pre := R.state
    (ReachableResolutionRecursor.repeatedOrdinalRequest (Z := Z) u₀)
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i)
  let u : V := (repeatedRequest i : Z)
  exact if u ∈ pre.blueprint.realPart.terminals ∨
      pre.blueprint.RealLinksTo u B then u else u₀

theorem repeatedScheduled_mem_linked
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z))
    (i : RepeatedRequestIndex Z) :
    repeatedScheduled S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K i ∈
      ((repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K).stage i).linked := by
  classical
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  let request := ReachableResolutionRecursor.repeatedOrdinalRequest
    (Z := Z) u₀
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
        ReachableResolutionRecursor.repeatedOrdinalRequest_typein
          (Z := Z) u₀ i
    rw [hrequest]
    exact S.terminal_or_completed_linked_step _ u hready
  · change (if _ then u else u₀) ∈ _
    rw [if_neg hready]
    have hu₀linked : u₀ ∈ R.seed.linked :=
      S.request_linked_step seed u₀ hu₀
    have hmono := R.state_linked_mono_below request (rank + 1)
      (ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength i)
      0 bot_le
    exact hmono (by simpa only [R.state_zero request] using hu₀linked)

theorem repeatedChain_seed_absorbed
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z))
    (i : RepeatedRequestIndex Z) :
    seed.blueprint.RealExtends
      ((repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K).stage i).blueprint B := by
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  let request := ReachableResolutionRecursor.repeatedOrdinalRequest
    (Z := Z) u₀
  change seed.blueprint.RealExtends
    (R.state request
      (Ordinal.typein
        (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)).blueprint B
  have hseed : seed.blueprint.RealExtends R.seed.blueprint B :=
    (S.step_extends seed u₀).realExtends
  have hrun := R.state_realExtends_below request
    (Ordinal.typein
      (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1)
    (ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength i)
    0 bot_le
  exact realExtends_trans hseed
    (by simpa only [R.state_zero request] using hrun.realExtends)

/-- Every real terminal appearing at any stage is named by a later
successful successor stage. -/
theorem repeatedChain_covers_stage_realTerminals
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z))
    (i : RepeatedRequestIndex Z) (x : V)
    (hx : x ∈
      ((repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K).stage i).blueprint.realPart.terminals) :
    ∃ j, repeatedScheduled S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K j = x := by
  classical
  let R := repeatedRecursor S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  let request := ReachableResolutionRecursor.repeatedOrdinalRequest
    (Z := Z) u₀
  have hxvertex : x ∈
      ((repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K).stage i).blueprint.vertexSet := by
    simpa only [realPart_vertices] using hx.1
  have hxZ : x ∈ Z :=
    ((repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K).stage i).isBlueprint.vertices_closed
        hxvertex
  let xZ : Z := ⟨x, hxZ⟩
  obtain ⟨j, hij, hjrequest⟩ :=
    ReachableResolutionRecursor.exists_strictly_later_repeatedRequest i xZ
  have hord :
      Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) i + 1 ≤
        Ordinal.typein (fun a b : RepeatedRequestIndex Z ↦ a < b) j :=
    (add_one_le_iff).2 ((Ordinal.typein_lt_typein _).2 hij)
  have hextends := R.state_realExtends_below request
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
    simpa only [repeatedChain, repeatedStage, R, request] using hx
  refine ⟨j, ?_⟩
  have hjvalue : (repeatedRequest j : Z).1 = x :=
    congrArg Subtype.val hjrequest
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

/-- The execution certificate consumed by the final honest all-real
relation-limit compiler. -/
noncomputable def successfulRepeatedEnumeration
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z)) :
    ResolutionChain.SuccessfulResolutionEnumeration
      (repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
        hBtarget hterminalB hstableB K) seed where
  scheduled := repeatedScheduled S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  seed_absorbed := repeatedChain_seed_absorbed S seed u₀ hu₀ hYwarp
    hGamma hkappa hZ hBtarget hterminalB hstableB K
  scheduled_linked := repeatedScheduled_mem_linked S seed u₀ hu₀ hYwarp
    hGamma hkappa hZ hBtarget hterminalB hstableB K
  covers_stage_realTerminals :=
    repeatedChain_covers_stage_realTerminals S seed u₀ hu₀ hYwarp hGamma
      hkappa hZ hBtarget hterminalB hstableB K

/-- A fair final relation-limit certificate.  All scheduler and boundary
fields are derived; `H` is exactly the remaining final reverse-ray
compatibility datum. -/
noncomputable def fairRepeatedLimit
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z))
    (H : (repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K).toRealExtensionChain.RelationLimitCore) :
    FairResolutionLimit S.compiler S.persistent_subset_slice seed := by
  have hu₀vertex : u₀ ∈ seed.blueprint.vertexSet := by
    simpa only [realPart_vertices] using hu₀.1
  letI : Nonempty Z :=
    ⟨⟨u₀, seed.isBlueprint.vertices_closed hu₀vertex⟩⟩
  exact ResolutionChain.FairResolutionLimit.ofSuccessfulEnumeration_of_normalizedCore
    H hYwarp hkappa
    (mk_repeatedRequestIndex_le hkappa hZ) hGamma hBtarget hterminalB
    hstableB
    (successfulRepeatedEnumeration S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K)

/-- Predecessor refinement supplies the final all-real relation core, so the
fair limit has no independent reverse-ray premise. -/
noncomputable def fairRepeatedLimit_of_refinement
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (K : ProperLimitCompatibilityProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B)
      (ReachableResolutionRecursor.repeatedRequestLength Z)) :
    FairResolutionLimit S.compiler S.persistent_subset_slice seed := by
  have hu₀vertex : u₀ ∈ seed.blueprint.vertexSet := by
    simpa only [realPart_vertices] using hu₀.1
  letI : Nonempty Z :=
    ⟨⟨u₀, seed.isBlueprint.vertices_closed hu₀vertex⟩⟩
  let C := repeatedChain S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB K
  let H : C.toRealExtensionChain.PredecessorRefinement :=
    repeatedChainPredecessorRefinement S seed u₀ hu₀ hYwarp hGamma hkappa hZ
      hBtarget hterminalB hstableB K
  exact fairRepeatedLimit S seed u₀ hu₀ hYwarp hGamma hkappa hZ hBtarget
    hterminalB hstableB K
      (C.toRealExtensionChain.relationLimitCore_of_predecessorRefinement H)

/-- Canonical fixed-slice fair scheduler: predecessor refinement derives
both every proper-limit compatibility record and the final relation core. -/
noncomputable def fairRepeatedLimit_of_refiningSuccessor
    [LinearOrder Z] [WellFoundedLT Z]
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    FairResolutionLimit S.compiler S.persistent_subset_slice seed :=
  fairRepeatedLimit_of_refinement S seed u₀ hu₀ hYwarp hGamma hkappa hZ
    hBtarget hterminalB hstableB
      (properLimitCompatibilityProvider_of_refinement
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (T := T) (Z := Z) (persistent := persistent) (B := B)
        (ReachableResolutionRecursor.repeatedRequestLength Z))

/-- Choose a well-order on the closed carrier; no order is part of the
source-facing interface. -/
noncomputable def fairRepeatedLimit_of_refiningSuccessorChoice
    (S : CompatibleSchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (T := T) (Z := Z) (persistent := persistent) (B := B))
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa) (hZ : #Z ≤ kappa)
    (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent) :
    FairResolutionLimit S.compiler S.persistent_subset_slice seed := by
  letI : LinearOrder Z := WellOrderingRel.isWellOrder.linearOrder
  letI : WellFoundedLT Z := ⟨WellOrderingRel.isWellOrder.wf⟩
  exact fairRepeatedLimit_of_refiningSuccessor S seed u₀ hu₀ hYwarp hGamma
    hkappa hZ hBtarget hterminalB hstableB

end CompatibleReachableResolutionRecursor
end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
