/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySchedulerConstruction
import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# Scheduler adapter for source-faithful compatible proper limits

This is the scheduler-state wrapper around
`compatibleEventualRelationLimit`.  Its input stores direct reverse-ray
exclusion rather than the false full predecessor-preservation invariant.
The resulting state carries the exact real-extension and linked-request
conclusions required at a proper limit.  It intentionally exports no
predecessor-preservation conclusion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace TerminalResolutionState

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}
variable {I : Type u} [LinearOrder I] [Nonempty I]
variable {compiler : Stable934Compiler
  (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B}
variable {hpersistent : persistent ⊆ T}

/-- Scheduler-facing proper-limit input with the exact direct
well-foundedness boundary. -/
structure CompatibleIntermediateLimitData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  compatibility :
    C.toRealExtensionChain.EventualRelationLimitCompatibility
  reference_isWarp : Gamma.IsWarp Y
  target_boundary : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_target : B ∩ T ⊆ persistent
  relation_boundary :
    C.toRealExtensionChain.EventualRelationLimitBoundary

/-- Normalized proper-limit data.  The strong-ray boundary is derived from
normalization; reverse-ray exclusion remains explicit because it does not
follow from `RealExtends` at an arbitrary proper limit. -/
structure NormalizedCompatibleIntermediateLimitData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  compatibility :
    C.toRealExtensionChain.EventualRelationLimitCompatibility
  reference_isWarp : Gamma.IsWarp Y
  normalized : Gamma.IsNormalized
  completion_target : B ⊆ Gamma.target
  target_boundary : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_target : B ∩ T ⊆ persistent
  kappa_infinite : aleph0 ≤ kappa
  index_small : #I ≤ kappa

def NormalizedCompatibleIntermediateLimitData.toCompatibleData
    {C : ResolutionChain I compiler hpersistent}
    (D : NormalizedCompatibleIntermediateLimitData C) :
    CompatibleIntermediateLimitData C where
  compatibility := D.compatibility
  reference_isWarp := D.reference_isWarp
  target_boundary := D.target_boundary
  stable_target := D.stable_target
  relation_boundary :=
    C.toRealExtensionChain.eventualRelationLimitBoundary_of_normalized_index
      D.normalized D.completion_target D.kappa_infinite D.index_small

/-- Countable boundedness discharges reverse-ray exclusion as well as the
strong-ray boundary. -/
def compatibleIntermediateLimitData_of_countablyBounded
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.CountablyBounded)
    (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (hcard : #C.toRealExtensionChain.realVertexLimit ≤ kappa) :
    CompatibleIntermediateLimitData C where
  compatibility :=
    RealExtensionChain.EventualRelationLimitCompatibility.ofCountablyBounded
      C.toRealExtensionChain H
  reference_isWarp := hYwarp
  target_boundary := hB
  stable_target := hstableB
  relation_boundary :=
    RealExtensionChain.EventualRelationLimitBoundary.ofCountablyBounded
      C.toRealExtensionChain H hcard

/-- A predecessor-refining chain supplies the compatibility field, while
the remaining blueprint boundary is kept explicit. -/
def compatibleIntermediateLimitData_of_refinement
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.PredecessorRefinement)
    (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (D : C.toRealExtensionChain.EventualRelationLimitBoundary) :
    CompatibleIntermediateLimitData C where
  compatibility :=
    RealExtensionChain.EventualRelationLimitCompatibility.ofPredecessorRefinement
      C.toRealExtensionChain H
  reference_isWarp := hYwarp
  target_boundary := hB
  stable_target := hstableB
  relation_boundary := D

/-- In the normalized setting predecessor refinement supplies the only
remaining infinitary compatibility field; the strong-ray boundary is then
derived automatically by `toCompatibleData`. -/
def normalizedCompatibleIntermediateLimitData_of_refinement
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.PredecessorRefinement)
    (hYwarp : Gamma.IsWarp Y) (hGamma : Gamma.IsNormalized)
    (hBtarget : B ⊆ Gamma.target)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (hkappa : aleph0 ≤ kappa) (hindex : #I ≤ kappa) :
    NormalizedCompatibleIntermediateLimitData C where
  compatibility :=
    RealExtensionChain.EventualRelationLimitCompatibility.ofPredecessorRefinement
      C.toRealExtensionChain H
  reference_isWarp := hYwarp
  normalized := hGamma
  completion_target := hBtarget
  target_boundary := hB
  stable_target := hstableB
  kappa_infinite := hkappa
  index_small := hindex

/-- The actual scheduler state at a source-faithful compatible proper
limit. -/
noncomputable def compatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := C.toRealExtensionChain.compatibleEventualRelationLimit
    D.compatibility
  isBlueprint :=
    C.toRealExtensionChain
      |>.compatibleEventualRelationLimit_isLinkageBlueprint
        D.compatibility D.reference_isWarp D.target_boundary
          D.relation_boundary
  stable :=
    C.toRealExtensionChain.compatibleEventualRelationLimit_stable
      D.compatibility D.stable_target
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toRealExtensionChain
        |>.realPart_extends_compatibleEventualRelationLimit
          D.compatibility i)
      ((C.stage i).links x hxi)

noncomputable def normalizedCompatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedCompatibleIntermediateLimitData C) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  compatibleIntermediateLimitState C D.toCompatibleData

@[simp] theorem compatibleIntermediateLimitState_blueprint
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) :
    (compatibleIntermediateLimitState C D).blueprint =
      C.toRealExtensionChain.compatibleEventualRelationLimit
        D.compatibility :=
  rfl

@[simp] theorem compatibleIntermediateLimitState_linked
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) :
    (compatibleIntermediateLimitState C D).linked =
      ⋃ i, (C.stage i).linked :=
  rfl

/-- Every earlier state is related to the compatible limit by the exact
9.32 real-extension relation. -/
theorem realExtends_compatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.RealExtends
      (compatibleIntermediateLimitState C D).blueprint B := by
  change (C.toRealExtensionChain.stage i).RealExtends
    (C.toRealExtensionChain.compatibleEventualRelationLimit
      D.compatibility) B
  exact C.toRealExtensionChain
    |>.realExtends_compatibleEventualRelationLimit D.compatibility i

theorem linked_subset_compatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) (i : I) :
    (C.stage i).linked ⊆
      (compatibleIntermediateLimitState C D).linked :=
  Set.subset_iUnion (fun j ↦ (C.stage j).linked) i

/-- The source-faithful predecessor-refinement invariant passes from every
earlier stage to the bundled proper-limit state. -/
theorem predecessorRefines_compatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.PredecessorRefinement)
    (D : CompatibleIntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.PredecessorRefines
      (compatibleIntermediateLimitState C D).blueprint := by
  change (C.toRealExtensionChain.stage i).PredecessorRefines
    (C.toRealExtensionChain.compatibleEventualRelationLimit
      D.compatibility)
  exact C.toRealExtensionChain
    |>.predecessorRefines_compatibleEventualRelationLimit
      H D.compatibility i

/-- Scheduler-state form of the source-faithful proper-limit conclusion. -/
theorem stableLimitConclusion_compatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : CompatibleIntermediateLimitData C) :
    StableLimitConclusion (fun i ↦ (C.stage i).blueprint)
      (compatibleIntermediateLimitState C D).blueprint
        T Z persistent B := by
  simpa only [compatibleIntermediateLimitState_blueprint,
    ResolutionChain.toRealExtensionChain] using
    C.toRealExtensionChain
      |>.stableLimitConclusion_compatibleEventualRelationLimit
        D.compatibility D.reference_isWarp D.target_boundary
          D.stable_target D.relation_boundary

theorem realExtends_normalizedCompatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedCompatibleIntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.RealExtends
      (normalizedCompatibleIntermediateLimitState C D).blueprint B :=
  realExtends_compatibleIntermediateLimitState C D.toCompatibleData i

theorem linked_subset_normalizedCompatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedCompatibleIntermediateLimitData C) (i : I) :
    (C.stage i).linked ⊆
      (normalizedCompatibleIntermediateLimitState C D).linked :=
  linked_subset_compatibleIntermediateLimitState C D.toCompatibleData i

theorem stableLimitConclusion_normalizedCompatibleIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedCompatibleIntermediateLimitData C) :
    StableLimitConclusion (fun i ↦ (C.stage i).blueprint)
      (normalizedCompatibleIntermediateLimitState C D).blueprint
        T Z persistent B :=
  stableLimitConclusion_compatibleIntermediateLimitState
    C D.toCompatibleData

end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
