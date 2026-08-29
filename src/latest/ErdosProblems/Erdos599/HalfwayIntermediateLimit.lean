/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySchedulerConstruction
import ErdosProblems.Erdos599.IntermediateRelationLimitRay

/-!
# Scheduler-state adapter for proper half-way limits

This file packages the eventual full-edge limit as an actual
`TerminalResolutionState`.  It is deliberately downstream of
`HalfwaySchedulerConstruction`: the core 9.33 construction remains usable
without depending on scheduler state, while a transfinite scheduler can use
the bundled state directly at each nonfinal limit ordinal.
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

/-- The scheduler-facing boundary input at a proper limit.  All other
blueprint and stability fields are derived by `IntermediateRelationLimit`. -/
structure IntermediateLimitData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  noNewPredecessors : C.toRealExtensionChain.NoNewPredecessors
  reference_isWarp : Gamma.IsWarp Y
  target_boundary : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_target : B ∩ T ⊆ persistent
  relation_boundary :
    C.toRealExtensionChain.EventualRelationLimitBoundary

/-- The cardinal field of an intermediate boundary is automatic when the
proper initial segment has cardinality at most `kappa`. -/
def intermediateRelationBoundary_of_ray
    (C : ResolutionChain I compiler hpersistent)
    (hkappa : aleph0 ≤ kappa) (hindex : #I ≤ kappa)
    (hray : ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.toRealExtensionChain.eventualEdgeLimit →
        (strongEdgeIndices r).Infinite) :
    C.toRealExtensionChain.EventualRelationLimitBoundary where
  card_vertices :=
    C.toRealExtensionChain.mk_realVertexLimit_le hkappa hindex
  every_relation_ray_strong := hray

/-- Scheduler-facing proper-limit input in the normalized situation of
Erdos--Menger.  In contrast to `IntermediateLimitData`, this record contains
no raw infinitary ray premise: normalization and the target inclusion force
that condition. -/
structure NormalizedIntermediateLimitData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  noNewPredecessors : C.toRealExtensionChain.NoNewPredecessors
  reference_isWarp : Gamma.IsWarp Y
  normalized : Gamma.IsNormalized
  completion_target : B ⊆ Gamma.target
  target_boundary : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_target : B ∩ T ⊆ persistent
  kappa_infinite : aleph0 ≤ kappa
  index_small : #I ≤ kappa

/-- Compile normalized scheduler invariants to the general proper-limit
input.  The relation-ray field is the theorem proved in
`IntermediateRelationLimitRay`. -/
def NormalizedIntermediateLimitData.toIntermediateLimitData
    {C : ResolutionChain I compiler hpersistent}
    (D : NormalizedIntermediateLimitData C) : IntermediateLimitData C where
  noNewPredecessors := D.noNewPredecessors
  reference_isWarp := D.reference_isWarp
  target_boundary := D.target_boundary
  stable_target := D.stable_target
  relation_boundary :=
    C.toRealExtensionChain.eventualRelationLimitBoundary_of_normalized_index
      D.normalized D.completion_target D.kappa_infinite D.index_small

/-- The actual scheduler state at a nonfinal limit ordinal.  Previously
linked requests are unioned; their real target paths transport into the
exact real-edge union carried by the proper limit. -/
noncomputable def intermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := C.toRealExtensionChain.eventualRelationLimit
    D.noNewPredecessors
  isBlueprint :=
    C.toRealExtensionChain.eventualRelationLimit_isLinkageBlueprint
      D.noNewPredecessors D.reference_isWarp D.target_boundary
      D.relation_boundary
  stable :=
    C.toRealExtensionChain.eventualRelationLimit_stable
      D.noNewPredecessors D.stable_target
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toRealExtensionChain.realPart_extends_eventualRelationLimit
        D.noNewPredecessors i)
      ((C.stage i).links x hxi)

/-- The canonical proper-limit scheduler state under normalized invariants,
with no separately supplied ray oracle. -/
noncomputable def normalizedIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) :
    TerminalResolutionState Gamma Y kappa T Z persistent B :=
  intermediateLimitState C D.toIntermediateLimitData

@[simp] theorem intermediateLimitState_blueprint
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) :
    (intermediateLimitState C D).blueprint =
      C.toRealExtensionChain.eventualRelationLimit D.noNewPredecessors :=
  rfl

@[simp] theorem intermediateLimitState_linked
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) :
    (intermediateLimitState C D).linked = ⋃ i, (C.stage i).linked :=
  rfl

@[simp] theorem normalizedIntermediateLimitState_blueprint
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) :
    (normalizedIntermediateLimitState C D).blueprint =
      C.toRealExtensionChain.eventualRelationLimit D.noNewPredecessors :=
  rfl

@[simp] theorem normalizedIntermediateLimitState_linked
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) :
    (normalizedIntermediateLimitState C D).linked =
      ⋃ i, (C.stage i).linked :=
  rfl

/-- Every earlier state really extends the bundled proper-limit state. -/
theorem realExtends_intermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.RealExtends
      (intermediateLimitState C D).blueprint B := by
  change (C.toRealExtensionChain.stage i).RealExtends
    (C.toRealExtensionChain.eventualRelationLimit D.noNewPredecessors) B
  exact C.toRealExtensionChain.realExtends_eventualRelationLimit
    D.noNewPredecessors i

/-- The full predecessor invariant is retained across the proper limit, so a
later successor can be composed with every stage below the limit. -/
theorem noNewPredecessorsTo_intermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.NoNewPredecessorsTo
      (intermediateLimitState C D).blueprint := by
  change (C.toRealExtensionChain.stage i).NoNewPredecessorsTo
    (C.toRealExtensionChain.eventualRelationLimit D.noNewPredecessors)
  exact C.toRealExtensionChain.noNewPredecessorsTo_eventualRelationLimit
    D.noNewPredecessors i

/-- Every request linked before the proper limit remains recorded there. -/
theorem linked_subset_intermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) (i : I) :
    (C.stage i).linked ⊆ (intermediateLimitState C D).linked :=
  Set.subset_iUnion (fun j ↦ (C.stage j).linked) i

/-- The bundled state exposes the exact source Assertion 9.33 conclusion. -/
theorem stableLimitConclusion_intermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : IntermediateLimitData C) :
    StableLimitConclusion (fun i ↦ (C.stage i).blueprint)
      (intermediateLimitState C D).blueprint T Z persistent B := by
  simpa only [intermediateLimitState_blueprint,
    ResolutionChain.toRealExtensionChain] using
    C.toRealExtensionChain.stableLimitConclusion_eventualRelationLimit
      D.noNewPredecessors D.reference_isWarp D.target_boundary
      D.stable_target D.relation_boundary

/-- Every earlier scheduler state really extends the normalized proper
limit. -/
theorem realExtends_normalizedIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.RealExtends
      (normalizedIntermediateLimitState C D).blueprint B :=
  realExtends_intermediateLimitState C D.toIntermediateLimitData i

/-- The full predecessor invariant passes to the normalized proper limit. -/
theorem noNewPredecessorsTo_normalizedIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) (i : I) :
    (C.stage i).blueprint.NoNewPredecessorsTo
      (normalizedIntermediateLimitState C D).blueprint :=
  noNewPredecessorsTo_intermediateLimitState
    C D.toIntermediateLimitData i

/-- Previously linked requests remain linked at the normalized proper
limit. -/
theorem linked_subset_normalizedIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) (i : I) :
    (C.stage i).linked ⊆
      (normalizedIntermediateLimitState C D).linked :=
  linked_subset_intermediateLimitState C D.toIntermediateLimitData i

/-- Assertion 9.33 in scheduler-state form, with the infinitary ray clause
derived from normalization. -/
theorem stableLimitConclusion_normalizedIntermediateLimitState
    (C : ResolutionChain I compiler hpersistent)
    (D : NormalizedIntermediateLimitData C) :
    StableLimitConclusion (fun i ↦ (C.stage i).blueprint)
      (normalizedIntermediateLimitState C D).blueprint
        T Z persistent B :=
  stableLimitConclusion_intermediateLimitState
    C D.toIntermediateLimitData

namespace ResolutionChain

/-- Normalization discharges the only ray premise left by the final all-real
relation-limit compiler. -/
def rayRelationBoundaryData_of_normalized
    (C : ResolutionChain I compiler hpersistent)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target) :
    RayRelationBoundaryData C where
  every_relation_ray_strong :=
    C.toRealExtensionChain.realEdgeLimit_every_ray_strong
      hGamma hBtarget

/-- The final fair relation schedule from a successful enumeration, with
both sink fields supplied by fairness and the ray field derived from
normalization.  This is the no-oracle final-limit counterpart of
`normalizedIntermediateLimitState`. -/
noncomputable def FairRelationSchedule.ofSuccessfulEnumeration_of_normalized
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (hYwarp : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hindex : #I ≤ kappa)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairRelationSchedule C seed :=
  FairRelationSchedule.ofSuccessfulEnumeration_of_rayBoundary
    H hYwarp hkappa hindex hterminalB hstableB
      (rayRelationBoundaryData_of_normalized C hGamma hBtarget) E

end ResolutionChain

end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
