/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# Target routes confined to a stopped roof

The honest old-stage interval transaction keeps only its first-hit front in
the roof of the later frontier and retains the remaining target suffix as
external data.  This file records why that distinction is forced by the
existing public interfaces.

A target vertex which lies in the roof of a set belongs to the set, by the
trivial target path.  Consequently every `ClubStageUnionData.target_path`
currently ends in the selected club frontier.  More generally, every
`StableExtensionConclusion` whose target route is carried by a blueprint
roofed at `T` forces the target set to meet `T`.  These are positive boundary
theorems, but they rule out inserting an arbitrary post-frontier suffix into
either fixed-roof record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

namespace ClubStageUnionData

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : SimultaneousAssignment Zf.paths Y} {z : V}

/-- A target route stored inside a roofed club-stage carrier necessarily
finishes in the selected frontier. -/
theorem target_path_finish_mem_newSlice
    (D : ClubStageUnionData C W A z) :
    D.target_path.finish ∈ C.newSlice := by
  apply CardinalInduction.SliceSpliceConstructor.target_mem_of_mem_roof
    D.target_path_finish
  exact D.carrier_roofed
    (D.target_path_vertices D.target_path.finish_mem_support)

end ClubStageUnionData

namespace StableExtensionConclusion

variable {W U : LinkageBlueprint Gamma Y kappa}
variable {z : V} {T Z persistent B : Set V}

/-- A completed target route carried by a blueprint roofed at `T` supplies
an actual target endpoint in `T`. -/
theorem exists_target_mem_slice
    (hB : B ⊆ Gamma.target)
    (h : StableExtensionConclusion W U z T Z persistent B) :
    (B ∩ T).Nonempty := by
  obtain ⟨p, _hpStart, hpFinish, hpSupport, _hpEdges⟩ := h.links
  refine ⟨p.finish, hpFinish, ?_⟩
  apply CardinalInduction.SliceSpliceConstructor.target_mem_of_mem_roof
    (hB hpFinish)
  apply h.isLinkageBlueprint.vertices_roofed
  change p.finish ∈ U.realPart.vertices
  exact hpSupport p.finish_mem_support

/-- In particular, a fixed-roof stable successor cannot carry a route to a
target set disjoint from its stopping frontier. -/
theorem false_of_disjoint_target_slice
    (hB : B ⊆ Gamma.target) (hBT : Disjoint B T)
    (h : StableExtensionConclusion W U z T Z persistent B) : False := by
  obtain ⟨b, hbB, hbT⟩ := h.exists_target_mem_slice hB
  exact Set.disjoint_left.1 hBT hbB hbT

end StableExtensionConclusion

#print axioms ClubStageUnionData.target_path_finish_mem_newSlice
#print axioms StableExtensionConclusion.exists_target_mem_slice

end LinkageBlueprint
end Blueprint
end Erdos599
