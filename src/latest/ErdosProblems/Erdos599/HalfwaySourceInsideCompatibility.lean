/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceFrontAbsorption
import ErdosProblems.Erdos599.HalfwaySourceInsideRestriction

/-!
# Compatibility of the literal inside restriction

The club-stage roof theorem proves that the old family is star-compatible
with the complete later linkage.  Assertion 9.31 uses only `W[X]` on the
right of the diamond.  This file proves that compatibility descends to that
literal restriction from its exact carrier and edge inclusions.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Star compatibility descends to a subrelation whose carrier is contained
in the full later carrier.  Edge containment is what makes a full-later root
remain a root after restriction. -/
theorem starCompatible_of_right_vertex_edge_subset
    (old full inside : LinkageBlueprint Gamma Y kappa)
    (hfull : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths full.paths)
    (hvertices : inside.vertexSet ⊆ full.vertexSet)
    (hedges : inside.edgeSet ⊆ full.edgeSet) :
    (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths inside.paths := by
  intro p hpOld q hqInside x hxp hxq
  have hxInside : x ∈ inside.vertexSet := ⟨q, hqInside, hxq⟩
  obtain ⟨r, hrFull, hxr⟩ := hvertices hxInside
  have hmeet := hfull p hpOld r hrFull x hxp hxr
  refine ⟨hmeet.1, ?_⟩
  have hxFullInitial : x ∈ full.initialSet :=
    ⟨r, hrFull, hmeet.2⟩
  have hnoFull := SourceFrontAbsorption.no_incoming_of_mem_initialSet
    full hxFullInitial
  have hxInsideInitial : x ∈ inside.initialSet := by
    rw [SourceFrontAbsorption.initialSet_eq_no_incoming]
    refine ⟨hxInside, ?_⟩
    rintro ⟨y, hyx⟩
    exact hnoFull ⟨y, hedges hyx⟩
  obtain ⟨s, hsInside, hsinitial⟩ := hxInsideInitial
  have hqs : q = s :=
    inside.path_eq_of_mem_support hqInside hsInside hxq
      (hsinitial.symm ▸ s.initial_mem_support)
  exact (congrArg Path.initial hqs).trans hsinitial

/-- Exact specialization to the source object `W[X]`.  A complete later
blueprint realizing the original row supplies the already-proved club-stage
compatibility; the exact equations of both realizations discharge the
restriction inclusions. -/
theorem SourceInsideRestriction.starCompatible_of_fullRow
    {W : Set Gamma.DPath} {X : Set V}
    (I : SourceInsideRestriction (Y := Y) (kappa := kappa) W X)
    (old full : LinkageBlueprint Gamma Y kappa)
    (hfullVertices : full.vertexSet = Gamma.vertexSet W)
    (hfullEdges : full.edgeSet = familyEdges W)
    (hfull : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths full.paths) :
    (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths I.family.paths := by
  apply starCompatible_of_right_vertex_edge_subset old full I.family hfull
  · rw [I.family_vertexSet, hfullVertices]
    exact Set.inter_subset_left
  · rw [I.family_edgeSet, hfullEdges]
    exact Set.inter_subset_left

#print axioms starCompatible_of_right_vertex_edge_subset
#print axioms SourceInsideRestriction.starCompatible_of_fullRow

end Erdos599.Blueprint.LinkageBlueprint

