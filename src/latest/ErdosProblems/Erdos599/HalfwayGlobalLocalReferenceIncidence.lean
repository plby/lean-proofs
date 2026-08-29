/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceExtension

/-! # Exact global/local reference incidence

A selected-stage reference member is a finite prefix of its unique member
of the limiting warp.  This file records the stronger incidence fact used
by Assertion 9.31: along that limiting member, the whole selected-reference
carrier is exactly the chosen finite prefix.  Thus its future tail has no
further selected-reference vertex or edge.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

namespace ladderReference

variable {L : Gamma.KappaLadder kappa} {a : Ladder.Stage kappa}

/-- A local reference member meeting a fixed limiting member is the unique
selected prefix of that limiting member. -/
theorem eq_of_mem_support_of_extends_limit
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {q : Gamma.DPath} (hq : q ∈ ladderReference L a)
    (hqp : Gamma.Extends q p)
    {r : Gamma.DPath} (hr : r ∈ ladderReference L a)
    {x : V} (hxr : x ∈ r.support) (hxp : x ∈ p.support) :
    r = q := by
  let rs : ladderReference L a := ⟨r, hr⟩
  have hxOwner : x ∈ (limitExtension hL rs).support :=
    Gamma.support_mono_of_extends (extends_limitExtension hL rs) hxr
  have howner : limitExtension hL rs = p := by
    apply DWeb.IsWarp.eq_of_mem_support
      (hL.warpStages (Ladder.finalStage kappa))
      (limitExtension_mem hL rs) hp hxOwner hxp
  apply DWeb.IsWarp.eq_of_initial_eq Gamma (ladderReference.isWarp hL)
    hr hq
  calc
    r.initial = (limitExtension hL rs).initial :=
      Gamma.extends_initial (extends_limitExtension hL rs)
    _ = p.initial := congrArg Path.initial howner
    _ = q.initial := (Gamma.extends_initial hqp).symm

/-- Exact carrier incidence of a limiting reference member with the
selected-stage reference.  In particular no vertex of its proper future
tail can return to the selected reference carrier. -/
theorem support_inter_vertexSet_eq_of_extends
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {q : Gamma.DPath} (hq : q ∈ ladderReference L a)
    (hqp : Gamma.Extends q p) :
    p.support ∩ Gamma.vertexSet (ladderReference L a) = q.support := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxp, r, hr, hxr⟩
    have hrq := eq_of_mem_support_of_extends_limit hL hp hq hqp hr hxr hxp
    rwa [hrq] at hxr
  · intro x hxq
    exact ⟨Gamma.support_mono_of_extends hqp hxq, ⟨q, hq, hxq⟩⟩

/-- Exact edge incidence of the same limiting member with the selected
reference relation. -/
theorem edgeSet_inter_familyEdges_eq_of_extends
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {q : Gamma.DPath} (hq : q ∈ ladderReference L a)
    (hqp : Gamma.Extends q p) :
    p.edgeSet ∩ familyEdges (ladderReference L a) = q.edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨hep, heLocal⟩
    simp only [familyEdges, Set.mem_iUnion] at heLocal
    obtain ⟨r, hr, her⟩ := heLocal
    have hend := r.edgeSet_subset_support_prod her
    have hrq := eq_of_mem_support_of_extends_limit hL hp hq hqp hr
      hend.1 (p.edgeSet_subset_support_prod hep).1
    rwa [hrq] at her
  · intro e heq
    exact ⟨Path.edgeSet_mono_of_extends hqp heq,
      Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, heq⟩⟩⟩

/-- Every selected-reference edge is a limiting-reference edge. -/
theorem familyEdges_subset_limitWarp
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    familyEdges (ladderReference L a) ⊆ familyEdges L.limitWarp := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨q, hq, heq⟩ := he
  let qs : ladderReference L a := ⟨q, hq⟩
  exact ⟨limitExtension hL qs, limitExtension_mem hL qs,
    Path.edgeSet_mono_of_extends (extends_limitExtension hL qs) heq⟩

#print axioms eq_of_mem_support_of_extends_limit
#print axioms support_inter_vertexSet_eq_of_extends
#print axioms edgeSet_inter_familyEdges_eq_of_extends
#print axioms familyEdges_subset_limitWarp

end ladderReference
end Erdos599.Blueprint.LinkageBlueprint
