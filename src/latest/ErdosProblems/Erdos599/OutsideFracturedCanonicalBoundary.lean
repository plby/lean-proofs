/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutConstruction
import ErdosProblems.Erdos599.FracturedCanonicalBoundary

/-!
# The actual outside cut has no junction on the peeled reference

Away from the cut, a simultaneous fragment initial and terminal has no
incident outside edge, hence its starting member is a singleton. Boundary
alignment makes any reference member through it the same singleton, which
was peeled. Thus the canonical projection's extra geometry is proved for
the actual outside family, without excluding common singleton members.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp

open Set DirectedPath Alternating FracturedDuplication FracturedAssignmentPeel

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {X : Set V}

/-- An outside-cut junction away from the cut is the vertex of an actual
singleton fractured member. -/
theorem singleton_of_junction_off_cut (F : OutsideFracturedWarp W X)
    {x : V} (hx : IsJunction F.holes x) (hxNot : x ∉ X) :
    Gamma.trivialPath x ∈ F.holes.paths := by
  have hxTerminal := hx.2
  rw [F.terminalFrontier_eq] at hxTerminal
  have hxNoOut : ¬ ∃ y, (x, y) ∈ outsideFamilyEdges W X := by
    rcases hxTerminal with hxCut | hxOutside
    · exact False.elim (hxNot hxCut.1)
    · exact hxOutside.2.2
  obtain ⟨p, hp, hpInitial⟩ := hx.1
  obtain ⟨p, rfl⟩ := F.finiteCharacter hp
  have hpStart : p.start = x := hpInitial
  have hpEnd : p.start = p.finish := by
    by_contra hne
    obtain ⟨y, hy⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish p
      p.start_mem_support hne
    apply hxNoOut
    refine ⟨y, ?_⟩
    rw [← F.familyEdges_eq]
    refine Set.mem_iUnion.mpr ⟨.inl p, Set.mem_iUnion.mpr ⟨hp, ?_⟩⟩
    change (x, y) ∈ p.edgeSet
    simpa only [hpStart] using hy
  have hpTriv := finitePath_eq_trivial_of_start_eq_finish p hpEnd
  have hpTriv' : (.inl p : Gamma.DPath) = Gamma.trivialPath x := by
    rw [hpTriv, hpStart]
    rfl
  exact hpTriv' ▸ hp

/-- The no-junction hypothesis needed by canonical occurrence projection is
an actual consequence of outside-cut geometry and the peeled reference. -/
theorem noJunctionOnPeeledReference (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hdisjoint : Disjoint X (Gamma.vertexSet Y)) :
    FracturedCanonicalBoundary.NoJunctionOnReference F.holes
      (activeReference F.holes Y) := by
  intro x hxReference hxJunction
  obtain ⟨p, hp, hxp⟩ := hxReference
  have hxY : x ∈ Gamma.vertexSet Y := ⟨p, hp.1, hxp⟩
  have hxNot : x ∉ X := fun hxX ↦ Set.disjoint_left.mp hdisjoint hxX hxY
  have hxSingleton := F.singleton_of_junction_off_cut hxJunction hxNot
  have hpTriv := referencePath_eq_trivial_of_singletonHole F.holes
    hboundary hY hxSingleton hp.1 hxp
  apply hp.2
  exact ⟨⟨x, hxSingleton, hpTriv.symm⟩, hp.1⟩

#print axioms singleton_of_junction_off_cut
#print axioms noJunctionOnPeeledReference

end Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp
