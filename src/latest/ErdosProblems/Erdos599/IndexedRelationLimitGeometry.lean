/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedRelationLimitBoundary
import ErdosProblems.Erdos599.IndexedRelationLimitStrongRay

/-!
# Geometric fields of an indexed blueprint limit

Cardinality is universe-polymorphic: ordinal stage subtypes can live above
the vertex universe.  The limit slice is not identified with any old slice.
Stability uses strict frontier chronology on the old roof, not an extra
assumption that all popular vertices lie in the persistent set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedRealExtensionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {B persistent : Set V}

/-- Cardinality of the actual union carrier; no global closure is counted. -/
theorem mk_realVertexLimit_le
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hkappa : aleph0 ≤ kappa)
    (hindex : lift.{u} #I ≤ lift.{v} kappa)
    (hpaths : ∀ i, #(C.stage i).paths ≤ kappa) :
    #C.realVertexLimit ≤ kappa := by
  apply Cardinal.lift_le.{v}.mp
  refine (Cardinal.mk_iUnion_le_lift
    (fun i ↦ (C.stage i).realPart.vertices)).trans ?_
  apply Cardinal.mul_le_of_le (Cardinal.aleph0_le_lift.2 hkappa) hindex
  apply ciSup_le
  intro i
  apply Cardinal.lift_le.2
  exact (C.stage i).mk_vertexSet_le_of_mk_paths_le hkappa (hpaths i)

/-- The canonical decomposition has at most one path per carrier vertex. -/
theorem eventualRelationBlueprint_card_paths_le
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hcard : #C.realVertexLimit ≤ kappa) :
    #C.eventualRelationBlueprint.paths ≤ kappa := by
  change #(Set.range C.eventualRelationOrientation.rootPath) ≤ kappa
  refine Cardinal.mk_range_le.trans ?_
  refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
  simpa only [C.eventualRelationOrientation_spec.2] using hcard

theorem realRelationBlueprint_card_paths_le
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hcard : #C.realVertexLimit ≤ kappa) :
    #C.realRelationBlueprint.paths ≤ kappa := by
  change #(Set.range C.realRelationOrientation.rootPath) ≤ kappa
  refine Cardinal.mk_range_le.trans ?_
  refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
  simpa only [C.realRelationOrientation_spec.2] using hcard

/-- The strong-ray field is inherited through genuine real-extension
accounting, independently of the moving slice. -/
theorem eventualRelationBlueprint_infinitelyManyStrong
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target) :
    C.eventualRelationBlueprint.InfinitelyManyStrongEdges := by
  intro r hr
  apply C.eventualRelationLimit_every_ray_strong hstrong hGamma hB r
  intro e he
  rw [← C.eventualRelationBlueprint_edgeSet]
  exact Set.mem_iUnion.2 ⟨Sum.inr r, Set.mem_iUnion.2 ⟨hr, he⟩⟩

theorem realRelationBlueprint_infinitelyManyStrong
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target) :
    C.realRelationBlueprint.InfinitelyManyStrongEdges := by
  intro r hr
  apply C.realEdgeLimit_every_ray_strong hstrong hGamma hB r
  intro e he
  rw [← C.realRelationBlueprint_edgeSet]
  exact Set.mem_iUnion.2 ⟨Sum.inr r, Set.mem_iUnion.2 ⟨hr, he⟩⟩

/-- Stability at the supremum slice follows from its avoidance of every
old strict roof, expressed as the resulting old-frontier containment. -/
theorem eventualRelationBlueprint_stable
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice closed : I → Set V) (T : Set V)
    (hstage : ∀ i, (C.stage i).IsLinkageBlueprint
      (slice i) (closed i) persistent)
    (hstable : ∀ i, (C.stage i).Stable (slice i) persistent)
    (hchron : ∀ i, Gamma.roof (slice i) ∩ T ⊆ slice i)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.eventualRelationBlueprint.Stable T persistent := by
  rintro x ⟨hx, hxT⟩
  have hxlimit : x ∈ C.realVertexLimit := by
    rw [← C.eventualRelationBlueprint_vertexSet]
    exact (mem_familyGraph_terminals_of_mem_terminalSet hx).1
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxlimit
  rcases C.eventualTerminal_mem_target_or_stage_terminal hx i hxi with
    hxB | hxterm
  · exact hB ⟨hxB, hxlimit⟩
  · exact hstable i ⟨hxterm, hchron i ⟨(hstage i).vertices_roofed hxi, hxT⟩⟩

/-- Construct all six proper-limit blueprint fields from the actual
moving frontier and closure geometry. No limit IsLB certificate is assumed. -/
theorem eventualRelationBlueprint_isLinkageBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice closed R D : I → Set V) (T Z : Set V)
    (hstage : ∀ i, (C.stage i).IsLinkageBlueprint
      (slice i) (closed i) persistent)
    (hstable : ∀ i, (C.stage i).Stable (slice i) persistent)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hslice : ∀ i, slice i = R i \ D i)
    (hD : Monotone D) (hT : ((⋃ i, R i) \ ⋃ i, D i) ⊆ T)
    (hroof : ∀ i, Gamma.roof (slice i) ⊆ Gamma.roof T)
    (hclosed : ∀ i, closed i ⊆ Z)
    (hkappa : aleph0 ≤ kappa)
    (hindex : lift.{u} #I ≤ lift.{v} kappa)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.eventualRelationBlueprint.IsLinkageBlueprint T Z persistent where
  vertices_roofed := by
    intro x hx
    rw [C.eventualRelationBlueprint_vertexSet] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact hroof i ((hstage i).vertices_roofed hxi)
  covers_source := C.eventualRelationBlueprint_covers_source_of_limitBoundary_subset slice R D T
    (fun i ↦ (hstage i).covers_source) hYwarp
    (by
      intro p hp
      obtain ⟨q, rfl⟩ := hYfinite hp
      exact q.support_finite)
    hslice hD hT
  vertices_closed := by
    intro x hx
    rw [C.eventualRelationBlueprint_vertexSet] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact hclosed i ((hstage i).vertices_closed hxi)
  card_paths := C.eventualRelationBlueprint_card_paths_le
    (C.mk_realVertexLimit_le hkappa hindex (fun i ↦ (hstage i).card_paths))
  infinitely_many_strong := C.eventualRelationBlueprint_infinitelyManyStrong
    (fun i ↦ (hstage i).infinitely_many_strong) hGamma hBtarget
  terminals_popular := by
    intro x hx
    apply Or.inl
    rcases C.eventualTerminal_popular_or_persistent slice closed
        hstage hstable hB hx with hxpop | hxpersistent
    · exact hxpop
    · exact Or.inl hxpersistent

#print axioms mk_realVertexLimit_le
#print axioms eventualRelationBlueprint_stable
#print axioms eventualRelationBlueprint_isLinkageBlueprint

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599


