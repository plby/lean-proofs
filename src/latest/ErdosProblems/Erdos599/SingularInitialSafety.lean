/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLink
import ErdosProblems.Erdos599.SafeLinkReducedProperties
import ErdosProblems.Erdos599.SingularExtension

/-!
# Initial deletion safety for the singular construction

The singular two-track construction may reserve an arbitrary collection of
source vertices before its first quotient step.  This file records that this
does not create a hindrance: a wave after deleting the reserved sources can
be lifted and supplemented by the trivial paths at all reserved vertices.

The argument is the set-valued version of `delete_source_isUnhindered`.
-/

noncomputable section

open Set Erdos599.DirectedPath

namespace Erdos599
namespace CardinalInduction
namespace SingularInitialSafety

open SingularExtension

universe u

variable {V : Type u}

/-- Deleting an arbitrary set of source vertices from an unhindered web
leaves an unhindered web.  The trivial paths at the deleted vertices turn a
wave in the deletion into a wave of the original web. -/
theorem delete_sources_isUnhindered (G : DWeb V) {Q : Set V}
    (hG : G.IsUnhindered) (hQ : Q ⊆ G.source) :
    (G.delete Q).IsUnhindered := by
  rw [(G.delete Q).isUnhindered_iff]
  intro W hW
  let L : Set G.DPath := G.liftDeleteFamily Q W
  let R : Set G.DPath := G.trivialPath '' Q ∪ L
  have hLavoid : Disjoint (G.vertexSet L) Q :=
    G.vertexSet_liftDeleteFamily_disjoint hW.2.1
  have hLwarp : G.IsWarp L := hW.1.liftDeleteFamily
  have hRwarp : G.IsWarp R := by
    apply Set.PairwiseDisjoint.union (G.isWarp_trivialPaths Q) hLwarp
    rintro p ⟨a, haQ, rfl⟩ q hqL _hpq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_left.2
    intro haq
    exact Set.disjoint_left.1 hLavoid
      (G.mem_vertexSet.mpr ⟨q, hqL, haq⟩) haQ
  have hRinitial :
      G.initialSet R = Q ∪ (G.delete Q).initialSet W := by
    simp only [R, G.initialSet_union, G.initialSet_trivialPaths,
      L, G.initialSet_liftDeleteFamily]
  have hRstart : G.initialSet R ⊆ G.source := by
    rw [hRinitial]
    exact Set.union_subset hQ (hW.2.1.trans Set.sdiff_subset)
  have hQfrontier : Q ⊆ G.terminalFrontier R := by
    intro a haQ
    refine ⟨G.trivialPath a, Or.inl ⟨a, haQ, rfl⟩, ?_⟩
    exact G.terminal?_trivialPath a
  have hRseparates : G.source ⊆ G.roof (G.terminalFrontier R) := by
    intro a ha p hp
    by_cases hpmeets : (p.support ∩ Q).Nonempty
    · obtain ⟨x, hxp, hxQ⟩ := hpmeets
      exact ⟨x, hxp, hQfrontier hxQ⟩
    · have havoid : SafeLink.Walk.Avoids p.walk Q := by
        intro x hxp hxQ
        exact hpmeets ⟨x, hxp, hxQ⟩
      let q : DirectedPath.FinitePath (G.delete Q).graph :=
        SafeLink.FinitePath.toDelete G Q p havoid
      have haDelete : a ∈ (G.delete Q).source := by
        exact ⟨ha, havoid a (hp.1 ▸ p.walk.start_mem_support)⟩
      have hpfinishDelete : p.finish ∈ (G.delete Q).target := by
        exact ⟨hp.2, havoid p.finish p.walk.end_mem_support⟩
      obtain ⟨x, hxq, hxFrontier⟩ :=
        hW.2.2 haDelete q
          ⟨by simpa [q] using hp.1, by simpa [q] using hpfinishDelete⟩
      obtain ⟨r, hrW, hrterm⟩ := hxFrontier
      have hxSupport : x ∈ p.support := by
        simpa [q] using hxq
      have hxR : x ∈ G.terminalFrontier R := by
        refine ⟨G.liftDeletePath Q r, Or.inr ?_, ?_⟩
        · exact ⟨r, hrW, rfl⟩
        · simpa using hrterm
      exact ⟨x, hxSupport, hxR⟩
  have hReq : G.initialSet R = G.source :=
    (G.isUnhindered_iff.mp hG) R ⟨hRwarp, hRstart, hRseparates⟩
  apply Set.Subset.antisymm hW.2.1
  intro a ha
  have haR : a ∈ G.initialSet R := by
    rw [hReq]
    exact ha.1
  rw [hRinitial] at haR
  exact haR.resolve_left ha.2

/-- In particular, deleting any collection of vertices which are both
sources and targets preserves unhinderedness.  This is the initial reserve
used for already-completed trivial source paths. -/
theorem delete_source_target_isUnhindered (G : DWeb V) {Q : Set V}
    (hG : G.IsUnhindered) (hQ : Q ⊆ G.source ∩ G.target) :
    (G.delete Q).IsUnhindered :=
  delete_sources_isUnhindered G hG (fun _ hx ↦ (hQ hx).1)

/-- If the original web is normalized, quotienting the source-deleted web
by the *old* source is unhindered.  The deleted vertices are inessential in
the deleted web, so quotienting by the old source agrees with quotienting by
the retained source.  This is the base quotient-safety fact needed when the
initial clean row still records trivial paths at the reserved sources. -/
theorem delete_quotient_oldSource_isUnhindered
    (G : DWeb V) {Q : Set V}
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    (hQ : Q ⊆ G.source) :
    ((G.delete Q).quotient G.source).IsUnhindered := by
  let H : DWeb V := G.delete Q
  have hH : H.IsUnhindered := delete_sources_isUnhindered G hG hQ
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNoEnterH : H.NoEdgeEnters H.source := hNoEnter.delete
  have hretained : H.source ⊆ G.source := Set.sdiff_subset
  have hEssOldSubset : H.essential G.source ⊆ H.source := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxQ
    exact Set.disjoint_left.1
      (G.disjoint_delete_essential_deleted G.source Q) hx hxQ
  have hEssRetained : H.essential H.source = H.source := by
    apply Set.Subset.antisymm (H.essential_subset H.source)
    exact source_subset_essential_source_of_unhindered H hH
  have hEssOld : H.essential G.source = H.source := by
    have hsandwich : H.essential H.source = H.essential G.source :=
      RelationalRoof.essential_sandwich H.graph.Adj H.target
        hEssOldSubset hretained
    exact hsandwich.symm.trans hEssRetained
  have hroof : H.source ⊆ H.roof G.source := by
    intro x hx
    exact H.subset_roof G.source (hretained hx)
  have hquotient : H.quotient H.source = H.quotient G.source := by
    calc
      H.quotient H.source = H.quotient (H.essential G.source) := by
        rw [hEssOld]
      _ = H.quotient G.source :=
        H.quotient_essential_eq_of_subset_roof G.source hroof
  rw [← hquotient]
  exact quotient_source_isUnhindered H hNoEnterH hH

end SingularInitialSafety
end CardinalInduction
end Erdos599
