/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularInitialSafety
import ErdosProblems.Erdos599.SingularPendingReentry

/-!
# Initial pending-safety certificate for the singular row machine

At the initial trivial full-source row, precisely the source vertices which
are already targets give completed components.  Freeze those vertices.  All
pending requests remain sources after the deletion, and the quotient of the
deleted web by the old source is unhindered.  This packages the exact
`DeletedPendingSafety` certificate consumed by the three-piece continuation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularInitialPendingSafety

open SingularExtension SingularInitialSafety SingularPendingDecomposition
  SingularPendingReentry

universe u

variable {V : Type u}

/-- The initial displayed row consists of the trivial paths at every source. -/
def initialTrivialRow (G : DWeb V) : Set G.DPath :=
  G.trivialPath '' G.source

/-- The carrier frozen before the first continuation. -/
def initialFrozenSet (G : DWeb V) : Set V :=
  G.source ∩ G.target

/-- The old-source quotient after deleting source vertices has exactly the
retained sources.  This is the source-coordinate companion to
`delete_quotient_oldSource_isUnhindered`. -/
theorem delete_quotient_oldSource_source_eq
    (G : DWeb V) {Q : Set V}
    (hG : G.IsUnhindered) (hQ : Q ⊆ G.source) :
    ((G.delete Q).quotient G.source).source = (G.delete Q).source := by
  let H : DWeb V := G.delete Q
  have hH : H.IsUnhindered := delete_sources_isUnhindered G hG hQ
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
  change H.essential (H.source ∪ G.source) = H.source
  rw [Set.union_eq_right.2 hretained, hEssOld]

/-- Every pending request of the trivial row survives deletion of any
already-completed source vertices. -/
theorem pendingRequests_initialTrivialRow_subset_deleteSource
    (G : DWeb V) {Q : Set V}
    (hQ : Q ⊆ G.source ∩ G.target) :
    pendingRequests G (initialTrivialRow G) G.source ⊆
      (G.delete Q).source := by
  rintro x (hxClean | hxBoundary)
  · obtain ⟨p, hp, _hpx⟩ := hxClean
    exact (hp.2.2 hp.2.1).elim
  · obtain ⟨p, hp, hpx⟩ := hxBoundary
    refine ⟨hpx ▸ hp.2.1, ?_⟩
    intro hxQ
    apply hp.1.2
    refine ⟨hp.1.1, x, (hQ hxQ).2, ?_⟩
    obtain ⟨a, ha, rfl⟩ := hp.1.1
    rw [G.terminal?_trivialPath]
    simpa only [G.initial_trivialPath] using congrArg some hpx

/-- The vertices of the completed part of the initial trivial row are all
contained in `source ∩ target`. -/
theorem completedPart_initialTrivialRow_vertexSet_subset
    (G : DWeb V) :
    G.vertexSet (completedPart G (initialTrivialRow G)) ⊆
      initialFrozenSet G := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨a, haSource, rfl⟩ := hp.1
  rw [G.support_trivialPath] at hxp
  subst x
  obtain ⟨b, hbTarget, hab⟩ := hp.2
  have hab' : a = b :=
    Option.some.inj ((G.terminal?_trivialPath a).symm.trans hab)
  exact ⟨haSource, by simpa only [hab'] using hbTarget⟩

/-- The exact future-safety certificate for the initial trivial row.  Its
cardinal parameter is supplied in the form used by the singular scale. -/
theorem deletedPendingSafety_initialTrivialRow
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {mu : Cardinal.{u}}
    (hcard : #(pendingRequests G (initialTrivialRow G) G.source) = mu) :
    DeletedPendingSafety G (initialTrivialRow G) G.source
      (initialFrozenSet G) mu := by
  apply DeletedPendingSafety.of_deletedQuotient hNorm
  · exact delete_quotient_oldSource_isUnhindered G hG hNorm
      (fun _ hx ↦ hx.1)
  · rw [delete_quotient_oldSource_source_eq G hG
      (fun _ hx ↦ hx.1)]
    exact pendingRequests_initialTrivialRow_subset_deleteSource G
      Set.Subset.rfl
  · exact hcard

end SingularInitialPendingSafety
end CardinalInduction
end Erdos599
