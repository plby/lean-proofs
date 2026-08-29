/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularBoundarySplit
import ErdosProblems.Erdos599.SingularExtension

/-!
# The clean pending decomposition for a singular row

The whole pending part of a half-way row need not be terminal-clean at a
separating stop-over: a pending member may start in the stop-over and end at
another point of it.  The sound decomposition keeps such members separate.

* `cleanPendingPart` consists of pending members which start outside the
  stop-over.  Endpoint purity makes this part terminal-clean.
* `boundaryPendingPart` consists of pending members which start in the
  stop-over.  Their old paths cannot in general be used in a clean star;
  their initial vertices must instead be treated as direct requests in the
  quotient row.

The final request set is therefore the union of the terminals of the clean
part and the initials of the boundary part.  Both halves lie in the
separating stop-over, hence in the quotient source.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularPendingDecomposition

open SliceSpliceSource

universe u

variable {V : Type u}

/-- Pending members whose initial vertex is strictly outside the current
stop-over. -/
def cleanPendingPart (G : DWeb V) (W : Set G.DPath) (D : Set V) :
    Set G.DPath :=
  initialRestriction G (SingularExtension.pendingPart G W) (G.source \ D)

/-- Pending members whose initial vertex already belongs to the current
stop-over.  Their paths are not asserted to be terminal-clean. -/
def boundaryPendingPart (G : DWeb V) (W : Set G.DPath) (D : Set V) :
    Set G.DPath :=
  initialRestriction G (SingularExtension.pendingPart G W) (G.source ∩ D)

@[simp] theorem mem_cleanPendingPart
    {G : DWeb V} {W : Set G.DPath} {D : Set V} {p : G.DPath} :
    p ∈ cleanPendingPart G W D ↔
      p ∈ SingularExtension.pendingPart G W ∧
        p.initial ∈ G.source \ D :=
  Iff.rfl

@[simp] theorem mem_boundaryPendingPart
    {G : DWeb V} {W : Set G.DPath} {D : Set V} {p : G.DPath} :
    p ∈ boundaryPendingPart G W D ↔
      p ∈ SingularExtension.pendingPart G W ∧
        p.initial ∈ G.source ∩ D :=
  Iff.rfl

/-- The two pieces are exactly the pending part of a full-source family. -/
theorem clean_union_boundary
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hfull : G.initialSet W = G.source) :
    cleanPendingPart G W D ∪ boundaryPendingPart G W D =
      SingularExtension.pendingPart G W := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (fun _ hp ↦ hp.1) (fun _ hp ↦ hp.1)
  · intro p hp
    have hpSource : p.initial ∈ G.source := by
      rw [← hfull]
      exact ⟨p, hp.1, rfl⟩
    by_cases hpD : p.initial ∈ D
    · exact Or.inr ⟨hp, hpSource, hpD⟩
    · exact Or.inl ⟨hp, hpSource, hpD⟩

/-- The clean and boundary pending pieces are disjoint. -/
theorem disjoint_clean_boundary
    (G : DWeb V) (W : Set G.DPath) (D : Set V) :
    Disjoint (cleanPendingPart G W D) (boundaryPendingPart G W D) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact hp.2.2 hq.2.2

/-- Endpoint purity of the original linkage makes precisely the outside
pending part terminal-clean. -/
theorem cleanPendingPart_terminalClean
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : IsLinkageBetween G G.source D W) :
    SingularContinuation.TerminalCleanAt G (cleanPendingPart G W D) D := by
  intro p hp x hxp hxD
  obtain ⟨f, rfl, hends, _hsource⟩ := hW.endpointPure p hp.1.1
  have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxD⟩
  have hxFinish : x = f.finish := by
    rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
    · exfalso
      apply hp.2.2
      change f.start ∈ D
      exact hxStart ▸ hxD
    · exact Set.mem_singleton_iff.1 hxFinish
  exact congrArg some hxFinish.symm

/-- Restriction preserves the warp property. -/
theorem cleanPendingPart_isWarp
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.IsWarp W) : G.IsWarp (cleanPendingPart G W D) := by
  intro p hp q hq hpq
  exact hW hp.1.1 hq.1.1 hpq

/-- Restriction preserves finite character. -/
theorem cleanPendingPart_finiteCharacter
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (cleanPendingPart G W D) := by
  intro p hp
  exact hW hp.1.1

/-- The terminals to be continued from the clean pending part lie in the
stop-over. -/
theorem terminalFrontier_cleanPendingPart_subset
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : IsLinkageBetween G G.source D W) :
    G.terminalFrontier (cleanPendingPart G W D) ⊆ D := by
  rintro x ⟨p, hp, hpx⟩
  exact hW.terminalFrontier_subset ⟨p, hp.1.1, hpx⟩

/-- The direct requests contributed by boundary-starting pending members
also lie in the stop-over. -/
theorem initialSet_boundaryPendingPart_subset
    (G : DWeb V) (W : Set G.DPath) (D : Set V) :
    G.initialSet (boundaryPendingPart G W D) ⊆ D := by
  rintro x ⟨p, hp, hpx⟩
  exact hpx ▸ hp.2.2

/-- The exact quotient request set for one clean continuation step. -/
def pendingRequests (G : DWeb V) (W : Set G.DPath) (D : Set V) : Set V :=
  G.terminalFrontier (cleanPendingPart G W D) ∪
    G.initialSet (boundaryPendingPart G W D)

theorem pendingRequests_subset
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : IsLinkageBetween G G.source D W) :
    pendingRequests G W D ⊆ D :=
  Set.union_subset (terminalFrontier_cleanPendingPart_subset hW)
    (initialSet_boundaryPendingPart_subset G W D)

/-- For a separating trimmed stop-over, every pending request is a source
of the quotient. -/
theorem pendingRequests_subset_quotientSource
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D) :
    pendingRequests G W D ⊆ (G.quotient D).source := by
  rw [SingularContinuation.quotient_source_eq_stopover
    G hD.separator hD.stopover.minimal]
  exact pendingRequests_subset hD.linkage

end SingularPendingDecomposition
end CardinalInduction
end Erdos599
