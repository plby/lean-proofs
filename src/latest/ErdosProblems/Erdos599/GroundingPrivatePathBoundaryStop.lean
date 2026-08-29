/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# A private terminal path cannot have a boundary-valued incoming tail

The finite-priority grounding argument repeatedly cuts a source--boundary
path at the last deleted edge.  When the ambient witness meets the stopping
set only at its terminal boundary vertex, the tail of that deleted edge is
outside the stopping set.  This elementary fact is independent of the
particular switched relation and is useful before classifying the cause of
the deletion.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPrivatePathBoundaryStop

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The tail of an edge on a finite path is outside a set met only at the
path's terminal vertex. -/
theorem edge_tail_not_mem_of_support_inter_eq_finish
    (p : FinitePath Gamma.graph) (T : Set V)
    (hprivate : p.support ∩ T = {p.finish})
    {u v : V} (huv : (u, v) ∈ p.edgeSet) :
    u ∉ T := by
  intro huT
  have huSupport : u ∈ p.support :=
    (p.edgeSet_subset_support_prod huv).1
  have huEq : u = p.finish := by
    have huSingleton : u ∈ ({p.finish} : Set V) := by
      rw [← hprivate]
      exact ⟨huSupport, huT⟩
    simpa only [Set.mem_singleton_iff] using huSingleton
  exact
    (_root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
      p huv) huEq

/-- A finite prefix ending at the private boundary inherits the same
non-boundary conclusion for the tail of each of its edges.  Only support
containment in the ambient private witness is needed. -/
theorem edge_tail_not_mem_of_private_superpath
    (ambient q : FinitePath Gamma.graph) (T : Set V) (boundary : V)
    (hprivate : ambient.support ∩ T = {boundary})
    (hsupport : q.support ⊆ ambient.support)
    (hfinish : q.finish = boundary)
    {u v : V} (huv : (u, v) ∈ q.edgeSet) :
    u ∉ T := by
  intro huT
  have huSupportPrefix : u ∈ q.support :=
    (q.edgeSet_subset_support_prod huv).1
  have huSupport : u ∈ ambient.support := hsupport huSupportPrefix
  have huEqBoundary : u = boundary := by
    have huSingleton : u ∈ ({boundary} : Set V) := by
      rw [← hprivate]
      exact ⟨huSupport, huT⟩
    simpa only [Set.mem_singleton_iff] using huSingleton
  have huNeFinish : u ≠ q.finish :=
    _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
      q huv
  exact huNeFinish (huEqBoundary.trans hfinish.symm)

#print axioms edge_tail_not_mem_of_support_inter_eq_finish
#print axioms edge_tail_not_mem_of_private_superpath

end GroundingPrivatePathBoundaryStop
end Erdos599
