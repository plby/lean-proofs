/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteInputCoordinateInterval

/-!
# Raw direction-edge coverage for an infinite compressor

The infinite compressor retains every chronological raw edge in the
direction-labelled relation of the unique maximal run containing it.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- The raw edge at coordinate `n` belongs to the parent trace's edge set
labelled by its raw colour. -/
theorem rawEdge_mem_directionEdges
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) :
    S.rawEdge n ∈
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).directionEdges (S.colour n) := by
  obtain ⟨i, hlo, hhi⟩ := S.exists_runInterval hchange n
  have hcolour : S.colour n =
      S.colour (runBoundary S.colour hchange i) :=
    colour_eq_on_run S.colour hchange hlo hhi
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  refine ⟨((S.toInfiniteRunWalk hchange).run i).link,
    (S.toInfiniteRunWalk hchange).run_link_mem i, ?_, ?_⟩
  · rw [S.toInfiniteRunWalk_run_direction hchange i]
    exact hcolour.symm
  · change S.rawEdge n ∈ (S.projectedRun hchange i).link.path.edgeSet
    cases hdir : S.colour (runBoundary S.colour hchange i) with
    | forward =>
        rw [S.projectedRun_edgeSet_eq_forward hchange i hdir]
        refine ⟨n, hlo, hhi, ?_⟩
        simp [rawEdge, hcolour.trans hdir]
    | backward =>
        rw [S.projectedRun_edgeSet_eq_backward hchange i hdir]
        refine ⟨n, hlo, hhi, ?_⟩
        simp [rawEdge, hcolour.trans hdir]

/-- At a closing-set contact the outgoing raw coordinate is forward if
every backward link of the compressed trace avoids the closing set. -/
theorem colour_eq_forward_of_vertex_mem
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (n : Nat) (hnX : S.vertex n ∈ X) :
    S.colour n = .forward := by
  cases hcolour : S.colour n with
  | forward => rfl
  | backward =>
      have hraw := S.rawEdge_mem_directionEdges hchange n
      rw [hcolour] at hraw
      simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
      obtain ⟨l, hl, hdir, he⟩ := hraw
      have hnSupport : S.vertex n ∈ l.path.support := by
        have := (l.path.edgeSet_subset_support_prod he).2
        simpa only [rawEdge, hcolour] using this
      exact False.elim
        (Set.disjoint_left.1 (hbackwardOff l hl hdir) hnSupport hnX)

end Erdos599.Alternating.RunCompressor.InfiniteInput

#print axioms Erdos599.Alternating.RunCompressor.InfiniteInput.rawEdge_mem_directionEdges
#print axioms Erdos599.Alternating.RunCompressor.InfiniteInput.colour_eq_forward_of_vertex_mem
