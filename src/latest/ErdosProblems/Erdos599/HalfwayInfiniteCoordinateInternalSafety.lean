/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteCoordinateBackwardProvenance

/-!
# Internal safety of bounded infinite-compressor intervals

A bounded coordinate interval of the actual infinite compressor inherits
the parent's indexed backward owners.  Its literal raw-edge description
also embeds in the parent infinite trace, so the ray and cycle exclusions
restrict without any finite-character premise on the reference.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

/-- Every bounded coordinate interval of an internally safe infinite
compressor trace is internally safe for the same reference. -/
theorem InternallySafe.infiniteCoordinateInterval
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (hparent : InternallySafe Y
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace))
    (P : (AltPath.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I) :
    InternallySafe Y
      (.finite
        (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace) := by
  let Pchild := S.coordinateIntervalIndexedBackwardProvenance
    hchange a b hab P
  have hedges :
      (AltPath.finite
        (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace
        ).edgeSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).edgeSet := by
    intro e he
    change e ∈
      (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.edgeSet at he
    rw [S.coordinateInterval_trace_edgeSet a b hab] at he
    obtain ⟨n, _han, _hnb, rfl⟩ := he
    change S.rawEdge n ∈
      (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet
    exact S.rawEdge_mem_toInfiniteTrace hchange n
  refine ⟨hparent.1, Pchild.backwardLinksOn,
    Pchild.intervals hparent.1, ?_, ?_⟩
  · rintro ⟨R, hR⟩
    exact hparent.2.2.2.1 ⟨R, hR.trans (by
      rintro e ⟨he, hnot⟩
      exact ⟨hedges he, hnot⟩)⟩
  · rintro ⟨C, hC⟩
    exact hparent.2.2.2.2 ⟨C, hC.trans (by
      rintro e ⟨he, hnot⟩
      exact ⟨hedges he, hnot⟩)⟩

end Erdos599.Blueprint

#print axioms Erdos599.Blueprint.InternallySafe.infiniteCoordinateInterval
