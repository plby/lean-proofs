/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteCoordinateInternalSafety
import ErdosProblems.Erdos599.HalfwayInfiniteSuffixBackwardProvenance

/-!
# Internal safety of infinite compressor suffixes

The exact shifted compressor retains the parent's backward owners and is an
edge subtrace of the original infinite alternating path.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

/-- A shifted suffix of an internally safe infinite compressor trace is
internally safe for the same reference. -/
theorem InternallySafe.infiniteShift
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat)
    (hparent : InternallySafe Y
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace))
    (P : (AltPath.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I) :
    InternallySafe Y
      (.infinite ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace) := by
  let Pchild := S.shiftIndexedBackwardProvenance hchange a P
  have hedges :
      (AltPath.infinite ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace).edgeSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).edgeSet := by
    intro e he
    change e ∈ ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace.edgeSet at he
    rw [S.shift_trace_edgeSet hchange a] at he
    obtain ⟨n, _han, rfl⟩ := he
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

#print axioms Erdos599.Blueprint.InternallySafe.infiniteShift
