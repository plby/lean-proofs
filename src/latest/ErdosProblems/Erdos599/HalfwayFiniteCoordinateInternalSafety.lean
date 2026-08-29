/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteCoordinateBackwardProvenance

/-!
# Internal safety of finite coordinate restrictions

Every coordinate interval of a compressor trace inherits the parent's
indexed backward-owner certificate.  The remaining ray and cycle clauses
are monotone under the exact edge-set restriction.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

/-- A coordinate interval cut from a finite compressor trace is internally
safe whenever the parent trace is internally safe and carries the compressor's
indexed backward-owner certificate. -/
theorem InternallySafe.coordinateInterval
    (S : RunCompressor.FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (hparent : InternallySafe Y
      (.finite S.toFiniteRunWalk.toFiniteTrace))
    (P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y I) :
    InternallySafe Y
      (.finite
        (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace) := by
  let Pchild := S.coordinateIntervalIndexedBackwardProvenance
    a b hab hb P
  have hedges :
      (AltPath.finite
        (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace
        ).edgeSet ⊆
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).edgeSet :=
    S.coordinateInterval_trace_edgeSet_subset a b hab hb
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

#print axioms Erdos599.Blueprint.InternallySafe.coordinateInterval
