/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCrossContactInternalSafety
import ErdosProblems.Erdos599.HalfwayIndexedBackwardInternalSubtrace

/-!
# Internal safety of a cross-contact interval in the actual assignment

The post-closure producer supplies internal safety, rather than endpoint
safety, for its whole assigned trace.  A cross-contact interval changes
only its two forward boundary links, so the retained indexed backward
owners and literal edge containment suffice to inherit that certificate.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

/-- The actual internally-safe parent form used by the post-closure
assignment. -/
theorem crossContactInterval_internallySafe_of_internal
    (Q : FiniteTrace Gamma.graph) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X)
    (hparent : InternallySafe Y (.finite Q))
    (P : (AltPath.finite Q).IndexedBackwardProvenance Y I) :
    InternallySafe Y (.finite (Q.crossContactInterval X first last hfl
      Sfirst Slast hlastContact hbackwardOff)) := by
  apply InternallySafe.of_backwardLiteralInternalSubtrace hparent P
  · exact crossContactInterval_backwardLink_mem_parent Q X first last hfl
      Sfirst Slast hlastContact hbackwardOff
  · exact Q.crossContactInterval_edgeSet_subset X first last hfl Sfirst Slast
      hlastContact hbackwardOff

end Erdos599.Blueprint

#print axioms Erdos599.Blueprint.crossContactInterval_internallySafe_of_internal
