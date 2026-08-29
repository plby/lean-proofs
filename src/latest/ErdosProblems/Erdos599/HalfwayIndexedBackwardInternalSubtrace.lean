/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedBackwardSubtraceFlexible

/-!
# Restricting a globally internally-safe trace

The post-closure assignment is globally internally safe, not globally safe
at its exposed endpoints.  Literal contact subtraces inherit exactly that
internal certificate using their restricted indexed backward owners.
-/

noncomputable section

namespace Erdos599.Blueprint

open Set DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {parent child : AltPath Gamma.graph} {I : Type w}

theorem InternallySafe.of_backwardLiteralInternalSubtrace
    (hparent : InternallySafe Y parent)
    (P : parent.IndexedBackwardProvenance Y I)
    (hback : ∀ l ∈ child.links, l.direction = .backward → l ∈ parent.links)
    (hedges : child.edgeSet ⊆ parent.edgeSet) :
    InternallySafe Y child := by
  let Pchild := P.restrictBackwardLinks hback
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

#print axioms Erdos599.Blueprint.InternallySafe.of_backwardLiteralInternalSubtrace
