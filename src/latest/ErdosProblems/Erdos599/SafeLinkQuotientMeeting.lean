/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientRoofTransport

/-!
# Support rigidity for paths in a quotient

A path in `G / X` cannot enter `X` after its initial vertex.  This small
same-path lemma is the support fact used when tracing an essential path of
the Section 6 countable arrow back through the dependent stages.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Every occurrence of a quotient-set vertex on a quotient path is its
initial vertex. -/
theorem eq_initial_of_mem_support_of_mem_quotient
    (X : Set V) (p : (G.quotient X).DPath) {x : V}
    (hxp : x ∈ p.support) (hxX : x ∈ X) :
    x = p.initial := by
  rcases p with p | r
  · rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient X).graph.Adj p.walk).1 hxp with hxstart | hxtail
    · exact hxstart
    · exact ((G.quotientWalk_tail_avoids p.walk hxtail).2 hxX).elim
  · obtain ⟨n, rfl⟩ := hxp
    cases n with
    | zero => rfl
    | succ n =>
        have h := G.quotient_adj_endpoints (S := X) (r.adj_succ n)
        exact (h.2.2 hxX).elim

end DWeb

end Erdos599
