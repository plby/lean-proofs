/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Real-terminal preservation from port equations

These graph-independent criteria apply to the exact output of any finite
or one-port splice. They do not require a particular bundled splice data
type, and therefore also cover an absent second port and connector cases.
-/

namespace Erdos599.ColouredSafeLocalTransactionRealLedger

open Set DirectedPath Alternating

universe u

variable {V : Type u} {D : DWeb V} {W K U : Set D.DPath} {R : V → V → Prop}
variable {s t x : V}

theorem realEdges_subset_of_cut
    (hs : IsRealTerminal (Gamma := D) R W s)
    (hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U) :
    RealEdges (Gamma := D) R W ⊆ RealEdges (Gamma := D) R U := by
  rintro e ⟨he, hreal⟩
  refine ⟨hcut ⟨he, ?_⟩, hreal⟩
  intro hest
  have hest' : e = (s, t) := Set.mem_singleton_iff.mp hest
  subst e
  exact hs.2 ⟨t, he, hreal⟩

/-- At the possible second contact the inserted family has no outgoing
edge, whether that contact is supplied by the connector or another path. -/
theorem isRealTerminal_of_finitePortEquations
    (hK : D.IsWarp K)
    (hhead : t ∈ D.vertexSet K → t ∈ D.terminalFrontier K)
    (hcap : D.vertexSet K ∩ D.vertexSet W ⊆ {s, t})
    (hV : D.vertexSet W ⊆ D.vertexSet U)
    (hE : familyEdges U ⊆ familyEdges W ∪ familyEdges K)
    (hx : IsRealTerminal (Gamma := D) R W x) (hxs : x ≠ s) :
    IsRealTerminal (Gamma := D) R U x := by
  refine ⟨hV hx.1, ?_⟩
  rintro ⟨y, hxy, hreal⟩
  rcases hE hxy with hold | hnew
  · exact hx.2 ⟨y, hold, hreal⟩
  · have hxK : x ∈ D.vertexSet K := (familyEdges_subset_vertexSet_prod K hnew).1
    rcases hcap ⟨hxK, hx.1⟩ with hxs' | hxt
    · exact hxs hxs'
    · have hxt' : x = t := Set.mem_singleton_iff.mp hxt
      subst x
      exact (not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp hK
        (hhead hxK)) ⟨y, hnew⟩

theorem isRealTerminal_of_onePortEquations
    (hcap : D.vertexSet K ∩ D.vertexSet W ⊆ {s})
    (hV : D.vertexSet W ⊆ D.vertexSet U)
    (hE : familyEdges U ⊆ familyEdges W ∪ familyEdges K)
    (hx : IsRealTerminal (Gamma := D) R W x) (hxs : x ≠ s) :
    IsRealTerminal (Gamma := D) R U x := by
  refine ⟨hV hx.1, ?_⟩
  rintro ⟨y, hxy, hreal⟩
  rcases hE hxy with hold | hnew
  · exact hx.2 ⟨y, hold, hreal⟩
  · exact hxs (Set.mem_singleton_iff.mp
      (hcap ⟨(familyEdges_subset_vertexSet_prod K hnew).1, hx.1⟩))

#print axioms realEdges_subset_of_cut
#print axioms isRealTerminal_of_finitePortEquations
#print axioms isRealTerminal_of_onePortEquations

end Erdos599.ColouredSafeLocalTransactionRealLedger
