/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeOneSidedEdgeSplice
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger

/-!
# Real-edge ledger for the one-sided edge splice

This is the exact local transaction needed when the pruned inserted switch
has a real component starting at the cut tail `s`, but no component ending at
the cut head `t`.  The old suffix beginning at `t` is retained as a separate
path.  Thus no terminal hypothesis on `t` in the inserted warp is needed;
the genuine premise is `t ∉ V[K]`.

For an arbitrary predicate selecting real edges, an old real-terminal
hypothesis at `s` makes the removed edge non-real.  Consequently all old
real edges survive.  The single carrier intersection at `s` ensures that no
new inserted edge can destroy any other old real terminal.  A displayed
nontrivial all-real source path witnesses that `s` itself ceases to be a
real terminal.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeOneSidedEdgeRealLedger

open DirectedPath Alternating
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The exact one-sided splice together with its edge and pending-terminal
ledger. -/
theorem exists_oneSidedEdgeSplice_realLedger
    {R : V → V → Prop} {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (htOff : t ∉ Gamma.vertexSet K)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V))
    (hsReal : IsRealTerminal (Gamma := Gamma) R W s)
    (hsourceReal : ∀ e ∈ sourcePath.edgeSet, R e.1 e.2)
    (hsourceNontrivial : sourcePath.start ≠ sourcePath.finish) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        (Gamma.initialSet W ∪ (Gamma.initialSet K \ {s})) ∪ {t} ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      RealEdges (Gamma := Gamma) R W ⊆ RealEdges (Gamma := Gamma) R U ∧
      (∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R U x) ∧
      ¬ IsRealTerminal (Gamma := Gamma) R U s ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, hsourceEdges, htrace⟩ :=
    ColouredSafeOneSidedEdgeSplice.exists_oneSidedEdgeSplice_exact
      hW hK hKfinite hst sourcePath hsource hstart htOff hinter
  have hcut : ¬ R s t := cut_not_real hsReal hst
  have hrealEdges : RealEdges (Gamma := Gamma) R W ⊆
      RealEdges (Gamma := Gamma) R U := by
    rintro e ⟨heW, heR⟩
    refine ⟨?_, heR⟩
    rw [hUE]
    apply Or.inl
    refine ⟨heW, ?_⟩
    intro he
    have heq : e = (s, t) := Set.mem_singleton_iff.mp he
    subst e
    exact hcut heR
  have hrealTerminals : ∀ x : V,
      IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R U x := by
    intro x hx hxs
    refine ⟨?_, ?_⟩
    · rw [hUV]
      exact Or.inl hx.1
    · rintro ⟨y, hyU, hRxy⟩
      rw [hUE] at hyU
      rcases hyU with hyW | hyK
      · exact hx.2 ⟨y, hyW.1, hRxy⟩
      · have hxK : x ∈ Gamma.vertexSet K :=
          (familyEdges_subset_vertexSet_prod K hyK).1
        have hxPort : x ∈ ({s} : Set V) := hinter ⟨hxK, hx.1⟩
        exact hxs (Set.mem_singleton_iff.mp hxPort)
  have hsNot : ¬ IsRealTerminal (Gamma := Gamma) R U s := by
    have hnotAtStart := not_isRealTerminal_of_nontrivial_path sourcePath
      hsourceEdges hsourceReal hsourceNontrivial
    exact hstart ▸ hnotAtStart
  exact ⟨U, hU, hUE, hUV, hUI, hUT, hsourceEdges,
    hrealEdges, hrealTerminals, hsNot, htrace⟩

#print axioms exists_oneSidedEdgeSplice_realLedger

end Erdos599.ColouredSafeOneSidedEdgeRealLedger
