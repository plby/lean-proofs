/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeConnectorSplice
import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger

/-!
# Real-edge ledger for a graph-independent connector splice

A finite member of a finite-character switch warp replaces one represented
edge of an old warp; all other switch members are retained as companions.
If the old tail is an `R`-terminal and every connector edge is selected by
`R`, the exact splice preserves every old `R`-edge and every other old
`R`-terminal, while the connector makes its source nonterminal.

The terminal-port fact needed at the second possible carrier intersection
is derived from the distinguished member itself; it is not a premise.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeConnectorRealLedger

open DirectedPath Alternating
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The exact connector splice together with its predicate-parametric real
edge and pending-terminal ledger. -/
theorem exists_connectorSplice_realLedger
    {R : V → V → Prop} {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hedge : (s, t) ∈ familyEdges W)
    (p : FinitePath Gamma.graph)
    (hpK : (Sum.inl p : Gamma.DPath) ∈ K)
    (hps : p.start = s) (hpt : p.finish = t) (hne : s ≠ t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ {s, t})
    (hsReal : IsRealTerminal (Gamma := Gamma) R W s)
    (hpReal : ∀ e ∈ p.edgeSet, R e.1 e.2) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      Gamma.initialSet U = Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      p.edgeSet ⊆ familyEdges U ∧
      RealEdges (Gamma := Gamma) R W ⊆ RealEdges (Gamma := Gamma) R U ∧
      (∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R U x) ∧
      ¬IsRealTerminal (Gamma := Gamma) R U s ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet) := by
  obtain ⟨U, hU, hUI, hUT, hUV, hUE, hpU, htrace⟩ :=
    hW.exists_connectorSplice_with_rayTrace hK hKfinite hedge p hpK hps hpt hne hinter
  have hcut : ¬R s t := cut_not_real hsReal hedge
  have htK : t ∈ Gamma.terminalFrontier K := by
    refine ⟨Sum.inl p, hpK, ?_⟩
    change some p.finish = some t
    rw [hpt]
  have hRealEdges : RealEdges (Gamma := Gamma) R W ⊆
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
  have hRealTerminals : ∀ x : V,
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
        have hxPorts : x ∈ ({s, t} : Set V) := hinter ⟨hxK, hx.1⟩
        rcases Set.mem_insert_iff.mp hxPorts with hxeq | hxeq
        · exact hxs hxeq
        · have hxt : x = t := Set.mem_singleton_iff.mp hxeq
          subst x
          exact (not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
            hK htK) ⟨y, hyK⟩
  have hsNotReal : ¬IsRealTerminal (Gamma := Gamma) R U s := by
    have hpne : p.start ≠ p.finish := hps ▸ hpt ▸ hne
    have hnot := not_isRealTerminal_of_nontrivial_path p hpU hpReal hpne
    exact hps ▸ hnot
  exact ⟨U, hU, hUI, hUT, hUV, hUE, hpU,
    hRealEdges, hRealTerminals, hsNotReal, htrace⟩

#print axioms exists_connectorSplice_realLedger

end Erdos599.ColouredSafeConnectorRealLedger
