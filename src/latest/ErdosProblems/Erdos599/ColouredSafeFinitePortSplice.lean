/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeConnectorSplice
import ErdosProblems.Erdos599.ColouredSafeOneSidedEdgeSplice

/-!
# Exact insertion of a finite replacement with an optional terminal port

The source member either connects both old endpoints, ends separately while
another member supplies the terminal port, or ends separately with that
terminal absent. Reuse the existing connector, two-port and one-sided
constructions. Their common identities retain every companion and record
the extra old-suffix initial exactly when the terminal port is absent.
-/

noncomputable section

namespace Erdos599.ColouredSafeFinitePortSplice

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem exists_finitePortSplice_exact
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K) (hKfinite : Gamma.HasFiniteCharacter K)
    (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    (p : FinitePath Gamma.graph) (hpK : (Sum.inl p : Gamma.DPath) ∈ K)
    (hps : p.start = s)
    (hterminal : t ∈ Gamma.vertexSet K → t ∈ Gamma.terminalFrontier K)
    (hfresh : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ {s, t}) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        (Gamma.initialSet W ∪ (Gamma.initialSet K \ {s})) ∪ ({t} \ Gamma.vertexSet K) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      p.edgeSet ⊆ familyEdges U ∧
      (p.finish ≠ t → p.finish ∈ Gamma.terminalFrontier U) ∧
      ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
  have hmissing_of_mem : t ∈ Gamma.vertexSet K → ({t} \ Gamma.vertexSet K : Set V) = ∅ := by
    intro htK
    apply Set.Subset.antisymm ?_ (Set.empty_subset _)
    rintro x ⟨hxt, hxNot⟩
    exact hxNot (hxt ▸ htK)
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, htrace⟩ :
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
        familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
        Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
        Gamma.initialSet U =
          (Gamma.initialSet W ∪ (Gamma.initialSet K \ {s})) ∪ ({t} \ Gamma.vertexSet K) ∧
        Gamma.terminalFrontier U =
          Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
        ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
          ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
            ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
    by_cases hpt : p.finish = t
    · have htK : t ∈ Gamma.vertexSet K := ⟨.inl p, hpK, hpt ▸ p.finish_mem_support⟩
      obtain ⟨U, hU, hUI, hUT, hUV, hUE, _hpE, htrace⟩ :=
        hW.exists_connectorSplice_with_rayTrace hK hKfinite hedge p hpK hps hpt hne hfresh
      refine ⟨U, hU, hUE, hUV, ?_, hUT, ?_⟩
      · simpa only [hmissing_of_mem htK, Set.union_empty] using hUI
      · intro r hr
        obtain ⟨r0, hr0, hsub⟩ := htrace r hr
        exact ⟨r0, hr0, {(s, t)}, Set.finite_singleton _, hsub⟩
    · by_cases htK : t ∈ Gamma.vertexSet K
      · obtain ⟨q0, hq0, hq0t⟩ := hterminal htK
        obtain ⟨q, rfl⟩ := hKfinite hq0
        have hqt : q.finish = t := Option.some.inj hq0t
        have hpq : (Sum.inl p : Gamma.DPath) ≠ Sum.inl q := by
          intro heq
          exact hpt ((congrArg FinitePath.finish (Sum.inl.inj heq)).trans hqt)
        obtain ⟨U, hU, hUE, hUV, hUI, hUT, htrace⟩ :=
          ColouredSafeStrongTwoPortSplice.exists_twoPortSplice_exact
            hW hK hKfinite hedge p q hpK hq0 hpq hps hqt hfresh
        refine ⟨U, hU, hUE, hUV, ?_, hUT, htrace⟩
        simpa only [hmissing_of_mem htK, Set.union_empty] using hUI
      · have hmissing : ({t} \ Gamma.vertexSet K : Set V) = {t} := by
          ext x
          constructor
          · exact fun hx ↦ hx.1
          · intro hx
            exact ⟨hx, hx ▸ htK⟩
        have hterminalMissing : Gamma.terminalFrontier K \ {t} = Gamma.terminalFrontier K := by
          ext x
          constructor
          · exact fun hx ↦ hx.1
          · intro hx
            refine ⟨hx, ?_⟩
            intro hxt
            obtain ⟨q, hq, hqx⟩ := hx
            exact htK (hxt ▸ (show x ∈ Gamma.vertexSet K from
              ⟨q, hq, Gamma.terminal_mem_support hqx⟩))
        have hcontact : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ {s} := by
          intro x hx
          rcases hfresh hx with hxs | hxt
          · exact hxs
          · exact False.elim (htK (hxt ▸ hx.1))
        obtain ⟨U, hU, hUE, hUV, hUI, hUT, _hpE, htrace⟩ :=
          ColouredSafeOneSidedEdgeSplice.exists_oneSidedEdgeSplice_exact
            hW hK hKfinite hedge p hpK hps htK hcontact
        exact ⟨U, hU, hUE, hUV, hmissing.symm ▸ hUI,
          hterminalMissing.symm ▸ hUT, htrace⟩
  refine ⟨U, hU, hUE, hUV, hUI, hUT, ?_, ?_, htrace⟩
  · rw [hUE]
    intro edge he
    exact Or.inr (Set.mem_iUnion.mpr ⟨.inl p, Set.mem_iUnion.mpr ⟨hpK, he⟩⟩)
  · intro hpt
    rw [hUT]
    exact Or.inr ⟨⟨.inl p, hpK, rfl⟩, hpt⟩

#print axioms exists_finitePortSplice_exact

end Erdos599.ColouredSafeFinitePortSplice
