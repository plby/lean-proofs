/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TerminalContactSwitchInfinite
import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# Rooting sinks after a finite perturbation of a path/ray warp

No reverse ray and local biuniqueness suffice to root each nonisolated sink
at a positive-balance vertex. Directed cycles do not affect this statement:
discarding their components preserves every nonzero boundary balance.
Finite perturbations of an arbitrary warp, including one with rays, have
no reverse ray. Thus a finite component transaction needs actual signed
boundary accounting, not an extra finite-character assumption.
-/

noncomputable section

open Set

namespace Erdos599.GroundingFinitePerturbationRooting

open DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Cycle-discarding realization retaining the exact surviving edge set. -/
theorem exists_warp_with_edges_sdiff_cyclic
    (E : Set (V × V))
    (hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hreverse : ¬ ContainsReverseDirectedRay E) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W = E \ cyclicEdges E ∧
        isolatedVertices W = ∅ ∧
        ∀ x, edgeBalance (familyEdges W) x = edgeBalance E x := by
  have hbi' : Relator.BiUnique fun x y ↦ (x, y) ∈ E \ cyclicEdges E :=
    ⟨fun _ _ _ hx hy ↦ hbi.1 hx.1 hy.1,
      fun _ _ _ hx hy ↦ hbi.2 hx.1 hy.1⟩
  obtain ⟨W, hW, hWE, hWI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma (E \ cyclicEdges E) ∅
      (fun _ he ↦ hgraph he.1) hbi'
      (sdiff_cyclicEdges_not_containsDirectedCycle E)
      (fun h ↦ hreverse ⟨h.choose, fun n ↦ (h.choose_spec n).1⟩)
      (by simp)
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hWE]
  exact edgeBalance_sdiff_cyclicEdges hbi x

/-- A nonisolated sink is reached from a positive-balance vertex whenever
the relation has no reverse ray. Cycles elsewhere are permitted. -/
theorem sink_rooted_of_noReverseRay
    (E : Set (V × V)) (A : Set V)
    (hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hreverse : ¬ ContainsReverseDirectedRay E)
    (hboundary : ∀ x, edgeBalance E x = 1 → x ∈ A)
    {t : V} (ht : t ∈ A ∨ HasIncoming E t)
    (hsink : ¬HasOutgoing E t) :
    ∃ a ∈ A, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t := by
  rcases ht with ht | ht
  · exact ⟨t, ht, .refl⟩
  obtain ⟨W, hW, hWE, hWI, hbalance⟩ :=
    exists_warp_with_edges_sdiff_cyclic E hgraph hbi hreverse
  have htBalance : edgeBalance (familyEdges W) t = -1 := by
    rw [hbalance]
    exact edgeBalance_eq_neg_one_iff.mpr ⟨ht, hsink⟩
  have htW : t ∈ Gamma.terminalFrontier W :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp hW).mpr
      (Or.inr htBalance)
  obtain ⟨p, hpW, hpterm⟩ := htW
  rcases p with p | r
  · have hfinish : p.finish = t := Option.some.inj hpterm
    have hstart : p.start ∈ Gamma.initialSet W := ⟨.inl p, hpW, rfl⟩
    have hstartBalance : edgeBalance (familyEdges W) p.start = 1 := by
      rcases (mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hW).mp
          hstart with hi | hb
      · simp only [hWI, Set.mem_empty_iff_false] at hi
      · exact hb
    have hstartA : p.start ∈ A := hboundary p.start (by
      rw [← hbalance]; exact hstartBalance)
    refine ⟨p.start, hstartA, ?_⟩
    rw [← hfinish]
    have hpE : p.edgeSet ⊆ E := by
      intro e he
      have heW : e ∈ familyEdges W := by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨.inl p, hpW, he⟩
      rw [hWE] at heW
      exact heW.1
    exact Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
      (fun _ _ he ↦ hpE he) p.start p.finish
      (Alternating.Walk.reflTransGen_edgeSet p.walk)
  · cases hpterm

/-- Actual sink coverage after a finite edge perturbation of an arbitrary
path/ray warp. The only remaining boundary premise is the explicit local
positive-balance condition produced by a transaction. -/
theorem sink_rooted_of_finitePerturbation
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (E F : Set (V × V)) (A : Set V)
    (hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hfinite : F.Finite) (hE : E ⊆ familyEdges W ∪ F)
    (hboundary : ∀ x, edgeBalance E x = 1 → x ∈ A)
    {t : V} (ht : t ∈ A ∨ HasIncoming E t)
    (hsink : ¬HasOutgoing E t) :
    ∃ a ∈ A, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t := by
  apply sink_rooted_of_noReverseRay E A hgraph hbi _ hboundary ht hsink
  exact not_containsReverseDirectedRay_of_subset_union_finite hE
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay hW)
    hfinite

#print axioms exists_warp_with_edges_sdiff_cyclic
#print axioms sink_rooted_of_noReverseRay
#print axioms sink_rooted_of_finitePerturbation

end Erdos599.GroundingFinitePerturbationRooting
