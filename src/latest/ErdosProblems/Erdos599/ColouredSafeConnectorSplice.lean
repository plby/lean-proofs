/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakSubdivision

/-!
# A graph-independent connector splice

A distinguished finite member of a finite-character warp replaces one edge
of an old warp.  The other members of the new warp are then adjoined as
disjoint companions.  The result records the exact edge, carrier, initial,
and terminal changes and traces every ray back to the old warp.
-/

noncomputable section

namespace Erdos599.DWeb

open Set Cardinal Order _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Replace an old edge `s → t` by the distinguished finite member `p` of
`K`, and adjoin every other member of `K`.  The only permitted intersection
of the two input warps is at the connector endpoints. -/
theorem IsWarp.exists_connectorSplice_with_rayTrace
    {W K : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    {s t : V} (hedge : (s, t) ∈ familyEdges W)
    (p : FinitePath Gamma.graph) (hpK : (Sum.inl p : Gamma.DPath) ∈ K)
    (hps : p.start = s) (hpt : p.finish = t) (hne : s ≠ t)
    (hfresh : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ {s, t}) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      Gamma.initialSet U = Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      p.edgeSet ⊆ familyEdges U ∧
      ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet := by
  let pd : Gamma.DPath := Sum.inl p
  let C : Set Gamma.DPath := K \ {pd}
  have hpInitial : pd.initial = s := by
    change p.start = s
    exact hps
  have hpTerminal : pd.terminal? = some t := by
    change some p.finish = some t
    rw [hpt]
  have hpFresh : Gamma.vertexSet W ∩ p.support ⊆ {s, t} := by
    intro x hx
    exact hfresh ⟨⟨pd, hpK, hx.2⟩, hx.1⟩
  obtain ⟨U0, hU0, hU0I, hU0T, hU0V, hU0E, hU0Trace⟩ :=
    hW.exists_edgeSubdivision_with_rayTrace hedge p hps hpt hpFresh
  have hC : Gamma.IsWarp C := fun q hq r hr hqr ↦ hK hq.1 hr.1 hqr
  have hCp : Disjoint (Gamma.vertexSet C) p.support := by
    apply Set.disjoint_left.mpr
    intro x hxC hxp
    obtain ⟨q, hqC, hxq⟩ := hxC
    exact Set.disjoint_left.mp
      (hK hqC.1 hpK (fun h ↦ hqC.2 (Set.mem_singleton_iff.mpr h)))
      hxq hxp
  have hCW : Disjoint (Gamma.vertexSet C) (Gamma.vertexSet W) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxW
    obtain ⟨q, hqC, hxq⟩ := hxC
    have hx := hfresh ⟨⟨q, hqC.1, hxq⟩, hxW⟩
    have hqp : q ≠ pd := fun h ↦ hqC.2 (Set.mem_singleton_iff.mpr h)
    have hdisj := hK hqC.1 hpK hqp
    rcases Set.mem_insert_iff.mp hx with rfl | hxt
    · exact Set.disjoint_left.mp hdisj hxq (hps.symm ▸ p.start_mem_support)
    · have hxt' : x = t := Set.mem_singleton_iff.mp hxt
      exact Set.disjoint_left.mp hdisj hxq (hxt'.symm ▸ hpt.symm ▸ p.finish_mem_support)
  have hCU0 : Disjoint (Gamma.vertexSet U0) (Gamma.vertexSet C) := by
    rw [hU0V, Set.disjoint_union_left]
    exact ⟨hCW.symm, hCp.symm⟩
  let U : Set Gamma.DPath := U0 ∪ C
  have hU : Gamma.IsWarp U := by
    intro q hq r hr hqr
    rcases hq with hq | hq <;> rcases hr with hr | hr
    · exact hU0 hq hr hqr
    · apply Set.disjoint_left.mpr
      intro x hxq hxr
      exact Set.disjoint_left.mp hCU0 ⟨q, hq, hxq⟩ ⟨r, hr, hxr⟩
    · apply Set.disjoint_left.mpr
      intro x hxq hxr
      exact Set.disjoint_left.mp hCU0 ⟨r, hr, hxr⟩ ⟨q, hq, hxq⟩
    · exact hC hq hr hqr
  have hUIunion : Gamma.initialSet U =
      Gamma.initialSet U0 ∪ Gamma.initialSet C := by
    ext x
    change (∃ q ∈ U0 ∪ C, q.initial = x) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hUTunion : Gamma.terminalFrontier U =
      Gamma.terminalFrontier U0 ∪ Gamma.terminalFrontier C := by
    ext x
    change (∃ q ∈ U0 ∪ C, q.terminal? = some x) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hVUnion : Gamma.vertexSet U =
      Gamma.vertexSet U0 ∪ Gamma.vertexSet C := by
    ext x
    change (∃ q ∈ U0 ∪ C, x ∈ q.support) ↔ _
    simp only [Set.mem_union, or_and_right, exists_or]
    rfl
  have hEUnion : familyEdges U = familyEdges U0 ∪ familyEdges C := by
    ext e
    simp only [familyEdges, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq | hq, he⟩
      · exact Or.inl ⟨q, hq, he⟩
      · exact Or.inr ⟨q, hq, he⟩
    · rintro (⟨q, hq, he⟩ | ⟨q, hq, he⟩)
      · exact ⟨q, Or.inl hq, he⟩
      · exact ⟨q, Or.inr hq, he⟩
  have hCI : Gamma.initialSet C = Gamma.initialSet K \ {s} := by
    ext x
    constructor
    · rintro ⟨q, hqC, hqx⟩
      refine ⟨⟨q, hqC.1, hqx⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      intro hxs
      have hqxp : q.initial ∈ pd.support := by
        rw [hqx, hxs, ← hpInitial]
        exact p.start_mem_support
      exact Set.disjoint_left.mp
        (hK hqC.1 hpK (fun h ↦ hqC.2 (Set.mem_singleton_iff.mpr h)))
        (q.initial_mem_support) hqxp
    · rintro ⟨⟨q, hqK, hqx⟩, hxs⟩
      refine ⟨q, ⟨hqK, ?_⟩, hqx⟩
      rw [Set.mem_singleton_iff]
      intro hqpd
      subst q
      exact hxs (Set.mem_singleton_iff.mpr (hqx.symm.trans hpInitial))
  have hCT : Gamma.terminalFrontier C = Gamma.terminalFrontier K \ {t} := by
    ext x
    constructor
    · rintro ⟨q, hqC, hqx⟩
      refine ⟨⟨q, hqC.1, hqx⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      intro hxt
      have hxq : x ∈ q.support := Gamma.terminal_mem_support hqx
      have hxp : x ∈ pd.support := by
        rw [hxt, ← hpt]
        exact p.finish_mem_support
      exact Set.disjoint_left.mp
        (hK hqC.1 hpK (fun h ↦ hqC.2 (Set.mem_singleton_iff.mpr h)))
        hxq hxp
    · rintro ⟨⟨q, hqK, hqx⟩, hxt⟩
      refine ⟨q, ⟨hqK, ?_⟩, hqx⟩
      rw [Set.mem_singleton_iff]
      intro hqpd
      subst q
      have : x = t := Option.some.inj (hqx.symm.trans hpTerminal)
      exact hxt (Set.mem_singleton_iff.mpr this)
  have hKV : p.support ∪ Gamma.vertexSet C = Gamma.vertexSet K := by
    ext x
    constructor
    · rintro (hxp | ⟨q, hqC, hxq⟩)
      · exact ⟨pd, hpK, hxp⟩
      · exact ⟨q, hqC.1, hxq⟩
    · rintro ⟨q, hqK, hxq⟩
      by_cases hqpd : q = pd
      · subst q
        exact Or.inl hxq
      · exact Or.inr ⟨q, ⟨hqK, hqpd⟩, hxq⟩
  have hKE : p.edgeSet ∪ familyEdges C = familyEdges K := by
    ext e
    simp only [familyEdges, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hep | ⟨q, hqC, heq⟩)
      · exact ⟨pd, hpK, hep⟩
      · exact ⟨q, hqC.1, heq⟩
    · rintro ⟨q, hqK, heq⟩
      by_cases hqpd : q = pd
      · subst q
        exact Or.inl heq
      · exact Or.inr ⟨q, ⟨hqK, hqpd⟩, heq⟩
  refine ⟨U, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUIunion, hU0I, hCI]
  · rw [hUTunion, hU0T, hCT]
  · rw [hVUnion, hU0V, Set.union_assoc, hKV]
  · rw [hEUnion, hU0E, Set.union_assoc, hKE]
  · rw [hEUnion, hU0E, Set.union_assoc, hKE]
    intro e hep
    right
    rw [← hKE]
    exact Or.inl hep
  · intro r hr
    rcases hr with hr | hr
    · exact hU0Trace r hr
    · obtain ⟨q, hqr⟩ := hKfinite hr.1
      cases hqr

#print axioms IsWarp.exists_connectorSplice_with_rayTrace

end Erdos599.DWeb
