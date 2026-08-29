/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.DeferredStageReferenceEmbedding
import ErdosProblems.Erdos599.NondegenerateHammockClosure

/-!
# Nondegeneracy under passage to the limiting ladder reference

Inside one selected stage roof, a finite degeneracy witness for the limiting
reference is already a degeneracy witness for the stage reference.  The roof
hypothesis on the alternating path is essential: it makes the inserted edges
roofed, while the no-late-entry theorem reflects every retained limiting
reference edge back to the selected stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DWeb.DirectedPath Ladder Alternating Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

private theorem pathFamilyEdgeSet_eq_familyEdges
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    Gamma.pathFamilyEdgeSet W = familyEdges W := by
  ext e
  simp only [DWeb.pathFamilyEdgeSet, familyEdges, Set.mem_ofPred_eq,
    Set.mem_iUnion]
  constructor <;> rintro ⟨p, hp, he⟩ <;> exact ⟨p, hp, he⟩

private theorem finitePath_support_subset_roof_of_switchedLimit
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {p : DirectedPath.FinitePath Gamma.graph}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hpEdges : p.edgeSet ⊆ switchedEdges L.limitWarp Q)
    (hfinishRoof : p.finish ∈ Gamma.roof (L.frontier a)) :
    p.support ⊆ Gamma.roof (L.frontier a) := by
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (L.frontier a) →
      x ∈ Gamma.roof (L.frontier a) := by
    intro x y hxy hyRoof
    rcases hpEdges hxy with hreference | hpath
    · have hreference' := hreference.1
      change (x, y) ∈ familyEdges
        (L.accumulated (Ladder.finalStage kappa)) at hreference'
      rw [← pathFamilyEdgeSet_eq_familyEdges] at hreference'
      have hstage : (x, y) ∈ Gamma.pathFamilyEdgeSet (L.warpAt a) :=
        pathFamilyEdgeSet_of_head_mem_roof_frontier hL a
          kappa.ord le_rfl a.2.le hreference' hyRoof
      have hxRaw := edge_tail_mem_strictRoof_of_mem_warpAt hL a hstage
      rw [L.frontier_eq_essential_terminalFrontier
        hL.roofsSourceAtStages, Gamma.roof_essential]
      exact hxRaw.1
    · exact hQRoof (Q.edgeSet_subset_vertexSet_prod hpath.1).1
  intro x hxp
  let s := p.suffixFrom x hxp
  have hs :=
    _root_.Erdos599.DWeb.KappaLadder.Walk.start_mem_of_meets_of_backwardClosed
      (w := s.walk) (R := Gamma.roof (L.frontier a))
      (fun {_y _z} hyz hzRoof ↦
        hback (p.suffixFrom_edgeSet_subset x hxp hyz) hzRoof)
      ⟨p.finish, s.finish_mem_support, by simpa [s] using hfinishRoof⟩
  simpa [s] using hs

/-- A finite degeneracy witness against the limiting reference which stays
inside the selected roof is already a witness against the stage reference. -/
theorem isDegenerate_warpAt_of_limitWarp_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hvRoof : v ∈ Gamma.roof (L.frontier a))
    (hdeg : IsDegenerate L.limitWarp Q (.vertex v)) :
    IsDegenerate (L.warpAt a) Q (.vertex v) := by
  change ∃ p : DirectedPath.FinitePath Gamma.graph,
    p.start = Q.initial ∧ p.finish = v ∧
      (Cyclowarp.application L.limitWarp Q).ContainsFinitePath p at hdeg
  change ∃ p : DirectedPath.FinitePath Gamma.graph,
    p.start = Q.initial ∧ p.finish = v ∧
      (Cyclowarp.application (L.warpAt a) Q).ContainsFinitePath p
  obtain ⟨p, hpStart, hpFinish, hpEdges, hpNontrivial⟩ := hdeg
  have hpRoof : p.support ⊆ Gamma.roof (L.frontier a) :=
    finitePath_support_subset_roof_of_switchedLimit hL hQRoof hpEdges
      (hpFinish.symm ▸ hvRoof)
  refine ⟨p, hpStart, hpFinish, ?_, ?_⟩
  · intro e he
    rcases hpEdges he with hreference | hpath
    · have hreference' := hreference.1
      change e ∈ familyEdges
        (L.accumulated (Ladder.finalStage kappa)) at hreference'
      rw [← pathFamilyEdgeSet_eq_familyEdges] at hreference'
      have hstage := pathFamilyEdgeSet_of_head_mem_roof_frontier hL a
          kappa.ord le_rfl a.2.le hreference'
            (hpRoof (p.edgeSet_subset_support_prod he).2)
      rw [pathFamilyEdgeSet_eq_familyEdges] at hstage
      exact Or.inl ⟨hstage, hreference.2⟩
    · exact Or.inr ⟨hpath.1, fun hstage ↦
        hpath.2 ((hL.stageReferenceEmbedding a).familyEdges_subset hstage)⟩
  · rcases hpNontrivial with hpNontrivial | hpIsolated
    · exact Or.inl hpNontrivial
    · right
      have hxRoof : p.start ∈ Gamma.roof (L.frontier a) := by
        rw [hpStart]
        exact hQRoof Q.initial_mem_vertexSet
      obtain ⟨q, hqStage, hqLimit⟩ :=
        exists_warpAt_prefix_of_limitComponent_initial_mem_roof hL a
          hpIsolated hxRoof
      have hqSupport : q.support ⊆ {q.initial} := by
        intro x hxq
        have hxLimit := Gamma.support_mono_of_extends hqLimit hxq
        rw [Gamma.support_trivialPath] at hxLimit
        simpa [Gamma.extends_initial hqLimit] using hxLimit
      have hqTrivial := Gamma.path_eq_trivial_of_support_subset q hqSupport
      have hqInitial : q.initial = p.start := by
        simpa using Gamma.extends_initial hqLimit
      change Gamma.trivialPath p.start ∈ L.warpAt a
      rw [← hqInitial, ← hqTrivial]
      exact hqStage

/-- Contrapositive form used by filtered hammock rows. -/
theorem not_isDegenerate_limitWarp_of_warpAt_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hvRoof : v ∈ Gamma.roof (L.frontier a))
    (hnondeg : ¬IsDegenerate (L.warpAt a) Q (.vertex v)) :
    ¬IsDegenerate L.limitWarp Q (.vertex v) := by
  intro hdeg
  exact hnondeg
    (isDegenerate_warpAt_of_limitWarp_of_subset_roof hL hQRoof hvRoof hdeg)

/-- For distinct finite endpoints the converse also holds.  A stage
reference edge remains a limiting-reference edge.  Conversely, an inserted
edge of `Q` cannot disappear later: its head is roofed, so the no-late-entry
lemma would already put that reference edge at the selected stage.  Endpoint
distinctness excludes the singleton-component clause of degeneracy. -/
theorem isDegenerate_limitWarp_of_warpAt_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hne : Q.initial ≠ v)
    (hdeg : IsDegenerate (L.warpAt a) Q (.vertex v)) :
    IsDegenerate L.limitWarp Q (.vertex v) := by
  change ∃ p : DirectedPath.FinitePath Gamma.graph,
    p.start = Q.initial ∧ p.finish = v ∧
      (Cyclowarp.application (L.warpAt a) Q).ContainsFinitePath p at hdeg
  change ∃ p : DirectedPath.FinitePath Gamma.graph,
    p.start = Q.initial ∧ p.finish = v ∧
      (Cyclowarp.application L.limitWarp Q).ContainsFinitePath p
  obtain ⟨p, hpStart, hpFinish, hpEdges, _hpNontrivial⟩ := hdeg
  have hpNe : p.start ≠ p.finish := by
    intro heq
    apply hne
    exact hpStart.symm.trans (heq.trans hpFinish)
  refine ⟨p, hpStart, hpFinish, ?_, Or.inl hpNe⟩
  intro e he
  rcases hpEdges he with hreference | hpath
  · exact Or.inl ⟨
      (hL.stageReferenceEmbedding a).familyEdges_subset hreference.1,
      hreference.2⟩
  · refine Or.inr ⟨hpath.1, ?_⟩
    intro hlimit
    have hlimit' := hlimit
    change e ∈ familyEdges
      (L.accumulated (Ladder.finalStage kappa)) at hlimit'
    rw [← pathFamilyEdgeSet_eq_familyEdges] at hlimit'
    have hstage := pathFamilyEdgeSet_of_head_mem_roof_frontier hL a
      kappa.ord le_rfl a.2.le hlimit'
        (hQRoof (Q.edgeSet_subset_vertexSet_prod hpath.1).2)
    rw [pathFamilyEdgeSet_eq_familyEdges] at hstage
    exact hpath.2 hstage

/-- With distinct endpoints, degeneracy is exactly invariant between a
stage reference and the limiting reference for a path contained in that
stage roof. -/
theorem isDegenerate_limitWarp_iff_warpAt_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hvRoof : v ∈ Gamma.roof (L.frontier a))
    (hne : Q.initial ≠ v) :
    IsDegenerate L.limitWarp Q (.vertex v) ↔
      IsDegenerate (L.warpAt a) Q (.vertex v) := by
  constructor
  · exact isDegenerate_warpAt_of_limitWarp_of_subset_roof hL hQRoof hvRoof
  · exact isDegenerate_limitWarp_of_warpAt_of_subset_roof hL hQRoof hne

/-- Nondegeneracy is therefore invariant under the same hypotheses. -/
theorem not_isDegenerate_limitWarp_iff_warpAt_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hvRoof : v ∈ Gamma.roof (L.frontier a))
    (hne : Q.initial ≠ v) :
    (¬IsDegenerate L.limitWarp Q (.vertex v)) ↔
      ¬IsDegenerate (L.warpAt a) Q (.vertex v) := by
  rw [isDegenerate_limitWarp_iff_warpAt_of_subset_roof hL hQRoof hvRoof hne]

/-- The roof-filtered nondegeneracy predicate persists to every later
stage.  The proof deliberately factors through the limiting reference;
there is no monotonicity claim for unroofed alternating paths. -/
theorem roofedNondegenerate_warpAt_mono
    (hL : HalfwayGeometry L)
    {b : Stage kappa} (hab : a ≤ b)
    {Q : AltPath Gamma.graph} {v : V}
    (hterminal : Q.terminal? = some v) (hne : Q.initial ≠ v)
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hnondeg : ¬IsDegenerate (L.warpAt a) Q (.vertex v)) :
    Q.vertexSet ⊆ Gamma.roof (L.frontier b) ∧
      ¬IsDegenerate (L.warpAt b) Q (.vertex v) := by
  have hQRoofB : Q.vertexSet ⊆ Gamma.roof (L.frontier b) := by
    rcases hab.eq_or_lt with rfl | hab
    · exact hQRoof
    · exact hQRoof.trans (Gamma.roof_cut (hL.frontierChronology hab))
  have hvRoofA : v ∈ Gamma.roof (L.frontier a) :=
    hQRoof (Q.mem_vertexSet_of_terminal_eq hterminal)
  have hvRoofB : v ∈ Gamma.roof (L.frontier b) :=
    hQRoofB (Q.mem_vertexSet_of_terminal_eq hterminal)
  have hglobal : ¬IsDegenerate L.limitWarp Q (.vertex v) :=
    (not_isDegenerate_limitWarp_iff_warpAt_of_subset_roof
      hL hQRoof hvRoofA hne).2 hnondeg
  exact ⟨hQRoofB,
    (not_isDegenerate_limitWarp_iff_warpAt_of_subset_roof
      hL hQRoofB hvRoofB hne).1 hglobal⟩

/-- A globally nondegenerate finite-end path is locally nondegenerate at
every stage whose roof already contains it. -/
theorem not_isDegenerate_warpAt_of_limitWarp_of_subset_roof
    (hL : HalfwayGeometry L)
    {Q : AltPath Gamma.graph} {v : V}
    (hterminal : Q.terminal? = some v) (hne : Q.initial ≠ v)
    (hQRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hnondeg : ¬IsDegenerate L.limitWarp Q (.vertex v)) :
    ¬IsDegenerate (L.warpAt a) Q (.vertex v) := by
  exact (not_isDegenerate_limitWarp_iff_warpAt_of_subset_roof
    hL hQRoof (hQRoof (Q.mem_vertexSet_of_terminal_eq hterminal)) hne).1
      hnondeg

/-- Once a stage-nondegenerate family has separately been transported as a
limiting-reference hammock, same-stage roof containment upgrades it to a
nondegenerate limiting-reference hammock. -/
theorem nondegenerateHammock_limitWarp_of_warpAt_of_subset_roof
    (hL : HalfwayGeometry L)
    {H : Set (AltPath Gamma.graph)} {u v : V}
    (hHammock : Hammock Gamma L.limitWarp u (.vertex v) H)
    (hnondeg : ∀ Q ∈ H, ¬IsDegenerate (L.warpAt a) Q (.vertex v))
    (hRoof : ∀ Q ∈ H, Q.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hvRoof : v ∈ Gamma.roof (L.frontier a)) :
    NondegenerateHammock Gamma L.limitWarp u (.vertex v) H := by
  refine ⟨hHammock, ?_⟩
  intro Q hQ
  exact not_isDegenerate_limitWarp_of_warpAt_of_subset_roof hL
    (hRoof Q hQ) hvRoof (hnondeg Q hQ)

#print axioms isDegenerate_warpAt_of_limitWarp_of_subset_roof
#print axioms not_isDegenerate_limitWarp_of_warpAt_of_subset_roof
#print axioms isDegenerate_limitWarp_of_warpAt_of_subset_roof
#print axioms isDegenerate_limitWarp_iff_warpAt_of_subset_roof
#print axioms not_isDegenerate_limitWarp_iff_warpAt_of_subset_roof
#print axioms roofedNondegenerate_warpAt_mono
#print axioms not_isDegenerate_warpAt_of_limitWarp_of_subset_roof
#print axioms nondegenerateHammock_limitWarp_of_warpAt_of_subset_roof

end Deferred
end KappaLadder
end DWeb
end Erdos599
