/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterLawCompression
import ErdosProblems.Erdos207.SupportedConditionedPreliminaryKernel
import ErdosProblems.Erdos207.IterationReserveCandidates

/-!
# Outside-pair survival from a master state

The preliminary stopped process is phrased using `OutsideLeavePairsAlive`.
For an occurring master state this is not an extra invariant: cumulative
coverage puts every eligible uncovered pair into the current graph, and the
one-edge instance of iteration typicality supplies an available extension in
the next vortex set.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The pointwise master clauses say precisely that the current available
family is a legal constrained-greedy extension family of the old selected
packing. -/
theorem greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A I D : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (hpoint : IsMasterStagePointwiseGood W k F G A I D p eta xi h) :
    GreedyInvariant F (relativePreliminaryInitialState (I ∪ D) A) := by
  refine ⟨hpoint.2.1, hpoint.2.2.1, ?_⟩
  intro T hTA
  simp only [relativePreliminaryInitialState_available] at hTA
  simp only [relativePreliminaryInitialState_chosen]
  rw [isLegalExtension_iff hpoint.2.1 hpoint.2.2.1 T]
  have havoids : TriangleAvoidsGraph (coveredGraph (I ∪ D)) T := by
    intro u hu v hv huv hcovered
    have huvG := hpoint.2.2.2.2.2.1 T hTA u hu v hv huv
    have hleave := hpoint.2.2.2.2.1 huvG
    exact (leaveGraph_adj.mp hleave).2 (coveredGraph_adj.mp hcovered)
  have hTnot : T ∉ I ∪ D := by
    intro hT
    have hTlarge : 1 < T.1.card := by rw [T.2]; omega
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hTlarge
    exact havoids u hu v hv huv
      (coveredGraph_adj.mpr ⟨T, hT, hu, hv, huv⟩)
  exact ⟨hTnot, havoids, hpoint.2.2.2.2.2.2 T hTA⟩

/-- A pointwise-good supported master state has every eligible outside leave
pair alive, provided the next-level one-edge target is positive. -/
theorem outsideLeavePairsAlive_of_masterPointwiseGood
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} (i : Fin ell)
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B I D A : TripleSystemOn V} {G : SimpleGraph V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (hX : X = W.U i.succ)
    (hpoint : IsMasterStagePointwiseGood W i.castSucc
      (absorberErdosForbiddenConfigurationsOn q B) G A I D
      p eta xi h)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G I D)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hpositive : 0 < (1 - xi) *
      (p ^ 2 * eta * (W.U i.succ).card)) :
    OutsideLeavePairsAlive H X
      (relativePreliminaryInitialState (I ∪ D) A) := by
  subst X
  intro u v hnotH hnotBoth hleave
  have huv : u ≠ v := hleave.ne
  have horiginal :
      (graphDifference (SimpleGraph.completeGraph V) H).Adj u v := by
    refine ⟨?_, huv, hnotH⟩
    simpa using huv
  have hcoveredOrG := hcover horiginal
  rw [SimpleGraph.sup_adj] at hcoveredOrG
  have hnotCovered : ¬(coveredGraph (I ∪ D)).Adj u v := hleave.2
  have huvG : G.Adj u v := hcoveredOrG.resolve_left hnotCovered
  have huOuter : u ∈ W.U i.castSucc := (hGsupp huvG).1
  have hvOuter : v ∈ W.U i.castSucc := (hGsupp huvG).2
  have hwindow := hpoint.2.2.2.1.edge_extension_window i le_rfl
    huv huOuter hvOuter huvG hh
  have hcardPositive : 0 <
      ((iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.succ)).card : ℝ≥0) := hpositive.trans_le hwindow.1
  have hcardNat : 0 <
      (iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.succ)).card := by
    exact_mod_cast hcardPositive
  obtain ⟨w, hw⟩ := card_pos.mp hcardNat
  have hwdata := mem_iterationExtensionVertices_iff.mp hw
  have hedge : s(u, v) ∈ graphEdges (SimpleGraph.edge u v) := by
    rw [graphEdges_edge huv]
    simp
  obtain ⟨T, hTA, _hwT, heT⟩ := hwdata.2 s(u, v) hedge
  have huvT := mk_mem_tripleEdgeFinset_iff.mp heT
  refine ⟨T, mem_availableTrianglesContainingPair_iff.mpr ⟨hTA, ?_⟩⟩
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact huvT.1
  · exact huvT.2.1

end

end Erdos207
