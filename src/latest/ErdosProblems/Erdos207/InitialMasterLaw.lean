/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterIterationData
import ErdosProblems.Erdos207.CoverDownPacking

/-!
# The deterministic initial master law

Before any triangle is selected, the one-point law has the exact strong
distribution estimate with `p = C = 1` and zero additive error.  Thus an
initial pointwise typicality theorem is enough to start the finite master
iteration without any probabilistic assumption.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The deterministic empty selected family is exactly strongly
well-distributed at every vortex index. -/
theorem stronglyWellDistributed_pure_empty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) :
    IsStronglyWellDistributed (FiniteLaw.pure PUnit.unit) W k
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V)) 1 1 0 := by
  classical
  intro Ifix Dfix Efix _hdisjoint
  rw [FiniteLaw.probability_pure]
  by_cases hevent : StrongDistributionEvent
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      Ifix Dfix Efix PUnit.unit
  · have hIfix : Ifix = ∅ := subset_empty.mp hevent.1
    have hDfix : Dfix = ∅ := subset_empty.mp hevent.2.1
    subst Ifix
    subst Dfix
    rw [if_pos hevent]
    simp
  · rw [if_neg hevent]
    exact bot_le

/-- A deterministic pointwise-good initial state starts an
`IsMasterIterationGood` law on the one-point probability space. -/
theorem initialMasterIterationGood_of_pointwise
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {eta xi : ℝ≥0} {h : ℕ}
    (heven : ∀ v : V, Even ((neighborsIn G univ v).card))
    (hpoint : IsMasterStagePointwiseGood W k F G A ∅ ∅
      1 eta xi h) :
    IsMasterIterationGood (FiniteLaw.pure PUnit.unit) W k F
      (fun _ : PUnit ↦ G) (fun _ : PUnit ↦ A)
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      1 eta xi 1 0 h := by
  classical
  refine ⟨FiniteLaw.supportedOn_pure _ heven,
    stronglyWellDistributed_pure_empty W k, ?_⟩
  rw [FiniteLaw.probability_pure]
  simp only [hpoint, if_pos]
  exact tsub_le_self

/-- At an admissible order, deleting the triangle-divisible absorber graph
from the complete graph leaves even degree at every vertex, as required by
the initial master law. -/
theorem initialRemainder_even_of_admissible_absorber
    {n q : ℕ} {H : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {B : TripleSystem n}
    (hadmissible : Admissible n)
    (hA : HasHighGirthAbsorptionBank q H X B) :
    ∀ v : Fin n, Even ((neighborsIn
      (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
      univ v).card) := by
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) H
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hHle : H ≤ SimpleGraph.completeGraph (Fin n) := le_top
  have hsup : H ⊔ G = SimpleGraph.completeGraph (Fin n) :=
    sup_graphDifference_eq hHle
  have hcomplete : TriangleDivisible (H ⊔ G) := by
    simpa only [hsup] using admissible_complete_triangleDivisible hadmissible
  have hGdiv : TriangleDivisible G :=
    TriangleDivisible.right_of_sup hcomplete hA.graph_triangleDivisible
      (disjoint_graphDifference _ _)
  intro v
  have hneighbors : neighborsIn G univ v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborsIn_iff, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
  rw [hneighbors, SimpleGraph.card_neighborFinset_eq_degree]
  exact hGdiv.1 v

/-- Once initial typicality has been established, all remaining pointwise
master clauses follow from the canonical absorber-relative initial state. -/
theorem initialMasterStagePointwiseGood_of_typical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V}
    {eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 eta xi h) :
    IsMasterStagePointwiseGood W k
      (absorberErdosForbiddenConfigurationsOn q B)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      ∅ ∅ 1 eta xi h := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A₀ := outsideAvailableTriangles H B
  let S₀ := absorberGreedyInitialState F A₀
  have hInv : AbsorberGreedyInvariant F A₀ S₀ :=
    absorberGreedyInitialState_invariant F A₀
      (fun _S hS ↦ absorberErdosForbidden_nonempty hS)
  refine ⟨by simp, hInv.1.1, hInv.1.2.1, htyp, ?_, ?_, ?_⟩
  · intro u v huv
    rw [leaveGraph_adj]
    refine ⟨huv.ne, ?_⟩
    simp
  · intro T hT u huT v hvT huv
    have hTout : T ∈ A₀ := hInv.2.1.2 hT
    have havoid := (mem_outsideAvailableTriangles_iff.mp hTout).2
    exact ⟨by simpa using huv, huv, havoid u huT v hvT huv⟩
  · intro T hT
    have hlegal := hInv.1.2.2 T hT
    exact (avoidsForbidden_insert_iff_not_completes hInv.1.2.1 T).mp
      hlegal.2.2

end

end Erdos207
