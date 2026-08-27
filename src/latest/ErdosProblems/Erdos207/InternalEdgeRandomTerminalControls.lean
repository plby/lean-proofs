/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomMoments
import ErdosProblems.Erdos207.InternalEdgeRandomBlockerBound
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Simultaneous terminal controls for the random internal-edge stage

The B4 consequences for vertex stars and rooted threats concern one index at
a time.  This file performs the finite union bound and extracts one
positive-mass terminal outcome satisfying all structural, star, and rooted
controls simultaneously.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- One terminal outcome simultaneously retains any support-level structural
certificate and satisfies every vertex-star and rooted-active cutoff. -/
theorem exists_internalEdgeGreedyState_with_terminalControls
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (Good : InternalEdgeGreedyStateOn V -> Prop)
    (hGood : (internalEdgeGreedyProcessLaw
      F G U omega S edges hne D P0).SupportedOn Good)
    (k s : Nat) (hfamily : ∀ C ∈ F, C.card <= k)
    (kappa : DistinctPair V -> NNReal)
    (hkappa : ∀ e : DistinctPair V, HasExtensionBound
      (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
        relativeRootedThreatRemainder P0 z)
      (fun _ : TripleOn V => (D : NNReal)⁻¹) (kappa e))
    (aStar aRoot : NNReal) (haStar : 0 < aStar) (haRoot : 0 < aRoot)
    (hsmall :
      (∑ v : V,
        ((s.factorial : NNReal) *
          (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s)) /
            aStar ^ s) +
      ∑ e : DistinctPair V,
        (((s * (k - 1)).factorial : NNReal) *
          (((2 : NNReal) ^ (s * (k - 1)) * kappa e) ^ s)) /
            aRoot ^ s < 1) :
    ∃ z : InternalEdgeGreedyStateOn V,
      Good z ∧
      (∀ v : V, ((triplesThrough (z.chosen \ P0) v).card : NNReal) < aStar) ∧
      (∀ e : DistinctPair V,
        ((rootedActiveForbiddenConfigurations
          F z.chosen e.1.1 e.1.2).card : NNReal) < aRoot) := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  let starEps : V -> NNReal := fun v =>
    ((s.factorial : NNReal) *
      (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s)) /
        aStar ^ s
  let rootEps : DistinctPair V -> NNReal := fun e =>
    (((s * (k - 1)).factorial : NNReal) *
      (((2 : NNReal) ^ (s * (k - 1)) * kappa e) ^ s)) /
        aRoot ^ s
  let bad : Option (Sum V (DistinctPair V)) ->
      InternalEdgeGreedyStateOn V -> Prop
    | none, z => ¬ Good z
    | some (Sum.inl v), z =>
        aStar <= (triplesThrough (z.chosen \ P0) v).card
    | some (Sum.inr e), z =>
        aRoot <= (rootedActiveForbiddenConfigurations
          F z.chosen e.1.1 e.1.2).card
  have hstruct : L.probability (bad none) = 0 := by
    change L.probability (fun z => ¬ Good z) = 0
    rw [L.probability_not, L.probability_eq_one_of_supported Good hGood]
    simp
  have hstar : ∀ v : V,
      L.probability (bad (some (Sum.inl v))) <= starEps v := by
    intro v
    exact internalEdgeGreedyProcess_probability_newVertexStar_ge_le
      F G U omega S edges hne hnodup hu hv hSU D hD P0
        s v aStar haStar
  have hroot : ∀ e : DistinctPair V,
      L.probability (bad (some (Sum.inr e))) <= rootEps e := by
    intro e
    exact internalEdgeGreedyProcess_probability_rootedActive_ge_le
      F G U omega S edges hne hnodup hu hv hSU D hD P0
        e.1.1 e.1.2 k s hfamily (kappa e) aRoot haRoot (hkappa e)
  have hsum : ∑ i : Option (Sum V (DistinctPair V)),
      L.probability (bad i) < 1 := by
    rw [Fintype.sum_option, hstruct, zero_add, Fintype.sum_sum_type]
    calc
      (∑ v : V, L.probability (bad (some (Sum.inl v)))) +
          ∑ e : DistinctPair V,
            L.probability (bad (some (Sum.inr e))) <=
        (∑ v : V, starEps v) + ∑ e : DistinctPair V, rootEps e := by
          apply add_le_add
          · exact sum_le_sum fun v _hv => hstar v
          · exact sum_le_sum fun e _he => hroot e
      _ < 1 := by simpa only [starEps, rootEps] using hsmall
  obtain ⟨z, hz⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset (Option (Sum V (DistinctPair V)))) bad (by simpa using hsum)
  have hzGood : Good z := not_not.mp (hz none (mem_univ none))
  refine ⟨z, hzGood, ?_, ?_⟩
  · intro v
    exact lt_of_not_ge (hz (some (Sum.inl v)) (mem_univ _))
  · intro e
    exact lt_of_not_ge (hz (some (Sum.inr e)) (mem_univ _))

/-- Complete deterministic endpoint of the random internal-edge phase under
residual-degree, rooted-active, and moment-budget hypotheses. -/
theorem IsIterationTypical.exists_internalOuterEdge_state_with_terminalControls
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P0 : TripleSystemOn V}
    {p eta xi : NNReal} {h : Nat}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val <= i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hh : 2 <= h) (r : NNReal) (hr : r <= 1)
    (m a D d R k s : Nat) (hD : 0 < D)
    (hm : (m : NNReal) <=
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : Nat) : Real) <=
      ((r ^ 2 : NNReal) : Real) * m / 4)
    (hreserveSmall : ((internalOuterEdges G (W.U i.succ)).card : Real) *
      Real.exp (-(((r ^ 2 : NNReal) : Real) * m) / 4) < 1)
    (hfamily : ∀ C ∈ F, C.card <= k)
    (hblockScalar : 4 * d + R * k <= a)
    (hdegree : ∀ v : V, G.degree v <= d)
    (hrootBound : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P0 Q ->
      Q ⊆ P0 ∪ A ->
      (Q \ P0).card <= (internalOuterEdges G (W.U i.succ)).card ->
      e ∈ internalOuterEdges G (W.U i.succ) ->
      (rootedActiveForbiddenConfigurations F Q e.out.1 e.out.2).card <= R)
    (kappa : DistinctPair V -> NNReal)
    (hkappa : ∀ e : DistinctPair V, HasExtensionBound
      (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
        relativeRootedThreatRemainder P0 z)
      (fun _ : TripleOn V => (D : NNReal)⁻¹) (kappa e))
    (aStar aRoot : NNReal) (haStar : 0 < aStar) (haRoot : 0 < aRoot)
    (hmomentSmall :
      (∑ v : V,
        ((s.factorial : NNReal) *
          (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s)) /
            aStar ^ s) +
      ∑ e : DistinctPair V,
        (((s * (k - 1)).factorial : NNReal) *
          (((2 : NNReal) ^ (s * (k - 1)) * kappa e) ^ s)) /
            aRoot ^ s < 1) :
    ∃ omega : Sym2 V -> Bool, ∃ z : InternalEdgeGreedyStateOn V,
      GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
      (z.chosen \ P0).card <=
        (internalOuterEdges G (W.U i.succ)).card ∧
      (∀ e ∈ internalOuterEdges G (W.U i.succ),
        (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      (∀ v : V,
        ((triplesThrough (z.chosen \ P0) v).card : NNReal) < aStar) ∧
      (∀ e : DistinctPair V,
        ((rootedActiveForbiddenConfigurations
          F z.chosen e.1.1 e.1.2).card : NNReal) < aRoot) := by
  obtain ⟨omega, homega⟩ :=
    htyp.exists_internalOuterEdge_randomGreedyLaw_of_degree_rooted
      htri i hstage hGsupp hpacking0 havoid0 hinitial hh r hr
        m a D d R k hD hm ha hreserveSmall hfamily hblockScalar
        hdegree hrootBound
  let E := internalOuterEdges G (W.U i.succ)
  let candidates : Sym2 V -> Finset V := fun e =>
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  let hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := fun e he =>
    out_fst_ne_snd_of_mem_graphEdges
      (internalOuterEdges_subset_graphEdges G (W.U i.succ)
        (by simpa only [E, Finset.mem_toList] using he))
  let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega candidates
    E.toList hne D P0
  let Good : InternalEdgeGreedyStateOn V -> Prop := fun z =>
    GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
      (z.chosen \ P0).card <= E.card ∧
      ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2
  have hLaw : L.SupportedOn Good := by
    simpa only [L, Good, E, candidates, hne] using homega.1
  have hnodup : E.toList.Nodup := E.nodup_toList
  have hu : ∀ e, e ∈ E.toList -> e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.1
  have hv : ∀ e, e ∈ E.toList -> e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.2
  have hsub : ∀ e, e ∈ E.toList -> candidates e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  obtain ⟨z, hzGood, hzStar, hzRoot⟩ :=
    exists_internalEdgeGreedyState_with_terminalControls
      F G (W.U i.succ) omega candidates E.toList hne hnodup hu hv hsub
        D hD P0 Good hLaw k s hfamily kappa hkappa
        aStar aRoot haStar haRoot hmomentSmall
  exact ⟨omega, z, hzGood.1, hzGood.2.1, hzGood.2.2.1,
    hzGood.2.2.2, hzStar, hzRoot⟩

/-- Cardinality-only specialization of the simultaneous terminal controls.
It is useful as a finite fallback before applying the sharper well-spread
relative extension estimate. -/
theorem exists_internalEdgeGreedyState_with_terminalControls_crude
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (Good : InternalEdgeGreedyStateOn V -> Prop)
    (hGood : (internalEdgeGreedyProcessLaw
      F G U omega S edges hne D P0).SupportedOn Good)
    (k s : Nat) (hfamily : ∀ C ∈ F, C.card <= k)
    (aStar aRoot : NNReal) (haStar : 0 < aStar) (haRoot : 0 < aRoot)
    (hsmall :
      (∑ v : V,
        ((s.factorial : NNReal) *
          (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s)) /
            aStar ^ s) +
      (Fintype.card (DistinctPair V) : NNReal) *
        ((((s * (k - 1)).factorial : NNReal) *
          (((2 : NNReal) ^ (s * (k - 1)) * (F.card * k : NNReal)) ^ s)) /
            aRoot ^ s) < 1) :
    ∃ z : InternalEdgeGreedyStateOn V,
      Good z ∧
      (∀ v : V, ((triplesThrough (z.chosen \ P0) v).card : NNReal) < aStar) ∧
      (∀ e : DistinctPair V,
        ((rootedActiveForbiddenConfigurations
          F z.chosen e.1.1 e.1.2).card : NNReal) < aRoot) := by
  apply exists_internalEdgeGreedyState_with_terminalControls
    F G U omega S edges hne hnodup hu hv hSU D hD P0 Good hGood
      k s hfamily (fun _ => (F.card * k : NNReal))
  · intro e
    apply relativeRootedThreatRemainder_hasExtensionBound_crude
      F P0 e.1.1 e.1.2 (fun _ : TripleOn V => (D : NNReal)⁻¹)
        k hfamily
    intro T
    apply (inv_le_one₀ (by exact_mod_cast hD)).2
    exact_mod_cast hD
  · exact haStar
  · exact haRoot
  · simpa using hsmall

end

end Erdos207
