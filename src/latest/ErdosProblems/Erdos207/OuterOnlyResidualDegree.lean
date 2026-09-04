/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyPairStarBounds
import ErdosProblems.Erdos207.InternalEdgeStarBound
import ErdosProblems.Erdos207.AvailablePairDegreeTrajectory

/-!
# Deterministic residual degree after an outer-only phase

All triangles selected in the initial phase are supported on the complement
of the next vortex level.  On that smaller vertex set, packinghood and the
exact chosen-cardinality clock alone force every residual degree to be small
once the packing is close to the maximum possible size.  This avoids paying
for a linear-size residual-star witness in the initial product estimate.
-/

namespace Erdos207

open Finset

noncomputable section

/-- `scheduledEdgesAt` is the ordinary finite incidence set when its edge
family comes from a simple graph. -/
lemma scheduledEdgesAt_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    scheduledEdgesAt (graphEdges G) v = G.incidenceFinset v := by
  classical
  rw [SimpleGraph.incidenceFinset_eq_filter]
  ext e
  simp [scheduledEdgesAt, graphEdges_eq_edgeFinset]

@[simp]
lemma card_scheduledEdgesAt_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (scheduledEdgesAt (graphEdges G) v).card = G.degree v := by
  rw [scheduledEdgesAt_graphEdges, SimpleGraph.card_incidenceFinset_eq_degree]

/-- A family of outer-only triangles of `G` covers only internal outer edges
of `G`. -/
lemma covered_edges_subset_internalOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A P : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) (hPA : P ⊆ A)
    (houter : TrianglesDisjointFrom U P) :
    graphEdges (coveredGraph P) ⊆ internalOuterEdges G U := by
  intro e he
  have hadj : (coveredGraph P).Adj e.out.1 e.out.2 :=
    graph_adj_out_of_mem_graphEdges he
  obtain ⟨T, hTP, hleft, hright, hne⟩ := coveredGraph_adj.mp hadj
  have hdisj := houter T hTP
  have hleftOut : e.out.1 ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp hdisj hleft hU
  have hrightOut : e.out.2 ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp hdisj hright hU
  apply mem_internalOuterEdges_iff.mpr
  refine ⟨?_, hleftOut, hrightOut⟩
  rw [mem_graphEdges_iff]
  rw [← e.out_eq]
  exact htri T (hPA hTP) e.out.1 hleft e.out.2 hright hne

/-- No outer-only selected triangle contains a vertex of the excluded set. -/
lemma triplesThrough_eq_empty_of_trianglesDisjointFrom
    {V : Type*} [DecidableEq V]
    {U : Finset V} {P : TripleSystemOn V}
    (houter : TrianglesDisjointFrom U P) {v : V} (hv : v ∈ U) :
    triplesThrough P v = ∅ := by
  ext T
  constructor
  · intro hT
    have hdata := mem_filter.mp hT
    exact (Finset.disjoint_left.mp (houter T hdata.1) hdata.2 hv).elim
  · simp

/-- The internal outer edge star has size at most the number of other
vertices outside `U`. -/
lemma card_scheduledEdgesAt_internalOuterEdges_le_compl_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) {v : V} (hv : v ∉ U) :
    (scheduledEdgesAt (internalOuterEdges G U) v).card ≤
      (univ \ U).card - 1 := by
  classical
  let Gout := internalOuterGraph G U
  let : DecidableRel Gout.Adj := Classical.decRel Gout.Adj
  have hsub : Gout.neighborFinset v ⊆
      (univ \ U).erase v := by
    intro w hw
    have hadj : Gout.Adj v w := by
      simpa only [SimpleGraph.mem_neighborFinset] using hw
    have he : s(v, w) ∈ internalOuterEdges G U := by
      rw [← graphEdges_internalOuterGraph G U, mem_graphEdges_iff]
      exact hadj
    have hout := (mem_internalOuterEdges_iff.mp he).2
    apply mem_erase.mpr
    refine ⟨hadj.ne.symm, mem_sdiff.mpr ⟨mem_univ w, ?_⟩⟩
    intro hwU
    have hw : w ∈ (s(v, w) : Sym2 V) := by simp
    rw [← (s(v, w) : Sym2 V).out_eq] at hw
    rcases Sym2.mem_iff.mp hw with hw | hw
    · exact hout.1 (hw ▸ hwU)
    · exact hout.2 (hw ▸ hwU)
  calc
    (scheduledEdgesAt (internalOuterEdges G U) v).card = Gout.degree v := by
      rw [← graphEdges_internalOuterGraph G U]
      exact card_scheduledEdgesAt_graphEdges Gout v
    _ = (Gout.neighborFinset v).card := by
      symm
      exact SimpleGraph.card_neighborFinset_eq_degree Gout v
    _ ≤
        ((univ \ U).erase v).card := card_le_card hsub
    _ = (univ \ U).card - 1 := by
      rw [card_erase_of_mem (mem_sdiff.mpr ⟨mem_univ v, hv⟩)]

/-- Every outer vertex star of an outer-only packing uses at most all other
outer vertices. -/
lemma two_mul_triplesThrough_le_outer_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (htri : ConsistsOfTriangles G A)
    (hPA : P ⊆ A) (houter : TrianglesDisjointFrom U P)
    {v : V} (hv : v ∉ U) :
    2 * (triplesThrough P v).card ≤ (univ \ U).card - 1 := by
  have hcovered : graphEdges (coveredGraph P) ⊆ internalOuterEdges G U :=
    covered_edges_subset_internalOuterEdges htri hPA houter
  have hstar : scheduledEdgesAt (graphEdges (coveredGraph P)) v ⊆
      scheduledEdgesAt (internalOuterEdges G U) v := by
    intro e he
    exact mem_scheduledEdgesAt_iff.mpr
      ⟨hcovered (mem_scheduledEdgesAt_iff.mp he).1,
        (mem_scheduledEdgesAt_iff.mp he).2⟩
  calc
    2 * (triplesThrough P v).card = (coveredGraph P).degree v := by
      symm
      exact hpacking.coveredGraph_degree_eq_two_mul_triplesThrough v
    _ = (scheduledEdgesAt (graphEdges (coveredGraph P)) v).card := by simp
    _ ≤ (scheduledEdgesAt (internalOuterEdges G U) v).card :=
      card_le_card hstar
    _ ≤ (univ \ U).card - 1 :=
      card_scheduledEdgesAt_internalOuterEdges_le_compl_card_sub_one G U hv

/-- Twice the sum of the selected outer vertex stars is exactly six times
the number of selected triangles. -/
lemma sum_outer_two_mul_triplesThrough
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {P : TripleSystemOn V}
    (houter : TrianglesDisjointFrom U P) :
    ∑ v ∈ univ \ U, 2 * (triplesThrough P v).card = 6 * P.card := by
  have hsum : ∑ v : V, 2 * (triplesThrough P v).card = 6 * P.card := by
    rw [← mul_sum, sum_card_triplesThrough]
    ring
  rw [← hsum]
  apply sum_subset (sdiff_subset : univ \ U ⊆ univ)
  intro v _hvUniv hvNotOuter
  have hvU : v ∈ U := by
    simpa using hvNotOuter
  rw [triplesThrough_eq_empty_of_trianglesDisjointFrom houter hvU,
    card_empty, mul_zero]

/-- At one outer vertex, the residual internal star and the already covered
star are disjoint subfamilies of the original internal star. -/
lemma residual_add_covered_star_le_outer_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (htri : ConsistsOfTriangles G A)
    (hPA : P ⊆ A) (houter : TrianglesDisjointFrom U P)
    {v : V} (hv : v ∉ U) :
    (scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v).card +
        2 * (triplesThrough P v).card ≤ (univ \ U).card - 1 := by
  let R := scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v
  let C := scheduledEdgesAt (graphEdges (coveredGraph P)) v
  let E := scheduledEdgesAt (internalOuterEdges G U) v
  have hRE : R ⊆ E := by
    intro e he
    have hdata := mem_scheduledEdgesAt_iff.mp he
    exact mem_scheduledEdgesAt_iff.mpr
      ⟨preliminaryResidualInternalEdges_subset_internalOuterEdges G U P
        hdata.1, hdata.2⟩
  have hcovered := covered_edges_subset_internalOuterEdges htri hPA houter
  have hCE : C ⊆ E := by
    intro e he
    have hdata := mem_scheduledEdgesAt_iff.mp he
    exact mem_scheduledEdgesAt_iff.mpr ⟨hcovered hdata.1, hdata.2⟩
  have hRC : Disjoint R C := by
    rw [Finset.disjoint_left]
    intro e heR heC
    have hres := preliminaryResidualInternalEdges_subset_residualOuterEdges
      G U P (mem_scheduledEdgesAt_iff.mp heR).1
    exact (mem_sdiff.mp hres).2 (mem_scheduledEdgesAt_iff.mp heC).1
  have hunion : R ∪ C ⊆ E := union_subset hRE hCE
  have hCcard : C.card = 2 * (triplesThrough P v).card := by
    dsimp only [C]
    rw [card_scheduledEdgesAt_graphEdges]
    exact hpacking.coveredGraph_degree_eq_two_mul_triplesThrough v
  calc
    R.card + 2 * (triplesThrough P v).card = R.card + C.card := by rw [hCcard]
    _ = (R ∪ C).card := (card_union_of_disjoint hRC).symm
    _ ≤ E.card := card_le_card hunion
    _ ≤ (univ \ U).card - 1 := by
      dsimp only [E]
      exact card_scheduledEdgesAt_internalOuterEdges_le_compl_card_sub_one
        G U hv

/-- Exact-clock deterministic residual-degree bound for an outer-only
packing.  The right side is the deficiency from the maximum packing size on
the outer vertex set. -/
theorem scheduled_residualInternal_degree_le_outer_deficiency
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (htri : ConsistsOfTriangles G A)
    (hPA : P ⊆ A) (houter : TrianglesDisjointFrom U P) :
    ∀ v : V,
      (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U P) v).card ≤
        (univ \ U).card * ((univ \ U).card - 1) - 6 * P.card := by
  intro v
  by_cases hv : v ∈ U
  · have hzero : scheduledEdgesAt
        (preliminaryResidualInternalEdges G U P) v = ∅ := by
      ext e
      constructor
      · intro heScheduled
        have heData := mem_scheduledEdgesAt_iff.mp heScheduled
        have heInternal :=
          preliminaryResidualInternalEdges_subset_internalOuterEdges
            G U P heData.1
        have hout := (mem_internalOuterEdges_iff.mp heInternal).2
        have hve := heData.2
        rw [← e.out_eq] at hve
        rcases Sym2.mem_iff.mp hve with hve | hve
        · exact (hout.1 (hve ▸ hv)).elim
        · exact (hout.2 (hve ▸ hv)).elim
      · simp
    simp [hzero]
  · let O := univ \ U
    have hvO : v ∈ O := mem_sdiff.mpr ⟨mem_univ v, hv⟩
    have hsplit :
        ∑ w ∈ O, 2 * (triplesThrough P w).card =
          2 * (triplesThrough P v).card +
            ∑ w ∈ O.erase v, 2 * (triplesThrough P w).card := by
      rw [add_comm]
      exact sum_erase_add _ _ hvO |>.symm
    have htotal :
        ∑ w ∈ O, 2 * (triplesThrough P w).card = 6 * P.card := by
      simpa only [O] using sum_outer_two_mul_triplesThrough houter
    have hother :
        ∑ w ∈ O.erase v, 2 * (triplesThrough P w).card ≤
          (O.card - 1) ^ 2 := by
      calc
        ∑ w ∈ O.erase v, 2 * (triplesThrough P w).card ≤
            ∑ _w ∈ O.erase v, (O.card - 1) := by
          apply sum_le_sum
          intro w hw
          have hwO : w ∈ O := (mem_erase.mp hw).2
          exact two_mul_triplesThrough_le_outer_card_sub_one hpacking htri
            hPA houter (by simpa only [O, mem_sdiff, mem_univ, true_and]
              using hwO)
        _ = (O.card - 1) * (O.card - 1) := by
          simp only [sum_const, nsmul_eq_mul, card_erase_of_mem hvO]
          norm_num
        _ = (O.card - 1) ^ 2 := by ring
    have hres :
        (scheduledEdgesAt
            (preliminaryResidualInternalEdges G U P) v).card +
          2 * (triplesThrough P v).card ≤ O.card - 1 := by
      simpa only [O] using residual_add_covered_star_le_outer_card_sub_one
        hpacking htri hPA houter hv
    have hidentity : O.card * (O.card - 1) =
        (O.card - 1) + (O.card - 1) ^ 2 := by
      have hOpos : 0 < O.card := card_pos.mpr ⟨v, hvO⟩
      have hcard : O.card = (O.card - 1) + 1 := by omega
      calc
        O.card * (O.card - 1) =
            ((O.card - 1) + 1) * (O.card - 1) := by
          exact congrArg (fun x : ℕ ↦ x * (O.card - 1)) hcard
        _ = (O.card - 1) + (O.card - 1) ^ 2 := by ring
    rw [htotal] at hsplit
    have hcombined :
        (scheduledEdgesAt
            (preliminaryResidualInternalEdges G U P) v).card + 6 * P.card ≤
          O.card * (O.card - 1) := by
      rw [hidentity]
      omega
    change (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U P) v).card ≤
      O.card * (O.card - 1) - 6 * P.card
    exact Nat.le_sub_of_add_le (by simpa only [add_comm] using hcombined)

/-- An outer-only invariant state whose residual internal graph has maximum
degree at most `Delta` has available pair-codegree at most `Delta`.  The
third vertex of every available triangle through a pair injects into a
residual edge incident with either endpoint. -/
theorem hasAvailablePairCutoff_of_outerOnly_residual_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {U : Finset V} {A : TripleSystemOn V} {S : GreedyStateOn V} {Delta : ℕ}
    (hInv : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (hdegree : ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U S.chosen) v).card ≤ Delta) :
    HasAvailablePairCutoff Delta S := by
  intro P hP
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hP
  let w := fun T : availableTrianglesContainingPair S {u, v} ↦
    availableThroughPairLeaveNeighbor hInv.1 huv T
  let target := scheduledEdgesAt
    (preliminaryResidualInternalEdges G U S.chosen) u
  let f : availableTrianglesContainingPair S {u, v} → {e // e ∈ target} :=
    fun T ↦ ⟨s(u, (w T).1), by
      have hTdata := mem_availableTrianglesContainingPair_iff.mp T.2
      have hTout : T.1 ∈ outerOnlyAvailable U A := hInv.2.1.2 hTdata.1
      have hToutData := mem_outerOnlyAvailable_iff.mp hTout
      have huT : u ∈ T.1.1 := hTdata.2 (by simp)
      have hwT : (w T).1 ∈ T.1.1 := by
        exact availableThroughPairLeaveNeighbor_mem hInv.1 huv T
      have huOut : u ∉ U := by
        intro huU
        exact Finset.disjoint_left.mp hToutData.2 huT huU
      have hwOut : (w T).1 ∉ U := by
        intro hwU
        exact Finset.disjoint_left.mp hToutData.2 hwT hwU
      have hleave : (leaveGraph S.chosen).Adj u (w T).1 := by
        simpa only [SimpleGraph.mem_neighborFinset] using (w T).2
      have hG : G.Adj u (w T).1 :=
        htri T.1 hToutData.1 u huT (w T).1 hwT hleave.ne
      have houtside_of_mem : ∀ x : V, x ∈ s(u, (w T).1) → x ∉ U := by
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact huOut
        · exact hwOut
      have heInternal : s(u, (w T).1) ∈ internalOuterEdges G U := by
        rw [mem_internalOuterEdges_iff]
        refine ⟨mem_graphEdges_iff.mpr hG, ?_, ?_⟩
        · exact houtside_of_mem _ (Sym2.out_fst_mem _)
        · exact houtside_of_mem _ (Sym2.out_snd_mem _)
      have heResidual : s(u, (w T).1) ∈
          preliminaryResidualOuterEdges G U S.chosen := by
        apply mem_sdiff.mpr
        refine ⟨internalOuterEdges_subset_outerGraphEdges G U heInternal, ?_⟩
        intro heCovered
        exact (leaveGraph_adj.mp hleave).2
          (mem_graphEdges_iff.mp heCovered)
      apply mem_scheduledEdgesAt_iff.mpr
      exact ⟨mem_inter.mpr ⟨heInternal, heResidual⟩, by simp⟩⟩
  have hf : Function.Injective f := by
    intro T R hTR
    apply availableThroughPairLeaveNeighbor_injective hInv.1 huv
    apply Subtype.ext
    have hedge : s(u, (w T).1) = s(u, (w R).1) :=
      congrArg Subtype.val hTR
    rw [Sym2.eq_iff] at hedge
    rcases hedge with hedge | hedge
    · exact hedge.2
    · have hleaveR : (leaveGraph S.chosen).Adj u (w R).1 := by
        simpa only [SimpleGraph.mem_neighborFinset] using (w R).2
      exact (hleaveR.ne hedge.1).elim
  calc
    (availableTrianglesContainingPair S {u, v}).card =
        Fintype.card (availableTrianglesContainingPair S {u, v}) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card {e // e ∈ target} :=
      Fintype.card_le_of_injective f hf
    _ = target.card := Fintype.card_coe _
    _ ≤ Delta := hdegree u

/-- Every outer-only invariant state has pair-codegree at most the number of
vertices outside the protected set.  This is the sharp initial cap used by
the decreasing pair trajectory; unlike the ambient-cardinality cap, it
retains the fixed positive gap created by the first vortex level. -/
theorem hasAvailablePairCutoff_outerOnly_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S) :
    HasAvailablePairCutoff (univ \ U).card S := by
  intro P hP
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hP
  let target : Finset V := univ \ U
  let w := fun T : availableTrianglesContainingPair S {u, v} ↦
    availableThroughPairLeaveNeighbor hInv.1 huv T
  let f : availableTrianglesContainingPair S {u, v} → {x // x ∈ target} :=
    fun T ↦ ⟨(w T).1, by
      change (w T).1 ∈ univ \ U
      apply mem_sdiff.mpr
      refine ⟨mem_univ _, ?_⟩
      have hTdata := mem_availableTrianglesContainingPair_iff.mp T.2
      have hTout := mem_outerOnlyAvailable_iff.mp (hInv.2.1.2 hTdata.1)
      exact fun hxU ↦ Finset.disjoint_left.mp hTout.2
        (availableThroughPairLeaveNeighbor_mem hInv.1 huv T) hxU⟩
  have hf : Function.Injective f := by
    intro T R hTR
    apply availableThroughPairLeaveNeighbor_injective hInv.1 huv
    apply Subtype.ext
    exact congrArg (fun x : {x // x ∈ target} ↦ x.1) hTR
  calc
    (availableTrianglesContainingPair S {u, v}).card =
        Fintype.card (availableTrianglesContainingPair S {u, v}) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card {x // x ∈ target} :=
      Fintype.card_le_of_injective f hf
    _ = target.card := Fintype.card_coe _
    _ = (univ \ U).card := rfl

/-- Exact-clock outer-only packinghood supplies a deterministic decreasing
pair-codegree envelope, equal to the deficiency from the maximum possible
packing size on the outer vertex set. -/
theorem hasAvailablePairCutoff_outerOnly_deficiency
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {U : Finset V} {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A) :
    HasAvailablePairCutoff
      ((univ \ U).card * ((univ \ U).card - 1) - 6 * S.chosen.card) S := by
  apply hasAvailablePairCutoff_of_outerOnly_residual_degree hInv htri
  exact scheduled_residualInternal_degree_le_outer_deficiency hInv.1.1 htri
    (hInv.2.1.1.trans (outerOnlyAvailable_subset U A))
    (fun T hT ↦ (mem_outerOnlyAvailable_iff.mp (hInv.2.1.1 hT)).2)

/-- For the stopped sharp process, failure of the deterministic residual
degree bound can occur only when the sharp active predicate has already
failed.  Thus the existing five-event error also pays for the residual
incidence conditioning event. -/
theorem timedSharpScheduledOuterOnly_probability_not_residualDegree_le_inactive
    {V : Type*} [Fintype V] [DecidableEq V]
    (fuel : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut r : ℕ)
    (D d M u : ℕ → ℕ)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (htri : ConsistsOfTriangles G A)
    (hchosen₀ : S₀.chosen = ∅)
    (hdeficiency :
      (univ \ U).card * ((univ \ U).card - 1) - 6 * fuel ≤ r) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d M u
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ ¬ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card < r + 1) ≤
      L.probability (fun z ↦ ¬ active z.1.1 z.2) := by
  dsimp only
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut D d M u
  let L := FiniteLaw.timedStoppedProcessLaw fuel
    (fun _ ↦ greedyKernel F) active S₀
  have hInv : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2) := by
    apply FiniteLaw.timedStoppedProcessLaw_supported fuel
      (fun _ ↦ greedyKernel F) active S₀ hAbs₀
    intro _i _hi S hS
    exact absorberGreedyKernel_supported hS
  have hcard : L.SupportedOn (fun z ↦
      z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    simpa only [L, active] using
      (timedSharpScheduledAggregatePairBandProcessLaw_supported_chosen_card
        (n := fuel) (F := F) (Kpair := Kpair) (Kglobal := Kglobal)
        (Kinc := Kinc) (Delta := Delta) (delta := delta) (I := I)
        (Dcut := Dcut) (D := D) (d := d) (M := M) (u := u)
        (S₀ := S₀) hAbs₀.1)
  have hterminal : L.SupportedOn (fun z ↦
      z.1.1 = fuel ∨ ¬ active z.1.1 z.2) := by
    simpa only [L, active] using
      FiniteLaw.timedStoppedProcessLaw_supported_terminal fuel
        (fun _ ↦ greedyKernel F) active S₀
  have hsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2 ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1 ∧
        (z.1.1 = fuel ∨ ¬ active z.1.1 z.2)) := by
    intro z hz
    exact ⟨hInv z hz, hcard z hz, hterminal z hz⟩
  apply L.probability_mono_of_supported hsupport
  intro z hz hbad
  have hzInv := hz.1
  have hzCard := hz.2.1
  rcases hz.2.2 with htime | hinactive
  · exfalso
    have hchosenCard : z.2.chosen.card = fuel := by
      rw [hzCard, hchosen₀, card_empty, zero_add, htime]
    have hsubset : z.2.chosen ⊆ A :=
      hzInv.2.1.1.trans (outerOnlyAvailable_subset U A)
    have houter : TrianglesDisjointFrom U z.2.chosen := by
      intro T hT
      exact (mem_outerOnlyAvailable_iff.mp (hzInv.2.1.1 hT)).2
    have hdegree := scheduled_residualInternal_degree_le_outer_deficiency
      hzInv.1.1 htri hsubset houter
    push_neg at hbad
    obtain ⟨v, hv⟩ := hbad
    have hle : (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card ≤ r := by
      exact (hdegree v).trans (by simpa only [hchosenCard] using hdeficiency)
    omega
  · exact hinactive

end

end Erdos207
