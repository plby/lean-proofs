/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.MasterIterationData
import ErdosProblems.Erdos551.External.Erdos207.CompatibleCandidateDegree

/-!
# Deterministic verification of a KSSS master-step update

The probabilistic construction of Proposition 10.6 must produce the fields
in `IsMasterCoverStep`.  This file proves that those fields give all
deterministic clauses IG2 and IG4 for the updated data; only parity,
iteration-typicality, and the law-level strong-distribution estimate remain.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The deterministic output shared by properties A1--A2, B1--B3, and
C1--C3 in the three parts of KSSS Proposition 10.6. -/
structure IsMasterCoverStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (A I D M : TripleSystemOn V) : Prop where
  selected : M ⊆ A
  disjoint_initial : Disjoint I (D ∪ M)
  packing : IsPackingOn (I ∪ (D ∪ M))
  avoids : AvoidsForbidden (I ∪ (D ∪ M)) F
  covers_outside : ∀ u v : V, G.Adj u v →
    (u ∉ U ∨ v ∉ U) → (coveredGraph M).Adj u v

/-- The old graph is the disjoint union of edges covered in the master step
and edges retained by the update, provided all outside edges were covered. -/
theorem IsMasterCoverStep.graph_le_covered_sup_updated
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A I D M : TripleSystemOn V}
    (h : IsMasterCoverStep F G U A I D M) :
    G ≤ coveredGraph M ⊔ updatedStageGraph G U M := by
  intro u v huv
  rw [SimpleGraph.sup_adj]
  by_cases hM : (coveredGraph M).Adj u v
  · exact Or.inl hM
  · apply Or.inr
    have huU : u ∈ U := by
      by_contra hu
      exact hM (h.covers_outside u v huv (Or.inl hu))
    have hvU : v ∈ U := by
      by_contra hv
      exact hM (h.covers_outside u v huv (Or.inr hv))
    exact ⟨graphRestrictedTo_adj.mpr ⟨huv, huU, hvU⟩,
      huv.ne, hM⟩

/-- Covering every edge outside `U` by a packing of triangles preserves
even degrees in the graph retained inside `U`.  Thus parity in a master
transition is a deterministic consequence of the old parity and the cover
step, rather than an additional probabilistic event. -/
theorem IsMasterCoverStep.updated_even
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A I D M : TripleSystemOn V}
    (hstep : IsMasterCoverStep F G U A I D M)
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (htri : ConsistsOfTriangles G A) :
    ∀ v, Even ((neighborsIn (updatedStageGraph G U M) univ v).card) := by
  classical
  have hMpacking : IsPackingOn M := hstep.packing.mono (by
    intro T hT
    exact mem_union_right I (mem_union_right D hT))
  have hcoveredLe : coveredGraph M ≤ G := by
    intro u v huv
    obtain ⟨T, hTM, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
    exact htri T (hstep.selected hTM) u huT v hvT huv
  have hsup : coveredGraph M ⊔ updatedStageGraph G U M = G := by
    apply le_antisymm
    · exact sup_le hcoveredLe (updatedStageGraph_le G U M)
    · exact hstep.graph_le_covered_sup_updated
  have hdisjoint : Disjoint (coveredGraph M) (updatedStageGraph G U M) :=
    (updatedStageGraph_disjoint_covered G U M).symm
  intro v
  have hneighborsG : neighborsIn G univ v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborsIn_iff, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
  have hneighborsUpdated : neighborsIn (updatedStageGraph G U M) univ v =
      (updatedStageGraph G U M).neighborFinset v := by
    ext w
    simp only [mem_neighborsIn_iff, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
  have hneighborsDecomp : G.neighborFinset v =
      (coveredGraph M).neighborFinset v ∪
        (updatedStageGraph G U M).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union]
    have hadj : G.Adj v w ↔
        (coveredGraph M ⊔ updatedStageGraph G U M).Adj v w := by
      rw [hsup]
    simpa only [SimpleGraph.sup_adj] using hadj
  have hneighborsDisjoint : Disjoint ((coveredGraph M).neighborFinset v)
      ((updatedStageGraph G U M).neighborFinset v) :=
    SimpleGraph.disjoint_neighborFinset_of_disjoint
      (coveredGraph M) (updatedStageGraph G U M) v hdisjoint
  have hdegree : G.degree v =
      (coveredGraph M).degree v + (updatedStageGraph G U M).degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighborsDecomp,
      Finset.card_union_of_disjoint hneighborsDisjoint,
      SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hevenDegree : Even (G.degree v) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hneighborsG]
    exact heven v
  have hcoveredDegree :=
    hMpacking.coveredGraph_degree_eq_two_mul_triplesThrough v
  have hcoveredEven : Even ((coveredGraph M).degree v) := by
    rw [hcoveredDegree]
    exact ⟨(triplesThrough M v).card, by omega⟩
  obtain ⟨a, ha⟩ := hevenDegree
  obtain ⟨c, hc⟩ := hcoveredEven
  have hca : c ≤ a := by omega
  rw [hneighborsUpdated, SimpleGraph.card_neighborFinset_eq_degree]
  exact ⟨a - c, by omega⟩

/-- Every updated graph edge is uncovered by the enlarged packing. -/
theorem updatedStageGraph_le_leave_enlarged
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {I D M : TripleSystemOn V}
    (hold : G ≤ leaveGraph (I ∪ D)) :
    updatedStageGraph G U M ≤ leaveGraph (I ∪ (D ∪ M)) := by
  intro u v huv
  have huvG : G.Adj u v := updatedStageGraph_le G U M huv
  have holdLeave := leaveGraph_adj.mp (hold huvG)
  have hnotM : ¬ (coveredGraph M).Adj u v := huv.2.2
  apply leaveGraph_adj.mpr
  refine ⟨huvG.ne, ?_⟩
  rintro ⟨T, hT, huT, hvT, hne⟩
  rw [mem_union] at hT
  rcases hT with hTI | hTDM
  · apply holdLeave.2
    exact ⟨T, mem_union_left D hTI, huT, hvT, hne⟩
  · rw [mem_union] at hTDM
    rcases hTDM with hTD | hTM
    · apply holdLeave.2
      exact ⟨T, mem_union_right I hTD, huT, hvT, hne⟩
    · apply hnotM
      exact coveredGraph_adj.mpr ⟨T, hTM, huT, hvT, hne⟩

/-- A triangle retained by Definition 10.5 is a triangle of the updated
graph. -/
theorem updatedStageAvailable_consistsOfTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A I D M : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) :
    ConsistsOfTriangles (updatedStageGraph G U M)
      (updatedStageAvailable F U A I D M) := by
  intro T hT u huT v hvT huv
  obtain ⟨hTA, hlegal, hTU⟩ := mem_updatedStageAvailable_iff.mp hT
  have huvG : G.Adj u v := htri T hTA u huT v hvT huv
  refine ⟨graphRestrictedTo_adj.mpr ⟨huvG, hTU huT, hTU hvT⟩,
    huv, ?_⟩
  intro hcovered
  obtain ⟨S, hSM, huS, hvS, _hne⟩ := coveredGraph_adj.mp hcovered
  have hSbig : S ∈ I ∪ (D ∪ M) := by simp [hSM]
  have hEq := hlegal.2.1 u v huv T
    (mem_insert_self T (I ∪ (D ∪ M))) huT hvT S
    (mem_insert_of_mem hSbig) huS hvS
  exact hlegal.1 (hEq.symm ▸ hSbig)

/-- Retained available triangles cannot complete a forbidden configuration
over the enlarged selected family. -/
theorem updatedStageAvailable_not_completes
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {A I D M : TripleSystemOn V} :
    ∀ T ∈ updatedStageAvailable F U A I D M,
      ¬ CompletesForbidden F (I ∪ (D ∪ M)) T := by
  intro T hT hcomplete
  obtain ⟨_hTA, hlegal, _hTU⟩ := mem_updatedStageAvailable_iff.mp hT
  obtain ⟨C, hCF, hTC, hrest⟩ := hcomplete
  apply hlegal.2.2 C hCF
  intro S hSC
  by_cases hST : S = T
  · subst S
    exact mem_insert_self T (I ∪ (D ∪ M))
  · exact mem_insert_of_mem (hrest (mem_erase.mpr ⟨hST, hSC⟩))

/-- Deterministic next-stage verification.  The new typicality assertion is
the one genuinely probabilistic IG3 output needed in addition to the cover
step certificate. -/
theorem IsMasterStagePointwiseGood.updated
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A I D M : TripleSystemOn V} {p eta ξ ξ' : ℝ≥0} {h : ℕ}
    (hold : IsMasterStagePointwiseGood W k F G A I D p eta ξ h)
    (hstep : IsMasterCoverStep F G (W.U next) A I D M)
    (htyp : IsIterationTypical W next
      (updatedStageGraph G (W.U next) M)
      (updatedStageAvailable F (W.U next) A I D M) p eta ξ' h) :
    IsMasterStagePointwiseGood W next F
      (updatedStageGraph G (W.U next) M)
      (updatedStageAvailable F (W.U next) A I D M)
      I (D ∪ M) p eta ξ' h := by
  obtain ⟨_hID, _hpacking, _havoid, _htypOld, hGleave, htri, _hlegal⟩ := hold
  refine ⟨hstep.disjoint_initial, hstep.packing, hstep.avoids, htyp,
    updatedStageGraph_le_leave_enlarged hGleave,
    updatedStageAvailable_consistsOfTriangles htri, ?_⟩
  exact updatedStageAvailable_not_completes

/-- Law-level assembly after the probabilistic part has established parity,
strong distribution, and typicality for the update throughout the support.
This is the deterministic final paragraph of Proposition 10.6. -/
theorem masterIterationGood_of_supported_update
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V}
    {A I D M : Ω → TripleSystemOn V}
    {p eta ξ ξ' C b : ℝ≥0} {h : ℕ}
    (heven : HasEvenStageGraphs L
      (fun ω ↦ updatedStageGraph (G ω) (W.U next) (M ω)))
    (hstrong : IsStronglyWellDistributed L W next I
      (fun ω ↦ D ω ∪ M ω) p C b)
    (hold : L.SupportedOn fun ω ↦
      IsMasterStagePointwiseGood W k F
        (G ω) (A ω) (I ω) (D ω) p eta ξ h)
    (hstep : L.SupportedOn fun ω ↦
      IsMasterCoverStep F (G ω) (W.U next)
        (A ω) (I ω) (D ω) (M ω))
    (htyp : L.SupportedOn fun ω ↦
      IsIterationTypical W next
        (updatedStageGraph (G ω) (W.U next) (M ω))
        (updatedStageAvailable F (W.U next)
          (A ω) (I ω) (D ω) (M ω)) p eta ξ' h) :
    IsMasterIterationGood L W next F
      (fun ω ↦ updatedStageGraph (G ω) (W.U next) (M ω))
      (fun ω ↦ updatedStageAvailable F (W.U next)
        (A ω) (I ω) (D ω) (M ω))
      I (fun ω ↦ D ω ∪ M ω) p eta ξ' C b h := by
  let Good : Ω → Prop := fun ω ↦
    IsMasterStagePointwiseGood W next F
      (updatedStageGraph (G ω) (W.U next) (M ω))
      (updatedStageAvailable F (W.U next)
        (A ω) (I ω) (D ω) (M ω))
      (I ω) (D ω ∪ M ω) p eta ξ' h
  have hGood : L.SupportedOn Good := by
    intro ω hmass
    exact (hold ω hmass).updated (hstep ω hmass) (htyp ω hmass)
  refine ⟨heven, hstrong, ?_⟩
  change 1 - ξ' ≤ L.probability Good
  rw [L.probability_eq_one_of_supported Good hGood]
  exact tsub_le_self

/-- Probability-level form of the master update.  Structural clauses remain
supported throughout the law, while next-stage typicality need only hold
with the probability required by `IsMasterIterationGood`.  This is the form
used for the T1--T3 concentration estimates in KSSS Proposition 10.6. -/
theorem masterIterationGood_of_probability_update
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega -> SimpleGraph V}
    {A I D M : Omega -> TripleSystemOn V}
    {p eta xi xi' C b : NNReal} {h : Nat}
    (heven : HasEvenStageGraphs L
      (fun omega => updatedStageGraph (G omega) (W.U next) (M omega)))
    (hstrong : IsStronglyWellDistributed L W next I
      (fun omega => D omega ∪ M omega) p C b)
    (hold : L.SupportedOn fun omega =>
      IsMasterStagePointwiseGood W k F
        (G omega) (A omega) (I omega) (D omega) p eta xi h)
    (hstep : L.SupportedOn fun omega =>
      IsMasterCoverStep F (G omega) (W.U next)
        (A omega) (I omega) (D omega) (M omega))
    (htyp : 1 - xi' <= L.probability (fun omega =>
      IsIterationTypical W next
        (updatedStageGraph (G omega) (W.U next) (M omega))
        (updatedStageAvailable F (W.U next)
          (A omega) (I omega) (D omega) (M omega)) p eta xi' h)) :
    IsMasterIterationGood L W next F
      (fun omega => updatedStageGraph (G omega) (W.U next) (M omega))
      (fun omega => updatedStageAvailable F (W.U next)
        (A omega) (I omega) (D omega) (M omega))
      I (fun omega => D omega ∪ M omega) p eta xi' C b h := by
  let Typical : Omega -> Prop := fun omega =>
    IsIterationTypical W next
      (updatedStageGraph (G omega) (W.U next) (M omega))
      (updatedStageAvailable F (W.U next)
        (A omega) (I omega) (D omega) (M omega)) p eta xi' h
  let Good : Omega -> Prop := fun omega =>
    IsMasterStagePointwiseGood W next F
      (updatedStageGraph (G omega) (W.U next) (M omega))
      (updatedStageAvailable F (W.U next)
        (A omega) (I omega) (D omega) (M omega))
      (I omega) (D omega ∪ M omega) p eta xi' h
  have hmono : L.probability Typical <= L.probability Good := by
    classical
    unfold FiniteLaw.probability
    apply sum_le_sum
    intro omega _homega
    by_cases hmass : 0 < L.mass omega
    · have himp : Typical omega -> Good omega := fun htypical =>
        (hold omega hmass).updated (hstep omega hmass) htypical
      by_cases htypical : Typical omega
      · simp [htypical, himp htypical]
      · simp [htypical]
    · have hzero : L.mass omega = 0 :=
        le_antisymm (not_lt.mp hmass) zero_le
      simp [hzero]
  refine ⟨heven, hstrong, ?_⟩
  have htypicalProbability : 1 - xi' <= L.probability Typical := by
    simpa only [Typical] using htyp
  exact htypicalProbability.trans hmono

end

end Erdos207
