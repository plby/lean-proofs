/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterIterationUpdate
import ErdosProblems.Erdos207.MasterIterationConditioning
import ErdosProblems.Erdos207.CoverDownProbability
import ErdosProblems.Erdos207.OutsideAvailability
import ErdosProblems.Erdos207.SupportedReserveAwareMasterIteration

/-!
# Deterministic extraction from the final master cover step

At the last vortex level, the old selected family together with the current
stage covers every non-absorber edge outside the flexible set.  This is
already exactly the support condition required of a KSSS outside packing.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The cumulative invariant threaded through the deterministic master
updates: every original edge is either already covered or remains in the
current stage graph. -/
def CoversOriginalGraph
    {V : Type*} [DecidableEq V]
    (G₀ G : SimpleGraph V) (I D : TripleSystemOn V) : Prop :=
  G₀ ≤ coveredGraph (I ∪ D) ⊔ G

/-- One valid master cover step preserves the cumulative coverage invariant. -/
theorem CoversOriginalGraph.updated
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G₀ G : SimpleGraph V} {U : Finset V}
    {A I D M : TripleSystemOn V}
    (hcover : CoversOriginalGraph G₀ G I D)
    (hstep : IsMasterCoverStep F G U A I D M) :
    CoversOriginalGraph G₀ (updatedStageGraph G U M) I (D ∪ M) := by
  intro u v huv
  have h := hcover huv
  rw [SimpleGraph.sup_adj] at h ⊢
  rcases h with hold | hG
  · left
    obtain ⟨T, hT, huT, hvT, huvT⟩ := coveredGraph_adj.mp hold
    apply coveredGraph_adj.mpr
    refine ⟨T, ?_, huT, hvT, huvT⟩
    rcases mem_union.mp hT with hTI | hTD
    · exact mem_union_left _ hTI
    · exact mem_union_right _ (mem_union_left _ hTD)
  · have hnext := hstep.graph_le_covered_sup_updated hG
    rw [SimpleGraph.sup_adj] at hnext
    rcases hnext with hM | hnext
    · left
      obtain ⟨T, hTM, huT, hvT, huvT⟩ := coveredGraph_adj.mp hM
      exact coveredGraph_adj.mpr
        ⟨T, mem_union_right I (mem_union_right D hTM), huT, hvT, huvT⟩
    · exact Or.inr hnext

/-- If all originally non-absorber edges are either already covered or still
present in the current stage graph, a final master cover step into `X`
produces the exact outside packing required by the absorber reduction.  The
current available family may be any subfamily of the original absorber-
relative availability; after the first iteration it is generally a proper
subfamily. -/
theorem hasKSSSOutsidePacking_of_finalMasterCoverStep_of_available_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A I D M : TripleSystemOn V} {G : SimpleGraph V}
    (hA : A ⊆ outsideAvailableTriangles H B)
    (holdSelected : I ∪ D ⊆ outsideAvailableTriangles H B)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G I D)
    (hstep : IsMasterCoverStep
      (absorberErdosForbiddenConfigurationsOn q B) G X A I D M) :
    HasKSSSOutsidePacking q H X B (I ∪ (D ∪ M)) := by
  have hselectedOutside :
      I ∪ (D ∪ M) ⊆ outsideAvailableTriangles H B := by
    intro T hT
    rcases mem_union.mp hT with hTI | hTDM
    · exact holdSelected (mem_union_left D hTI)
    · rcases mem_union.mp hTDM with hTD | hTM
      · exact holdSelected (mem_union_right I hTD)
      · exact hA (hstep.selected hTM)
  have hsupport : GraphSupportedOn
      (graphDifference (leaveGraph (I ∪ (D ∪ M))) H) (X : Set V) := by
    intro u v huv
    have hleave := leaveGraph_adj.mp huv.1
    have hnotH : ¬ H.Adj u v := huv.2.2
    have horiginal :
        (graphDifference (SimpleGraph.completeGraph V) H).Adj u v := by
      refine ⟨?_, huv.1.ne, hnotH⟩
      simpa using huv.1.ne
    have hcoveredOrG := hcover horiginal
    rw [SimpleGraph.sup_adj] at hcoveredOrG
    have hnotOld : ¬ (coveredGraph (I ∪ D)).Adj u v := by
      intro hcovered
      obtain ⟨T, hT, huT, hvT, huvT⟩ := coveredGraph_adj.mp hcovered
      apply hleave.2
      refine ⟨T, ?_, huT, hvT, huvT⟩
      rcases mem_union.mp hT with hTI | hTD
      · exact mem_union_left _ hTI
      · exact mem_union_right _ (mem_union_left _ hTD)
    have huvG : G.Adj u v := hcoveredOrG.resolve_left hnotOld
    constructor
    · by_contra huX
      have hM := hstep.covers_outside u v huvG (Or.inl huX)
      obtain ⟨T, hTM, huT, hvT, huvT⟩ := coveredGraph_adj.mp hM
      apply hleave.2
      exact ⟨T, mem_union_right I (mem_union_right D hTM), huT, hvT, huvT⟩
    · by_contra hvX
      have hM := hstep.covers_outside u v huvG (Or.inr hvX)
      obtain ⟨T, hTM, huT, hvT, huvT⟩ := coveredGraph_adj.mp hM
      apply hleave.2
      exact ⟨T, mem_union_right I (mem_union_right D hTM), huT, hvT, huvT⟩
  apply hasKSSSOutsidePacking_of_maximal hstep.packing
  · exact hselectedOutside
  · exact hstep.avoids
  · exact hsupport

/-- Equality with the original availability is the initial-stage
specialization of the subset form above. -/
theorem hasKSSSOutsidePacking_of_finalMasterCoverStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A I D M : TripleSystemOn V} {G : SimpleGraph V}
    (hA : A = outsideAvailableTriangles H B)
    (holdSelected : I ∪ D ⊆ A)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G I D)
    (hstep : IsMasterCoverStep
      (absorberErdosForbiddenConfigurationsOn q B) G X A I D M) :
    HasKSSSOutsidePacking q H X B (I ∪ (D ∪ M)) := by
  refine hasKSSSOutsidePacking_of_finalMasterCoverStep_of_available_subset
    (A := A) (hA := ?_) ?_ hcover hstep
  · rw [hA]
  · simpa only [hA] using holdSelected

/-- In the first master stage there is no old selected family, so the
coverage invariant reduces to the equality saying that `G` is the entire
non-absorber graph. -/
theorem hasKSSSOutsidePacking_of_initialMasterCoverStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B M : TripleSystemOn V}
    {G : SimpleGraph V}
    (hG : G = graphDifference (SimpleGraph.completeGraph V) H)
    (hstep : IsMasterCoverStep
      (absorberErdosForbiddenConfigurationsOn q B) G X
      (outsideAvailableTriangles H B) ∅ ∅ M) :
    HasKSSSOutsidePacking q H X B M := by
  have h := hasKSSSOutsidePacking_of_finalMasterCoverStep
    (q := q) (H := H) (X := X) (B := B)
    (A := outsideAvailableTriangles H B) (I := ∅) (D := ∅)
    (M := M) (G := G) rfl (by simp) (by
      intro u v huv
      rw [hG]
      exact Or.inr huv) hstep
  simpa using h

/-- A final iteration-good law whose remainder graph is supported on the
flexible set contains a positive-mass outcome that is already the required
outside packing. -/
theorem exists_ksssOutsidePacking_of_finalMasterIterationGood
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsMasterIterationGood law W k
      (absorberErdosForbiddenConfigurationsOn q B) G A I D
      p eta xi C b h)
    (hxi : xi < 1)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hsupport : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (X : Set V)) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let Good : Omega → Prop := fun omega ↦
    IsMasterStagePointwiseGood W k
      (absorberErdosForbiddenConfigurationsOn q B)
      (G omega) (A omega) (I omega) (D omega) p eta xi h
  have hprob : 0 < law.probability Good := by
    exact (tsub_pos_iff_lt.mpr hxi).trans_le hgood.2.2
  obtain ⟨omega, homega, hmass⟩ :=
    law.exists_of_probability_pos_with_mass hprob
  let P := I omega ∪ D omega
  have hPselected : P ⊆ outsideAvailableTriangles H B :=
    hselected omega hmass
  have hPsupport : GraphSupportedOn
      (graphDifference (leaveGraph P) H) (X : Set V) := by
    intro u v huv
    have hleave := leaveGraph_adj.mp huv.1
    have horiginal :
        (graphDifference (SimpleGraph.completeGraph V) H).Adj u v := by
      refine ⟨?_, huv.1.ne, huv.2.2⟩
      simpa using huv.1.ne
    have hcoveredOrG := hcover omega hmass horiginal
    rw [SimpleGraph.sup_adj] at hcoveredOrG
    rcases hcoveredOrG with hcovered | hG
    · exact (hleave.2 hcovered).elim
    · exact hsupport omega hmass hG
  refine ⟨P, hasKSSSOutsidePacking_of_maximal ?_ hPselected ?_ hPsupport⟩
  · exact homega.2.1
  · exact homega.2.2.1

/-- Support-sensitive terminal extraction for an iterated available family.
The current available family only has to remain inside the original
absorber-relative family; previously selected triangles are tracked
separately because they have been removed from current availability. -/
theorem exists_ksssOutsidePacking_of_supportedFinalLinkKernel_available_subset
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    (hA : law.SupportedOn fun omega ↦
      A omega ⊆ outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) X (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover
        (absorberErdosForbiddenConfigurationsOn q B) (A z.1)
        (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let J := law.jointBind linkLaw
  have hstep : J.SupportedOn fun z ↦
      IsMasterCoverStep (absorberErdosForbiddenConfigurationsOn q B)
        (G z.1) X (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2) :=
    hstate.jointBind_masterCoverStep_of_jointLink hlink
  have havailableJoint : J.SupportedOn fun z ↦
      A z.1 ⊆ outsideAvailableTriangles H B := by
    have h := hA.jointBind (K := linkLaw)
      (Q := fun _omega _M ↦ True)
      (fun _omega _hA ↦ by intro _M _hmass; trivial)
    exact fun z hz ↦ (h z hz).1
  have hselectedJoint : J.SupportedOn fun z ↦
      I z.1 ∪ D z.1 ⊆ outsideAvailableTriangles H B := by
    have h := hselected.jointBind (K := linkLaw)
      (Q := fun _omega _M ↦ True)
      (fun _omega _hselected ↦ by intro _M _hmass; trivial)
    exact fun z hz ↦ (h z hz).1
  have hcoverJoint : J.SupportedOn fun z ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G z.1) (I z.1) (D z.1) := by
    have h := hcover.jointBind (K := linkLaw)
      (Q := fun _omega _M ↦ True)
      (fun _omega _hcover ↦ by intro _M _hmass; trivial)
    exact fun z hz ↦ (h z hz).1
  have hpos : 0 < ∑ z, J.mass z := by
    rw [J.sum_mass]
    exact zero_lt_one
  obtain ⟨z, _hzuniv, hmass⟩ := Finset.sum_pos_iff.mp hpos
  refine ⟨I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2)), ?_⟩
  exact hasKSSSOutsidePacking_of_finalMasterCoverStep_of_available_subset
    (havailableJoint z hmass)
    (hselectedJoint z hmass) (hcoverJoint z hmass)
    (hstep z hmass)

/-- Initial-stage specialization in which current and original availability
coincide. -/
theorem exists_ksssOutsidePacking_of_supportedFinalLinkKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    (hA : ∀ omega, A omega = outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ A omega)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) X (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover
        (absorberErdosForbiddenConfigurationsOn q B) (A z.1)
        (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  apply exists_ksssOutsidePacking_of_supportedFinalLinkKernel_available_subset
    (law := law) (linkLaw := linkLaw) (G := G) (A := A)
    (I := I) (D := D) (R := R) (K := K)
    (hA := fun omega _hmass ↦ by rw [hA omega])
  · intro omega hmass
    simpa only [hA omega] using hselected omega hmass
  · exact hcover
  · exact hstate
  · exact hlink

end

end Erdos207
