/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawInternalResidualLinks
import ErdosProblems.Erdos207.LocalizedRawInternalRootedConditioning
import ErdosProblems.Erdos207.PreliminaryInternalSafeCandidates
import ErdosProblems.Erdos207.LocalizedInternalStageLoss

/-!
# Partition-preserving residual links after the raw internal stage

The deterministic residual-link construction uses the whole preliminary
family as its structural `Mstar`, with empty structural `I/D`.  The strong
law must nevertheless retain the preliminary first-nibble family in its
distinguished `initial` component.  This file conditions on retrospective
raw-internal success, reconstructs the residual links, and records that the
probabilistic initial/later split is a disjoint partition of the same
structural family.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Root-condition a raw internal law and expose both its structural
intermediate-link state and its probability-sensitive initial/later
classification. -/
theorem exists_localizedPartitionedRawInternalResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {level : Fin (ell + 1)} {i : Fin ell}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {M initial later : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R d : ℕ}
    {sampled : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed
      (law.jointBind (rawResidualInternalKernel W i F (fun _ ↦ G)
        (fun omega ↦ pairSafeAvailable A (M omega)) M bits D))
      W level (jointInitial initial)
      (jointLater later (rawResidualInternalAdded M))
      (fun z ↦ preliminaryAugmentedReserve G (W.U i.succ)
        (sampled z.1) (M z.1)) p reserveDensity C b)
    (hclassification0 : ∀ omega,
      Disjoint (initial omega) (later omega) ∧
        initial omega ∪ later omega = M omega)
    (hraw : (law.jointBind (rawResidualInternalKernel W i F
      (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
      M bits D)).SupportedOn (fun z ↦
        LocalizedRawResidualInternalOutcomeGood W i F (fun _ ↦ G)
          (fun omega ↦ pairSafeAvailable A (M omega)) M bits D R
          z.1 z.2))
    (hpre : (law.jointBind (rawResidualInternalKernel W i F
      (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
      M bits D)).SupportedOn (fun z ↦
        M z.1 ⊆ A ∧ IsPackingOn (M z.1) ∧
          AvoidsForbidden (M z.1) F ∧
          TrianglesDisjointFrom (W.U i.succ) (M z.1) ∧
          ∀ v : V,
            (scheduledEdgesAt
              (preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
              v).card ≤ d))
    (hC : 1 ≤ C) {q : ℕ}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight W level p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2
            (W.U i.succ) ↦ localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight W level p)
        (∅ : TripleSystemOn V) ≤ kappa)
    (htail : strongLocalizedRootedFirstTail V C kappa R q < 1)
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (hGleave : G ≤ leaveGraph (∅ : TripleSystemOn V))
    (htri : ConsistsOfTriangles G A) :
    let Kint := rawResidualInternalKernel W i F (fun _ ↦ G)
      (fun omega ↦ pairSafeAvailable A (M omega)) M bits D
    let J := law.jointBind Kint
    let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
      RootedActiveCapsGoodIn F
        (jointInitial initial z ∪
          jointLater later (rawResidualInternalAdded M) z)
        (W.U i.succ) R
    ∃ hpos : 0 < J.probability RootGood,
      let Lc := J.conditionOn RootGood hpos
      let Gf : Omega × InternalEdgeGreedyStateOn V →
          SimpleGraph V := fun _ ↦ G
      let Af : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ A
      let If : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ ∅
      let Df : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ ∅
      let Mf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦ M z.1
      let Qf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦ z.2.chosen
      let Rf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦
        internalStageFamily (If z) (Df z) (Mf z) (Qf z)
      let reservef : Omega × InternalEdgeGreedyStateOn V →
          Finset (Sym2 V) := fun z ↦
        preliminaryAugmentedReserve G (W.U i.succ)
          (sampled z.1) (M z.1)
      let links := internalOutcomeResidualLinks Gf (W.U i.succ)
        reservef F Af If Df Mf Qf
      IsReserveStronglyWellDistributed Lc W level
          (jointInitial initial)
          (jointLater later (rawResidualInternalAdded M)) reservef
          p reserveDensity
          (C / (1 - strongLocalizedRootedFirstTail V C kappa R q)) b ∧
        Lc.SupportedOn (fun z ↦
          IsIntermediateLinkState (Gf z) (W.U i.succ) (Af z)
              (If z) (Df z) (Rf z) (links z) ∧
            (∀ o, (links z o).center =
              outsideVertexEmbedding (W.U i.succ) o) ∧
            (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉
              W.U i.succ) ∧
            (∀ o, (links z o).left ⊆ W.U i.succ) ∧
            (∀ o, (links z o).right ⊆ W.U i.succ) ∧
            (∀ o, (links z o).SpokesIn (reservef z))) ∧
        Lc.SupportedOn (fun z ↦
          ∀ o : {x : V // x ∉ W.U i.succ},
            ((coveredGraph (Rf z)).neighborFinset o.1 ∩
              W.U i.succ).card ≤ d) ∧
        Lc.SupportedOn (fun z ↦
          ConsistsOfTriangles (Gf z) (Af z) ∧
            Gf z ≤ leaveGraph (If z ∪ Df z) ∧
            IsPackingOn (If z ∪ (Df z ∪ Rf z)) ∧
            AvoidsForbidden (If z ∪ (Df z ∪ Rf z)) F) ∧
        Lc.SupportedOn (fun z ↦
          Disjoint (jointInitial initial z)
            (jointLater later (rawResidualInternalAdded M) z) ∧
          jointInitial initial z ∪
              jointLater later (rawResidualInternalAdded M) z =
            If z ∪ (Df z ∪ Rf z)) := by
  dsimp only
  let Kint := rawResidualInternalKernel W i F (fun _ ↦ G)
    (fun omega ↦ pairSafeAvailable A (M omega)) M bits D
  let J := law.jointBind Kint
  have hroot :=
    hstrong.conditionOn_localizedRawResidualInternal_rootedSuccess_firstMoment
    (G := fun _ ↦ G) (A := fun omega ↦ pairSafeAvailable A (M omega))
    (P0 := M) (bits := bits) (initial := initial) (later := later)
    (reserve := fun omega ↦ preliminaryAugmentedReserve G (W.U i.succ)
      (sampled omega) (M omega)) i (fun _ ↦ True)
    (by
      intro z hz
      exact ⟨trivial, hraw z (by simpa only [J, Kint] using hz)⟩)
    (fun omega _ ↦ (hclassification0 omega).2) hC hFcard hbroot
    kappa hkappa htail
  obtain ⟨hpos, hstrongC, hcomplete, _hlower⟩ := hroot
  refine ⟨hpos, ?_⟩
  let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGoodIn F
      (jointInitial initial z ∪
        jointLater later (rawResidualInternalAdded M) z)
        (W.U i.succ) R
  let Lc := J.conditionOn RootGood hpos
  let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V :=
    fun _ ↦ G
  let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ A
  let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ ∅
  let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ ∅
  let Mf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ M z.1
  let Qf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ z.2.chosen
  let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ internalStageFamily (If z) (Df z) (Mf z) (Qf z)
  let reservef : Omega × InternalEdgeGreedyStateOn V →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) (sampled z.1) (M z.1)
  let links := internalOutcomeResidualLinks Gf (W.U i.succ) reservef F
    Af If Df Mf Qf
  have hpreC : Lc.SupportedOn fun z ↦
      M z.1 ⊆ A ∧ IsPackingOn (M z.1) ∧
        AvoidsForbidden (M z.1) F ∧
        TrianglesDisjointFrom (W.U i.succ) (M z.1) ∧
        ∀ v : V,
          (scheduledEdgesAt
            (preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
            v).card ≤ d := by
    simpa only [Lc, J, Kint, RootGood] using hpre.conditionOn hpos
  have hrawC : Lc.SupportedOn fun z ↦
      LocalizedRawResidualInternalOutcomeGood W i F (fun _ ↦ G)
        (fun omega ↦ pairSafeAvailable A (M omega)) M bits D R
        z.1 z.2 := by
    simpa only [Lc, J, Kint, RootGood] using hraw.conditionOn hpos
  have hbase : Lc.SupportedOn fun z ↦
      (∀ v, Even ((neighborsIn (Gf z) univ v).card)) ∧
      Gf z ≤ leaveGraph (If z ∪ Df z) ∧
      ConsistsOfTriangles (Gf z) (Af z) ∧
      Mf z ⊆ Af z ∧ Disjoint (If z) (Df z ∪ Mf z) ∧
      IsPackingOn (Mf z) := by
    intro z hz
    exact ⟨heven, by simpa [Gf, If, Df] using hGleave, htri,
      (hpreC z hz).1, by simp [If], (hpreC z hz).2.1⟩
  have hinternal : Lc.SupportedOn fun z ↦
      GreedyReachable F (Mf z) (Qf z) ∧
      Qf z ⊆ Mf z ∪ Af z ∧
      (Qf z \ Mf z).card ≤
        (internalOuterEdges (Gf z) (W.U i.succ)).card ∧
      ∀ e ∈ internalOuterEdges (Gf z) (W.U i.succ),
        (coveredGraph (Qf z)).Adj e.out.1 e.out.2 := by
    intro z hz
    have hc := hcomplete z hz
    refine ⟨hc.2.1, ?_, hc.2.2.2.1, hc.2.2.2.2.1⟩
    intro T hT
    rcases mem_union.mp (hc.2.2.1 hT) with hTM | hTsafe
    · exact mem_union_left (Af z) hTM
    · exact mem_union_right (Mf z)
        (pairSafeAvailable_subset_left A (M z.1) hTsafe)
  have hlinks : Lc.SupportedOn fun z ↦
      IsIntermediateLinkState (Gf z) (W.U i.succ) (Af z)
          (If z) (Df z) (Rf z) (links z) ∧
        (∀ o, (links z o).center =
          outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (links z o).left ⊆ W.U i.succ) ∧
        (∀ o, (links z o).right ⊆ W.U i.succ) ∧
        (∀ o, (links z o).SpokesIn (reservef z)) := by
    have hs := hbase.rawPreliminaryInternalResidualLinks
      (U := W.U i.succ) (sampled := fun z ↦ sampled z.1) (F := F)
      (A := Af) (I := If) (D := Df) (Mstar := Mf) (P0 := Mf) (Q := Qf)
      (fun _ ↦ by simp [If, Df]) hinternal
    simpa only [Gf, reservef, Rf, links] using hs
  have hcovered : Lc.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (Rf z)).neighborFinset o.1 ∩
          W.U i.succ).card ≤ d := by
    intro z hz o
    have hp := hpreC z hz
    have hr := hrawC z hz
    have hreach := (hinternal z hz).1
    apply card_coveredNeighborsIn_internalStageFamily_le_scheduledIncidence
      (I := If z) (D := Df z) (Mstar := Mf z) (P0 := Mf z) (Q := Qf z)
      (E := preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
    · simp [If, Df, Mf]
    · exact hp.2.2.2.1
    · exact hreach.initial_subset
    · exact hreach.isPacking hp.2.1
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (preliminaryResidualInternalEdges_subset_internalOuterEdges
          G (W.U i.succ) (M z.1) he)).2
    · simpa only [Gf, Af, Mf, Qf] using hr.2.2.1
    · simpa only [Gf, Mf] using hp.2.2.2.2
    · exact o.2
  have hstruct : Lc.SupportedOn fun z ↦
      ConsistsOfTriangles (Gf z) (Af z) ∧
        Gf z ≤ leaveGraph (If z ∪ Df z) ∧
        IsPackingOn (If z ∪ (Df z ∪ Rf z)) ∧
        AvoidsForbidden (If z ∪ (Df z ∪ Rf z)) F := by
    intro z hz
    have hreach := (hinternal z hz).1
    have hRsub : Rf z ⊆ Qf z := by
      intro T hT
      rcases mem_union.mp hT with hTM | hTnew
      · exact hreach.initial_subset
          (by simpa only [If, Df, Mf, empty_union] using hTM)
      · exact (mem_sdiff.mp hTnew).1
    refine ⟨htri, by simpa [Gf, If, Df] using hGleave, ?_, ?_⟩
    · exact (hreach.isPacking (hpreC z hz).2.1).mono (by
        simpa only [If, Df, empty_union] using hRsub)
    · exact (hreach.avoidsForbidden (hpreC z hz).2.2.1).mono (by
        simpa only [If, Df, empty_union] using hRsub)
  have hclassification : Lc.SupportedOn fun z ↦
      Disjoint (jointInitial initial z)
          (jointLater later (rawResidualInternalAdded M) z) ∧
        jointInitial initial z ∪
            jointLater later (rawResidualInternalAdded M) z =
          If z ∪ (Df z ∪ Rf z) := by
    intro z hz
    have hclass := hclassification0 z.1
    have hMsub : M z.1 ⊆ Qf z := (hinternal z hz).1.initial_subset
    have hdisjNew : Disjoint (initial z.1)
        (later z.1 ∪ (Qf z \ M z.1)) := by
      rw [Finset.disjoint_left]
      intro T hTI hT
      rcases mem_union.mp hT with hTL | hTnew
      · exact Finset.disjoint_left.mp hclass.1 hTI hTL
      · exact (mem_sdiff.mp hTnew).2 (hclass.2 ▸
          mem_union_left (later z.1) hTI)
    refine ⟨by simpa only [jointInitial, jointLater,
      rawResidualInternalAdded, Qf] using hdisjNew, ?_⟩
    dsimp only [jointInitial, jointLater, rawResidualInternalAdded,
      If, Df, Rf, Mf, Qf]
    rw [← union_assoc, hclass.2]
    simp [internalStageFamily]
  refine ⟨?_, hlinks, hcovered, hstruct, hclassification⟩
  simpa only [Lc, J, Kint, RootGood, reservef] using hstrongC

end

end Erdos207
