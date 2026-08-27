/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedInitialProductOuterOnlyInternalStage
import ErdosProblems.Erdos207.LocalizedPartitionedRawInternalResidualLinks

/-!
# The initial product law at the first compressed-link boundary

This file closes the first probabilistic composition boundary.  The long
initial product phase is conditioned on bounded residual outer incidence,
the raw internal cover is conditioned on rooted success, and the resulting
law exposes canonical residual links.  Its distinguished initial family is
retained separately from all later internal choices, while the structural
master state uses empty `I/D` and the whole internal-stage family as `R`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The initial product/outer-only/internal construction, after rooted
conditioning, gives the partition-preserving localized intermediate law
needed by the sharp compressed transition. -/
theorem exists_localizedInitialProductPartitionedRootedResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell}
    {level next stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p C b xi : ℝ≥0} {h : ℕ}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C)
    (hselected : L.SupportedOn fun omega ↦
      selected omega ⊆ A ∧ IsPackingOn (selected omega) ∧
        AvoidsForbidden (selected omega) F)
    (i : Fin ell)
    (houterOnly : L.SupportedOn fun omega ↦
      TrianglesDisjointFrom (W.U i.succ) (selected omega))
    (htyp : IsIterationTypical W stage G A 1 1 xi h)
    (htri : ConsistsOfTriangles G A)
    (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (d : ℕ)
    (epsilonInternal : ℝ≥0)
    (hincidence : L.probability (fun omega ↦ ¬ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G (W.U i.succ)
          (selected omega)) v).card < d + 1) ≤ epsilonInternal)
    (hepsilonInternal : epsilonInternal < 1)
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (m a D R q : ℕ) (hD : 0 < D)
    (hh : 2 ≤ h)
    (hm : (m : ℝ≥0) ≤ (1 - xi) * (W.U i.succ).card)
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmallUniform : ∀ omega,
      let E := preliminaryResidualInternalEdges G (W.U i.succ)
        (selected omega)
      (E.card : ℝ) *
        Real.exp (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hscalar : 4 * d + R * q ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (CPre pFinal bFinal : ℝ≥0)
    (hconditionFactor :
      C / (1 - epsilonInternal) ≤ CPre)
    (hCPre : 1 ≤ CPre)
    (hlevelNext : level ≤ next)
    (hpFinal : p ≤ pFinal)
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1)
    (hbFinal : b ≤ bFinal)
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        pFinal / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      bFinal ≤ setWeight (masterUnionTriangleWeight W next pFinal) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2
            (W.U i.succ) ↦ localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight W next pFinal)
        (∅ : TripleSystemOn V) ≤ kappa)
    (htailRoot :
      strongLocalizedRootedFirstTail V (2 * CPre) kappa R q < 1)
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (hGleave : G ≤ leaveGraph (∅ : TripleSystemOn V)) :
    ∃ law : FiniteLaw (Omega × InternalEdgeGreedyStateOn V),
      let empty : Omega → TripleSystemOn V := fun _ ↦ ∅
      let Gf : Omega × InternalEdgeGreedyStateOn V →
          SimpleGraph V := fun _ ↦ G
      let Af : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ A
      let If : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ ∅
      let Df : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun _ ↦ ∅
      let Mf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦ selected z.1
      let Qf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦ z.2.chosen
      let Rf : Omega × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦
        internalStageFamily (If z) (Df z) (Mf z) (Qf z)
      let reservef : Omega × InternalEdgeGreedyStateOn V →
          Finset (Sym2 V) := fun z ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected z.1)
      let links := internalOutcomeResidualLinks Gf (W.U i.succ)
        reservef F Af If Df Mf Qf
      IsReserveStronglyWellDistributed law W next
          (jointInitial selected)
          (jointLater empty (rawResidualInternalAdded selected)) reservef
          pFinal 1
          ((2 * CPre) /
            (1 - strongLocalizedRootedFirstTail V (2 * CPre) kappa R q)) bFinal ∧
        law.SupportedOn (fun z ↦
          IsIntermediateLinkState (Gf z) (W.U i.succ) (Af z)
              (If z) (Df z) (Rf z) (links z) ∧
            (∀ o, (links z o).center =
              outsideVertexEmbedding (W.U i.succ) o) ∧
            (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉
              W.U i.succ) ∧
            (∀ o, (links z o).left ⊆ W.U i.succ) ∧
            (∀ o, (links z o).right ⊆ W.U i.succ) ∧
            (∀ o, (links z o).SpokesIn (reservef z))) ∧
        law.SupportedOn (fun z ↦
          ∀ o : {x : V // x ∉ W.U i.succ},
            ((coveredGraph (Rf z)).neighborFinset o.1 ∩
              W.U i.succ).card ≤ d) ∧
        law.SupportedOn (fun z ↦
          ConsistsOfTriangles (Gf z) (Af z) ∧
            Gf z ≤ leaveGraph (If z ∪ Df z) ∧
            IsPackingOn (If z ∪ (Df z ∪ Rf z)) ∧
            AvoidsForbidden (If z ∪ (Df z ∪ Rf z)) F) ∧
        law.SupportedOn (fun z ↦
          Disjoint (jointInitial selected z)
            (jointLater empty (rawResidualInternalAdded selected) z) ∧
          jointInitial selected z ∪
              jointLater empty (rawResidualInternalAdded selected) z =
            If z ∪ (Df z ∪ Rf z)) := by
  let Good : Omega → Prop := fun omega ↦ ∀ v : V,
    (scheduledEdgesAt
      (preliminaryResidualInternalEdges G (W.U i.succ)
        (selected omega)) v).card < d + 1
  obtain ⟨hGood, bits, hstrong, hraw, hpre⟩ :=
    exists_localizedInitialProductOuterOnlyInternalStage hproduct hC hselected i
      houterOnly htyp htri hstage hGsupp d epsilonInternal hincidence
      hepsilonInternal reserveRate
      hreserveRate m a D R q hD hh hm ha hsmallUniform hfamily hscalar
      hnonempty CPre pFinal bFinal hconditionFactor hCPre hlevelNext
      hpFinal hfactor hbFinal hnew
  let Lc := L.conditionOn Good hGood
  let empty : Omega → TripleSystemOn V := fun _ ↦ ∅
  have hraw' : (Lc.jointBind (rawResidualInternalKernel W i F
      (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (selected omega))
      selected bits D)).SupportedOn (fun z ↦
        LocalizedRawResidualInternalOutcomeGood W i F (fun _ ↦ G)
          (fun omega ↦ pairSafeAvailable A (selected omega)) selected bits
          D R z.1 z.2) := by
    intro z hz
    exact (hraw z hz).2
  have hCroot : 1 ≤ 2 * CPre := by
    calc
      1 ≤ CPre := hCPre
      _ ≤ 2 * CPre := by
        simpa only [two_mul] using
          (le_add_self : CPre ≤ CPre + CPre)
  have hroot := exists_localizedPartitionedRawInternalResidualLinks
    (law := Lc) (W := W) (level := next) (i := i) (F := F)
    (G := G) (A := A) (M := selected) (initial := selected)
    (later := empty) (bits := bits) (D := D) (R := R) (d := d)
    (sampled := fun _ ↦ ∅) (p := pFinal) (reserveDensity := 1)
    (C := 2 * CPre) (b := bFinal) hstrong
    (fun omega ↦ by simp [empty]) hraw' hpre hCroot hfamily hbroot
    kappa hkappa htailRoot heven hGleave htri
  obtain ⟨hpos, hresult⟩ := hroot
  let Kint := rawResidualInternalKernel W i F (fun _ ↦ G)
    (fun omega ↦ pairSafeAvailable A (selected omega)) selected bits D
  let J := Lc.jointBind Kint
  let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGoodIn F
      (jointInitial selected z ∪
        jointLater empty (rawResidualInternalAdded selected) z)
      (W.U i.succ) R
  refine ⟨J.conditionOn RootGood hpos, ?_⟩
  simpa only [Lc, empty, Kint, J, RootGood] using hresult

end

end Erdos207
