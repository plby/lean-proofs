/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedPreliminaryInternalSafeCandidates
import ErdosProblems.Erdos207.LocalizedPreliminaryResidualInternalComposition

/-!
# Strong-law composition with preliminary-safe internal candidates

An outer-only preliminary family preserves every initial internal extension
triangle whose pair is still uncovered.  This file combines that geometric
fact with the generic direct-kernel composition theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsReserveStronglyWellDistributed.exists_jointBind_localizedRawResidualInternalKernel_of_outerOnly
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {level next stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A P M : Omega → TripleSystemOn V}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {pMaster reserveDensity C b p' C' b' : ℝ≥0}
    {pTypical eta xi : ℝ≥0} {h : ℕ}
    (hstrong : IsReserveStronglyWellDistributed law W level initial later
      reserve pMaster reserveDensity C b)
    (Good : Omega → Prop) (hgoodSupport : law.SupportedOn Good)
    (htyp : ∀ omega, Good omega →
      IsIterationTypical W stage (G omega) (A omega)
        pTypical eta xi h)
    (htri : ∀ omega, Good omega → ConsistsOfTriangles (G omega) (A omega))
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : ∀ omega, Good omega →
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hpacking : ∀ omega, Good omega →
      IsPackingOn (P omega ∪ M omega))
    (havoid : ∀ omega, Good omega →
      AvoidsForbidden (P omega ∪ M omega) F)
    (hold : ∀ omega, Good omega → ∀ T ∈ A omega,
      TriangleAvoidsGraph (coveredGraph (P omega)) T)
    (houterOnly : ∀ omega, Good omega →
      TrianglesDisjointFrom (W.U i.succ) (M omega))
    (hh : 2 ≤ h) (reserveRate : ℝ≥0)
    (hreserveRate : reserveRate ≤ 1)
    (m a D d R q : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (pTypical ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmallUniform : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P omega ∪ M omega)
      (E.card : ℝ) *
        Real.exp
          (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hincidence : ∀ omega, Good omega → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges (G omega) (W.U i.succ)
          (P omega ∪ M omega)) v).card ≤ d)
    (hscalar : 4 * d + R * q ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hlevelNext : level ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpMaster : pMaster ≤ p') (hfactor : (D : ℝ≥0)⁻¹ ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let Aint : Omega → TripleSystemOn V := fun omega ↦
      pairSafeAvailable (A omega) (P omega ∪ M omega)
    let P0 : Omega → TripleSystemOn V := fun omega ↦
      P omega ∪ M omega
    ∃ bits : Omega → Sym2 V → Bool,
      let K := rawResidualInternalKernel W i F G Aint P0 bits D
      let added := rawResidualInternalAdded P0
      IsReserveStronglyWellDistributed (law.jointBind K) W next
          (jointInitial initial) (jointLater later added)
          (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
        (law.jointBind K).SupportedOn (fun z ↦
          Good z.1 ∧
            LocalizedRawResidualInternalOutcomeGood W i F G Aint P0 bits D R
              z.1 z.2) := by
  dsimp only
  let Aint : Omega → TripleSystemOn V := fun omega ↦
    pairSafeAvailable (A omega) (P omega ∪ M omega)
  let P0 : Omega → TripleSystemOn V := fun omega ↦
    P omega ∪ M omega
  have hkernel : ∃ bits : Omega → Sym2 V → Bool,
      (∀ omega, Good omega →
        LocalizedRawResidualInternalFiberGood W i F G Aint P0 bits D R omega) ∧
      ∀ omega Q,
        (rawResidualInternalKernel W i F G Aint P0 bits D omega).probability
          (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
            ((D : ℝ≥0)⁻¹ ^ Q.card) := by
    simpa only [Aint, P0] using
      (exists_localizedRawResidualInternalKernel_of_outerOnly Good htyp htri i
        hstage hGsupp hpacking havoid hold houterOnly hh reserveRate
        hreserveRate m a D d R q hD hm ha hsmallUniform hfamily
        hincidence hscalar)
  exact hstrong.exists_jointBind_localizedRawResidualInternalKernel_of_certificate
    Good hgoodSupport hkernel hnonempty hlevelNext hCC' hC' hpMaster
      hfactor hbb' hnew

end

end Erdos207
