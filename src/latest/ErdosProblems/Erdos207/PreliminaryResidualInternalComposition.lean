/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalKernel
import ErdosProblems.Erdos207.ReservePreservingScaleUpdate

/-!
# Adjoining the raw residual-internal kernel

This is the probabilistic composition step needed before rooted-cap
extraction.  The internal law is deliberately *not* conditioned on success:
its sharp C4 estimate updates the strong master law, while its support retains
the certificate saying that any terminal rooted-cap outcome must be
successful.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsReserveStronglyWellDistributed.exists_jointBind_rawResidualInternalKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {level next stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
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
    (hpacking0 : ∀ omega, Good omega → IsPackingOn (P0 omega))
    (havoid0 : ∀ omega, Good omega → AvoidsForbidden (P0 omega) F)
    (hinitial : ∀ omega, Good omega →
      ∀ T ∈ A omega, TriangleAvoidsGraph (coveredGraph (P0 omega)) T)
    (hh : 2 ≤ h) (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (m a D d R q : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (pTypical ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      (E.card : ℝ) *
        Real.exp (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hincidence : ∀ omega, Good omega → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges
          (G omega) (W.U i.succ) (P0 omega)) v).card ≤ d)
    (hscalar : 4 * d + R * q ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hlevelNext : level ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpMaster : pMaster ≤ p') (hfactor : (D : ℝ≥0)⁻¹ ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    ∃ bits : Omega → Sym2 V → Bool,
      let K := rawResidualInternalKernel W i F G A P0 bits D
      let added := rawResidualInternalAdded P0
      IsReserveStronglyWellDistributed (law.jointBind K) W next
          (jointInitial initial) (jointLater later added)
          (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
        (law.jointBind K).SupportedOn (fun z ↦
          Good z.1 ∧
            RawResidualInternalOutcomeGood W i F G A P0 bits D R
              z.1 z.2) := by
  obtain ⟨bits, hbits, hC4⟩ := exists_rawResidualInternalKernel Good htyp
    htri i hstage hGsupp hpacking0 havoid0 hinitial hh reserveRate
    hreserveRate m a D d R q hD hm ha hsmall hfamily hincidence hscalar
  refine ⟨bits, ?_⟩
  dsimp only
  let K := rawResidualInternalKernel W i F G A P0 bits D
  let added := rawResidualInternalAdded P0
  have hupdated : IsReserveStronglyWellDistributed (law.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' := by
    apply hstrong.jointBind_adjoin_preserve_of_numeric added
      (fun omega Q ↦ hC4 omega Q) hnonempty hlevelNext hCC' hC'
      hpMaster hfactor hbb' hnew
  have hsupported : (law.jointBind K).SupportedOn (fun z ↦
      Good z.1 ∧
        RawResidualInternalOutcomeGood W i F G A P0 bits D R z.1 z.2) := by
    exact hgoodSupport.jointBind fun omega hgood ↦
      (hbits omega hgood).supportedOn_outcome
  exact ⟨by simpa only [K, added] using hupdated,
    by simpa only [K] using hsupported⟩

end

end Erdos207
