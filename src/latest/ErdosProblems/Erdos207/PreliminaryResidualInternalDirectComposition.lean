/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalDirectKernel
import ErdosProblems.Erdos207.ReservePreservingScaleUpdate

/-!
# Adjoining a directly supplied raw residual-internal kernel

This is the composition counterpart of
`exists_rawResidualInternalKernel_of_directSupply`.  It separates the local
candidate-supply proof from the strong-distribution update, so that an
outer-only preliminary phase can retain all crossing spokes and supply the
internal kernel from the initial typicality certificate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsReserveStronglyWellDistributed.exists_jointBind_rawResidualInternalKernel_of_directSupply
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {pMaster reserveDensity C b p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed law W level initial later
      reserve pMaster reserveDensity C b)
    (Good : Omega → Prop) (hgoodSupport : law.SupportedOn Good)
    (htri : ∀ omega, Good omega → ConsistsOfTriangles (G omega) (A omega))
    (i : Fin ell)
    (hpacking0 : ∀ omega, Good omega → IsPackingOn (P0 omega))
    (havoid0 : ∀ omega, Good omega → AvoidsForbidden (P0 omega) F)
    (hinitial : ∀ omega, Good omega →
      ∀ T ∈ A omega, TriangleAvoidsGraph (coveredGraph (P0 omega)) T)
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (a D d R q : ℕ) (hD : 0 < D)
    (hsupply : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      ∀ e ∈ E,
        let S := residualInternalExtensionSet W i (A omega) e
        ((a + D : ℕ) : ℝ) ≤
          ((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card / 4)
    (hsmall : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      ∑ e ∈ E,
        (let S := residualInternalExtensionSet W i (A omega) e;
          Real.exp
            (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card) / 4)) < 1)
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
  obtain ⟨bits, hbits, hC4⟩ :=
    exists_rawResidualInternalKernel_of_directSupply Good htri i
      hpacking0 havoid0 hinitial reserveRate hreserveRate a D d R q hD
      hsupply hsmall hfamily hincidence hscalar
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

/-- Generic composition form: any pointwise residual-internal kernel
certificate with the sharp inclusion estimate can be adjoined to a
reserve-aware strong law. -/
theorem IsReserveStronglyWellDistributed.exists_jointBind_rawResidualInternalKernel_of_certificate
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {pMaster reserveDensity C b p' C' b' : ℝ≥0}
    {D R : ℕ}
    (hstrong : IsReserveStronglyWellDistributed law W level initial later
      reserve pMaster reserveDensity C b)
    (Good : Omega → Prop) (hgoodSupport : law.SupportedOn Good)
    (hkernel : ∃ bits : Omega → Sym2 V → Bool,
      (∀ omega, Good omega →
        RawResidualInternalFiberGood W i F G A P0 bits D R omega) ∧
      ∀ omega Q,
        (rawResidualInternalKernel W i F G A P0 bits D omega).probability
          (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
            ((D : ℝ≥0)⁻¹ ^ Q.card))
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
  obtain ⟨bits, hbits, hC4⟩ := hkernel
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
