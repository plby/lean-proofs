/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceReservePreparation
import ErdosProblems.Erdos207.ResidualSupportedSubtype
import ErdosProblems.Erdos207.IterationRegularizedAuxiliaryMass

/-! # Construct a prepared reserve law with a nonempty actual auxiliary family in every fiber -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.exists_prepared_reserve_law
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {Gamma : SimpleGraph V} {initial later : Omega → TripleSystemOn V} {p eta xi C beta r : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W i.castSucc Gamma initial later p C beta)
    (G : Omega → SimpleGraph V) (A : Omega → TripleSystemOn V) (h : ℕ)
    (htyp : ∀ omega, 0 < L.mass omega → IsIterationTypical W i.castSucc (G omega) (A omega) p eta xi h)
    (htri : ∀ omega, 0 < L.mass omega → ConsistsOfTriangles (G omega) (A omega))
    (hGsupp : ∀ omega, 0 < L.mass omega → GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hC : 1 ≤ C) (hp : 0 < p) (hp1 : p ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hh : 4 ≤ h) (hr : r ≤ 1) (hrsmall : r ≤ 1 / 24576)
    (epsilon theta : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxi : (xi : ℝ) ≤ epsilon / 4) (hxiSmall : xi ≤ 1 / 1536)
    (hendpoint : 1 ≤ (epsilon / 4) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card))
    (supply : ℕ) (hsupply : (supply : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8)
    (hdensity : 6144 ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card)
    (hinner : ((W.U i.succ).card : ℝ≥0) ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card / 1536)
    (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hsampling : 2 * ((W.U i.castSucc).card : ℝ) ^ 2 *
      Real.exp (-theta ^ 2 * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card) / 16) < 1)
    (eta0 : ℝ≥0) (heta0 : 0 < eta0) (hetaLower : eta0 ≤ eta)
    (hn : 0 < (W.U i.castSucc).card)
    (error : ℝ≥0)
    (herrorBound : sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon +
      reserveRegularizationFailureBound (W.U i.castSucc).card p eta r ≤ error)
    (herror : error < 1) :
    let joint := L.jointBind (fun omega ↦ reserveEdgeLaw (G omega) (W.U i.succ) r hr)
    let Good := fun x : Omega × (Sym2 V → Bool) ↦ 0 < L.mass x.1 ∧
      SourceReservePreparationGood (G x.1) (A x.1) (W.U i.castSucc) (W.U i.succ)
        p eta r epsilon theta supply x.2
    ∃ hpos : 0 < joint.probability Good,
      1 - error ≤ joint.probability Good ∧
      IsResidualReserveStronglyWellDistributed (joint.conditionSubtype Good hpos) W i.castSucc Gamma
        (fun x ↦ initial x.val.1) (fun x ↦ later x.val.1)
        (fun x ↦ reserveEdges (G x.val.1) (W.U i.succ) x.val.2) p r (C / (1 - error)) beta ∧
      ∃ B : {x // Good x} → TripleSystemOn V, ∀ x,
        B x ⊆ reserveProtectedOuterAvailable (G x.val.1) (W.U i.succ)
          (reserveEdges (G x.val.1) (W.U i.succ) x.val.2) (A x.val.1) ∧
        (B x).Nonempty ∧
        p ^ 3 * ((W.U i.castSucc).card : ℝ≥0) ^ 3 / (192 / eta0) ≤ (B x).card ∧
        ∀ e ∈ graphEdges (reserveProtectedOuterGraph (G x.val.1) (W.U i.succ)
          (reserveEdges (G x.val.1) (W.U i.succ) x.val.2)),
          |(((B x).filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
            (p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4| ≤
              theta * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4) := by
  dsimp only
  let K := fun omega ↦ reserveEdgeLaw (G omega) (W.U i.succ) r hr
  let joint := L.jointBind K
  let Good := fun x : Omega × (Sym2 V → Bool) ↦ 0 < L.mass x.1 ∧
    SourceReservePreparationGood (G x.1) (A x.1) (W.U i.castSucc) (W.U i.succ)
      p eta r epsilon theta supply x.2
  have hprior : L.probability (fun omega ↦ ¬ (0 < L.mass omega)) ≤ 0 := by
    rw [L.probability_not (fun omega ↦ 0 < L.mass omega),
      L.probability_eq_one_of_supported (fun omega ↦ 0 < L.mass omega) (fun _ h ↦ h)]
    simp only [tsub_self, le_refl]
  have hfailure : joint.probability (fun x ↦ ¬ Good x) ≤ error := by
    have hb := L.jointBind_not_good_pair_le K (fun omega ↦ 0 < L.mass omega)
      (fun omega bits ↦ SourceReservePreparationGood (G omega) (A omega) (W.U i.castSucc) (W.U i.succ)
        p eta r epsilon theta supply bits) 0
      (sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon +
        reserveRegularizationFailureBound (W.U i.castSucc).card p eta r) hprior
      (fun omega hmass _ ↦ (htyp omega hmass).sourceReservePreparation_failure_probability_le
        (htri omega hmass) hp hp1 heta heta1 i le_rfl (hGsupp omega hmass) hh r hr hrsmall
        epsilon theta hepsilon hepsilon1 hxi hxiSmall hendpoint supply hsupply hdensity hinner
        htheta (by linarith) hsampling)
    apply le_trans _ herrorBound
    simpa only [zero_add] using hb
  have hlower : 1 - error ≤ joint.probability Good := by
    rw [joint.probability_not Good] at hfailure
    exact tsub_le_iff_tsub_le.mp hfailure
  have hden : 0 < 1 - error := tsub_pos_iff_lt.mpr herror
  have hpos : 0 < joint.probability Good := hden.trans_le hlower
  refine ⟨hpos, hlower, ?_, ?_⟩
  · have hreserved := hstrong.jointBind_reserveEdges (G := G) (U := W.U i.succ) hC hr
    exact (hreserved.conditionSubtype Good hpos).mono
      (div_le_div_of_nonneg_left zero_le hden hlower) le_rfl
  · have hxiHalf : xi ≤ 1 / 2 := hxiSmall.trans (by
      apply NNReal.coe_le_coe.mp
      norm_num)
    have hexists : ∀ x : {x // Good x}, ∃ B ⊆ reserveProtectedOuterAvailable (G x.val.1) (W.U i.succ)
        (reserveEdges (G x.val.1) (W.U i.succ) x.val.2) (A x.val.1),
        B.Nonempty ∧ p ^ 3 * ((W.U i.castSucc).card : ℝ≥0) ^ 3 / (192 / eta0) ≤ B.card ∧
        ∀ e ∈ graphEdges (reserveProtectedOuterGraph (G x.val.1) (W.U i.succ)
          (reserveEdges (G x.val.1) (W.U i.succ) x.val.2)),
          |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
            (p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4| ≤
              theta * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4) := by
      intro x
      exact (htyp x.val.1 x.property.1).exists_reserve_regularized_auxiliary_mass i le_rfl hxiHalf
        (hGsupp x.val.1 x.property.1) (W.U i.succ) x.val.2 hp hp1 heta1 eta0 heta0 hetaLower
        hn hinner theta hthetaHalf x.property.2.2
    choose B hB using hexists
    exact ⟨B, hB⟩

end

end Erdos207
