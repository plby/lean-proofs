/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalFixedReserveKernel
import ErdosProblems.Erdos207.ReservePreservingScaleUpdate

/-!
# Adjoining a residual-internal kernel using the already sampled reserve

Unlike the earlier existential composition theorem, this result keeps the
given reserve realization definitionally unchanged.  This is required when
the same sampled crossing edges both protected the preliminary phase and
supply the two spokes used by the internal phase.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Bind an exact fixed-reserve raw internal certificate to a reserve-aware
strong law. -/
theorem IsReserveStronglyWellDistributed.jointBind_rawResidualInternalKernel_of_fixedReserve
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {pMaster reserveDensity C b p' C' b' : ℝ≥0}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    (hstrong : IsReserveStronglyWellDistributed law W level initial later
      reserve pMaster reserveDensity C b)
    (Good : Omega → Prop) (hgoodSupport : law.SupportedOn Good)
    (hfiber : ∀ omega, Good omega →
      RawResidualInternalFiberGood W i F G A P0 bits D R omega)
    (hC4 : ∀ omega Q,
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
    let K := rawResidualInternalKernel W i F G A P0 bits D
    let added := rawResidualInternalAdded P0
    IsReserveStronglyWellDistributed (law.jointBind K) W next
        (jointInitial initial) (jointLater later added)
        (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
      (law.jointBind K).SupportedOn (fun z ↦
        Good z.1 ∧
          RawResidualInternalOutcomeGood W i F G A P0 bits D R
            z.1 z.2) := by
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
      (hfiber omega hgood).supportedOn_outcome
  exact ⟨by simpa only [K, added] using hupdated,
    by simpa only [K] using hsupported⟩

end

end Erdos207
