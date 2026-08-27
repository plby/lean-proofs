/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawLinkFutureTypicality
import ErdosProblems.Erdos207.RawLinkJointFutureDegree

/-! # Closing the actual link stage from its local-degree and quasi events -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem residualMasterIterationGood_of_rawLink_joint_caps
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k next : Fin (ell + 1)} {Gamma : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V}
    {A I D R : Ω → TripleSystemOn V} {result : Ω → TripleSystemOn V × TripleSystemOn V}
    {links : Ω → {x : V // x ∉ W.U next} → BipartiteLink V}
    {p eta xi xi' epsilon C b error errorDegree errorQuasi : ℝ≥0} {h : ℕ}
    (hstrong : IsResidualGraphStronglyWellDistributed L W next Gamma I
      (fun omega ↦ (D omega ∪ R omega) ∪ (result omega).2) p C b)
    (heven : HasEvenStageGraphs L G)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h))
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState (G omega) (W.U next)
      (A omega) (I omega) (D omega) (R omega) (links omega))
    (hstruct : L.SupportedOn fun omega ↦ IsSampledLinkJointOutcome F (A omega)
      (I omega ∪ (D omega ∪ R omega)) (links omega) (result omega))
    (hcoverage : L.probability
      (fun omega ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) (result omega).2) ≤ error)
    (herror : error < 1) (hbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hkn : k ≤ next) (hxi : xi ≤ xi') (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1 + h + h ^ 2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ a ∈ futureLevelPairs next,
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h ^ 2) * (W.U a.2).card)
    (hdegree : L.probability (fun omega ↦ ¬ LocalFutureDegreeCaps W next (G omega)
      (R omega ∪ (result omega).2) p eta epsilon h) ≤ errorDegree)
    (hquasi : L.probability (fun omega ↦ ¬ FutureQuasiCaps W next F Gamma (I omega)
      (D omega ∪ (R omega ∪ (result omega).2)) p eta epsilon h) ≤ errorQuasi)
    (hbudget : errorDegree + errorQuasi ≤ xi' * (1 - error)) :
    let Success := fun omega ↦ ∀ o, CoversBipartiteLink (links omega o) (result omega).2
    ∃ hpos : 0 < L.probability Success,
      1 - error ≤ L.probability Success ∧
      IsResidualMasterIterationGood (L.conditionOn Success hpos) W next Gamma F
        (fun omega ↦ updatedStageGraph (G omega) (W.U next) (R omega ∪ (result omega).2))
        (fun omega ↦ updatedStageAvailable F (W.U next)
          (A omega) (I omega) (D omega) (R omega ∪ (result omega).2))
        I (fun omega ↦ D omega ∪ (R omega ∪ (result omega).2))
        p eta xi' (C / (1 - error)) b h := by
  apply residualMasterIterationGood_of_rawLink_joint_success hstrong heven hold hstate hstruct
    hcoverage herror _ hbudget
  exact L.rawLinkJoint_updatedTypical_failure_le W k next F Gamma G A I D R result links
    p eta xi xi' epsilon errorDegree errorQuasi h hold hstruct hbase hkn hxi hp heta hh
    hepsilon hsupport hdegree hquasi

end

end Erdos207
