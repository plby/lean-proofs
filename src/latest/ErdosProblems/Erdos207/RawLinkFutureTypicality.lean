/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FutureTypicalityCaps
import ErdosProblems.Erdos207.RawLinkJointMasterUpdate

/-! # Future typicality on every raw outcome, without assuming coverage -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.updatedTypical_failure_le_of_local_quasi
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (Gamma : SimpleGraph V)
    (G : Ω → SimpleGraph V) (A I D M : Ω → TripleSystemOn V)
    (p eta xi xi' epsilon errorDegree errorQuasi : ℝ≥0) (h : ℕ)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h))
    (hpacking : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ (D omega ∪ M omega)))
    (havoids : L.SupportedOn fun omega ↦ AvoidsForbidden (I omega ∪ (D omega ∪ M omega)) F)
    (hbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hkn : k ≤ next) (hxi : xi ≤ xi') (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1 + h + h ^ 2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ a ∈ futureLevelPairs next,
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h ^ 2) * (W.U a.2).card)
    (hdegree : L.probability (fun omega ↦
      ¬ LocalFutureDegreeCaps W next (G omega) (M omega) p eta epsilon h) ≤ errorDegree)
    (hquasi : L.probability (fun omega ↦
      ¬ FutureQuasiCaps W next F Gamma (I omega) (D omega ∪ M omega) p eta epsilon h) ≤ errorQuasi) :
    L.probability (fun omega ↦ ¬ IsIterationTypical W next
      (updatedStageGraph (G omega) (W.U next) (M omega))
      (updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (M omega))
      p eta xi' h) ≤ errorDegree + errorQuasi := by
  let Degree := fun omega ↦ LocalFutureDegreeCaps W next (G omega) (M omega) p eta epsilon h
  let Quasi := fun omega ↦ FutureQuasiCaps W next F Gamma (I omega) (D omega ∪ M omega) p eta epsilon h
  have hstruct : L.SupportedOn fun omega ↦
      masterPointwiseGoodEvent W k F G A I D p eta xi h omega ∧
        IsPackingOn (I omega ∪ (D omega ∪ M omega)) ∧
        AvoidsForbidden (I omega ∪ (D omega ∪ M omega)) F ∧ G omega ≤ Gamma :=
    fun omega hm ↦ ⟨hold omega hm, hpacking omega hm, havoids omega hm, hbase omega hm⟩
  calc
    _ ≤ L.probability (fun omega ↦ ¬ Degree omega ∨ ¬ Quasi omega) := by
      apply L.probability_mono_of_supported hstruct
      intro omega hs hbad
      by_contra hnot
      have hd : Degree omega := by tauto
      have hq : Quasi omega := by tauto
      have hloss := masterTypicalityLossEvent_of_local_quasi_caps_packing hs.1 hs.2.1
        hs.2.2.1 hs.2.2.2 hp heta hh hepsilon
        (fun i hi iStar hStar ↦ hsupport (i, iStar)
          ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩))
        (fun i hi iStar hStar v hv ↦ hd (i, iStar)
          ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩) v hv)
        (fun i hi iStar hStar Q hQ e he ↦ hq (i, iStar)
          ((mem_futureLevelPairs_iff next _).mpr ⟨hi, hStar⟩) ⟨Q, hQ⟩ e he)
      exact hbad (hs.1.2.2.2.1.updatedStage_of_loss hkn hxi hloss.1 hloss.2.1 hloss.2.2)
    _ ≤ L.probability (fun omega ↦ ¬ Degree omega) + L.probability (fun omega ↦ ¬ Quasi omega) :=
      L.probability_or_le _ _
    _ ≤ _ := add_le_add hdegree hquasi

theorem FiniteLaw.rawLinkJoint_updatedTypical_failure_le
    {Ω O V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (Gamma : SimpleGraph V)
    (G : Ω → SimpleGraph V) (A I D R : Ω → TripleSystemOn V)
    (result : Ω → TripleSystemOn V × TripleSystemOn V) (links : Ω → O → BipartiteLink V)
    (p eta xi xi' epsilon errorDegree errorQuasi : ℝ≥0) (h : ℕ)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h))
    (hstruct : L.SupportedOn fun omega ↦ IsSampledLinkJointOutcome F (A omega)
      (I omega ∪ (D omega ∪ R omega)) (links omega) (result omega))
    (hbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hkn : k ≤ next) (hxi : xi ≤ xi') (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1 + h + h ^ 2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ a ∈ futureLevelPairs next,
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h ^ 2) * (W.U a.2).card)
    (hdegree : L.probability (fun omega ↦ ¬ LocalFutureDegreeCaps W next (G omega)
      (R omega ∪ (result omega).2) p eta epsilon h) ≤ errorDegree)
    (hquasi : L.probability (fun omega ↦ ¬ FutureQuasiCaps W next F Gamma (I omega)
      (D omega ∪ (R omega ∪ (result omega).2)) p eta epsilon h) ≤ errorQuasi) :
    L.probability (fun omega ↦ ¬ IsIterationTypical W next
      (updatedStageGraph (G omega) (W.U next) (R omega ∪ (result omega).2))
      (updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (R omega ∪ (result omega).2))
      p eta xi' h) ≤ errorDegree + errorQuasi := by
  apply L.updatedTypical_failure_le_of_local_quasi W k next F Gamma G A I D
    (fun omega ↦ R omega ∪ (result omega).2) p eta xi xi' epsilon errorDegree errorQuasi h hold
    _ _ hbase hkn hxi hp heta hh hepsilon hsupport hdegree hquasi
  · intro omega hm
    simpa only [union_assoc] using (hstruct omega hm).selected_safe.2.2.1
  · intro omega hm
    simpa only [union_assoc] using (hstruct omega hm).selected_safe.2.2.2

end

end Erdos207
