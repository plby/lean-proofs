/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterCompression

/-! # Compress a successful updated law after arbitrary finite conditioning -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsResidualMasterIterationGood.compress_updated
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell} {next : Fin (ell+1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D M : Omega → TripleSystemOn V}
    {p eta xi C beta : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood law W next Gzero F
      (fun omega ↦ updatedStageGraph (G omega) (W.U next) (M omega))
      (fun omega ↦ updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (M omega))
      I (fun omega ↦ D omega ∪ M omega) p eta xi C beta h)
    (hstep : law.SupportedOn fun omega ↦
      IsMasterCoverStep F (G omega) (W.U next) (A omega) (I omega) (D omega) (M omega))
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦ CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    IsResidualCompressedMasterLaw
      (law.map (packMasterState
        (fun omega ↦ updatedStageGraph (G omega) (W.U next) (M omega))
        (fun omega ↦ updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (M omega))
        I (fun omega ↦ D omega ∪ M omega)))
      W next F Gzero ambient p eta xi C beta h := by
  apply hgood.compress
  · intro omega hm
    exact (updatedStageAvailable_subset F (W.U next) (A omega) (I omega) (D omega) (M omega)).trans
      (havailable omega hm)
  · intro omega hm
    rw [← union_assoc]
    exact union_subset (hselected omega hm) ((hstep omega hm).selected.trans (havailable omega hm))
  · intro omega hm
    exact (hcover omega hm).updated (hstep omega hm)
  · intro omega hm
    exact (updatedStageGraph_le (G omega) (W.U next) (M omega)).trans (hsub omega hm)
  · intro omega _
    exact updatedStageGraph_supported (G omega) (W.U next) (M omega)

end

end Erdos207
