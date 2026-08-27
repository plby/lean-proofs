/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkRealizedCoordinates

/-! # Joint inclusion for every marked coordinate prescription -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_sourceLink_inclusion_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hstruct : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (U : Finset V) (candidate : Ω → Ξ → TripleSystemOn V) (sigma J delta : ℝ≥0)
    (hsigma : sigma ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hcandidate : ∀ ω, 0 < L.mass ω → ∀ Q,
      (K ω).probability (fun ξ ↦ Q ⊆ candidate ω ξ) ≤ sigma ^ Q.card + J ^ Q.card * delta)
    (H : Finset (SourceLinkCoordinate V)) :
    (L.jointBind K).probability (fun z ↦ H ⊆ sourceLinkRealizedCoordinates G U
      (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1)) ≤
      (max (C ^ 2) J) ^ H.card *
        (setWeight (sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
          (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma) (sourceLinkCanonicalEdgeWeight U p r)) H + b + delta) := by
  by_cases hdis : Disjoint H.toLeft.toLeft H.toLeft.toRight.toLeft
  · by_cases hE : H.toRight ⊆ graphEdges G
    · exact hstrong.jointBind_sourceLink_prescriptions U candidate sigma J delta hsigma hC hJ hcandidate H hdis hE
    · have hz : (L.jointBind K).probability (fun z ↦ H ⊆ sourceLinkRealizedCoordinates G U
          (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1)) ≤
          (L.jointBind K).probability (fun _ ↦ False) := by
        apply FiniteLaw.probability_mono
        intro z hH
        have hh := (subset_disjSum.mp hH).2
        exact hE ((sourceLinkRetainedEdges_subset_iff G U _ _ _ _).mp hh).1
      rw [FiniteLaw.probability_false] at hz
      exact hz.trans zero_le
  · have hstruct' : (L.jointBind K).SupportedOn fun z ↦ Disjoint (initial z.1) (later z.1) := by
      intro z hz
      exact hstruct z.1 ((L.jointBind_mass_pos_iff K z.1 z.2).mp hz).1
    have hz : (L.jointBind K).probability (fun z ↦ H ⊆ sourceLinkRealizedCoordinates G U
        (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1)) ≤
        (L.jointBind K).probability (fun _ ↦ False) := by
      apply (L.jointBind K).probability_mono_of_supported hstruct'
      intro z hd hH
      have hleft : H.toLeft ⊆ (initial z.1).disjSum ((later z.1).disjSum (candidate z.1 z.2)) :=
        (subset_disjSum.mp hH).1
      have hh := subset_disjSum.mp hleft
      exact hdis (hd.mono hh.1 (subset_disjSum.mp hh.2).1)
    rw [FiniteLaw.probability_false] at hz
    exact hz.trans zero_le

end

end Erdos207
