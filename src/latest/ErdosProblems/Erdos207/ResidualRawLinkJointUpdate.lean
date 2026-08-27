/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IntermediateLinkSourceGeometry
import ErdosProblems.Erdos207.ResidualForcedReserveNumeric

/-! # The actual joint reservoir/cover law preserves the corrected residual distribution -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.jointBind_rawLinkJoint_numeric
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell+1)} {Gamma : SimpleGraph V}
    {initial later historical available : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k Gamma initial later reserve p r C b)
    (U : Finset V) (center : Ω → O ↪ V) (links : Ω → O → BipartiteLink V)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (sigma factor : ℝ≥0) (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (hsigma : sigma ≤ 1)
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : sigma*p^3*r^2 ≤ factor*(p/((W.U k).card : ℝ≥0)))
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (initial omega) (later omega)
      (historical omega) (available omega) (reserve omega) (center omega) (links omega) orders F)
    (hstruct : ∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
      (IsSampledLinkJointOutcome (orders.biUnion F) (available omega) (initial omega ∪ later omega) (links omega)))
    (hpoint : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card) :
    IsResidualGraphStronglyWellDistributed (L.jointBind kernel) W next Gamma
      (fun result ↦ initial result.1) (fun result ↦ later result.1 ∪ result.2.2)
      p (2*max (C^5*factor) 1) b := by
  have hadded : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (kernel omega).probability (fun result ↦ Q ⊆ result.2) ≤ sigma^Q.card+(1 : ℝ≥0)^Q.card*0 := by
    intro omega hmass Q
    simpa only [mul_zero, add_zero] using (kernel omega).sampledLinkJoint_selected_probability_le
      (hstruct omega hmass) sigma (hpoint omega hmass) Q
  have hb := hstrong.jointBind_forcedReserve_numeric (K := kernel) (fun _ result ↦ result.2)
    (familyCrossingEdges U) 2 sigma 1 factor 0 hC le_rfl hfactor hsigma hkn hnonempty hnew hadded
  apply (by simpa only [add_zero] using hb)
  · intro omega hmass result hresult
    have hs := hstruct omega hmass result hresult
    have hg := hgeometry omega hmass
    exact ⟨hs.selected_safe.2.2.1, hs.selected_safe.2.1,
      fun T hT ↦ hg.triangles.triple_edges_subset (hs.selected_safe.1 hT)⟩
  · intro omega hmass result hresult Q hQ
    have hs := hstruct omega hmass result hresult
    have hg := hgeometry omega hmass
    exact (hs.selected_family.mono hQ).familyCrossingEdges_subset
      hg.center_eq hg.center_outside hg.left_inner hg.right_inner hg.reserve_spokes
  · intro omega hmass result hresult
    have hs := hstruct omega hmass result hresult
    have hg := hgeometry omega hmass
    refine ⟨fun T hT ↦ hg.terminal_available T (hs.selected_safe.1 hT), ?_⟩
    intro Q hQ
    exact (hs.selected_family.mono hQ).card_familyCrossingEdges
      hg.center_eq hg.center_outside hg.left_inner hg.right_inner
      (hs.selected_safe.2.2.1.mono (hQ.trans subset_union_right))

theorem IsSampledLinkJointOutcome.masterCoverStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {F : ForbiddenFamilyOn V} {A I D R : TripleSystemOn V}
    {links : {x : V // x ∉ U} → BipartiteLink V} {result : TripleSystemOn V × TripleSystemOn V}
    (hstruct : IsSampledLinkJointOutcome F A (I ∪ (D ∪ R)) links result)
    (hstate : IsIntermediateLinkState G U A I D R links)
    (hcover : ∀ o, CoversBipartiteLink (links o) result.2) :
    IsMasterCoverStep F G U A I D (R ∪ result.2) := by
  have hs := hstruct.selected_safe
  have hfull : IsSimultaneousLinkCover F A (I ∪ (D ∪ R)) links result.2 :=
    ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hcover⟩
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  exact hfull.isMasterCoverStep hstate.1 hstate.2.1 hstate.2.2

end

end Erdos207
