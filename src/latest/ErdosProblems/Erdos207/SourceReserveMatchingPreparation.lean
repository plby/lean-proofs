/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedReserveMatchingLinks
import ErdosProblems.Erdos207.PreliminaryDegreeCoverGeometry
import ErdosProblems.Erdos207.ReserveOverlapPowerBudgets

/-! # Actual degree and augmented-reserve tails prepare the support-preserving link choice -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem PreliminaryResidualDegreeGood.disjoint_internal_covered_neighbors
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {U : Finset V} {sampled : Finset (Sym2 V)} {P Q : TripleSystemOn V} {d : ℕ}
    (h : PreliminaryResidualDegreeGood (reserveProtectedOuterGraph G U sampled) U P d)
    (hsampled : sampled ⊆ crossingEdges G U) (hpacking : IsPackingOn (P ∪ Q)) (hdis : Disjoint P Q)
    (huse : NewTrianglesUseScheduledOuterEdges U (preliminaryResidualInternalEdges G U P) P (P ∪ Q))
    {center : V} (hc : center ∉ U) : ((coveredGraph Q).neighborFinset center ∩ U).card ≤ 2*d := by
  have hb := h.internal_covered_neighbors hsampled hpacking huse hc
  have heq : ((coveredGraph ((P ∪ Q) \ P)).neighborFinset center ∩ U) =
      ((coveredGraph Q).neighborFinset center ∩ U) := by
    ext x
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, union_sdiff_cancel_left hdis]
  exact heq ▸ hb

theorem IsResidualReserveStronglyWellDistributed.exists_source_reserve_matching_preparation
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V}
    {I D P Q R A : Omega → TripleSystemOn V} {G : Omega → SimpleGraph V}
    {bits : Omega → Sym2 V → Bool} {reserve : Omega → Finset (Sym2 V)}
    {p r C beta : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k Gamma I
      (fun omega ↦ D omega ∪ R omega) reserve p r C beta)
    (current U : Finset V) (F : ForbiddenFamilyOn V)
    (Kold : Omega → {x : V // x ∉ U} → BipartiteLink V)
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState (G omega) U (A omega)
      (I omega) (D omega) (R omega) (Kold omega))
    (hleft : L.SupportedOn fun omega ↦ ∀ o, (Kold omega o).left ⊆ U)
    (hright : L.SupportedOn fun omega ↦ ∀ o, (Kold omega o).right ⊆ U)
    (hspokes : L.SupportedOn fun omega ↦ ∀ o, (Kold omega o).SpokesIn (reserve omega))
    (hsupp : L.SupportedOn fun omega ↦ GraphSupportedOn (G omega) (current : Set V))
    (htri : L.SupportedOn fun omega ↦ ConsistsOfTriangles (G omega) (A omega))
    (hGleave : L.SupportedOn fun omega ↦ G omega ≤ leaveGraph (I omega ∪ D omega))
    (hmeet : L.SupportedOn fun omega ↦ TrianglesMeetAtMostOne U (R omega))
    (hpacking : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (havoid : L.SupportedOn fun omega ↦ AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) F)
    (hprotected : L.SupportedOn fun omega ↦ P omega ⊆
      reserveProtectedAvailable (reserveEdges (G omega) U (bits omega)) (A omega))
    (hR : L.SupportedOn fun omega ↦ R omega = P omega ∪ Q omega)
    (hdis : L.SupportedOn fun omega ↦ Disjoint (P omega) (Q omega))
    (huse : L.SupportedOn fun omega ↦ NewTrianglesUseScheduledOuterEdges U
      (preliminaryResidualInternalEdges (G omega) U (P omega)) (P omega) (R omega))
    (reference rho epsilon : ℝ)
    (hreference : L.SupportedOn fun omega ↦ ReserveLinkReferenceGood (G omega) (A omega) current U
      (reserveEdges (G omega) U (bits omega)) reference rho epsilon)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/524288)
    (d : ℕ) (degreeError : ℝ≥0) (hloss : (2*d : ℕ) ≤ epsilon*rho^2*reference)
    (hdegreeFailure : L.probability (fun omega ↦ ¬ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G omega) U (reserveEdges (G omega) U (bits omega))) U (P omega) d) ≤ degreeError)
    (sigma : ℝ≥0) (Delta collisionCap forbiddenCap degree overlap s t c overlapMoment : ℕ)
    (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference)
    (hc : (c : ℝ) ≤ rho*reference/40) (hdegree : 2*rho*reference ≤ degree)
    (hcap : collisionCap+forbiddenCap ≤ Delta) (hmoment : 2*s ≤ collisionCap+1)
    (hbudget : (Delta+t : ℝ≥0) ≤ sigma*c/2)
    (hsmall : 2*(Fintype.card V+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2)
    (hoverlapMoment : 2*overlapMoment ≤ overlap+1) :
    let Good := fun omega ↦ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G omega) U (reserveEdges (G omega) U (bits omega))) U (P omega) d ∧
      ∀ u ∈ U, ∀ v ∈ U, u ≠ v → (reserveCommonCenters (current \ U) (reserve omega) u v).card ≤ overlap
    ∃ links : Omega → {x : V // x ∉ U} → BipartiteLink V,
      L.SupportedOn (fun omega ↦
        IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) (R omega) (links omega) ∧
        (∀ o, (links omega o).left ⊆ U) ∧ (∀ o, (links omega o).right ⊆ U) ∧
        (∀ o, (links omega o).SpokesIn (reserve omega))) ∧
      (∀ omega, 0 < L.mass omega → Good omega →
        RawLinkMatchingGeometry U (outsideVertexEmbedding U) (links omega) F (A omega)
          (I omega) (D omega ∪ R omega) sigma Delta collisionCap forbiddenCap
            degree overlap s t (Fintype.card V) c) ∧
      L.probability (fun omega ↦ ¬ Good omega) ≤ degreeError+(Fintype.card V : ℝ≥0)^2*
        ((2*(current.card : ℝ≥0)*C^2*r^2/(overlap+1))^overlapMoment+
          (2*(current.card : ℝ≥0)*C^2/(overlap+1))^overlapMoment*beta) := by
  dsimp only
  let DegreeGood := fun omega ↦ PreliminaryResidualDegreeGood
    (reserveProtectedOuterGraph (G omega) U (reserveEdges (G omega) U (bits omega))) U (P omega) d
  let OverlapGood := fun omega ↦ ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
    (reserveCommonCenters (current \ U) (reserve omega) u v).card ≤ overlap
  let Good := fun omega ↦ DegreeGood omega ∧ OverlapGood omega
  have hloss' : (2 : ℝ)*d ≤ epsilon*rho^2*reference := by exact_mod_cast hloss
  have hextra : ∀ omega, 0 < L.mass omega → Good omega → ∀ center ∈ current, center ∉ U →
      ((protectedResidualSpokeVertices (G omega) U (reserveEdges (G omega) U (bits omega))
        (P omega) center).card : ℝ) ≤ (2 : ℝ)*d := by
    intro omega _hm hg center _hc hcenter
    have hh : (protectedResidualSpokeVertices (G omega) U
        (reserveEdges (G omega) U (bits omega)) (P omega) center).card ≤ 2*d :=
      (hg.1.protected_spokes hcenter).trans (by omega)
    exact_mod_cast hh
  have hcovered : ∀ omega, 0 < L.mass omega → Good omega → ∀ center ∈ current, center ∉ U →
      (((coveredGraph (Q omega)).neighborFinset center ∩ U).card : ℝ) ≤ (2 : ℝ)*d := by
    intro omega hm hg center _hc hcenter
    have hpackR : IsPackingOn (P omega ∪ Q omega) := by
      rw [← hR omega hm]
      exact (hpacking omega hm).mono (subset_union_right.trans subset_union_right)
    have huseR : NewTrianglesUseScheduledOuterEdges U
        (preliminaryResidualInternalEdges (G omega) U (P omega)) (P omega) (P omega ∪ Q omega) := by
      rw [← hR omega hm]
      exact huse omega hm
    have hh := hg.1.disjoint_internal_covered_neighbors
      (reserveEdges_subset_crossingEdges (G omega) U (bits omega)) hpackR (hdis omega hm) huseR hcenter
    exact_mod_cast hh
  obtain ⟨links, hlinks, hmatching⟩ := exists_supported_reserve_matching_links L current U F G A A I D P Q R
    bits reserve Kold hstate hleft hright hspokes hsupp htri hGleave hmeet hpacking havoid hprotected hR
    Good reference rho epsilon ((2 : ℝ)*d) (fun omega hm _ ↦ hreference omega hm)
    href hrho hrho1 hepsilon hepsilonSmall hloss' hextra hcovered
    sigma Delta collisionCap forbiddenCap degree overlap s t c hlarge hc hdegree
    (fun _ _ hg ↦ hg.2) hcap hmoment hbudget hsmall
  refine ⟨links, hlinks, hmatching, ?_⟩
  have hoverlap := L.reserveOverlap_failure_le reserve r C beta hstrong.reserve_prescription_le
    current U overlapMoment overlap hoverlapMoment
  have hb := L.probability_or_le (fun omega ↦ ¬ DegreeGood omega) (fun omega ↦ ¬ OverlapGood omega)
  simpa only [Good, not_and_or] using hb.trans (add_le_add hdegreeFailure hoverlap)

end

end Erdos207
