/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveCenteredMatchingInput
import ErdosProblems.Erdos207.IntermediateLinkSourceGeometry

/-! # Total reserve-derived recentering preserves source geometry on every supported input -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem exists_supported_reserve_matching_links
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (current U : Finset V) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A Apre I D P Q R : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (reserve : Omega → Finset (Sym2 V))
    (Kold : Omega → {x : V // x ∉ U} → BipartiteLink V)
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState
      (G omega) U (A omega) (I omega) (D omega) (R omega) (Kold omega))
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
      reserveProtectedAvailable (reserveEdges (G omega) U (bits omega)) (Apre omega))
    (hR : L.SupportedOn fun omega ↦ R omega = P omega ∪ Q omega)
    (Good : Omega → Prop) (reference rho epsilon loss : ℝ)
    (hgood : ∀ omega, 0 < L.mass omega → Good omega →
      ReserveLinkReferenceGood (G omega) (A omega) current U
        (reserveEdges (G omega) U (bits omega)) reference rho epsilon)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/524288)
    (hloss : loss ≤ epsilon*rho^2*reference)
    (hextra : ∀ omega, 0 < L.mass omega → Good omega → ∀ center ∈ current, center ∉ U →
      ((protectedResidualSpokeVertices (G omega) U
        (reserveEdges (G omega) U (bits omega)) (P omega) center).card : ℝ) ≤ loss)
    (hcovered : ∀ omega, 0 < L.mass omega → Good omega → ∀ center ∈ current, center ∉ U →
      (((coveredGraph (Q omega)).neighborFinset center ∩ U).card : ℝ) ≤ loss)
    (sigma : ℝ≥0) (Delta collisionCap forbiddenCap degree overlap s t c : ℕ)
    (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference)
    (hc : (c : ℝ) ≤ rho*reference/40) (hdegree : 2*rho*reference ≤ degree)
    (hoverlap : ∀ omega, 0 < L.mass omega → Good omega → ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      (reserveCommonCenters (current \ U) (reserve omega) u v).card ≤ overlap)
    (hcap : collisionCap+forbiddenCap ≤ Delta) (hmoment : 2*s ≤ collisionCap+1)
    (hbudget : (Delta+t : ℝ≥0) ≤ sigma*c/2)
    (hsmall : 2*(Fintype.card V+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2) :
    ∃ links : Omega → {x : V // x ∉ U} → BipartiteLink V,
      L.SupportedOn (fun omega ↦
        IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) (R omega) (links omega) ∧
        (∀ o, (links omega o).left ⊆ U) ∧ (∀ o, (links omega o).right ⊆ U) ∧
        (∀ o, (links omega o).SpokesIn (reserve omega))) ∧
      ∀ omega, 0 < L.mass omega → Good omega →
        RawLinkMatchingGeometry U (outsideVertexEmbedding U) (links omega) F (A omega)
          (I omega) (D omega ∪ R omega) sigma Delta collisionCap forbiddenCap
            degree overlap s t (Fintype.card V) c := by
  have hchoice : ∀ omega, ∃ links : {x : V // x ∉ U} → BipartiteLink V,
      (0 < L.mass omega →
        IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) (R omega) links ∧
        (∀ o, (links o).left ⊆ U) ∧ (∀ o, (links o).right ⊆ U) ∧
        (∀ o, (links o).SpokesIn (reserve omega))) ∧
      (0 < L.mass omega → Good omega →
        RawLinkMatchingGeometry U (outsideVertexEmbedding U) links F (A omega)
          (I omega) (D omega ∪ R omega) sigma Delta collisionCap forbiddenCap
            degree overlap s t (Fintype.card V) c) := by
    intro omega
    by_cases h : 0 < L.mass omega ∧ Good omega
    · obtain ⟨links, hlinks, hreserve, hgeometry⟩ :=
        (hgood omega h.1 h.2).exists_rawLinkMatchingGeometry (Kold omega)
          (hstate omega h.1) (hleft omega h.1) (hright omega h.1) (hspokes omega h.1)
          (hsupp omega h.1) (htri omega h.1) (hGleave omega h.1) (hmeet omega h.1)
          (hpacking omega h.1) (havoid omega h.1) (hprotected omega h.1) (hR omega h.1)
          reference rho epsilon loss href hrho hrho1 hepsilon hepsilonSmall hloss
          (hextra omega h.1 h.2) (hcovered omega h.1 h.2)
          sigma Delta collisionCap forbiddenCap degree overlap s t c hlarge hc hdegree
          (hoverlap omega h.1 h.2) hcap hmoment hbudget hsmall
      exact ⟨links, (fun _ ↦ ⟨hlinks, hgeometry.left_inner, hgeometry.right_inner, hreserve⟩),
        fun _ _ ↦ hgeometry⟩
    · refine ⟨Kold omega, ?_, ?_⟩
      · intro hm
        exact ⟨hstate omega hm, hleft omega hm, hright omega hm, hspokes omega hm⟩
      · intro hm hg
        exact (h ⟨hm, hg⟩).elim
  choose links hstructure hgeometry using hchoice
  exact ⟨links, hstructure, hgeometry⟩

theorem supported_rawLinkSourceGeometry_of_intermediate
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (k : Fin (ell+1)) (Gamma : SimpleGraph V)
    (U : Finset V) (G : Omega → SimpleGraph V) (I D R A : Omega → TripleSystemOn V)
    (reserve : Omega → Finset (Sym2 V))
    (links : Omega → {x : V // x ∉ U} → BipartiteLink V)
    (hstate : L.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) (R omega) (links omega) ∧
      (∀ o, (links omega o).left ⊆ U) ∧ (∀ o, (links omega o).right ⊆ U) ∧
      (∀ o, (links omega o).SpokesIn (reserve omega)))
    (hG : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hsupp : L.SupportedOn fun omega ↦ GraphSupportedOn (G omega) (W.U k : Set V))
    (htri : L.SupportedOn fun omega ↦ ConsistsOfTriangles (G omega) (A omega))
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (hinitial : L.SupportedOn fun omega ↦ ∀ T ∈ A omega,
      ¬ CompletesForbidden (orders.biUnion F) (I omega ∪ D omega) T) :
    L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (I omega) (D omega ∪ R omega)
      (D omega) (A omega) (reserve omega) (outsideVertexEmbedding U) (links omega) orders F := by
  intro omega hm
  obtain ⟨hs, hl, hr, hsp⟩ := hstate omega hm
  exact rawLinkSourceGeometry_of_intermediate hs hl hr hsp (hG omega hm) (hsupp omega hm)
    (htri omega hm) orders F (hinitial omega hm)

end

end Erdos207
