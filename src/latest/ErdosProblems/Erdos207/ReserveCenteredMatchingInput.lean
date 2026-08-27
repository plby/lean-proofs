/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveReferenceCenteredLinks
import ErdosProblems.Erdos207.ReferenceResidualLinkDegrees
import ErdosProblems.Erdos207.ResidualLinkCandidateSafety
import ErdosProblems.Erdos207.SupportedLinkCoordinateOverlap
import ErdosProblems.Erdos207.RawLinkMatchingGeometry

/-! # Assembling the actual reserve-derived geometric input for simultaneous matching -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem ReserveLinkReferenceGood.exists_rawLinkMatchingGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {current U : Finset V} {bits : Sym2 V → Bool}
    {reserve : Finset (Sym2 V)} {F : ForbiddenFamilyOn V} {A Apre I D P Q R : TripleSystemOn V}
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U) (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (hsupp : GraphSupportedOn G (current : Set V)) (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D)) (hmeet : TrianglesMeetAtMostOne U R)
    (hpacking : IsPackingOn (I ∪ (D ∪ R))) (havoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (hprotected : P ⊆ reserveProtectedAvailable (reserveEdges G U bits) Apre) (hR : R = P ∪ Q)
    (reference rho epsilon loss : ℝ)
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/524288)
    (hloss : loss ≤ epsilon*rho^2*reference)
    (hextra : ∀ center ∈ current, center ∉ U →
      ((protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card : ℝ) ≤ loss)
    (hcovered : ∀ center ∈ current, center ∉ U →
      (((coveredGraph Q).neighborFinset center ∩ U).card : ℝ) ≤ loss)
    (sigma : ℝ≥0) (Delta collisionCap forbiddenCap degree overlap s t c : ℕ)
    (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference) (hc : (c : ℝ) ≤ rho*reference/40)
    (hdegree : 2*rho*reference ≤ degree)
    (hoverlap : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → (reserveCommonCenters (current \ U) reserve u v).card ≤ overlap)
    (hcap : collisionCap+forbiddenCap ≤ Delta) (hmoment : 2*s ≤ collisionCap+1)
    (hbudget : (Delta+t : ℝ≥0) ≤ sigma*c/2)
    (hsmall : 2*(Fintype.card V+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧ (∀ o, (Knew o).SpokesIn reserve) ∧
      RawLinkMatchingGeometry U (outsideVertexEmbedding U) Knew F A I (D ∪ R)
        sigma Delta collisionCap forbiddenCap degree overlap s t (Fintype.card V) c := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have htail : (Fintype.card V : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) < 1 := by
    have hN : (Fintype.card V : ℝ≥0) ≤ (Fintype.card V+1 : ℝ≥0)^2 := by nlinarith
    calc
      _ = 2*(Fintype.card V : ℝ≥0)*(1/2 : ℝ≥0)^t := by ring
      _ ≤ 2*(Fintype.card V+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t := by gcongr
      _ ≤ 1/2 := hsmall
      _ < 1 := by norm_num
  obtain ⟨Knew, hstateNew, hcenter, hout, hleft, hright, hspokes, hcan⟩ :=
    hgood.exists_centeredResidualLinks Kold hstate hleftOld hrightOld hspokesOld hsupp htri hprotected hR
      reference rho epsilon loss href hrho hrho1 hepsilon hepsilonSmall hloss hextra hcovered c t hlarge hc htail
  have hinner : ∀ o : {x : V // x ∉ U}, residualNeighbors G R o.1 ⊆ U := by
    intro o x hx
    rw [← (hstateNew.1 o).2.1] at hx
    exact (mem_union.mp hx).elim (fun hx ↦ hleft o hx) (fun hx ↦ hright o hx)
  have hlossDegree : loss ≤ epsilon*rho*reference := by
    have hrhoSq : rho^2 ≤ rho := by nlinarith only [hrho, hrho1]
    have hb := mul_le_mul_of_nonneg_left hrhoSq (mul_nonneg hepsilon href)
    nlinarith only [hloss, hb]
  have hdegrees : ∀ o : {x : V // x ∉ U},
      (∀ a : ↥(Knew o).left, (univ.filter (linkAvailableRelation (Knew o) A a)).card ≤ degree) ∧
      (∀ b : ↥(Knew o).right, (univ.filter (fun a ↦ linkAvailableRelation (Knew o) A a b)).card ≤ degree) := by
    intro o
    exact hgood.residualChosen_degree_upper hsupp o.2 (hstateNew.1 o) (hinner o) hprotected hR
      href hrho hepsilon (by linarith only [hepsilonSmall]) hlossDegree (fun ho ↦ hextra o.1 ho o.2) degree hdegree
  refine ⟨Knew, hstateNew, hspokes, ?_⟩
  refine ⟨hcenter, hout, hleft, hright, hpacking, havoid, ?_, hcap,
    (fun o ↦ (hstateNew.1 o).2.2), (fun o ↦ ⟨card_le_univ _, card_le_univ _⟩),
    (fun o ↦ (hdegrees o).1), (fun o ↦ (hdegrees o).2), ?_, hmoment, hcan, hbudget, hsmall⟩
  · intro o a b hab
    have hs := (hstateNew.1 o).available_triangle_pair_safe (hleft o) (hright o) hmeet hGleave htri a b hab
    simpa only [union_assoc, simultaneousLinkPairTriple] using hs
  · exact residualLink_otherCoordinates_le_current_reserve_overlap Knew hstateNew.1 hsupp hleft hright hspokes
      (fun o ↦ linkAvailableRelation (Knew o) A) overlap hoverlap

end

end Erdos207
