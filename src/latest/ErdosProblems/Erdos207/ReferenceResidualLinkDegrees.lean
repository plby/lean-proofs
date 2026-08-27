/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveReferenceResidualBounds
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-! # Degree bounds for the actual chosen links, at the reserve reference scale -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem IsResidualBipartition.degree_bounds_of_full
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {R A : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G R center K) (D : ℕ)
    (hfull : ∀ x ∈ residualNeighbors G R center,
      (ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card ≤ D) :
    (∀ a : ↥K.left, (univ.filter (linkAvailableRelation K A a)).card ≤ D) ∧
    (∀ b : ↥K.right, (univ.filter (fun a ↦ linkAvailableRelation K A a b)).card ≤ D) := by
  have hleft : K.left ⊆ residualNeighbors G R center := by
    rw [← hK.2.1]
    exact subset_union_left
  have hright : K.right ⊆ residualNeighbors G R center := by
    rw [← hK.2.1]
    exact subset_union_right
  constructor
  · intro a
    change (relationNeighborsIn (linkAvailableRelation K A) univ a).card ≤ D
    rw [card_relationNeighborsIn_linkAvailable_eq_ambient, hK.1]
    apply le_trans _ (hfull a.1 (hleft a.2))
    exact card_le_card (filter_subset_filter _ hright)
  · intro b
    have hb : (relationNeighborsIn (transposeRelation (linkAvailableRelation K A)) univ b).card ≤ D := by
      rw [card_relationNeighborsIn_transpose_linkAvailable_eq_ambient, hK.1]
      apply le_trans _ (hfull b.1 (hright b.2))
      exact card_le_card (filter_subset_filter _ hleft)
    have heq : relationNeighborsIn (transposeRelation (linkAvailableRelation K A)) univ b =
        univ.filter (fun a ↦ linkAvailableRelation K A a b) := by
      ext a
      simp only [mem_relationNeighborsIn_iff, mem_filter, mem_univ, true_and, transposeRelation_apply]
    simpa only [heq] using hb

theorem ReserveLinkReferenceGood.residualFull_degree_upper
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current U : Finset V} {bits : Sym2 V → Bool} {A Apre P Q R : TripleSystemOn V}
    {reference rho epsilon loss : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    {center : V} (hc : center ∈ current) (hcU : center ∉ U)
    (hinner : residualNeighbors G R center ⊆ U)
    (_hprotected : P ⊆ reserveProtectedAvailable (reserveEdges G U bits) Apre) (hR : R = P ∪ Q)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (_hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/2)
    (hloss : loss ≤ epsilon*rho*reference)
    (hextra : ((protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card : ℝ) ≤ loss) :
    ∀ x ∈ residualNeighbors G R center,
      ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤ 2*rho*reference := by
  intro x hx
  have hs := (hgood.sampledDegree hc hcU (hinner hx) (mem_residualNeighbors_iff.mp hx).1).2
  have hPR : P ⊆ R := hR ▸ subset_union_left
  have hb := (card_le_card (ambientLinkNeighborsIn_residual_subset_sampled_union_extra
    (sampled := reserveEdges G U bits) (A := A) (x := x) hcU hPR hinner)).trans (card_union_le _ _)
  have hb' : ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤
      (ambientLinkNeighborsIn center A (spokeVerticesIn U (reserveEdges G U bits) center) x).card+
        (protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card := by exact_mod_cast hb
  have hepsR := mul_le_mul_of_nonneg_right hepsilonSmall (mul_nonneg hrho href)
  nlinarith only [hb', hextra, hloss, hs, hepsR]

theorem ReserveLinkReferenceGood.residualChosen_degree_upper
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current U : Finset V} {bits : Sym2 V → Bool} {A Apre P Q R : TripleSystemOn V}
    {reference rho epsilon loss : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    (hsupp : GraphSupportedOn G (current : Set V))
    {center : V} (hcU : center ∉ U) {K : BipartiteLink V} (hK : IsResidualBipartition G R center K)
    (hinner : residualNeighbors G R center ⊆ U)
    (hprotected : P ⊆ reserveProtectedAvailable (reserveEdges G U bits) Apre) (hR : R = P ∪ Q)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/2)
    (hloss : loss ≤ epsilon*rho*reference)
    (hextra : center ∈ current →
      ((protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card : ℝ) ≤ loss)
    (D : ℕ) (hD : 2*rho*reference ≤ D) :
    (∀ a : ↥K.left, (univ.filter (linkAvailableRelation K A a)).card ≤ D) ∧
    (∀ b : ↥K.right, (univ.filter (fun a ↦ linkAvailableRelation K A a b)).card ≤ D) := by
  apply hK.degree_bounds_of_full D
  intro x hx
  have hc : center ∈ current := (hsupp (mem_residualNeighbors_iff.mp hx).1).1
  have hb := (hgood.residualFull_degree_upper hc hcU hinner hprotected hR href hrho hepsilon hepsilonSmall
    hloss (hextra hc) x hx).trans hD
  exact_mod_cast hb

end

end Erdos207
