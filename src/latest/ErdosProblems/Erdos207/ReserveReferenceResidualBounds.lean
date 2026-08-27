/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveLinkReferenceTests
import ErdosProblems.Erdos207.ResidualLinkRecentering

/-! # Actual residual sizes and centered links on the simultaneous reserve event -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem residualNeighbors_eq_empty_of_not_supported
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current : Finset V} {R : TripleSystemOn V} {center : V}
    (hsupp : GraphSupportedOn G (current : Set V)) (hc : center ∉ current) :
    residualNeighbors G R center = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hc (hsupp (mem_residualNeighbors_iff.mp hx).1).1

theorem ReserveLinkReferenceGood.residualSize
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current U : Finset V} {bits : Sym2 V → Bool} {A Apre P Q R : TripleSystemOn V}
    {reference rho epsilon loss : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    {center : V} (hc : center ∈ current) (hcU : center ∉ U)
    (hinner : residualNeighbors G R center ⊆ U)
    (hprotected : P ⊆ reserveProtectedAvailable (reserveEdges G U bits) Apre) (hR : R = P ∪ Q)
    (href : 0 ≤ reference) (hloss : loss ≤ epsilon*reference)
    (hextra : ((protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card : ℝ) ≤ loss)
    (hcovered : (((coveredGraph Q).neighborFinset center ∩ U).card : ℝ) ≤ loss) :
    (1-2*epsilon)*reference ≤ ((residualNeighbors G R center).card : ℝ) ∧
      ((residualNeighbors G R center).card : ℝ) ≤ (1+2*epsilon)*reference := by
  have hs := hgood.sampledSize hc hcU
  have hcomp := residualNeighbor_card_comparison hcU hinner
    (reserveEdges_subset_graphEdges G U bits) hprotected hR
  have hupper : ((residualNeighbors G R center).card : ℝ) ≤
      (spokeVerticesIn U (reserveEdges G U bits) center).card+loss := by
    have hb : ((residualNeighbors G R center).card : ℝ) ≤
        (spokeVerticesIn U (reserveEdges G U bits) center).card+
          (protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card := by exact_mod_cast hcomp.1
    linarith only [hb, hextra]
  have hlower : ((spokeVerticesIn U (reserveEdges G U bits) center).card : ℝ) ≤
      (residualNeighbors G R center).card+loss := by
    have hb : ((spokeVerticesIn U (reserveEdges G U bits) center).card : ℝ) ≤
        (residualNeighbors G R center).card+((coveredGraph Q).neighborFinset center ∩ U).card := by
      exact_mod_cast hcomp.2
    linarith only [hb, hcovered]
  exact real_relative_count_perturbation reference epsilon _ _ loss href hs.1 hs.2 hupper hlower hloss

theorem ReserveLinkReferenceGood.residualCentered
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {current U : Finset V} {bits : Sym2 V → Bool} {A Apre P Q R : TripleSystemOn V}
    {reference rho epsilon loss : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    {center : V} (hc : center ∈ current) (hcU : center ∉ U)
    (hinner : residualNeighbors G R center ⊆ U) (htri : ConsistsOfTriangles G A)
    (hprotected : P ⊆ reserveProtectedAvailable (reserveEdges G U bits) Apre) (hR : R = P ∪ Q)
    (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1/8) (hloss : loss ≤ epsilon*rho^2*reference)
    (hextra : ((protectedResidualSpokeVertices G U (reserveEdges G U bits) P center).card : ℝ) ≤ loss)
    (hcovered : (((coveredGraph Q).neighborFinset center ∩ U).card : ℝ) ≤ loss) :
    (∀ x ∈ residualNeighbors G R center,
      (1-8*epsilon)*rho*(residualNeighbors G R center).card ≤
          ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤
          (1+8*epsilon)*rho*(residualNeighbors G R center).card) ∧
    ∀ x ∈ residualNeighbors G R center, ∀ y ∈ residualNeighbors G R center, x ≠ y →
      ((ambientLinkCommonNeighborsIn center A (residualNeighbors G R center) x y).card : ℝ) ≤
        (1+8*epsilon)*rho^2*(residualNeighbors G R center).card := by
  apply residualLink_centered_typicality_of_reserve_counts hcU hinner htri
    (reserveEdges_subset_graphEdges G U bits) hprotected hR reference rho epsilon loss
    href hrho hrho1 hepsilon hepsilon1 hloss hextra hcovered (hgood.sampledSize hc hcU)
  · intro x hx
    exact hgood.sampledDegree hc hcU (hinner hx) (mem_residualNeighbors_iff.mp hx).1
  · intro x hx y hy hxy
    exact hgood.sampledCodegree hc hcU (hinner hx) (mem_residualNeighbors_iff.mp hx).1
      (hinner hy) (mem_residualNeighbors_iff.mp hy).1 hxy

end

end Erdos207
