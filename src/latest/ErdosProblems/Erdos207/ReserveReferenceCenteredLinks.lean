/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveReferenceResidualBounds
import ErdosProblems.Erdos207.CenteredHallReferenceParameters
import ErdosProblems.Erdos207.CenteredResidualLinks

/-! # The actual reserve event supplies source-correct, uniformly robust residual links -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem ReserveLinkReferenceGood.exists_centeredResidualLinks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {current U : Finset V} {bits : Sym2 V → Bool}
    {reserve : Finset (Sym2 V)} {A Apre I D P Q R : TripleSystemOn V}
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U) (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (hsupp : GraphSupportedOn G (current : Set V)) (htri : ConsistsOfTriangles G A)
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
    (c t : ℕ) (hlarge : (18*(65537+4*t) : ℕ) ≤ rho*reference)
    (hc : (c : ℝ) ≤ rho*reference/40)
    (htail : (Fintype.card V : ℝ≥0)*(2*(1/2 : ℝ≥0)^t) < 1) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧
      (∀ o, (Knew o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (Knew o).left ⊆ U) ∧ (∀ o, (Knew o).right ⊆ U) ∧
      (∀ o, (Knew o).SpokesIn reserve) ∧
      ∀ o (h : OrientedSmallHallObstruction ↥(Knew o).left ↥(Knew o).right),
        c*orientedSmallHallSize h ≤ (orientedSmallHallCandidates (linkAvailableRelation (Knew o) A) h).card := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have heps : epsilon ≤ 1/8 := by linarith only [hepsilonSmall]
  have hxi : 0 ≤ 8*epsilon := by positivity
  have hxiSmall : 8*epsilon ≤ 1/65536 := by linarith only [hepsilonSmall]
  have hxi1 : 8*epsilon ≤ 1 := by linarith only [hxiSmall]
  have hlossSize : loss ≤ epsilon*reference := by
    have hrhoSq : rho^2 ≤ 1 := by nlinarith only [hrho, hrho1]
    have hb := mul_le_mul_of_nonneg_left hrhoSq (mul_nonneg hepsilon href)
    nlinarith only [hloss, hb]
  have hinner : ∀ o : {x : V // x ∉ U}, residualNeighbors G R o.1 ⊆ U := by
    intro o x hx
    rw [← (hstate.1 o).2.1] at hx
    rcases mem_union.mp hx with hx | hx
    · exact hleftOld o hx
    · exact hrightOld o hx
  have hcounts : ∀ o : {x : V // x ∉ U},
      (∀ x ∈ residualNeighbors G R o.1,
        (1-8*epsilon)*rho*(residualNeighbors G R o.1).card ≤
            ((ambientLinkNeighborsIn o.1 A (residualNeighbors G R o.1) x).card : ℝ) ∧
        ((ambientLinkNeighborsIn o.1 A (residualNeighbors G R o.1) x).card : ℝ) ≤
            (1+8*epsilon)*rho*(residualNeighbors G R o.1).card) ∧
      ∀ x ∈ residualNeighbors G R o.1, ∀ y ∈ residualNeighbors G R o.1, x ≠ y →
        ((ambientLinkCommonNeighborsIn o.1 A (residualNeighbors G R o.1) x y).card : ℝ) ≤
          (1+8*epsilon)*rho^2*(residualNeighbors G R o.1).card := by
    intro o
    by_cases ho : o.1 ∈ current
    · exact hgood.residualCentered ho o.2 (hinner o) htri hprotected hR href hrho hrho1
        hepsilon heps hloss (hextra o.1 ho o.2) (hcovered o.1 ho o.2)
    · have hempty := residualNeighbors_eq_empty_of_not_supported (R := R) hsupp ho
      simp only [hempty, forall_mem_empty_iff, and_self]
  have hsize : ∀ o : {x : V // x ∉ U},
      (residualNeighbors G R o.1).card = 0 ∨ reference/2 ≤ ((residualNeighbors G R o.1).card : ℝ) := by
    intro o
    by_cases ho : o.1 ∈ current
    · right
      have hb := (hgood.residualSize ho o.2 (hinner o) hprotected hR href hlossSize
        (hextra o.1 ho o.2) (hcovered o.1 ho o.2)).1
      have hepsRef := mul_le_mul_of_nonneg_right heps href
      nlinarith only [hb, hepsRef, href]
    · left
      rw [residualNeighbors_eq_empty_of_not_supported hsupp ho, card_empty]
  have hparameters : ∀ o : {x : V // x ∉ U}, ∃ m d : ℕ, ∃ error : ℝ, 0 ≤ error ∧
      (m : ℝ) ≤ (1-8*epsilon)*rho*(residualNeighbors G R o.1).card ∧
      2*rho*(residualNeighbors G R o.1).card+3*(8*epsilon)*rho^2*((residualNeighbors G R o.1).card : ℝ)^2 ≤ error^2 ∧
      (c : ℝ)+rho*(((residualNeighbors G R o.1).card/2+1)/2 : ℕ)+error ≤ d ∧
      ((residualNeighbors G R o.1).card : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) < 1 := by
    intro o
    exact exists_centeredHall_reference_parameters_or_empty _ (Fintype.card V) c t reference rho (8*epsilon)
      href hrho hrho1 hxi hxiSmall (card_le_univ _) (hsize o) hlarge hc htail
  choose m d error herror hmin hbudget hscalar hsmall using hparameters
  apply exists_reserveSupportedCenteredResidualLinks Kold hstate hleftOld hrightOld hspokesOld
    rho (8*epsilon) error hrho hxi hxi1 herror m d (fun _ ↦ c)
    (fun o ↦ (hcounts o).1) (fun o ↦ (hcounts o).2) hbudget _ hsmall hscalar
  intro o
  dsimp only
  intro v hv
  have hb := (hmin o).trans ((hcounts o).1 v hv).1
  exact_mod_cast hb

end

end Erdos207
