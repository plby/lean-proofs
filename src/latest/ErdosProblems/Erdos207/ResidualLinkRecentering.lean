/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseReserveResidualLinkBounds

/-! # Recentering sampled-link estimates on the actual residual-neighbor set -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem spokeVerticesIn_sampled_subset_residual_union_internalCovered
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)} {Apre P Q R : TripleSystemOn V} {center : V}
    (hsampled : sampled ⊆ graphEdges G) (hprotected : P ⊆ reserveProtectedAvailable sampled Apre)
    (hR : R = P ∪ Q) :
    spokeVerticesIn U sampled center ⊆ residualNeighbors G R center ∪
      ((coveredGraph Q).neighborFinset center ∩ U) := by
  intro x hx
  have hh := mem_spokeVerticesIn_iff.mp hx
  have hcx : G.Adj center x := mem_graphEdges_iff.mp (hsampled hh.2)
  by_cases hcovered : (coveredGraph Q).Adj center x
  · exact mem_union_right _ (mem_inter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hcovered, hh.1⟩)
  · apply mem_union_left
    apply mem_residualNeighbors_iff.mpr
    refine ⟨hcx, ?_⟩
    intro hcoveredR
    obtain ⟨T, hT, hcT, hxT, hne⟩ := coveredGraph_adj.mp hcoveredR
    rw [hR] at hT
    rcases mem_union.mp hT with hP | hQ
    · exact reserve_not_covered_of_subset_reserveProtected hprotected s(center,x) hh.2
        (mem_graphEdges_iff.mpr (coveredGraph_adj.mpr ⟨T, hP, hcT, hxT, hne⟩))
    · exact hcovered (coveredGraph_adj.mpr ⟨T, hQ, hcT, hxT, hne⟩)

theorem residualNeighbor_card_comparison
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)} {Apre P Q R : TripleSystemOn V} {center : V}
    (hc : center ∉ U) (hinner : residualNeighbors G R center ⊆ U)
    (hsampled : sampled ⊆ graphEdges G) (hprotected : P ⊆ reserveProtectedAvailable sampled Apre)
    (hR : R = P ∪ Q) :
    (residualNeighbors G R center).card ≤ (spokeVerticesIn U sampled center).card+
      (protectedResidualSpokeVertices G U sampled P center).card ∧
    (spokeVerticesIn U sampled center).card ≤ (residualNeighbors G R center).card+
      ((coveredGraph Q).neighborFinset center ∩ U).card := by
  have hPR : P ⊆ R := hR ▸ subset_union_left
  exact ⟨(card_le_card (residualNeighbors_subset_sampled_union_protectedResidual hc hPR hinner)).trans
      (card_union_le _ _),
    (card_le_card (spokeVerticesIn_sampled_subset_residual_union_internalCovered hsampled hprotected hR)).trans
      (card_union_le _ _)⟩

theorem real_relative_count_perturbation
    (expected epsilon sampled actual loss : ℝ) (_hbase : 0 ≤ expected)
    (hlo : (1-epsilon)*expected ≤ sampled) (hhi : sampled ≤ (1+epsilon)*expected)
    (hactual : actual ≤ sampled+loss) (hsampled : sampled ≤ actual+loss) (hloss : loss ≤ epsilon*expected) :
    (1-2*epsilon)*expected ≤ actual ∧ actual ≤ (1+2*epsilon)*expected := by
  constructor <;> nlinarith only [hlo, hhi, hactual, hsampled, hloss]

theorem real_relative_count_upper_recenter
    (reference size rate epsilon value : ℝ) (href : 0 ≤ reference) (hrate : 0 ≤ rate)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1/8)
    (hsize : (1-2*epsilon)*reference ≤ size)
    (hvalue : value ≤ (1+2*epsilon)*rate*reference) :
    value ≤ (1+8*epsilon)*rate*size := by
  have hcoeff : 1+2*epsilon ≤ (1+8*epsilon)*(1-2*epsilon) := by
    nlinarith [mul_nonneg hepsilon (show 0 ≤ 1/8-epsilon by linarith only [hepsilon1])]
  calc
    _ ≤ (1+2*epsilon)*(rate*reference) := by simpa only [mul_assoc] using hvalue
    _ ≤ ((1+8*epsilon)*(1-2*epsilon))*(rate*reference) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hrate href)
    _ = ((1+8*epsilon)*rate)*((1-2*epsilon)*reference) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsize (by positivity)

theorem real_relative_count_lower_recenter
    (reference size rate epsilon value : ℝ) (href : 0 ≤ reference) (hrate : 0 ≤ rate)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1/8)
    (hsize : size ≤ (1+2*epsilon)*reference)
    (hvalue : (1-2*epsilon)*rate*reference ≤ value) :
    (1-8*epsilon)*rate*size ≤ value := by
  have hcoeff : (1-8*epsilon)*(1+2*epsilon) ≤ 1-2*epsilon := by
    nlinarith [sq_nonneg epsilon]
  calc
    _ ≤ ((1-8*epsilon)*rate)*((1+2*epsilon)*reference) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg (by linarith only [hepsilon1]) hrate)
    _ = ((1-8*epsilon)*(1+2*epsilon))*(rate*reference) := by ring
    _ ≤ (1-2*epsilon)*(rate*reference) := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hrate href)
    _ ≤ _ := by simpa only [mul_assoc] using hvalue

theorem residualLink_centered_typicality_of_reserve_counts
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {sampled : Finset (Sym2 V)} {A Apre P Q R : TripleSystemOn V} {center : V}
    (hc : center ∉ U) (hinner : residualNeighbors G R center ⊆ U)
    (htri : ConsistsOfTriangles G A) (hsampled : sampled ⊆ graphEdges G)
    (hprotected : P ⊆ reserveProtectedAvailable sampled Apre) (hR : R = P ∪ Q)
    (reference rho epsilon loss : ℝ) (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1/8)
    (hloss : loss ≤ epsilon*rho^2*reference)
    (hextra : ((protectedResidualSpokeVertices G U sampled P center).card : ℝ) ≤ loss)
    (hcovered : (((coveredGraph Q).neighborFinset center ∩ U).card : ℝ) ≤ loss)
    (hsize : (1-epsilon)*reference ≤ ((spokeVerticesIn U sampled center).card : ℝ) ∧
      ((spokeVerticesIn U sampled center).card : ℝ) ≤ (1+epsilon)*reference)
    (hdegree : ∀ x ∈ residualNeighbors G R center,
      (1-epsilon)*rho*reference ≤ ((ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card : ℝ) ≤ (1+epsilon)*rho*reference)
    (hcodegree : ∀ x ∈ residualNeighbors G R center, ∀ y ∈ residualNeighbors G R center, x ≠ y →
      ((ambientLinkCommonNeighborsIn center A (spokeVerticesIn U sampled center) x y).card : ℝ) ≤
        (1+epsilon)*rho^2*reference) :
    (∀ x ∈ residualNeighbors G R center,
      (1-8*epsilon)*rho*(residualNeighbors G R center).card ≤
          ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤
          (1+8*epsilon)*rho*(residualNeighbors G R center).card) ∧
    ∀ x ∈ residualNeighbors G R center, ∀ y ∈ residualNeighbors G R center, x ≠ y →
      ((ambientLinkCommonNeighborsIn center A (residualNeighbors G R center) x y).card : ℝ) ≤
        (1+8*epsilon)*rho^2*(residualNeighbors G R center).card := by
  have hPR : P ⊆ R := hR ▸ subset_union_left
  have hrhoSq : rho^2 ≤ rho := by nlinarith only [hrho, hrho1]
  have hlossDegree : loss ≤ epsilon*(rho*reference) := by
    apply hloss.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hrhoSq href) hepsilon
  have hlossSize : loss ≤ epsilon*reference := hlossDegree.trans (by
    have h := mul_le_mul_of_nonneg_left hrho1 (mul_nonneg hepsilon href)
    nlinarith only [h])
  have hcompare := residualNeighbor_card_comparison hc hinner hsampled hprotected hR
  have hupperSize : ((residualNeighbors G R center).card : ℝ) ≤
      (spokeVerticesIn U sampled center).card+loss := by
    have hh : ((residualNeighbors G R center).card : ℝ) ≤
        (spokeVerticesIn U sampled center).card+(protectedResidualSpokeVertices G U sampled P center).card := by
      exact_mod_cast hcompare.1
    linarith only [hh, hextra]
  have hlowerSize : ((spokeVerticesIn U sampled center).card : ℝ) ≤
      (residualNeighbors G R center).card+loss := by
    have hh : ((spokeVerticesIn U sampled center).card : ℝ) ≤
        (residualNeighbors G R center).card+((coveredGraph Q).neighborFinset center ∩ U).card := by
      exact_mod_cast hcompare.2
    linarith only [hh, hcovered]
  have hactualSize := real_relative_count_perturbation reference epsilon _ _ loss href
    hsize.1 hsize.2 hupperSize hlowerSize hlossSize
  constructor
  · intro x hx
    have hupper : ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤
        (ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card+loss := by
      have hb := (card_le_card (ambientLinkNeighborsIn_residual_subset_sampled_union_extra
        (sampled := sampled) (A := A) (x := x) hc hPR hinner)).trans (card_union_le _ _)
      have hb' : ((ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card : ℝ) ≤
          (ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card+
            (protectedResidualSpokeVertices G U sampled P center).card := by exact_mod_cast hb
      linarith only [hb', hextra]
    have hlower : ((ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card : ℝ) ≤
        (ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card+loss := by
      have hb := (card_le_card (ambientLinkNeighborsIn_sampled_subset_residual_union_internalCovered
        (U := U) (center := center) (x := x) htri hprotected hR)).trans (card_union_le _ _)
      have hb' : ((ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).card : ℝ) ≤
          (ambientLinkNeighborsIn center A (residualNeighbors G R center) x).card+
            ((coveredGraph Q).neighborFinset center ∩ U).card := by exact_mod_cast hb
      linarith only [hb', hcovered]
    have hactual := real_relative_count_perturbation (rho*reference) epsilon _ _ loss (mul_nonneg hrho href)
      (by simpa only [mul_assoc] using (hdegree x hx).1)
      (by simpa only [mul_assoc] using (hdegree x hx).2) hupper hlower hlossDegree
    exact ⟨real_relative_count_lower_recenter reference _ rho epsilon _ href hrho hepsilon hepsilon1 hactualSize.2
        (by simpa only [mul_assoc] using hactual.1),
      real_relative_count_upper_recenter reference _ rho epsilon _ href hrho hepsilon hepsilon1 hactualSize.1
        (by simpa only [mul_assoc] using hactual.2)⟩
  · intro x hx y hy hxy
    have hb := (card_le_card (ambientLinkCommonNeighborsIn_residual_subset_sampled_union_extra
      (sampled := sampled) (A := A) (x := x) (y := y) hc hPR hinner)).trans (card_union_le _ _)
    have hb' : ((ambientLinkCommonNeighborsIn center A (residualNeighbors G R center) x y).card : ℝ) ≤
        (ambientLinkCommonNeighborsIn center A (spokeVerticesIn U sampled center) x y).card+
          (protectedResidualSpokeVertices G U sampled P center).card := by exact_mod_cast hb
    apply real_relative_count_upper_recenter reference _ (rho^2) epsilon _ href (sq_nonneg rho)
      hepsilon hepsilon1 hactualSize.1
    have hs := hcodegree x hx y hy hxy
    nlinarith only [hb', hextra, hloss, hs]

end

end Erdos207
