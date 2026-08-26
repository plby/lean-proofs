import ErdosProblems.Erdos745.SprinklingCoupling
import ErdosProblems.Erdos745.SprinklingCut

/-! # Finite macroscopic-component failure bound from sprinkling -/

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

open BernoulliUnion Erdos746.BernoulliFinset

theorem macro_implies_loss_or_separated {n K : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hK : (K : ℝ) ≤ δ * n) (A B : Finset (Edge n))
    (hmacro : δ * n < secondOrder n (Erdos746.graphOfEdges (A ∪ B))) :
    δ * n / 2 ≤ ((smallComponentVertices (Erdos746.graphOfEdges A) K \
      smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ) ∨
      SeparatedLargeUnions (Erdos746.graphOfEdges A) K (δ * n / 2) B := by
  let G := Erdos746.graphOfEdges A
  let H := Erdos746.graphOfEdges (A ∪ B)
  have hGH : G ≤ H := Erdos746.graphOfEdges_mono Finset.subset_union_left
  by_cases hloss : δ * n / 2 ≤ ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ)
  · exact Or.inl hloss
  right
  have hloss' : ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ) < δ * n / 2 :=
    lt_of_not_ge hloss
  have hpos : 0 < secondLargestComponentOrder H := by
    have hz : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
    have h : (0 : ℝ) < (secondLargestComponentOrder H : ℝ) := hz.trans_lt hmacro
    exact_mod_cast h
  obtain ⟨C, D, hCD, hC, hD⟩ := (le_secondLargestComponentOrder_iff_exists H hpos).mp le_rfl
  have hCr : δ * (n : ℝ) < (C.supp.ncard : ℝ) :=
    hmacro.trans_le (by change (secondLargestComponentOrder H : ℝ) ≤ _; exact_mod_cast hC)
  have hDr : δ * (n : ℝ) < (D.supp.ncard : ℝ) :=
    hmacro.trans_le (by change (secondLargestComponentOrder H : ℝ) ≤ _; exact_mod_cast hD)
  have hCK : K < C.supp.ncard := by exact_mod_cast hK.trans_lt hCr
  have hDK : K < D.supp.ncard := by exact_mod_cast hK.trans_lt hDr
  let J := componentsInside G H K C
  let L := componentsInside G H K D
  have hJ : J ∈ (largeBaseComponents G K).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hL : L ∈ (largeBaseComponents G K).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hdis : Disjoint (componentUnion J) (componentUnion L) :=
    componentUnion_inside_disjoint G H C D hCD
  refine ⟨J, hJ, L, hL, hdis, ?_, ?_, ?_⟩
  · have h := componentUnion_inside_card_lower hGH C hCK
    change _ ≤ ((componentUnion J).card : ℝ) at h
    linarith
  · have h := componentUnion_inside_card_lower hGH D hDK
    change _ ≤ ((componentUnion L).card : ℝ) at h
    linarith
  · apply (noEdgesAcross_iff_cut _ _ _ hdis).mpr
    rw [edgeCoordinates_graphOfEdges]
    apply crossingEdges_avoided_of_components H C D hCD _ _
      (componentUnion_inside_subset G H C) (componentUnion_inside_subset G H D) hdis B
    change B ⊆ edgeCoordinates (Erdos746.graphOfEdges (A ∪ B))
    rw [edgeCoordinates_graphOfEdges]
    exact Finset.subset_union_right

def sprinkleError (lam0 lam δ : ℝ) (K n : ℕ) : ℝ :=
  Real.exp ((Real.log 4 / ((K : ℝ) + 1) - (lam - lam0) * δ ^ 2 / 4) * n)

theorem eventMass_separatedLargeUnions_rate_bound {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ)
    {lam0 lam δ : ℝ} (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (hδ : 0 ≤ δ) :
    eventMass Finset.univ (sprinkleRate lam0 lam n) (SeparatedLargeUnions G K (δ * n / 2)) ≤
      sprinkleError lam0 lam δ K n := by
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt hlam0 (h01.trans hln)
  apply (eventMass_separatedLargeUnions_le_exp G K
    (sprinkleRate_pos h01 hln).le (sprinkleRate_lt_one h01 hln).le (by positivity)).trans
  apply Real.exp_le_exp.mpr
  have hq := sprinkleRate_ge_div hlam0 h01 hln
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg (δ * n / 2))
  have he : ((lam - lam0) / n) * (δ * n / 2) ^ 2 = (lam - lam0) * δ ^ 2 * n / 4 := by
    field_simp
    ring
  rw [he] at hm
  change Real.log 4 * ((n : ℝ) / (K + 1)) - sprinkleRate lam0 lam n * (δ * n / 2) ^ 2 ≤
    (Real.log 4 / ((K : ℝ) + 1) - (lam - lam0) * δ ^ 2 / 4) * n
  linear_combination hm

def sprinklingLossMass (lam0 lam δ : ℝ) (n K : ℕ) : ℝ :=
  sprinklingMass lam0 lam n (fun G H ↦ δ * n / 2 ≤
    ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ))

def sprinklingCutMass (lam0 lam δ : ℝ) (n K : ℕ) : ℝ :=
  jointMass (Finset.univ : Finset (Edge n)) (edgeProbability lam0 n : ℝ) (sprinkleRate lam0 lam n)
    (fun A B ↦ SeparatedLargeUnions (Erdos746.graphOfEdges A) K (δ * n / 2) B)

theorem sprinklingCutMass_le {lam0 lam δ : ℝ} {n K : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (hδ : 0 ≤ δ) :
    sprinklingCutMass lam0 lam δ n K ≤ sprinkleError lam0 lam δ K n := by
  apply jointMass_le_of_rows (edgeProbability lam0 n).property.1 (edgeProbability lam0 n).property.2
  intro A _
  exact eventMass_separatedLargeUnions_rate_bound (Erdos746.graphOfEdges A) K hlam0 h01 hln hδ

theorem macro_jointMass_split {n K : ℕ} {δ p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 ≤ δ)
    (hK : (K : ℝ) ≤ δ * n) :
    jointMass (Finset.univ : Finset (Edge n)) p q
      (fun A B ↦ δ * n < secondOrder n (Erdos746.graphOfEdges (A ∪ B))) ≤
      jointMass Finset.univ p q (fun A B : Finset (Edge n) ↦ δ * n / 2 ≤
        ((smallComponentVertices (Erdos746.graphOfEdges A) K \
          smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ)) +
        jointMass Finset.univ p q (fun A B : Finset (Edge n) ↦
          SeparatedLargeUnions (Erdos746.graphOfEdges A) K (δ * n / 2) B) := by
  apply (jointMass_mono hp0 hp1 hq0 hq1
    (fun A B h ↦ macro_implies_loss_or_separated hδ hK A B h)).trans
  exact jointMass_or_le hp0 hp1 hq0 hq1 _ _

theorem probability_macro_split {lam0 lam δ : ℝ} {n K : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (hδ : 0 < δ)
    (hK : (K : ℝ) ≤ δ * n) :
    probability lam n (fun H ↦ δ * n < secondOrder n H) ≤
      sprinklingLossMass lam0 lam δ n K + sprinklingCutMass lam0 lam δ n K := by
  rw [← sprinklingMass_final hlam0 h01 hln (fun H ↦ δ * n < secondOrder n H)]
  simp only [sprinklingLossMass, sprinklingCutMass, sprinklingMass]
  exact macro_jointMass_split (edgeProbability lam0 n).property.1
    (edgeProbability lam0 n).property.2 (sprinkleRate_pos h01 hln).le
    (sprinkleRate_lt_one h01 hln).le hδ.le hK

/-- The only stochastic errors are small-vertex loss and the conditional cut event. -/
theorem probability_macro_le_sprinkling {lam0 lam δ : ℝ} {n K : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (hδ : 0 < δ)
    (hK : (K : ℝ) ≤ δ * n) :
    probability lam n (fun H ↦ δ * n < secondOrder n H) ≤
      (expectation lam0 n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) -
        expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ))) / (δ * n / 2) +
          sprinkleError lam0 lam δ K n := by
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt hlam0 (h01.trans hln)
  exact (probability_macro_split hlam0 h01 hln hδ hK).trans
    (add_le_add (sprinkling_loss_markov hlam0 h01 hln (by positivity) K)
      (sprinklingCutMass_le hlam0 h01 hln hδ.le))

end

end Erdos745
