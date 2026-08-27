/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveReferenceProbability
import ErdosProblems.Erdos207.ReserveRelativeLinkConcentration

/-! # The actual finite reserve tests: sizes, degrees, and upper-only codegrees -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

abbrev ReserveLinkTest (V : Type*) := V ⊕ (V × V) ⊕ (V × V × V)

def reserveLinkTestEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V) :
    ReserveLinkTest V → Finset (Sym2 V)
  | .inl c => (neighborsIn G U c).image (fun x ↦ s(c,x))
  | .inr (.inl (c,x)) => ambientLinkSpokeEdges c A U x
  | .inr (.inr (c,x,y)) => ambientLinkCommonSpokeEdges c A U x y

def reserveLinkTestRelevant {V : Type*} (G : SimpleGraph V) (current U : Finset V) :
    ReserveLinkTest V → Prop
  | .inl c => c ∈ current ∧ c ∉ U
  | .inr (.inl (c,x)) => c ∈ current ∧ c ∉ U ∧ x ∈ U ∧ G.Adj c x
  | .inr (.inr (c,x,y)) => c ∈ current ∧ c ∉ U ∧ x ∈ U ∧ G.Adj c x ∧
      y ∈ U ∧ G.Adj c y ∧ x ≠ y

def reserveLinkTestLower {V : Type*} : ReserveLinkTest V → Bool
  | .inr (.inr _) => false
  | _ => true

def reserveLinkTestTarget {V : Type*} (reference rho : ℝ) : ReserveLinkTest V → ℝ
  | .inl _ => reference
  | .inr (.inl _) => rho*reference
  | .inr (.inr _) => rho^2*reference

def ReserveLinkReferenceGood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (current U : Finset V)
    (reserve : Finset (Sym2 V)) (reference rho epsilon : ℝ) : Prop :=
  ∀ j : ReserveLinkTest V, reserveLinkTestRelevant G current U j →
    ReferenceCountGood (reserveLinkTestLower j) epsilon
      (((reserveLinkTestEdges G A U j) ∩ reserve).card : ℝ)
      (reserveLinkTestTarget reference rho j)

theorem reserveLinkTestEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {current U : Finset V}
    (htri : ConsistsOfTriangles G A) (j : ReserveLinkTest V)
    (hj : reserveLinkTestRelevant G current U j) :
    reserveLinkTestEdges G A U j ⊆ crossingEdges G U := by
  rcases j with c | (⟨c,x⟩ | ⟨c,x,y⟩)
  · intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have hx' := mem_neighborsIn_iff.mp hx
    exact mem_crossingEdges_iff.mpr
      ⟨hx'.2, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hx'.1, hj.2⟩)⟩
  · exact ambientLinkSpokeEdges_subset_crossingEdges htri hj.2.1
  · exact ambientLinkCommonSpokeEdges_subset_crossingEdges htri hj.2.1

theorem reserveLinkTestTarget_ge_minimum
    {V : Type*} (reference rho : ℝ) (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (j : ReserveLinkTest V) : rho^2*reference ≤ reserveLinkTestTarget reference rho j := by
  have hsquare : rho^2 ≤ rho := by nlinarith only [hrho, hrho1]
  rcases j with c | (cx | cxy)
  · simpa only [reserveLinkTestTarget, one_mul] using
      mul_le_mul_of_nonneg_right (hsquare.trans hrho1) href
  · exact mul_le_mul_of_nonneg_right hsquare href
  · exact le_rfl

theorem reserveEdgeLaw_probability_not_reserveLinkReferenceGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (current U : Finset V)
    (htri : ConsistsOfTriangles G A) (r : ℝ≥0) (hr : r ≤ 1)
    (reference rho epsilon : ℝ) (href : 0 ≤ reference) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hmean : ∀ j : ReserveLinkTest V, reserveLinkTestRelevant G current U j →
      (reserveLinkTestLower j = true →
        (1-epsilon/2)*reserveLinkTestTarget reference rho j ≤
          (r : ℝ)*(reserveLinkTestEdges G A U j).card) ∧
        (r : ℝ)*(reserveLinkTestEdges G A U j).card ≤
          (1+epsilon/2)*reserveLinkTestTarget reference rho j) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      ¬ ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon) : ℝ) ≤
      2*((Fintype.card V : ℝ)+(Fintype.card V : ℝ)^2+(Fintype.card V : ℝ)^3)*
        Real.exp (-epsilon^2*(rho^2*reference)/32) := by
  have hb := reserveEdgeLaw_probability_not_all_referenceCounts_le G U r hr
    (reserveLinkTestEdges G A U) (reserveLinkTestRelevant G current U) reserveLinkTestLower
    (reserveLinkTestTarget reference rho) epsilon (rho^2*reference) hepsilon hepsilon1 (by positivity)
    (reserveLinkTestEdges_subset_crossingEdges htri)
    (fun j _ ↦ reserveLinkTestTarget_ge_minimum reference rho href hrho hrho1 j) hmean
  have hcard : (Fintype.card (ReserveLinkTest V) : ℝ) =
      (Fintype.card V : ℝ)+(Fintype.card V : ℝ)^2+(Fintype.card V : ℝ)^3 := by
    simp only [ReserveLinkTest, Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
    ring
  simpa only [ReserveLinkReferenceGood, hcard] using hb

theorem ReserveLinkReferenceGood.sampledSize
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {current U : Finset V}
    {bits : Sym2 V → Bool} {reference rho epsilon : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U (reserveEdges G U bits) reference rho epsilon)
    {center : V} (hc : center ∈ current) (hcU : center ∉ U) :
    (1-epsilon)*reference ≤ ((spokeVerticesIn U (reserveEdges G U bits) center).card : ℝ) ∧
      ((spokeVerticesIn U (reserveEdges G U bits) center).card : ℝ) ≤ (1+epsilon)*reference := by
  have hb := hgood (.inl center) ⟨hc, hcU⟩
  have hinj : Function.Injective (fun x : V ↦ s(center,x)) := fun _ _ h ↦ Sym2.congr_right.mp h
  have hcard : (((neighborsIn G U center).image (fun x ↦ s(center,x))) ∩ reserveEdges G U bits).card =
      (spokeVerticesIn U (reserveEdges G U bits) center).card := by
    rw [← reserve_neighbor_spoke_image G U center hcU bits, card_image_of_injective _ hinj]
  simpa only [ReferenceCountGood, reserveLinkTestLower, reserveLinkTestTarget, reserveLinkTestEdges,
    hcard, true_implies] using hb

theorem ReserveLinkReferenceGood.sampledDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {current U : Finset V}
    {reserve : Finset (Sym2 V)} {reference rho epsilon : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U reserve reference rho epsilon)
    {center x : V} (hc : center ∈ current) (hcU : center ∉ U) (hx : x ∈ U) (hcx : G.Adj center x) :
    (1-epsilon)*rho*reference ≤ ((ambientLinkNeighborsIn center A (spokeVerticesIn U reserve center) x).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A (spokeVerticesIn U reserve center) x).card : ℝ) ≤
        (1+epsilon)*rho*reference := by
  have hb := hgood (.inr (.inl (center,x))) ⟨hc, hcU, hx, hcx⟩
  simpa only [ReferenceCountGood, reserveLinkTestLower, reserveLinkTestTarget, reserveLinkTestEdges,
    ← sampledAmbientLinkNeighbors_card_eq_inter center A U reserve x hcU, true_implies, mul_assoc] using hb

theorem ReserveLinkReferenceGood.sampledCodegree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {current U : Finset V}
    {reserve : Finset (Sym2 V)} {reference rho epsilon : ℝ}
    (hgood : ReserveLinkReferenceGood G A current U reserve reference rho epsilon)
    {center x y : V} (hc : center ∈ current) (hcU : center ∉ U)
    (hx : x ∈ U) (hcx : G.Adj center x) (hy : y ∈ U) (hcy : G.Adj center y) (hxy : x ≠ y) :
    ((ambientLinkCommonNeighborsIn center A (spokeVerticesIn U reserve center) x y).card : ℝ) ≤
      (1+epsilon)*rho^2*reference := by
  have hb := (hgood (.inr (.inr (center,x,y))) ⟨hc, hcU, hx, hcx, hy, hcy, hxy⟩).2
  simpa only [reserveLinkTestTarget, reserveLinkTestEdges,
    ← sampledAmbientLinkCommonNeighbors_card_eq_inter center A U reserve x y hcU, mul_assoc] using hb

end

end Erdos207
