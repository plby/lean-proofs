/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0
-/
import ErdosProblems.Erdos76.PentagonOneFlipUpper
import ErdosProblems.Erdos76.PentagonTwoBlobMatchingGeneral

/-!
# Five compatible matching-avoiding two-blob packings

This is the assembly layer used in Proposition 7.4(b).  Each pair packing
may avoid a prescribed cross matching.  The exact half-load on internal
blob edges and the two-blob support bound imply the same pentagon capacity
estimate as in the complete-pair construction.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The local data supplied by a matching-avoiding two-blob packing. -/
structure TwoBlobAvoidingPackingData
    (G : SimpleGraph α) (A B : Finset α) (M : Finset (Sym2 α)) where
  weight : Finset α → ℝ
  packing : IsFractionalPacking G weight
  size_eq : fractionalSize G weight =
    ((sideEdgeFinset G A).card : ℝ) / 2 +
      ((sideEdgeFinset G B).card : ℝ) / 2
  load_left : ∀ e ∈ G.edgeFinset, e.toFinset ⊆ A →
    fractionalEdgeLoad G weight e = 1 / 2
  load_right : ∀ e ∈ G.edgeFinset, e.toFinset ⊆ B →
    fractionalEdgeLoad G weight e = 1 / 2
  load_outside : ∀ e : Sym2 α, ¬e.toFinset ⊆ A ∪ B →
    fractionalEdgeLoad G weight e = 0
  load_avoided : ∀ e ∈ M, fractionalEdgeLoad G weight e = 0

/-- Proposition 7.2(b) supplies local data in either size orientation when
the two blob sizes differ by at most one. -/
theorem exists_twoBlobAvoidingPackingData
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B, G.Adj a.1 b.1)
    (hAcard : 3 ≤ A.card) (hBcard : 3 ≤ B.card)
    (hABcard : A.card ≤ B.card + 1)
    (hBAcard : B.card ≤ A.card + 1) :
    Nonempty (TwoBlobAvoidingPackingData G A B M) := by
  classical
  rcases le_total A.card B.card with hAleB | hBleA
  · obtain ⟨w, hw, hsize, hA, hB, hout, havoid⟩ :=
      proposition72b_avoidMatching_with_loads
        hAB hM hcross hAcard hAleB hBAcard
    exact ⟨⟨w, hw.1, hsize, hA, hB, hout, havoid⟩⟩
  · obtain ⟨w, hw, hsize, hB, hA, hout, havoid⟩ :=
      proposition72b_avoidMatching_with_loads
        (G := G) hAB.symm (hM.symm hAB)
        (fun b a ↦ (hcross a b).symm) hBcard hBleA hABcard
    refine ⟨⟨w, hw.1, ?_, hA, hB, ?_, havoid⟩⟩
    · simpa [add_comm] using hsize
    · intro e he
      apply hout e
      intro hsub
      apply he
      simpa [union_comm] using hsub

private lemma fractionalEdgeLoad_eq_zero_of_mem_missingCrossMatching
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B,
      G.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M)
    (w : Finset α → ℝ) {e : Sym2 α} (heM : e ∈ M) :
    fractionalEdgeLoad G w e = 0 := by
  obtain ⟨p, rfl⟩ := hM.exists_orientation heM
  have hab : p.1.1 ≠ p.2.1 := by
    intro hEq
    exact Finset.disjoint_left.mp hAB p.1.2 (hEq ▸ p.2.2)
  apply fractionalEdgeLoad_eq_zero_of_not_edge G w
    (by simpa [Sym2.mk_isDiag_iff] using hab)
  intro heG
  have hAdj : G.Adj p.1.1 p.2.1 := by
    simpa [SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using heG
  exact (hcross p.1 p.2).mp hAdj heM

/-- The corresponding data constructor when the ambient cross graph itself
is complete except for the displayed matching. -/
theorem exists_twoBlobMissingMatchingPackingData
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a : A, ∀ b : B,
      G.Adj a.1 b.1 ↔ s(a.1, b.1) ∉ M)
    (hAcard : 3 ≤ A.card) (hBcard : 3 ≤ B.card)
    (hABcard : A.card ≤ B.card + 1)
    (hBAcard : B.card ≤ A.card + 1) :
    Nonempty (TwoBlobAvoidingPackingData G A B M) := by
  classical
  rcases le_total A.card B.card with hAleB | hBleA
  · obtain ⟨w, hw, hsize, hA, hB, hout⟩ :=
      proposition72b_arbitraryMatching_with_loads
        hAB hM hcross hAcard hAleB hBAcard
    refine ⟨⟨w, hw.1, hsize, hA, hB, hout, ?_⟩⟩
    intro e he
    exact fractionalEdgeLoad_eq_zero_of_mem_missingCrossMatching
      hAB hM hcross w he
  · have hM' := hM.symm hAB
    have hcross' : ∀ b : B, ∀ a : A,
        G.Adj b.1 a.1 ↔ s(b.1, a.1) ∉ M := by
      intro b a
      rw [SimpleGraph.adj_comm]
      simpa [Sym2.eq_swap] using hcross a b
    obtain ⟨w, hw, hsize, hB, hA, hout⟩ :=
      proposition72b_arbitraryMatching_with_loads
        (G := G) hAB.symm hM' hcross' hBcard hBleA hABcard
    refine ⟨⟨w, hw.1, ?_, hA, hB, ?_, ?_⟩⟩
    · simpa [add_comm] using hsize
    · intro e he
      apply hout e
      intro hsub
      apply he
      simpa [union_comm] using hsub
    · intro e he
      exact fractionalEdgeLoad_eq_zero_of_mem_missingCrossMatching
        hAB.symm hM' hcross' w he

/-- The local load of any avoiding pair packing is bounded by the same
simple edge-capacity function as the complete-pair packing. -/
lemma TwoBlobAvoidingPackingData.edgeLoad_le_pairCap
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    {M : Finset (Sym2 α)}
    (D : TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i) (pentagonBlobFinset blob j) M)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) :
    fractionalEdgeLoad G D.weight e ≤ pentagonPairEdgeCap blob i j e := by
  classical
  unfold pentagonPairEdgeCap
  split_ifs with heI heJ heIJ
  · rw [D.load_left e heG heI]
  · rw [D.load_right e heG heJ]
  · exact D.packing.edgeLoad_le_one heG
  · rw [D.load_outside e heIJ]

/-- Pointwise sum of five avoiding pair weights. -/
def pentagonAvoidingPairFamilyWeight
    {G : SimpleGraph α} {blob : α → Fin 5}
    (partner : Fin 5 → Fin 5) (M : Fin 5 → Finset (Sym2 α))
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i) (pentagonBlobFinset blob (partner i)) (M i)) :
    Finset α → ℝ :=
  fun t ↦ ∑ i : Fin 5, (D i).weight t

/-- Five avoiding packings on adjacent blob pairs form a fractional
packing. -/
theorem isFractionalPacking_pentagonAvoidingNextFamily
    {G : SimpleGraph α} {blob : α → Fin 5}
    {M : Fin 5 → Finset (Sym2 α)}
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonNext i)) (M i)) :
    IsFractionalPacking G
      (pentagonAvoidingPairFamilyWeight pentagonNext M D) := by
  classical
  constructor
  · intro t ht
    exact sum_nonneg fun i _ ↦ (D i).packing.nonneg_on ht
  · intro e heG
    change fractionalEdgeLoad G
      (fun t ↦ ∑ i : Fin 5, (D i).weight t) e ≤ 1
    rw [fractionalEdgeLoad_sum]
    calc
      (∑ i : Fin 5, fractionalEdgeLoad G (D i).weight e) ≤
          ∑ i : Fin 5,
            pentagonPairEdgeCap blob i (pentagonNext i) e := by
        apply sum_le_sum
        intro i _
        exact (D i).edgeLoad_le_pairCap heG
      _ ≤ 1 := sum_pentagonPairEdgeCap_next_le_one blob
        (G.not_isDiag_of_mem_edgeFinset heG)

/-- Five avoiding packings on distance-two blob pairs form a fractional
packing. -/
theorem isFractionalPacking_pentagonAvoidingSkipFamily
    {G : SimpleGraph α} {blob : α → Fin 5}
    {M : Fin 5 → Finset (Sym2 α)}
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonSkip i)) (M i)) :
    IsFractionalPacking G
      (pentagonAvoidingPairFamilyWeight pentagonSkip M D) := by
  classical
  constructor
  · intro t ht
    exact sum_nonneg fun i _ ↦ (D i).packing.nonneg_on ht
  · intro e heG
    change fractionalEdgeLoad G
      (fun t ↦ ∑ i : Fin 5, (D i).weight t) e ≤ 1
    rw [fractionalEdgeLoad_sum]
    calc
      (∑ i : Fin 5, fractionalEdgeLoad G (D i).weight e) ≤
          ∑ i : Fin 5,
            pentagonPairEdgeCap blob i (pentagonSkip i) e := by
        apply sum_le_sum
        intro i _
        exact (D i).edgeLoad_le_pairCap heG
      _ ≤ 1 := sum_pentagonPairEdgeCap_skip_le_one blob
        (G.not_isDiag_of_mem_edgeFinset heG)

/-- A pair-family edge load vanishes when every local packing either avoids
the edge explicitly or has two-blob support disjoint from it. -/
lemma fractionalEdgeLoad_pentagonAvoidingPairFamily_eq_zero
    {G : SimpleGraph α} {blob : α → Fin 5}
    {partner : Fin 5 → Fin 5} {M : Fin 5 → Finset (Sym2 α)}
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (partner i)) (M i))
    {e : Sym2 α}
    (he : ∀ i : Fin 5, e ∈ M i ∨
      ¬e.toFinset ⊆ pentagonBlobFinset blob i ∪
        pentagonBlobFinset blob (partner i)) :
    fractionalEdgeLoad G
      (pentagonAvoidingPairFamilyWeight partner M D) e = 0 := by
  change fractionalEdgeLoad G (fun t ↦ ∑ i : Fin 5, (D i).weight t) e = 0
  rw [fractionalEdgeLoad_sum]
  apply sum_eq_zero
  intro i _
  rcases he i with hi | hi
  · exact (D i).load_avoided e hi
  · exact (D i).load_outside e hi

private lemma fractionalEdgeLoad_integralSingleton_eq_zero
    {G : SimpleGraph α} {T : Finset α} {e : Sym2 α}
    (he : e ∉ T.sym2) :
    fractionalEdgeLoad G (integralPackingWeight {T}) e = 0 := by
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  have hne : t ≠ T := by
    intro hEq
    apply he
    simpa [hEq] using (mem_filter.mp ht).2
  simp [integralPackingWeight, hne]

/-- Add one unit triangle to a fractional packing which leaves all three of
its edges unused. -/
theorem isFractionalPacking_add_integralSingleton_of_zero_load
    {G : SimpleGraph α} {w : Finset α → ℝ} {T : Finset α}
    (hw : IsFractionalPacking G w) (hT : G.IsNClique 3 T)
    (hzero : ∀ e ∈ T.sym2, ¬e.IsDiag → fractionalEdgeLoad G w e = 0) :
    IsFractionalPacking G
      (addTriangleWeight w (integralPackingWeight {T})) := by
  have hInt : IsFractionalPacking G (integralPackingWeight {T}) :=
    isFractionalPacking_integralPackingWeight (by simp [EdgeDisjoint])
  constructor
  · intro t ht
    exact add_nonneg (hw.nonneg_on ht) (hInt.nonneg_on ht)
  · intro e heG
    rw [show addTriangleWeight w (integralPackingWeight {T}) =
        (fun t ↦ w t + integralPackingWeight {T} t) by rfl,
      fractionalEdgeLoad_add]
    by_cases heT : e ∈ T.sym2
    · rw [hzero e heT (G.not_isDiag_of_mem_edgeFinset heG), zero_add]
      exact hInt.edgeLoad_le_one heG
    · rw [fractionalEdgeLoad_integralSingleton_eq_zero heT, add_zero]
      exact hw.edgeLoad_le_one heG

/-- Adding the unit triangle increases total triangle weight by exactly one. -/
lemma fractionalSize_add_integralSingleton
    {G : SimpleGraph α} (w : Finset α → ℝ) {T : Finset α}
    (hT : G.IsNClique 3 T) :
    fractionalSize G (addTriangleWeight w (integralPackingWeight {T})) =
      fractionalSize G w + 1 := by
  rw [fractionalSize_addTriangleWeight,
    fractionalSize_integralPackingWeight]
  · simp
  · intro t ht
    have htEq : t = T := by simpa using ht
    subst t
    exact hT

private lemma card_sideEdgeFinset_eq_blobPairFinset
    (G : SimpleGraph α) (A : Finset α) :
    (sideEdgeFinset G A).card = (blobPairFinset G A).card := by
  exact card_filter_edgeFinset_internal_eq_blobPairFinset G A

/-- Exact total size of an adjacent-pair avoiding family. -/
lemma fractionalSize_pentagonAvoidingNextFamily
    {G : SimpleGraph α} {blob : α → Fin 5}
    {M : Fin 5 → Finset (Sym2 α)}
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonNext i)) (M i)) :
    fractionalSize G (pentagonAvoidingPairFamilyWeight pentagonNext M D) =
      ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
  change fractionalSize G (fun t ↦ ∑ i : Fin 5, (D i).weight t) = _
  rw [fractionalSize_sum_fin_five]
  calc
    (∑ i : Fin 5, fractionalSize G (D i).weight) =
        ∑ i : Fin 5,
          (((sideEdgeFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2 +
          ((sideEdgeFinset G
            (pentagonBlobFinset blob (pentagonNext i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _
      exact (D i).size_eq
    _ = ∑ i : Fin 5,
        (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2 +
        ((blobPairFinset G
          (pentagonBlobFinset blob (pentagonNext i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _
      rw [card_sideEdgeFinset_eq_blobPairFinset,
        card_sideEdgeFinset_eq_blobPairFinset]
    _ = ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
      rw [sum_add_distrib]
      rw [sum_comp_pentagonNext (fun i ↦
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2)]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

/-- Exact total size of a distance-two-pair avoiding family. -/
lemma fractionalSize_pentagonAvoidingSkipFamily
    {G : SimpleGraph α} {blob : α → Fin 5}
    {M : Fin 5 → Finset (Sym2 α)}
    (D : ∀ i, TwoBlobAvoidingPackingData G
      (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob (pentagonSkip i)) (M i)) :
    fractionalSize G (pentagonAvoidingPairFamilyWeight pentagonSkip M D) =
      ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
  change fractionalSize G (fun t ↦ ∑ i : Fin 5, (D i).weight t) = _
  rw [fractionalSize_sum_fin_five]
  calc
    (∑ i : Fin 5, fractionalSize G (D i).weight) =
        ∑ i : Fin 5,
          (((sideEdgeFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2 +
          ((sideEdgeFinset G
            (pentagonBlobFinset blob (pentagonSkip i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _
      exact (D i).size_eq
    _ = ∑ i : Fin 5,
        (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2 +
        ((blobPairFinset G
          (pentagonBlobFinset blob (pentagonSkip i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _
      rw [card_sideEdgeFinset_eq_blobPairFinset,
        card_sideEdgeFinset_eq_blobPairFinset]
    _ = ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
      rw [sum_add_distrib]
      rw [sum_comp_pentagonSkip (fun i ↦
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2)]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

end

end Erdos76
