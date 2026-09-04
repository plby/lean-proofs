/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostBipartiteCapacityAssembly

/-!
# Completed residual capacity witness for Proposition 4.2

This module is downstream from the edgewise capacity construction so that
Lean elaborates the two large induced-side witnesses through the compiled
interface rather than unfolding their compactness proofs.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The elementary quadratic identity behind the imbalance parameter in
Proposition 4.2. -/
lemma cast_choose_two_add_choose_two_eq_of_add
    (n a b : ℕ) (hab : a + b = n) :
    (((a.choose 2 + b.choose 2 : ℕ) : ℝ)) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 +
        ((n : ℝ) / 2 - (a : ℝ)) ^ 2 := by
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
  nlinarith

/-- Choose the smaller part as `n/2-x`.  The complementary internal-edge
count then has exactly the quadratic form required by the master inequality. -/
lemma exists_partitionImbalance_internalComplement_card
    {n : ℕ} (G : SimpleGraph (Fin n)) (s : Set (Fin n)) :
    ∃ x : ℝ,
      (n : ℝ) / 2 - x =
          min (s.ncard : ℝ) (sᶜ.ncard : ℝ) ∧
      (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ) ∧
      (n : ℝ) / 2 - x ≤ (sᶜ.toFinset.card : ℝ) ∧
      ((internalEdgeFinset Gᶜ s).card : ℝ) =
        (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
          ((internalEdgeFinset G s).card : ℝ) := by
  classical
  let a := s.ncard
  let b := sᶜ.ncard
  have hab : a + b = n := by
    dsimp only [a, b]
    rw [Set.ncard_add_ncard_compl]
    simp
  have hk : (internalEdgeFinset G s).card ≤ a.choose 2 + b.choose 2 := by
    have hk' : (internalEdgeFinset G s).card ≤
        s.ncard.choose 2 + sᶜ.ncard.choose 2 := by
      rw [← card_internalEdgeFinset_top s,
        ← internalEdgeFinset_union_compl G s]
      exact Finset.card_le_card Finset.subset_union_left
    simpa only [a, b] using hk'
  have hcompR : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (((a.choose 2 + b.choose 2 : ℕ) : ℝ)) -
        ((internalEdgeFinset G s).card : ℝ) := by
    rw [card_internalEdgeFinset_compl]
    rw [Nat.cast_sub hk]
  by_cases habOrder : a ≤ b
  · let x : ℝ := (n : ℝ) / 2 - (a : ℝ)
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · have habOrderR : (a : ℝ) ≤ b := by exact_mod_cast habOrder
      rw [show (s.ncard : ℝ) = a by rfl,
        show (sᶜ.ncard : ℝ) = b by rfl, min_eq_left habOrderR]
      dsimp only [x]
      ring
    · have ha : (a : ℝ) = (s.toFinset.card : ℝ) := by
        simp only [a, Set.ncard_eq_toFinset_card']
      dsimp only [x]
      linarith
    · have habOrderR : (a : ℝ) ≤ b := by exact_mod_cast habOrder
      have hb : (b : ℝ) = (sᶜ.toFinset.card : ℝ) := by
        simp only [b, Set.ncard_eq_toFinset_card']
      dsimp only [x]
      linarith
    · rw [hcompR, cast_choose_two_add_choose_two_eq_of_add n a b hab]
  · have hba : b ≤ a := by omega
    let x : ℝ := (n : ℝ) / 2 - (b : ℝ)
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
      rw [show (s.ncard : ℝ) = a by rfl,
        show (sᶜ.ncard : ℝ) = b by rfl, min_eq_right hbaR]
      dsimp only [x]
      ring
    · have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
      have ha : (a : ℝ) = (s.toFinset.card : ℝ) := by
        simp only [a, Set.ncard_eq_toFinset_card']
      dsimp only [x]
      linarith
    · have hb : (b : ℝ) = (sᶜ.toFinset.card : ℝ) := by
        simp only [b, Set.ncard_eq_toFinset_card']
      dsimp only [x]
      linarith
    · have hquad := cast_choose_two_add_choose_two_eq_of_add n b a (by omega)
      rw [hcompR, show a.choose 2 + b.choose 2 = b.choose 2 + a.choose 2 by omega,
        hquad]

/-- An induced graph is missing exactly the ambient complementary-colour
edges contained in that side.  The ambient formulation is independent of
the decidability instance used to enumerate the induced edge subtype. -/
lemma missingEdgeCount_induce_eq_card_sideEdgeFinset_compl
    (G : SimpleGraph α) (S : Finset α) :
    missingEdgeCount (G.induce (S : Set α)) =
      (sideEdgeFinset Gᶜ S).card := by
  have hgraph : (G.induce (S : Set α))ᶜ =
      Gᶜ.induce (S : Set α) := by
    rw [← compl_induce]
  have hncard : Nat.card (G.induce (S : Set α))ᶜ.edgeSet =
      Nat.card (Gᶜ.induce (S : Set α)).edgeSet :=
    congrArg (fun H : SimpleGraph S ↦ Nat.card H.edgeSet) hgraph
  have hsideNat : Nat.card (Gᶜ.induce (S : Set α)).edgeSet =
      (sideEdgeFinset Gᶜ S).card := by
    let : DecidableRel Gᶜ.Adj := Classical.decRel _
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact (card_sideEdgeFinset Gᶜ S).symm
  unfold missingEdgeCount
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, hncard]
  exact hsideNat

/-- Complete the two induced sides of an internal-cross packing with the
residual capacities left on their internal edges. -/
theorem exists_completedSideResidualPacking
    (hAC : AlmostCompleteFractionalDecomposition)
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    (hdeficitS :
      ((sideEdgeFinset Gᶜ s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset G s.toFinset, fractionalEdgeLoad G w e ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hdeficitT :
      ((sideEdgeFinset Gᶜ sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset G sᶜ.toFinset, fractionalEdgeLoad G w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    ∃ red : Finset α → ℝ,
      IsFractionalPacking G red ∧
      fractionalCoveredSize G red =
        ((internalEdgeFinset G s).card : ℝ) + 2 * fractionalSize G w := by
  classical
  have hwPack : IsFractionalPacking G w := hw.1
  have hdeficitS' :
      (missingEdgeCount (G.induce (s.toFinset : Set α)) : ℝ) +
          ∑ p ∈ (G.induce (s.toFinset : Set α)).edgeFinset,
            fractionalEdgeLoad G w
              ((inducedEmbedding s.toFinset).sym2Map p) ≤
        ((s.toFinset.card - 4 : ℕ) : ℝ) := by
    rw [missingEdgeCount_induce_eq_card_sideEdgeFinset_compl,
      sum_inducedEdge_mapped_load]
    simpa only [Set.ncard_eq_toFinset_card'] using hdeficitS
  have hdeficitT' :
      (missingEdgeCount (G.induce (sᶜ.toFinset : Set α)) : ℝ) +
          ∑ p ∈ (G.induce (sᶜ.toFinset : Set α)).edgeFinset,
            fractionalEdgeLoad G w
              ((inducedEmbedding sᶜ.toFinset).sym2Map p) ≤
        ((sᶜ.toFinset.card - 4 : ℕ) : ℝ) := by
    rw [missingEdgeCount_induce_eq_card_sideEdgeFinset_compl,
      sum_inducedEdge_mapped_load]
    simpa only [Set.ncard_eq_toFinset_card'] using hdeficitT
  let dS := sideResidualPackingData (α := α) hAC (G := G)
    (S := s.toFinset) (w := w) hwPack hsevenS hdeficitS'
  let dT := sideResidualPackingData (α := α) hAC (G := G)
    (S := sᶜ.toFinset) (w := w) hwPack hsevenT hdeficitT'
  let red : Finset α → ℝ :=
    addTriangleWeight w
      (addTriangleWeight (extendInducedWeight s.toFinset dS.weight)
        (extendInducedWeight sᶜ.toFinset dT.weight))
  refine ⟨red, ?_, ?_⟩
  · simpa only [red] using
      isFractionalPacking_add_cross_and_sideResiduals hw dS.isPacking dT.isPacking
        dS.edgeLoad_eq dT.edgeLoad_eq
  · have hthree := three_mul_fractionalSize_add_cross_and_sideResiduals
      hw dS.three_mul_size dT.three_mul_size
    have hthree' : 3 * fractionalSize G red =
        ((internalEdgeFinset G s).card : ℝ) + 2 * fractionalSize G w := by
      simpa only [red] using hthree
    simpa only [fractionalCoveredSize] using hthree'

/-- If the residual-capacity deficit fits on both sides, Corollary 2.12
completes the red cross packing, and an integral blue cross packing supplies
the other colour.  This is the exact non-truncated capacity callback used in
Proposition 4.2. -/
theorem hasFractionalCoveredSizeAtLeast_of_sideResiduals
    (hAC : AlmostCompleteFractionalDecomposition)
    {G R : SimpleGraph α} {s : Set α}
    {P : Finset (Finset α)} (hP : IsInternalCrossPacking G s P)
    {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking R s w)
    (hpacking : ∀ v : Finset α → ℝ,
      IsFractionalPacking R v → IsFractionalPacking Gᶜ v)
    (hcovered : ∀ v : Finset α → ℝ,
      fractionalCoveredSize Gᶜ v = fractionalCoveredSize R v)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    (hdeficitS :
      ((sideEdgeFinset Rᶜ s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset R s.toFinset, fractionalEdgeLoad R w e ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hdeficitT :
      ((sideEdgeFinset Rᶜ sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset R sᶜ.toFinset, fractionalEdgeLoad R w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    HasFractionalCoveredSizeAtLeast G
      (3 * (P.card : ℝ) + ((internalEdgeFinset R s).card : ℝ) +
        2 * fractionalSize R w) := by
  classical
  obtain ⟨red, hredR, hredSizeR⟩ :=
    exists_completedSideResidualPacking hAC hw hsevenS hsevenT hdeficitS hdeficitT
  have hred : IsFractionalPacking Gᶜ red := hpacking red hredR
  have hredSize : fractionalCoveredSize Gᶜ red =
      ((internalEdgeFinset R s).card : ℝ) + 2 * fractionalSize R w := by
    rw [hcovered]
    exact hredSizeR
  let blue : Finset α → ℝ := integralPackingWeight P
  have hblue : IsFractionalPacking G blue := by
    simpa only [blue] using isFractionalPacking_integralPackingWeight hP.2
  refine ⟨blue, red, hblue, hred, ?_⟩
  have hblueSize : fractionalCoveredSize G blue = 3 * (P.card : ℝ) := by
    have htri : ∀ t ∈ P, G.IsNClique 3 t := fun t ht ↦
      (mem_internalCrossTriangles.mp (hP.1 ht)).1
    simp only [blue, fractionalCoveredSize,
      fractionalSize_integralPackingWeight htri]
  rw [twoColorCoveredSize, hblueSize, hredSize]
  apply le_of_eq
  ring

/-- Full, non-truncated completion callback: when both exact residual deficits
fit, choose the canonical imbalance parameter and put the covered-size lower
bound into the master-inequality normal form. -/
theorem exists_masterCoveredSize_of_sideResiduals
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    (hdeficitS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset, fractionalEdgeLoad Gᶜ w e ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hdeficitT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset, fractionalEdgeLoad Gᶜ w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    ∃ x : ℝ,
      (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ) ∧
      (n : ℝ) / 2 - x ≤ (sᶜ.toFinset.card : ℝ) ∧
      HasFractionalCoveredSizeAtLeast G
        ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
          ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
            2 * fractionalSize Gᶜ w) := by
  classical
  obtain ⟨x, _hmin, hsideS, hsideT, hcard⟩ :=
    exists_partitionImbalance_internalComplement_card G s
  have hcovered := hasFractionalCoveredSizeAtLeast_of_sideResiduals
    hAC (R := Gᶜ) hP hw (fun _v hv ↦ hv) (fun _v ↦ rfl)
      hsevenS hsevenT (by simpa only [compl_compl] using hdeficitS)
        (by simpa only [compl_compl] using hdeficitT)
  refine ⟨x, hsideS, hsideT, ?_⟩
  convert hcovered using 1 <;> rw [hcard] <;> ring

/-- Every subfamily of internal edges carries at most the total cross-packing
weight.  This form avoids choosing either orientation of the bipartition. -/
lemma sum_fractionalEdgeLoad_le_fractionalSize_of_subset_internal
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w)
    {E : Finset (Sym2 α)} (hE : E ⊆ internalEdgeFinset G s) :
    (∑ e ∈ E, fractionalEdgeLoad G w e) ≤ fractionalSize G w := by
  calc
    (∑ e ∈ E, fractionalEdgeLoad G w e) ≤
        ∑ e ∈ internalEdgeFinset G s, fractionalEdgeLoad G w e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hE
      intro e _he _hnot
      unfold fractionalEdgeLoad
      exact Finset.sum_nonneg fun t ht ↦ hw.1.nonneg_on (Finset.mem_filter.mp ht).1
    _ = fractionalSize G w :=
      sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hw

/-- A single global `k+r` budget implies both exact side-residual capacity
bounds.  This is the corrected capacity estimate replacing the source's
unsupported `m+r` estimate. -/
lemma sideResidualDeficits_of_totalSize
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hbudgetS :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hbudgetT :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    (((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((s.ncard - 4 : ℕ) : ℝ)) ∧
      (((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) := by
  classical
  have hcardS : (sideEdgeFinset G s.toFinset).card ≤
      (internalEdgeFinset G s).card := by
    rw [internalEdgeFinset_eq_union_sides]
    exact Finset.card_le_card Finset.subset_union_left
  have hcardT : (sideEdgeFinset G sᶜ.toFinset).card ≤
      (internalEdgeFinset G s).card := by
    rw [internalEdgeFinset_eq_union_sides]
    exact Finset.card_le_card Finset.subset_union_right
  have hsubS : sideEdgeFinset Gᶜ s.toFinset ⊆
      internalEdgeFinset Gᶜ s := by
    rw [internalEdgeFinset_eq_union_sides]
    exact Finset.subset_union_left
  have hsubT : sideEdgeFinset Gᶜ sᶜ.toFinset ⊆
      internalEdgeFinset Gᶜ s := by
    rw [internalEdgeFinset_eq_union_sides]
    exact Finset.subset_union_right
  have hloadS := sum_fractionalEdgeLoad_le_fractionalSize_of_subset_internal hw hsubS
  have hloadT := sum_fractionalEdgeLoad_le_fractionalSize_of_subset_internal hw hsubT
  have hcardSR : ((sideEdgeFinset G s.toFinset).card : ℝ) ≤
      ((internalEdgeFinset G s).card : ℝ) := by exact_mod_cast hcardS
  have hcardTR : ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) ≤
      ((internalEdgeFinset G s).card : ℝ) := by exact_mod_cast hcardT
  constructor
  · exact (add_le_add hcardSR hloadS).trans hbudgetS
  · exact (add_le_add hcardTR hloadT).trans hbudgetT

/-- Sidewise capacity budgets retain the exact distribution of the blue
internal edges.  This refinement is needed only in the exceptional
`n = 24` boundary, where replacing each side count by the total internal
edge count loses one unit of capacity. -/
lemma sideResidualDeficits_of_sidewiseSize
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hbudgetS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hbudgetT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    (((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((s.ncard - 4 : ℕ) : ℝ)) ∧
      (((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) := by
  have hloadS := sum_sideEdge_fractionalEdgeLoad_le_fractionalSize hw
  have hloadT :
      (∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
          fractionalEdgeLoad Gᶜ w e) ≤ fractionalSize Gᶜ w := by
    have htotal := sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hw
    rw [internalEdgeFinset_eq_union_sides,
      sum_union (sideEdgeFinset_disjoint_compl Gᶜ s)] at htotal
    have hother : 0 ≤
        ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
          fractionalEdgeLoad Gᶜ w e := by
      apply sum_nonneg
      intro e _he
      unfold fractionalEdgeLoad
      apply sum_nonneg
      intro t ht
      exact hw.1.nonneg_on (mem_filter.mp ht).1
    linarith
  constructor
  · calc
      ((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
          ((sideEdgeFinset G s.toFinset).card : ℝ) + fractionalSize Gᶜ w :=
        add_le_add_right hloadS _
      _ ≤ ((s.ncard - 4 : ℕ) : ℝ) := hbudgetS
  · calc
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
          ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) + fractionalSize Gᶜ w :=
        add_le_add_right hloadT _
      _ ≤ ((sᶜ.ncard - 4 : ℕ) : ℝ) := hbudgetT

/-- Fixed-imbalance completion from the two exact residual-capacity budgets. -/
theorem masterCoveredSize_of_residualBudgetsAtImbalance
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    {x : ℝ}
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hdeficitS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hdeficitT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
            fractionalEdgeLoad Gᶜ w e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
          2 * fractionalSize Gᶜ w) := by
  have hcovered := hasFractionalCoveredSizeAtLeast_of_sideResiduals
    hAC (R := Gᶜ) hP hw (fun _v hv ↦ hv) (fun _v ↦ rfl)
      hsevenS hsevenT (by simpa only [compl_compl] using hdeficitS)
        (by simpa only [compl_compl] using hdeficitT)
  convert hcovered using 1 <;> rw [hcard] <;> ring

/-- Fixed-imbalance completion from exact sidewise blue-edge budgets. -/
theorem masterCoveredSize_of_sidewiseBudget_atImbalance
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    {x : ℝ}
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hbudgetS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hbudgetT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
          2 * fractionalSize Gᶜ w) := by
  obtain ⟨hdeficitS, hdeficitT⟩ :=
    sideResidualDeficits_of_sidewiseSize hw hbudgetS hbudgetT
  exact masterCoveredSize_of_residualBudgetsAtImbalance
    hAC hP hw hsevenS hsevenT hcard hdeficitS hdeficitT

/-- The fixed-imbalance form of the corrected capacity completion. -/
theorem masterCoveredSize_of_totalBudget_atImbalance
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    {x : ℝ}
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hbudgetS :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hbudgetT :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
          2 * fractionalSize Gᶜ w) := by
  obtain ⟨hdeficitS, hdeficitT⟩ :=
    sideResidualDeficits_of_totalSize hw hbudgetS hbudgetT
  have hcovered := hasFractionalCoveredSizeAtLeast_of_sideResiduals
    hAC (R := Gᶜ) hP hw (fun _v hv ↦ hv) (fun _v ↦ rfl)
      hsevenS hsevenT (by simpa only [compl_compl] using hdeficitS)
        (by simpa only [compl_compl] using hdeficitT)
  convert hcovered using 1 <;> rw [hcard] <;> ring

/-- Full completion from the corrected global `k+r` capacity budget. -/
theorem exists_masterCoveredSize_of_totalBudget
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    (hbudgetS :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hbudgetT :
      ((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) :
    ∃ x : ℝ,
      (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ) ∧
      (n : ℝ) / 2 - x ≤ (sᶜ.toFinset.card : ℝ) ∧
      HasFractionalCoveredSizeAtLeast G
        ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
          ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
            2 * fractionalSize Gᶜ w) := by
  obtain ⟨hdeficitS, hdeficitT⟩ :=
    sideResidualDeficits_of_totalSize hw hbudgetS hbudgetT
  exact exists_masterCoveredSize_of_sideResiduals hAC hP hw hsevenS hsevenT
    hdeficitS hdeficitT

/-- Exact truncation can preserve a prescribed family of zero edge loads.
This is used by the oriented `n = 24` witness, whose load on the smaller
opposite side must remain zero after its total weight is reduced to `9/2`. -/
lemma exists_fractionalInternalCrossPacking_of_size_between_preserving_zero
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ fractionalSize G w)
    {E : Finset (Sym2 α)}
    (hzero : ∀ e ∈ E, fractionalEdgeLoad G w e = 0) :
    ∃ u : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s u ∧
      fractionalSize G u = q ∧
      ∀ e ∈ E, fractionalEdgeLoad G u e = 0 := by
  by_cases hsize0 : fractionalSize G w = 0
  · have hqzero : q = 0 := by
      have hw0 : 0 ≤ fractionalSize G w := fractionalSize_nonneg hw.1
      linarith
    refine ⟨w, hw, hsize0.trans hqzero.symm, hzero⟩
  · have hwpos : 0 < fractionalSize G w := by
      exact lt_of_le_of_ne (fractionalSize_nonneg hw.1) (Ne.symm hsize0)
    let c := q / fractionalSize G w
    have hc0 : 0 ≤ c := div_nonneg hq0 hwpos.le
    have hc1 : c ≤ 1 := (div_le_one hwpos).mpr hq
    refine ⟨scaleTriangleWeight c w,
      isFractionalInternalCrossPacking_scaleTriangleWeight hw hc0 hc1, ?_, ?_⟩
    · rw [fractionalSize_scaleTriangleWeight]
      dsimp only [c]
      exact div_mul_cancel₀ q hsize0
    · intro e he
      change fractionalEdgeLoad G (fun t ↦ c * w t) e = 0
      rw [fractionalEdgeLoad_smul, hzero e he, mul_zero]

/-- A retained cross packing below the safe truncation level satisfies the
two total `k+r` budgets. -/
lemma totalBudgets_of_size_le_safeTruncation
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {w : Finset (Fin n) → ℝ} {x : ℝ}
    (hmin : (n : ℝ) / 2 - x =
      min (s.ncard : ℝ) (sᶜ.ncard : ℝ))
    (hpartS : (internalEdgeFinset G s).card + 4 ≤ s.ncard)
    (hpartT : (internalEdgeFinset G s).card + 4 ≤ sᶜ.ncard)
    (hsize : fractionalSize Gᶜ w ≤
      (n : ℝ) / 2 - x - 4 - ((internalEdgeFinset G s).card : ℝ)) :
    (((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((s.ncard - 4 : ℕ) : ℝ)) ∧
      (((internalEdgeFinset G s).card : ℝ) + fractionalSize Gᶜ w ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) := by
  have hsideS := hmin.le.trans (min_le_left _ _)
  have hsideT := hmin.le.trans (min_le_right _ _)
  constructor
  · rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  · rw [Nat.cast_sub (by omega)]
    norm_num
    linarith

/-- Convert a stable `Set.ncard` budget to the induced-side finset form used
by the capacity constructor. -/
lemma totalBudget_ncard_to_toFinset
    {s : Set α} {q : ℝ}
    (h : q ≤ ((s.ncard - 4 : ℕ) : ℝ)) :
    q ≤ ((s.toFinset.card - 4 : ℕ) : ℝ) := by
  simpa only [Set.ncard_eq_toFinset_card'] using h

/-- A cross packing with at least as many triangles as internal edges already
covers every internal edge. -/
lemma isInternalEdgeCoveringCrossPacking_of_internal_card_le
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hcard : (internalEdgeFinset G s).card ≤ P.card) :
    IsInternalEdgeCoveringCrossPacking G s P := by
  have heq : coveredInternalEdges G s P = internalEdgeFinset G s := by
    have hcardle : (internalEdgeFinset G s).card ≤
        (coveredInternalEdges G s P).card := by
      rw [card_coveredInternalEdges_eq_card hP]
      exact hcard
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcardle
  apply isInternalEdgeCoveringCrossPacking_of_covers hP
  intro e he
  have heCovered : e ∈ coveredInternalEdges G s P := by
    rw [heq]
    exact he
  exact (Finset.mem_filter.mp heCovered).2

end

end Erdos76
