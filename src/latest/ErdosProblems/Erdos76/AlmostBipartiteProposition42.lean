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
import ErdosProblems.Erdos76.AlmostBipartiteCapacityCompletion

/-!
# The corrected non-boundary part of Proposition 4.2

The source proof truncates against `m+r`; the monochromatic capacity deficit
is actually `k+r`.  The safe truncation therefore leaves one numerical
boundary `(n,k,m,x)=(24,3,0,1)`.  This module proves Proposition 4.2 away from
that boundary, using only the corrected `k+r` completion.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Any sidewise-feasible red cross packing of weight strictly larger than
four contradicts the sharp upper bound in the exceptional numerical case.
This isolates the common capacity-completion tail of the boundary argument. -/
private lemma proposition42_boundary_contradiction_of_sidewisePacking
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {P : Finset (Finset (Fin n))} (hP : IsInternalCrossPacking G s P)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    {v : Finset (Fin n) → ℝ}
    (hv : IsFractionalInternalCrossPacking Gᶜ s v)
    (hsevenS : 7 ≤ s.ncard) (hsevenT : 7 ≤ sᶜ.ncard)
    {x : ℝ}
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hn24 : n = 24) (hk3 : (internalEdgeFinset G s).card = 3)
    (hm0 : P.card = 0) (hx : x = 1)
    (hsize : 4 < fractionalSize Gᶜ v)
    (hdeficitS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
            fractionalEdgeLoad Gᶜ v e ≤
        ((s.ncard - 4 : ℕ) : ℝ))
    (hdeficitT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
          ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
            fractionalEdgeLoad Gᶜ v e ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ)) : False := by
  have hsevenSFin : 7 ≤ s.toFinset.card := by
    simpa only [← Set.ncard_eq_toFinset_card'] using hsevenS
  have hsevenTFin : 7 ≤ sᶜ.toFinset.card := by
    simpa only [← Set.ncard_eq_toFinset_card'] using hsevenT
  have hcovered := masterCoveredSize_of_residualBudgetsAtImbalance
    hAC hP hv hsevenSFin hsevenTFin hcard hdeficitS hdeficitT
  have hmaster := proposition42_master_inequality_of_coveredSize
    x (fractionalSize Gᶜ v) hcovered hupper
  norm_num [hn24, hk3, hm0, hx] at hmaster
  linarith

/-- Boundary contradiction when both sides contain an uncovered blue
internal edge.  Claim 4.3 supplies weight at least `11/2`; retaining weight
five leaves enough capacity on both sides because the three blue internal
edges split nontrivially. -/
private lemma proposition42_boundary_bothSides_contradiction
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    {P : Finset (Finset (Fin n))}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P)
    (hPmax : ∀ Q : Finset (Finset (Fin n)),
      IsInternalCrossPacking
          (G.deleteEdges (M : Set (Sym2 (Fin n)))) s Q → Q.card ≤ P.card)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hwmax : ∀ q : Finset (Fin n) → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    {x : ℝ}
    (hmin : (n : ℝ) / 2 - x =
      min (s.ncard : ℝ) (sᶜ.ncard : ℝ))
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hsevenS : 7 ≤ s.ncard) (hsevenT : 7 ≤ sᶜ.ncard)
    (hn24 : n = 24) (hk3 : (internalEdgeFinset G s).card = 3)
    (hm0 : P.card = 0) (hx : x = 1)
    (hS : (sideEdgeFinset G s.toFinset).Nonempty)
    (hT : (sideEdgeFinset G sᶜ.toFinset).Nonempty) : False := by
  have hPempty : P = ∅ := Finset.card_eq_zero.mp hm0
  obtain ⟨eS, heS⟩ := hS
  obtain ⟨eT, heT⟩ := hT
  have heSUncovered : eS ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
    simp [hPempty, coveredInternalEdges]
  have heTUncovered : eT ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
    simp [hPempty, coveredInternalEdges]
  have hlower := proposition42_claim43_pairs
    hM hP hPmax heS heT heSUncovered heTUncovered hwmax
  have hfive : (5 : ℝ) ≤ fractionalSize Gᶜ w := by
    norm_num [hn24, hk3, hm0] at hlower
    linarith
  obtain ⟨v, hv, hvSize⟩ :=
    exists_fractionalInternalCrossPacking_of_size_between hw
      (q := (5 : ℝ)) (by norm_num) hfive
  have hcards : (sideEdgeFinset G s.toFinset).card +
      (sideEdgeFinset G sᶜ.toFinset).card = 3 := by
    calc
      _ = (internalEdgeFinset G s).card := by
        rw [internalEdgeFinset_eq_union_sides,
          card_union_of_disjoint (sideEdgeFinset_disjoint_compl G s)]
      _ = 3 := hk3
  have hcardS : (sideEdgeFinset G s.toFinset).card ≤ 2 := by
    have hTpos : 0 < (sideEdgeFinset G sᶜ.toFinset).card :=
      Finset.card_pos.mpr ⟨eT, heT⟩
    omega
  have hcardT : (sideEdgeFinset G sᶜ.toFinset).card ≤ 2 := by
    have hSpos : 0 < (sideEdgeFinset G s.toFinset).card :=
      Finset.card_pos.mpr ⟨eS, heS⟩
    omega
  have hmin11 : min (s.ncard : ℝ) (sᶜ.ncard : ℝ) = 11 := by
    norm_num [hn24, hx] at hmin
    exact hmin.symm
  have hsideS11R : (11 : ℝ) ≤ s.ncard := by
    rw [← hmin11]
    exact min_le_left _ _
  have hsideT11R : (11 : ℝ) ≤ sᶜ.ncard := by
    rw [← hmin11]
    exact min_le_right _ _
  have hsideS11 : 11 ≤ s.ncard := by exact_mod_cast hsideS11R
  have hsideT11 : 11 ≤ sᶜ.ncard := by exact_mod_cast hsideT11R
  have hbudgetS :
      ((sideEdgeFinset G s.toFinset).card : ℝ) + fractionalSize Gᶜ v ≤
        ((s.ncard - 4 : ℕ) : ℝ) := by
    rw [hvSize, Nat.cast_sub (by omega)]
    have hcardSR : ((sideEdgeFinset G s.toFinset).card : ℝ) ≤ 2 := by
      exact_mod_cast hcardS
    have hsideS11R' : (11 : ℝ) ≤ s.ncard := by exact_mod_cast hsideS11
    norm_num
    linarith
  have hbudgetT :
      ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) + fractionalSize Gᶜ v ≤
        ((sᶜ.ncard - 4 : ℕ) : ℝ) := by
    rw [hvSize, Nat.cast_sub (by omega)]
    have hcardTR : ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) ≤ 2 := by
      exact_mod_cast hcardT
    rw [Set.toFinset_compl] at hcardTR
    have hsideT11R' : (11 : ℝ) ≤ sᶜ.ncard := by exact_mod_cast hsideT11
    norm_num
    linarith
  obtain ⟨hdeficitS, hdeficitT⟩ :=
    sideResidualDeficits_of_sidewiseSize hv hbudgetS hbudgetT
  exact proposition42_boundary_contradiction_of_sidewisePacking
    hAC (IsInternalCrossPacking.of_deleteEdges_cross hM.1 hP) hupper hv
      hsevenS hsevenT hcard hn24 hk3 hm0 hx (by rw [hvSize]; norm_num)
      hdeficitS hdeficitT

/-- Symmetric-pair wrapper for the oriented `9/2` boundary witness. -/
private lemma exists_oriented_saturatedSideCrossPacking_nine_halves_pair
    {α : Type*} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M) {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {e : Sym2 α} (he : e ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : e ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hm : P.card = 0) (hsidecard : 13 ≤ s.toFinset.card) :
    ∃ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q ∧
      (9 : ℝ) ≤ 2 * fractionalSize Gᶜ q ∧
      ∀ f ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
        fractionalEdgeLoad Gᶜ q f = 0 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
      exact exists_oriented_saturatedSideCrossPacking_nine_halves
        hM hP hPmax hcover he heUncovered hm hsidecard

/-- Boundary contradiction when `s` is saturated and the opposite side has
an uncovered internal edge.  If `s` is the larger part, use the oriented
zero-opposite-load witness; otherwise uniform truncation of the maximal
packing already fits both capacities. -/
private lemma proposition42_boundary_oneSaturated_contradiction
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    {P : Finset (Finset (Fin n))}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P)
    (hPmax : ∀ Q : Finset (Finset (Fin n)),
      IsInternalCrossPacking
          (G.deleteEdges (M : Set (Sym2 (Fin n)))) s Q → Q.card ≤ P.card)
    {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalInternalCrossPacking Gᶜ s w)
    (hwmax : ∀ q : Finset (Fin n) → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    {x : ℝ}
    (hmin : (n : ℝ) / 2 - x =
      min (s.ncard : ℝ) (sᶜ.ncard : ℝ))
    (hcard : ((internalEdgeFinset Gᶜ s).card : ℝ) =
      (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ))
    (hsevenS : 7 ≤ s.ncard) (hsevenT : 7 ≤ sᶜ.ncard)
    (hn24 : n = 24) (hk3 : (internalEdgeFinset G s).card = 3)
    (hm0 : P.card = 0) (hx : x = 1)
    (hSnone : ¬ (sideEdgeFinset G s.toFinset).Nonempty)
    (hT : ∃ e : Sym2 (Fin n), e ∈ G.edgeFinset ∧
      (e.toFinset : Set (Fin n)) ⊆ sᶜ) : False := by
  have hsevenSFin : 7 ≤ s.toFinset.card := by
    simpa only [← Set.ncard_eq_toFinset_card'] using hsevenS
  have hsevenTFin : 7 ≤ sᶜ.toFinset.card := by
    simpa only [← Set.ncard_eq_toFinset_card'] using hsevenT
  have hSempty : sideEdgeFinset G s.toFinset = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hSnone
  have hPempty : P = ∅ := Finset.card_eq_zero.mp hm0
  obtain ⟨eT, heTG, heTsub⟩ := hT
  have heT : eT ∈ sideEdgeFinset G sᶜ.toFinset := by
    apply mem_filter.mpr
    refine ⟨heTG, ?_⟩
    intro v hv
    exact Set.mem_toFinset.mpr (heTsub hv)
  have heTUncovered : eT ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
    simp [hPempty, coveredInternalEdges]
  have hcoverS : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P := by
    intro e he
    rw [hSempty] at he
    simp at he
  have hcards : (sideEdgeFinset G s.toFinset).card +
      (sideEdgeFinset G sᶜ.toFinset).card = 3 := by
    calc
      _ = (internalEdgeFinset G s).card := by
        rw [internalEdgeFinset_eq_union_sides,
          card_union_of_disjoint (sideEdgeFinset_disjoint_compl G s)]
      _ = 3 := hk3
  have hcardS : (sideEdgeFinset G s.toFinset).card = 0 := by rw [hSempty]; simp
  have hcardT : (sideEdgeFinset G sᶜ.toFinset).card = 3 := by omega
  have hmin11 : min (s.ncard : ℝ) (sᶜ.ncard : ℝ) = 11 := by
    norm_num [hn24, hx] at hmin
    exact hmin.symm
  have hsideS11R : (11 : ℝ) ≤ s.ncard := by
    rw [← hmin11]
    exact min_le_left _ _
  have hsideT11R : (11 : ℝ) ≤ sᶜ.ncard := by
    rw [← hmin11]
    exact min_le_right _ _
  have hsideS11 : 11 ≤ s.ncard := by exact_mod_cast hsideS11R
  have hsideT11 : 11 ≤ sᶜ.ncard := by exact_mod_cast hsideT11R
  have hsum24 : s.ncard + sᶜ.ncard = 24 := by
    have hsum := Set.ncard_add_ncard_compl s
    simpa [hn24] using hsum
  by_cases hlarge : 13 ≤ s.ncard
  · have hlargeFin : 13 ≤ s.toFinset.card := by
      simpa only [← Set.ncard_eq_toFinset_card'] using hlarge
    obtain ⟨q, hq, hqNine, hqZero⟩ :=
      exists_oriented_saturatedSideCrossPacking_nine_halves_pair
        hM hP hPmax hcoverS heT heTUncovered hm0 hlargeFin
    have hqHalf : (9 / 2 : ℝ) ≤ fractionalSize Gᶜ q := by linarith
    obtain ⟨v, hv, hvSize, hvZero⟩ :=
      exists_fractionalInternalCrossPacking_of_size_between_preserving_zero
        hq (q := (9 / 2 : ℝ)) (by norm_num) hqHalf hqZero
    have hloadS := sum_sideEdge_fractionalEdgeLoad_le_fractionalSize hv
    have hdeficitS :
        ((sideEdgeFinset G s.toFinset).card : ℝ) +
            ∑ e ∈ sideEdgeFinset Gᶜ s.toFinset,
              fractionalEdgeLoad Gᶜ v e ≤
          ((s.ncard - 4 : ℕ) : ℝ) := by
      rw [hcardS, Nat.cast_zero, zero_add, Nat.cast_sub (by omega)]
      have hlargeR : (13 : ℝ) ≤ s.ncard := by exact_mod_cast hlarge
      norm_num
      linarith [hloadS]
    have hloadTzero :
        (∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
          fractionalEdgeLoad Gᶜ v e) = 0 := by
      apply sum_eq_zero
      intro e he
      exact hvZero e he
    have hdeficitT :
        ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) +
            ∑ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
              fractionalEdgeLoad Gᶜ v e ≤
          ((sᶜ.ncard - 4 : ℕ) : ℝ) := by
      rw [hloadTzero, add_zero, Nat.cast_sub (by omega)]
      have hcardTR : ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) = 3 := by
        exact_mod_cast hcardT
      rw [Set.toFinset_compl] at hcardTR
      have hsideT11R' : (11 : ℝ) ≤ sᶜ.ncard := by exact_mod_cast hsideT11
      norm_num
      linarith
    exact proposition42_boundary_contradiction_of_sidewisePacking
      hAC (IsInternalCrossPacking.of_deleteEdges_cross hM.1 hP) hupper hv
        hsevenS hsevenT hcard hn24 hk3 hm0 hx (by rw [hvSize]; norm_num)
        hdeficitS hdeficitT
  · have hsideS12 : s.ncard ≤ 12 := by omega
    have hsideT12 : 12 ≤ sᶜ.ncard := by omega
    have hsideSR : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ) := by
      calc
        (n : ℝ) / 2 - x = min (s.ncard : ℝ) (sᶜ.ncard : ℝ) := hmin
        _ ≤ (s.ncard : ℝ) := min_le_left _ _
        _ = (s.toFinset.card : ℝ) := by
          rw [Set.ncard_eq_toFinset_card']
    have hlower := proposition42_claim44_pair
      hM hP hPmax hcoverS heT heTUncovered hwmax hsideSR hsevenSFin
    have hqHalf : (9 / 2 : ℝ) ≤ fractionalSize Gᶜ w := by
      rcases hlower with ⟨_hk, hlower⟩ | ⟨hk2, _hlower⟩
      · norm_num [hn24, hx, hm0] at hlower
        linarith
      · omega
    obtain ⟨v, hv, hvSize⟩ :=
      exists_fractionalInternalCrossPacking_of_size_between hw
        (q := (9 / 2 : ℝ)) (by norm_num) hqHalf
    have hbudgetS :
        ((sideEdgeFinset G s.toFinset).card : ℝ) + fractionalSize Gᶜ v ≤
          ((s.ncard - 4 : ℕ) : ℝ) := by
      rw [hcardS, Nat.cast_zero, zero_add, hvSize, Nat.cast_sub (by omega)]
      have hsideS11R' : (11 : ℝ) ≤ s.ncard := by exact_mod_cast hsideS11
      norm_num
      linarith
    have hbudgetT :
        ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) + fractionalSize Gᶜ v ≤
          ((sᶜ.ncard - 4 : ℕ) : ℝ) := by
      rw [hvSize, Nat.cast_sub (by omega)]
      have hcardTR : ((sideEdgeFinset G sᶜ.toFinset).card : ℝ) = 3 := by
        exact_mod_cast hcardT
      rw [Set.toFinset_compl] at hcardTR
      have hsideT12R : (12 : ℝ) ≤ sᶜ.ncard := by exact_mod_cast hsideT12
      norm_num
      linarith
    obtain ⟨hdeficitS, hdeficitT⟩ :=
      sideResidualDeficits_of_sidewiseSize hv hbudgetS hbudgetT
    exact proposition42_boundary_contradiction_of_sidewisePacking
      hAC (IsInternalCrossPacking.of_deleteEdges_cross hM.1 hP) hupper hv
        hsevenS hsevenT hcard hn24 hk3 hm0 hx (by rw [hvSize]; norm_num)
        hdeficitS hdeficitT

/-- Corrected Proposition 4.2, including the unique safe-truncation boundary. -/
theorem exists_internalEdgeCoveringCrossPacking_of_safeTruncation
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} (hn : 22 ≤ n) {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    (hk : (internalEdgeFinset G s).card ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hparts :
      (internalEdgeFinset G s).card + 4 ≤ s.ncard ∧
      (internalEdgeFinset G s).card + 4 ≤ sᶜ.ncard ∧
      7 ≤ s.ncard ∧ 7 ≤ sᶜ.ncard) :
    ∃ P : Finset (Finset (Fin n)),
      IsInternalEdgeCoveringCrossPacking
        (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
  classical
  obtain ⟨P, hP, hPmax⟩ :=
    exists_maximum_internalCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s
  have hPcard : P.card ≤ (internalEdgeFinset G s).card := by
    calc
      P.card = (coveredInternalEdges
          (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P).card :=
        (card_coveredInternalEdges_eq_card hP).symm
      _ ≤ (internalEdgeFinset
          (G.deleteEdges (M : Set (Sym2 (Fin n)))) s).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (internalEdgeFinset G s).card := by
        rw [internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
  by_cases hm : P.card < (internalEdgeFinset G s).card
  · obtain ⟨w, hw, hwmax⟩ :=
      exists_maximal_fractionalInternalCrossPacking Gᶜ s
    obtain ⟨x, hmin, hsideS, hsideT, hcard⟩ :=
      exists_partitionImbalance_internalComplement_card G s
    have hsevenS : 7 ≤ s.toFinset.card := by
      simpa only [← Set.ncard_eq_toFinset_card'] using hparts.2.2.1
    have hsevenT : 7 ≤ sᶜ.toFinset.card := by
      simpa only [← Set.ncard_eq_toFinset_card'] using hparts.2.2.2
    let q : ℝ := (n : ℝ) / 2 - x - 4 -
      ((internalEdgeFinset G s).card : ℝ)
    have hkminR : ((internalEdgeFinset G s).card : ℝ) + 4 ≤
        min (s.ncard : ℝ) (sᶜ.ncard : ℝ) := by
      apply le_min
      · exact_mod_cast hparts.1
      · exact_mod_cast hparts.2.1
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      linarith
    by_cases hr : fractionalSize Gᶜ w ≤ q
    · have hsizeSafe : fractionalSize Gᶜ w ≤
          (n : ℝ) / 2 - x - 4 -
            ((internalEdgeFinset G s).card : ℝ) := by
        simpa only [q] using hr
      obtain ⟨hbudgetSN, hbudgetTN⟩ :=
        totalBudgets_of_size_le_safeTruncation hmin hparts.1 hparts.2.1 hsizeSafe
      have hcovered := masterCoveredSize_of_totalBudget_atImbalance
        hAC (IsInternalCrossPacking.of_deleteEdges_cross hM.1 hP) hw
          hsevenS hsevenT hcard hbudgetSN hbudgetTN
      exact ⟨P, isInternalEdgeCoveringCrossPacking_of_proposition42_data
        hn hM hk hupper hP hPmax hwmax hsideS hsideT hsevenS hsevenT hcovered⟩
    · have hqle : q ≤ fractionalSize Gᶜ w := le_of_not_ge hr
      obtain ⟨u, hu, huSize⟩ :=
        exists_fractionalInternalCrossPacking_of_size_between hw hq0 hqle
      have hsizeSafe : fractionalSize Gᶜ u ≤
          (n : ℝ) / 2 - x - 4 -
            ((internalEdgeFinset G s).card : ℝ) := by
        rw [huSize]
      obtain ⟨hbudgetSN, hbudgetTN⟩ :=
        totalBudgets_of_size_le_safeTruncation hmin hparts.1 hparts.2.1 hsizeSafe
      have hcoveredU := masterCoveredSize_of_totalBudget_atImbalance
        hAC (IsInternalCrossPacking.of_deleteEdges_cross hM.1 hP) hu
          hsevenS hsevenT hcard hbudgetSN hbudgetTN
      rw [huSize] at hcoveredU
      have hmaster :
          2 * q - (n : ℝ) / 4 + 3 * (P.card : ℝ) -
              ((internalEdgeFinset G s).card : ℝ) + x ^ 2 ≤ 0 :=
        proposition42_master_inequality_of_coveredSize x q hcoveredU hupper
      have hboundary := proposition42_safe_truncation_boundary
        n (internalEdgeFinset G s).card P.card x hn hk hm (by
          simpa only [q] using hmaster)
      rcases hboundary with ⟨hn24, hk3, hm0, hx⟩
      by_cases hS : (sideEdgeFinset G s.toFinset).Nonempty
      · by_cases hT : (sideEdgeFinset G sᶜ.toFinset).Nonempty
        · exact (proposition42_boundary_bothSides_contradiction
            hAC hM hP hPmax hw hwmax hupper hmin hcard
              hparts.2.2.1 hparts.2.2.2
              hn24 hk3 hm0 hx hS hT).elim
        · have hTempty : sideEdgeFinset G sᶜ.toFinset = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hT
          have hMcomp : IsCrossMatching sᶜ M :=
            (isCrossMatching_set_compl s M).2 hM
          have hPcomp : IsInternalCrossPacking
              (G.deleteEdges (M : Set (Sym2 (Fin n)))) sᶜ P :=
            (isInternalCrossPacking_set_compl_iff
              (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P).2 hP
          have hPmaxComp : ∀ Q : Finset (Finset (Fin n)),
              IsInternalCrossPacking
                  (G.deleteEdges (M : Set (Sym2 (Fin n)))) sᶜ Q →
                Q.card ≤ P.card := by
            intro Q hQ
            exact hPmax Q ((isInternalCrossPacking_set_compl_iff
              (G.deleteEdges (M : Set (Sym2 (Fin n)))) s Q).1 hQ)
          have hwComp : IsFractionalInternalCrossPacking Gᶜ sᶜ w := by
            simpa [IsFractionalInternalCrossPacking] using hw
          have hwmaxComp : ∀ q : Finset (Fin n) → ℝ,
              IsFractionalInternalCrossPacking Gᶜ sᶜ q →
                fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w := by
            intro q hq
            apply hwmax q
            simpa [IsFractionalInternalCrossPacking] using hq
          have hminComp : (n : ℝ) / 2 - x =
              min (sᶜ.ncard : ℝ) ((sᶜ)ᶜ.ncard : ℝ) := by
            simpa only [compl_compl, min_comm] using hmin
          have hcardComp : ((internalEdgeFinset Gᶜ sᶜ).card : ℝ) =
              (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
                ((internalEdgeFinset G sᶜ).card : ℝ) := by
            simpa only [internalEdgeFinset_set_compl] using hcard
          have hk3Comp : (internalEdgeFinset G sᶜ).card = 3 := by
            simpa only [internalEdgeFinset_set_compl] using hk3
          have hsevenSComp : 7 ≤ sᶜ.ncard := hparts.2.2.2
          have hsevenTComp : 7 ≤ (sᶜ)ᶜ.ncard := by
            simpa only [compl_compl] using hparts.2.2.1
          have hotherComp : ∃ e : Sym2 (Fin n), e ∈ G.edgeFinset ∧
              (e.toFinset : Set (Fin n)) ⊆ (sᶜ)ᶜ := by
            rcases hS with ⟨e, he⟩
            rcases mem_filter.mp he with ⟨heG, hes⟩
            refine ⟨e, heG, ?_⟩
            intro v hv
            simpa only [compl_compl] using Set.mem_toFinset.mp (hes hv)
          exact (proposition42_boundary_oneSaturated_contradiction
            hAC hMcomp hPcomp hPmaxComp hwComp hwmaxComp hupper
              hminComp hcardComp hsevenSComp hsevenTComp hn24 hk3Comp
                hm0 hx (by
                  intro hnon
                  apply hT
                  rcases hnon with ⟨e, he⟩
                  exact ⟨e, by simpa [sideEdgeFinset] using he⟩)
                hotherComp).elim
      · have hSempty : sideEdgeFinset G s.toFinset = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        by_cases hT : (sideEdgeFinset G sᶜ.toFinset).Nonempty
        · have hTdata : ∃ e : Sym2 (Fin n), e ∈ G.edgeFinset ∧
              (e.toFinset : Set (Fin n)) ⊆ sᶜ := by
            rcases hT with ⟨e, he⟩
            rcases mem_filter.mp he with ⟨heG, hes⟩
            exact ⟨e, heG, fun _v hv ↦ Set.mem_toFinset.mp (hes hv)⟩
          exact (proposition42_boundary_oneSaturated_contradiction
            hAC hM hP hPmax hw hwmax hupper hmin hcard
              hparts.2.2.1 hparts.2.2.2
              hn24 hk3 hm0 hx hS hTdata).elim
        · have hTempty : sideEdgeFinset G sᶜ.toFinset = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hT
          have hcards : (sideEdgeFinset G s.toFinset).card +
              (sideEdgeFinset G sᶜ.toFinset).card = 3 := by
            calc
              _ = (internalEdgeFinset G s).card := by
                rw [internalEdgeFinset_eq_union_sides,
                  card_union_of_disjoint (sideEdgeFinset_disjoint_compl G s)]
              _ = 3 := hk3
          rw [hSempty, hTempty] at hcards
          simp at hcards
  · have hkP : (internalEdgeFinset G s).card ≤ P.card := by omega
    refine ⟨P, isInternalEdgeCoveringCrossPacking_of_internal_card_le hP ?_⟩
    rw [internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
    exact hkP

/-- Backwards-compatible nonboundary specialization of the corrected full
safe-truncation theorem. -/
theorem exists_internalEdgeCoveringCrossPacking_of_safeTruncation_nonboundary
    (hAC : AlmostCompleteFractionalDecomposition)
    {n : ℕ} (hn : 22 ≤ n) {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    (hk : (internalEdgeFinset G s).card ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hparts :
      (internalEdgeFinset G s).card + 4 ≤ s.ncard ∧
      (internalEdgeFinset G s).card + 4 ≤ sᶜ.ncard ∧
      7 ≤ s.ncard ∧ 7 ≤ sᶜ.ncard)
    (_hnotBoundary : n ≠ 24 ∨ (internalEdgeFinset G s).card ≠ 3) :
    ∃ P : Finset (Finset (Fin n)),
      IsInternalEdgeCoveringCrossPacking
        (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P :=
  exists_internalEdgeCoveringCrossPacking_of_safeTruncation
    hAC hn hM hk hupper hparts

/-- The corrected capacity argument and Proposition 4.1 discharge the full
matching-avoiding form of Proposition 4.2 from the almost-complete
decomposition theorem alone. -/
theorem almostBipartiteIntegralCrossPackingAvoiding_of_almostComplete
    (hAC : AlmostCompleteFractionalDecomposition) :
    AlmostBipartiteIntegralCrossPackingAvoiding := by
  intro n hn G s M hM hk hupper
  have hparts := almostBipartitePartSizeBound hAC n (by omega) G s hk hupper
  exact exists_internalEdgeCoveringCrossPacking_of_safeTruncation
    hAC hn hM hk hupper hparts

end

end Erdos76
