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
import ErdosProblems.Erdos76.AlmostBipartitePartSize
import ErdosProblems.Erdos76.AlmostCompleteCapacityCompactness
import ErdosProblems.Erdos76.AlmostCompleteStrongInduction
import ErdosProblems.Erdos76.Proposition42SafeTruncation

/-!
# Capacity completion for Proposition 4.2

This downstream module combines Proposition 4.1, the exact real-capacity
corollary, and the parameterized Claim 4.3/4.4 core in
`GruslysLetzter.lean`.  In particular it uses the monochromatically valid
capacity deficit `k+r`; it never uses the unsupported printed truncation
`m+r`.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Residual capacity on one side after reserving the internal-edge loads of
an ambient cross-triangle packing.  Nonedges of the induced monochromatic
graph have capacity zero. -/
def sideResidualCapacity (G : SimpleGraph α) (S : Finset α)
    (w : Finset α → ℝ) (p : Sym2 S) : ℝ :=
  if p ∈ (G.induce (S : Set α)).edgeFinset then
    1 - fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)
  else 0

private lemma mapped_induced_edge_mem
    (G : SimpleGraph α) (S : Finset α) {p : Sym2 S}
    (hp : p ∈ (G.induce (S : Set α)).edgeFinset) :
    (inducedEmbedding S).sym2Map p ∈ G.edgeFinset := by
  induction p using Sym2.inductionOn with
  | hf a b =>
      apply SimpleGraph.mem_edgeFinset.mpr
      change G.Adj a.1 b.1
      exact SimpleGraph.mem_edgeFinset.mp hp

private lemma fractionalEdgeLoad_nonneg_of_packing
    {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) (p : Sym2 α) :
    0 ≤ fractionalEdgeLoad G w p := by
  unfold fractionalEdgeLoad
  exact Finset.sum_nonneg fun t ht ↦ hw.nonneg_on (mem_filter.mp ht).1

lemma sideResidualCapacity_isEdgeCapacity
    {G : SimpleGraph α} {S : Finset α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) :
    IsEdgeCapacity (⊤ : SimpleGraph S) (sideResidualCapacity G S w) := by
  classical
  constructor
  · intro p hpTop
    by_cases hp : p ∈ (G.induce (S : Set α)).edgeFinset
    · rw [sideResidualCapacity, if_pos hp]
      have hpG := mapped_induced_edge_mem G S hp
      constructor
      · exact sub_nonneg.mpr (hw.edgeLoad_le_one hpG)
      · have hload := fractionalEdgeLoad_nonneg_of_packing hw
          ((inducedEmbedding S).sym2Map p)
        linarith
    · simp [sideResidualCapacity, hp]
  · intro p hp
    rw [sideResidualCapacity, if_neg]
    intro hpK
    apply hp
    induction p using Sym2.inductionOn with
    | hf a b =>
        have hab : (G.induce (S : Set α)).Adj a b :=
          SimpleGraph.mem_edgeFinset.mp hpK
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.top_adj] using hab.ne

private lemma filter_topEdgeFinset_induced_eq
    (G : SimpleGraph α) (S : Finset α) :
    (⊤ : SimpleGraph S).edgeFinset.filter
        (fun p ↦ p ∈ (G.induce (S : Set α)).edgeFinset) =
      (G.induce (S : Set α)).edgeFinset := by
  classical
  let K := G.induce (S : Set α)
  let E := (⊤ : SimpleGraph S).edgeFinset
  have hKsub : K.edgeFinset ⊆ E := by
    intro p hp
    exact SimpleGraph.edgeFinset_mono le_top hp
  have hfilterK : E.filter (fun p ↦ p ∈ K.edgeFinset) = K.edgeFinset := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp ↦ hp.2
    · exact fun hp ↦ ⟨hKsub hp, hp⟩
  simpa only [K, E] using hfilterK

private lemma filter_topEdgeFinset_not_induced_eq
    (G : SimpleGraph α) (S : Finset α) :
    (⊤ : SimpleGraph S).edgeFinset.filter
        (fun p ↦ p ∉ (G.induce (S : Set α)).edgeFinset) =
      (G.induce (S : Set α))ᶜ.edgeFinset := by
  classical
  ext p
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  induction p using Sym2.inductionOn with
  | hf a b => simp [SimpleGraph.compl_adj]

private lemma sum_induced_one_sub_sideResidualCapacity
    (G : SimpleGraph α) (S : Finset α) (w : Finset α → ℝ) :
    ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
        (1 - sideResidualCapacity G S w p) =
      ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
        fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  rw [sideResidualCapacity, if_pos hp]
  ring

private lemma sum_complInduced_one_sub_sideResidualCapacity
    (G : SimpleGraph α) (S : Finset α) (w : Finset α → ℝ) :
    ∑ p ∈ (G.induce (S : Set α))ᶜ.edgeFinset,
        (1 - sideResidualCapacity G S w p) =
      ((G.induce (S : Set α))ᶜ.edgeFinset.card : ℝ) := by
  classical
  calc
    ∑ p ∈ (G.induce (S : Set α))ᶜ.edgeFinset,
        (1 - sideResidualCapacity G S w p) =
        ∑ _p ∈ (G.induce (S : Set α))ᶜ.edgeFinset, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpNot : p ∉ (G.induce (S : Set α)).edgeFinset := by
            induction p using Sym2.inductionOn with
            | hf a b =>
                simp only [SimpleGraph.mem_edgeFinset,
                  SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at hp ⊢
                exact hp.2
          rw [sideResidualCapacity, if_neg hpNot]
          ring
    _ = ((G.induce (S : Set α))ᶜ.edgeFinset.card : ℝ) := by simp

/-- Exact deficit identity for the residual capacity on an induced side. -/
lemma capacityMissingWeight_sideResidualCapacity
    (G : SimpleGraph α) (S : Finset α) (w : Finset α → ℝ) :
    capacityMissingWeight (sideResidualCapacity G S w) =
      (missingEdgeCount (G.induce (S : Set α)) : ℝ) +
        ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
          fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) := by
  classical
  let K := G.induce (S : Set α)
  let E := (⊤ : SimpleGraph S).edgeFinset
  unfold capacityMissingWeight
  rw [← Finset.sum_filter_add_sum_filter_not E
    (fun p ↦ p ∈ K.edgeFinset)]
  change
    (∑ p ∈ E.filter (fun p ↦ p ∈ K.edgeFinset),
        (1 - sideResidualCapacity G S w p)) +
      (∑ p ∈ E.filter (fun p ↦ p ∉ K.edgeFinset),
        (1 - sideResidualCapacity G S w p)) = _
  rw [show E.filter (fun p ↦ p ∈ K.edgeFinset) = K.edgeFinset by
        simpa only [E, K] using filter_topEdgeFinset_induced_eq G S,
      show E.filter (fun p ↦ p ∉ K.edgeFinset) = Kᶜ.edgeFinset by
        simpa only [E, K] using filter_topEdgeFinset_not_induced_eq G S]
  rw [show (∑ p ∈ K.edgeFinset, (1 - sideResidualCapacity G S w p)) =
        ∑ p ∈ K.edgeFinset,
          fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) by
        simpa only [K] using sum_induced_one_sub_sideResidualCapacity G S w,
      show (∑ p ∈ Kᶜ.edgeFinset, (1 - sideResidualCapacity G S w p)) =
        (Kᶜ.edgeFinset.card : ℝ) by
        simpa only [K] using sum_complInduced_one_sub_sideResidualCapacity G S w]
  change _ + (Kᶜ.edgeFinset.card : ℝ) =
    (Kᶜ.edgeFinset.card : ℝ) + _
  exact add_comm _ _

/-- Renaming the edges of an induced side does not change the corresponding
sum of ambient edge loads. -/
lemma sum_inducedEdge_mapped_load
    (G : SimpleGraph α) (S : Finset α) (w : Finset α → ℝ) :
    (∑ p ∈ (G.induce (S : Set α)).edgeFinset,
        fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)) =
      ∑ e ∈ sideEdgeFinset G S, fractionalEdgeLoad G w e := by
  classical
  apply Finset.sum_bij (fun p _hp ↦ (inducedEmbedding S).sym2Map p)
  · intro p hp
    apply mem_filter.mpr
    refine ⟨mapped_induced_edge_mem G S hp, ?_⟩
    induction p using Sym2.inductionOn with
    | hf a b =>
        intro x hx
        have hxCases : x = a.1 ∨ x = b.1 := by
          simpa [Sym2.toFinset_mk_eq] using hx
        rcases hxCases with rfl | rfl
        · exact a.2
        · exact b.2
  · intro p hp q hq hpq
    exact (inducedEmbedding S).sym2Map.injective hpq
  · intro e he
    rcases mem_filter.mp he with ⟨heG, heS⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
        have haPair : a ∈ s(a, b).toFinset := by simp
        have hbPair : b ∈ s(a, b).toFinset := by simp
        let aS : S := ⟨a, heS haPair⟩
        let bS : S := ⟨b, heS hbPair⟩
        let p : Sym2 S := s(aS, bS)
        have hp : p ∈ (G.induce (S : Set α)).edgeFinset := by
          apply SimpleGraph.mem_edgeFinset.mpr
          change G.Adj a b
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
        refine ⟨p, hp, ?_⟩
        rfl
  · intro p hp
    rfl

/-- The induced-side contribution to residual capacity is bounded by the
total size of a cross-triangle packing. -/
lemma sum_inducedEdge_mapped_load_le_fractionalSize
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) :
    (∑ p ∈ (G.induce (s.toFinset : Set α)).edgeFinset,
        fractionalEdgeLoad G w ((inducedEmbedding s.toFinset).sym2Map p)) ≤
      fractionalSize G w := by
  rw [sum_inducedEdge_mapped_load]
  exact sum_sideEdge_fractionalEdgeLoad_le_fractionalSize hw

/-- Corollary 2.12 applied to one side after accounting for precisely the
ambient cross-packing load reserved on its internal edges. -/
theorem exists_sideResidualCapacityDecomposition
    (hAC : AlmostCompleteFractionalDecomposition)
    {G : SimpleGraph α} {S : Finset α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w)
    (hcard : 7 ≤ S.card)
    (hdeficit :
      (missingEdgeCount (G.induce (S : Set α)) : ℝ) +
          ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
            fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) ≤
        ((S.card - 4 : ℕ) : ℝ)) :
    ∃ u : Finset S → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph S)
        (sideResidualCapacity G S w) u := by
  have hcard' : 7 ≤ Fintype.card S := by simpa using hcard
  apply capacityDecomposition_of_almostComplete hAC hcard'
    (sideResidualCapacity G S w)
    (sideResidualCapacity_isEdgeCapacity hw)
  rw [capacityMissingWeight_sideResidualCapacity]
  simpa only [Fintype.card_coe] using hdeficit

/-- The induced-side residual packing together with its two exact
bookkeeping identities.  Packaging these dependent fields in a structure
keeps downstream complement applications within the default elaboration
budget. -/
structure SideResidualPackingData (G : SimpleGraph α) (S : Finset α)
    (w : Finset α → ℝ) where
  weight : Finset S → ℝ
  isPacking : IsFractionalPacking (G.induce (S : Set α)) weight
  edgeLoad_eq : ∀ p ∈ (G.induce (S : Set α)).edgeFinset,
    fractionalEdgeLoad (G.induce (S : Set α)) weight p =
      1 - fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)
  three_mul_size : 3 * fractionalSize (G.induce (S : Set α)) weight =
    ((G.induce (S : Set α)).edgeFinset.card : ℝ) -
      ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
        fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)

/-- The capacity decomposition restricted to its induced monochromatic
support. -/
theorem exists_sideResidualPacking
    (hAC : AlmostCompleteFractionalDecomposition)
    {G : SimpleGraph α} {S : Finset α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w)
    (hcard : 7 ≤ S.card)
    (hdeficit :
      (missingEdgeCount (G.induce (S : Set α)) : ℝ) +
          ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
            fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) ≤
        ((S.card - 4 : ℕ) : ℝ)) :
    ∃ v : Finset S → ℝ,
      IsFractionalPacking (G.induce (S : Set α)) v ∧
      (∀ p ∈ (G.induce (S : Set α)).edgeFinset,
        fractionalEdgeLoad (G.induce (S : Set α)) v p =
          1 - fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)) ∧
      3 * fractionalSize (G.induce (S : Set α)) v =
        ((G.induce (S : Set α)).edgeFinset.card : ℝ) -
          ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
            fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) := by
  classical
  let K := G.induce (S : Set α)
  let c := sideResidualCapacity G S w
  obtain ⟨u, hu⟩ := exists_sideResidualCapacityDecomposition hAC hw hcard hdeficit
  have hsupport : ∀ p, p ∉ K.edgeSet → c p = 0 := by
    intro p hp
    change sideResidualCapacity G S w p = 0
    rw [sideResidualCapacity, if_neg]
    intro hpFin
    exact hp (SimpleGraph.mem_edgeFinset.mp hpFin)
  have hcTop : IsEdgeCapacity (⊤ : SimpleGraph S) c :=
    sideResidualCapacity_isEdgeCapacity hw
  have hcK : IsEdgeCapacity K c := by
    constructor
    · intro p hp
      apply hcTop.1 p
      induction p using Sym2.inductionOn with
      | hf a b =>
          have hab : K.Adj a b := SimpleGraph.mem_edgeFinset.mp hp
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.top_adj] using hab.ne
    · intro p hp
      exact hsupport p (fun hpSet ↦ hp (SimpleGraph.mem_edgeFinset.mpr hpSet))
  let v : Finset S → ℝ := zeroExtendTriangleWeight K u
  have hvCap : IsCapacityPacking K c v := by
    simpa only [v] using
      (IsCapacityPacking.zeroExtend_support (H := K) (c := c) (w := u)
        hu.1 hsupport)
  have hvPack : IsFractionalPacking K v := hvCap.toFractionalPacking hcK
  have hload : ∀ p ∈ K.edgeFinset,
      fractionalEdgeLoad K v p =
        1 - fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) := by
    intro p hp
    calc
      fractionalEdgeLoad K v p = fractionalEdgeLoad K u p := by
        exact fractionalEdgeLoad_zeroExtend le_rfl u p
      _ = fractionalEdgeLoad (⊤ : SimpleGraph S) v p := by
        exact (fractionalEdgeLoad_zeroExtend le_top u p).symm
      _ = fractionalEdgeLoad (⊤ : SimpleGraph S) u p :=
        fractionalEdgeLoad_zeroExtend_eq_of_capacity_support hu.1 hsupport p
      _ = c p := by
        apply hu.2 p
        induction p using Sym2.inductionOn with
        | hf a b =>
            have hab : K.Adj a b := SimpleGraph.mem_edgeFinset.mp hp
            simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.top_adj] using hab.ne
      _ = 1 - fractionalEdgeLoad G w
          ((inducedEmbedding S).sym2Map p) := by
        simp [c, sideResidualCapacity, K, hp]
  refine ⟨v, hvPack, hload, ?_⟩
  have hsum := sum_fractionalEdgeLoad_eq_three_mul_fractionalSize_generic K v
  calc
    3 * fractionalSize K v =
        ∑ p ∈ K.edgeFinset, fractionalEdgeLoad K v p := hsum.symm
    _ = ∑ p ∈ K.edgeFinset,
        (1 - fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hload p hp
    _ = (K.edgeFinset.card : ℝ) -
        ∑ p ∈ K.edgeFinset,
          fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) := by
          rw [Finset.sum_sub_distrib]
          simp

/-- A choice of the preceding residual witness, exposed through a compact
data interface so complement-side consumers need not elaborate a large
nested existential. -/
noncomputable def sideResidualPackingData
    (hAC : AlmostCompleteFractionalDecomposition)
    {G : SimpleGraph α} {S : Finset α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w)
    (hcard : 7 ≤ S.card)
    (hdeficit :
      (missingEdgeCount (G.induce (S : Set α)) : ℝ) +
          ∑ p ∈ (G.induce (S : Set α)).edgeFinset,
            fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) ≤
        ((S.card - 4 : ℕ) : ℝ)) :
    SideResidualPackingData G S w := by
  let h := exists_sideResidualPacking hAC hw hcard hdeficit
  exact
    { weight := Classical.choose h
      isPacking := (Classical.choose_spec h).1
      edgeLoad_eq := (Classical.choose_spec h).2.1
      three_mul_size := (Classical.choose_spec h).2.2 }

/-- Splice a cross-triangle packing with exact residual packings on the two
sides.  Internal edges are filled to load one, while both zero-extended side
packings vanish on cross edges. -/
theorem isFractionalPacking_add_cross_and_sideResiduals
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w)
    {vS : Finset s.toFinset → ℝ} {vT : Finset sᶜ.toFinset → ℝ}
    (hvS : IsFractionalPacking (G.induce (s.toFinset : Set α)) vS)
    (hvT : IsFractionalPacking (G.induce (sᶜ.toFinset : Set α)) vT)
    (hloadS : ∀ p ∈ (G.induce (s.toFinset : Set α)).edgeFinset,
      fractionalEdgeLoad (G.induce (s.toFinset : Set α)) vS p =
        1 - fractionalEdgeLoad G w
          ((inducedEmbedding s.toFinset).sym2Map p))
    (hloadT : ∀ p ∈ (G.induce (sᶜ.toFinset : Set α)).edgeFinset,
      fractionalEdgeLoad (G.induce (sᶜ.toFinset : Set α)) vT p =
        1 - fractionalEdgeLoad G w
          ((inducedEmbedding sᶜ.toFinset).sym2Map p)) :
    IsFractionalPacking G
      (addTriangleWeight w
        (addTriangleWeight (extendInducedWeight s.toFinset vS)
          (extendInducedWeight sᶜ.toFinset vT))) := by
  classical
  let S := s.toFinset
  let T := sᶜ.toFinset
  let sideWeight := addTriangleWeight (extendInducedWeight S vS)
    (extendInducedWeight T vT)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hxs : x ∈ s := by simpa only [S, Set.mem_toFinset] using hxS
    have hxns : x ∉ s := by simpa only [T, Set.mem_toFinset, Set.mem_compl_iff] using hxT
    exact hxns hxs
  have hside : IsFractionalPacking G sideWeight := by
    exact isFractionalPacking_add_extendInduced_of_disjoint G S T hST
      vS vT (by simpa only [S] using hvS) (by simpa only [T] using hvT)
  constructor
  · intro t ht
    exact add_nonneg (hw.1.nonneg_on ht) (hside.nonneg_on ht)
  · intro e he
    change fractionalEdgeLoad G (fun t ↦ w t + sideWeight t) e ≤ 1
    rw [fractionalEdgeLoad_add]
    induction e using Sym2.inductionOn with
    | hf a b =>
      by_cases ha : a ∈ S
      · by_cases hb : b ∈ S
        · let aS : S := ⟨a, ha⟩
          let bS : S := ⟨b, hb⟩
          let p : Sym2 S := s(aS, bS)
          have hmap : (inducedEmbedding S).sym2Map p = s(a, b) := rfl
          have hp : p ∈ (G.induce (S : Set α)).edgeFinset := by
            apply SimpleGraph.mem_edgeFinset.mpr
            change G.Adj a b
            exact SimpleGraph.mem_edgeFinset.mp he
          have haT : a ∉ T := fun haT ↦
            Finset.disjoint_left.mp hST ha haT
          change fractionalEdgeLoad G w s(a, b) +
            fractionalEdgeLoad G
              (fun t ↦ extendInducedWeight S vS t +
                extendInducedWeight T vT t) s(a, b) ≤ 1
          rw [fractionalEdgeLoad_add]
          rw [show s(a, b) = (inducedEmbedding S).sym2Map p from hmap.symm,
            fractionalEdgeLoad_extendInducedWeight]
          have hzT : fractionalEdgeLoad G (extendInducedWeight T vT)
              ((inducedEmbedding S).sym2Map p) = 0 := by
            rw [hmap]
            exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G T vT a b haT
          rw [hzT, add_zero]
          have hfill := hloadS p (by simpa only [S] using hp)
          simpa only [S] using (show
            fractionalEdgeLoad G w ((inducedEmbedding S).sym2Map p) +
              fractionalEdgeLoad (G.induce (S : Set α)) vS p ≤ 1 by
                linarith)
        · have hbT : b ∈ T := by
            simpa only [T, Set.mem_toFinset, Set.mem_compl_iff, S,
              Set.mem_toFinset] using hb
          have hbSnot : b ∉ S := hb
          have haTnot : a ∉ T := fun haT ↦
            Finset.disjoint_left.mp hST ha haT
          change fractionalEdgeLoad G w s(a, b) +
            fractionalEdgeLoad G
              (fun t ↦ extendInducedWeight S vS t +
                extendInducedWeight T vT t) s(a, b) ≤ 1
          rw [fractionalEdgeLoad_add]
          have hzS : fractionalEdgeLoad G (extendInducedWeight S vS) s(a, b) = 0 := by
            rw [show s(a, b) = s(b, a) from Sym2.sound (Sym2.Rel.swap a b)]
            exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G S vS b a hbSnot
          have hzT : fractionalEdgeLoad G (extendInducedWeight T vT) s(a, b) = 0 :=
            fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G T vT a b haTnot
          rw [hzS, hzT]
          norm_num
          exact hw.1.edgeLoad_le_one he

      · have haT : a ∈ T := by
          simpa only [T, Set.mem_toFinset, Set.mem_compl_iff, S,
            Set.mem_toFinset] using ha
        by_cases hb : b ∈ T
        · let aT : T := ⟨a, haT⟩
          let bT : T := ⟨b, hb⟩
          let p : Sym2 T := s(aT, bT)
          have hmap : (inducedEmbedding T).sym2Map p = s(a, b) := rfl
          have hp : p ∈ (G.induce (T : Set α)).edgeFinset := by
            apply SimpleGraph.mem_edgeFinset.mpr
            change G.Adj a b
            exact SimpleGraph.mem_edgeFinset.mp he
          change fractionalEdgeLoad G w s(a, b) +
            fractionalEdgeLoad G
              (fun t ↦ extendInducedWeight S vS t +
                extendInducedWeight T vT t) s(a, b) ≤ 1
          rw [fractionalEdgeLoad_add,
            fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G S vS a b ha,
            zero_add]
          rw [show s(a, b) = (inducedEmbedding T).sym2Map p from hmap.symm,
            fractionalEdgeLoad_extendInducedWeight]
          have hfill := hloadT p (by simpa only [T] using hp)
          simpa only [T] using (show
            fractionalEdgeLoad G w ((inducedEmbedding T).sym2Map p) +
              fractionalEdgeLoad (G.induce (T : Set α)) vT p ≤ 1 by
                linarith)
        · have hbS : b ∈ S := by
            have hbNotT : b ∉ sᶜ := by simpa only [T, Set.mem_toFinset] using hb
            have hbs : b ∈ s := by simpa only [Set.mem_compl_iff, not_not] using hbNotT
            simpa only [S, Set.mem_toFinset] using hbs
          change fractionalEdgeLoad G w s(a, b) +
            fractionalEdgeLoad G
              (fun t ↦ extendInducedWeight S vS t +
                extendInducedWeight T vT t) s(a, b) ≤ 1
          rw [fractionalEdgeLoad_add]
          have hzS : fractionalEdgeLoad G (extendInducedWeight S vS) s(a, b) = 0 :=
            fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G S vS a b ha
          have hzT : fractionalEdgeLoad G (extendInducedWeight T vT) s(a, b) = 0 := by
            rw [show s(a, b) = s(b, a) from Sym2.sound (Sym2.Rel.swap a b)]
            exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G T vT b a hb
          rw [hzS, hzT]
          norm_num
          exact hw.1.edgeLoad_le_one he

/-- Exact size of the completed cross packing.  Every cross triangle
contributes one unit of reserved internal-edge load, so completing both
sides changes `3 * size` from `3r` to `|E_internal| + 2r`. -/
theorem three_mul_fractionalSize_add_cross_and_sideResiduals
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w)
    {vS : Finset s.toFinset → ℝ} {vT : Finset sᶜ.toFinset → ℝ}
    (hsizeS :
      3 * fractionalSize (G.induce (s.toFinset : Set α)) vS =
        ((G.induce (s.toFinset : Set α)).edgeFinset.card : ℝ) -
          ∑ p ∈ (G.induce (s.toFinset : Set α)).edgeFinset,
            fractionalEdgeLoad G w
              ((inducedEmbedding s.toFinset).sym2Map p))
    (hsizeT :
      3 * fractionalSize (G.induce (sᶜ.toFinset : Set α)) vT =
        ((G.induce (sᶜ.toFinset : Set α)).edgeFinset.card : ℝ) -
          ∑ p ∈ (G.induce (sᶜ.toFinset : Set α)).edgeFinset,
            fractionalEdgeLoad G w
              ((inducedEmbedding sᶜ.toFinset).sym2Map p)) :
    3 * fractionalSize G
        (addTriangleWeight w
          (addTriangleWeight (extendInducedWeight s.toFinset vS)
            (extendInducedWeight sᶜ.toFinset vT))) =
      ((internalEdgeFinset G s).card : ℝ) + 2 * fractionalSize G w := by
  classical
  have hload :
      (∑ p ∈ (G.induce (s.toFinset : Set α)).edgeFinset,
          fractionalEdgeLoad G w
            ((inducedEmbedding s.toFinset).sym2Map p)) +
        (∑ p ∈ (G.induce (sᶜ.toFinset : Set α)).edgeFinset,
          fractionalEdgeLoad G w
            ((inducedEmbedding sᶜ.toFinset).sym2Map p)) =
        fractionalSize G w := by
    rw [sum_inducedEdge_mapped_load, sum_inducedEdge_mapped_load]
    rw [← Finset.sum_union (sideEdgeFinset_disjoint_compl G s)]
    rw [← internalEdgeFinset_eq_union_sides]
    exact sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hw
  have hcard :
      ((G.induce (s.toFinset : Set α)).edgeFinset.card : ℝ) +
        ((G.induce (sᶜ.toFinset : Set α)).edgeFinset.card : ℝ) =
        ((internalEdgeFinset G s).card : ℝ) := by
    rw [← card_sideEdgeFinset G s.toFinset,
      ← card_sideEdgeFinset G sᶜ.toFinset]
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint
      (sideEdgeFinset_disjoint_compl G s)]
    rw [← internalEdgeFinset_eq_union_sides]
  rw [fractionalSize_addTriangleWeight,
    fractionalSize_addTriangleWeight,
    fractionalSize_extendInducedWeight,
    fractionalSize_extendInducedWeight]
  nlinarith

end


end Erdos76
