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
import ErdosProblems.Erdos76.PentagonInitialExtension

/-!
# Splicing a bad-pattern packing into residual fractional packings

The bad-pattern branch of the pentagon extension argument produces a small
edge-disjoint family of monochromatic triangles through the new vertex.  Its
red and blue parts can be added integrally to residual fractional packings,
provided the residual weights reserve every edge used by the corresponding
part.  This module packages that colour split and the exact objective gain.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The red triangles in a monochromatic family. -/
def monochromaticRedPart (G : SimpleGraph α) (P : Finset (Finset α)) :
    Finset (Finset α) :=
  P.filter fun t ↦ t ∈ G.cliqueFinset 3

/-- The blue triangles in a monochromatic family. -/
def monochromaticBluePart (G : SimpleGraph α) (P : Finset (Finset α)) :
    Finset (Finset α) :=
  P.filter fun t ↦ t ∈ Gᶜ.cliqueFinset 3

lemma monochromaticRedPart_subset
    (G : SimpleGraph α) (P : Finset (Finset α)) :
    monochromaticRedPart G P ⊆ G.cliqueFinset 3 := by
  intro t ht
  exact (mem_filter.mp ht).2

lemma monochromaticBluePart_subset
    (G : SimpleGraph α) (P : Finset (Finset α)) :
    monochromaticBluePart G P ⊆ Gᶜ.cliqueFinset 3 := by
  intro t ht
  exact (mem_filter.mp ht).2

lemma monochromaticRedPart_union_bluePart
    {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P) :
    monochromaticRedPart G P ∪ monochromaticBluePart G P = P := by
  ext t
  constructor
  · intro ht
    rcases mem_union.mp ht with ht | ht
    · exact (mem_filter.mp ht).1
    · exact (mem_filter.mp ht).1
  · intro ht
    have hmono := mem_monochromaticTriangles.mp (hP.1 ht)
    rcases hmono with hred | hblue
    · exact mem_union_left _ (mem_filter.mpr
        ⟨ht, SimpleGraph.mem_cliqueFinset_iff.mpr hred⟩)
    · exact mem_union_right _ (mem_filter.mpr
        ⟨ht, SimpleGraph.mem_cliqueFinset_iff.mpr hblue⟩)

lemma monochromaticRedPart_disjoint_bluePart
    (G : SimpleGraph α) (P : Finset (Finset α)) :
    Disjoint (monochromaticRedPart G P) (monochromaticBluePart G P) :=
  red_blue_packing_disjoint
    (monochromaticRedPart_subset G P)
    (monochromaticBluePart_subset G P)

lemma card_monochromaticRedPart_add_bluePart
    {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P) :
    (monochromaticRedPart G P).card +
        (monochromaticBluePart G P).card = P.card := by
  rw [← card_union_of_disjoint
    (monochromaticRedPart_disjoint_bluePart G P),
    monochromaticRedPart_union_bluePart hP]

lemma edgeDisjoint_monochromaticRedPart
    {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P) :
    EdgeDisjoint (monochromaticRedPart G P) := by
  intro s hs t ht hst
  exact hP.2 (mem_filter.mp hs).1 (mem_filter.mp ht).1 hst

lemma edgeDisjoint_monochromaticBluePart
    {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P) :
    EdgeDisjoint (monochromaticBluePart G P) := by
  intro s hs t ht hst
  exact hP.2 (mem_filter.mp hs).1 (mem_filter.mp ht).1 hst

/-- All unordered pairs used by a finite family of vertex sets. -/
def packingPairFinset (P : Finset (Finset α)) : Finset (Sym2 α) :=
  P.biUnion fun t ↦ t.sym2

@[simp] lemma mem_packingPairFinset
    {P : Finset (Finset α)} {e : Sym2 α} :
    e ∈ packingPairFinset P ↔ ∃ t ∈ P, e ∈ t.sym2 := by
  simp [packingPairFinset]

lemma fractionalEdgeLoad_integralPackingWeight_eq_zero_of_not_mem
    (G : SimpleGraph α) (P : Finset (Finset α)) {e : Sym2 α}
    (he : e ∉ packingPairFinset P) :
    fractionalEdgeLoad G (integralPackingWeight P) e = 0 := by
  unfold fractionalEdgeLoad integralPackingWeight
  apply sum_eq_zero
  intro t ht
  have hte := (mem_filter.mp ht).2
  rw [if_neg]
  intro htP
  exact he (mem_packingPairFinset.mpr ⟨t, htP, hte⟩)

/-- Add an integral triangle family to a fractional residual packing whose
load vanishes on every pair used by that family. -/
lemma isFractionalPacking_add_packingWeight_of_zero_load
    (G : SimpleGraph α) (P : Finset (Finset α))
    (hP : EdgeDisjoint P) (w : Finset α → ℝ)
    (hw : IsFractionalPacking G w)
    (hzero : ∀ e ∈ G.edgeFinset, e ∈ packingPairFinset P →
      fractionalEdgeLoad G w e = 0) :
    IsFractionalPacking G
      (addTriangleWeight (integralPackingWeight P) w) := by
  have hInt := isFractionalPacking_integralPackingWeight (G := G) hP
  constructor
  · intro t ht
    exact add_nonneg (hInt.nonneg_on ht) (hw.nonneg_on ht)
  · intro e heG
    change fractionalEdgeLoad G
      (fun t ↦ integralPackingWeight P t + w t) e ≤ 1
    rw [fractionalEdgeLoad_add]
    by_cases heP : e ∈ packingPairFinset P
    · rw [hzero e heG heP, add_zero]
      exact hInt.edgeLoad_le_one heG
    · rw [fractionalEdgeLoad_integralPackingWeight_eq_zero_of_not_mem
        G P heP, zero_add]
      exact hw.edgeLoad_le_one heG

lemma fractionalCoveredSize_add_packingWeight
    (G : SimpleGraph α) (P : Finset (Finset α))
    (hPtri : ∀ t ∈ P, G.IsNClique 3 t)
    (w : Finset α → ℝ) :
    fractionalCoveredSize G
      (addTriangleWeight (integralPackingWeight P) w) =
      3 * (P.card : ℝ) + fractionalCoveredSize G w := by
  simp only [fractionalCoveredSize]
  rw [fractionalSize_addTriangleWeight,
    fractionalSize_integralPackingWeight hPtri]
  ring

/-- Exact two-colour splice used in the bad-pattern branch.  The hypotheses
on `wR` and `wB` express precisely the edge reservations that the Section 7
two-blob constructions must provide. -/
theorem exists_twoColorPacking_add_monochromaticPacking
    {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsMonochromaticPacking G P)
    (wR wB : Finset α → ℝ)
    (hwR : IsFractionalPacking G wR)
    (hwB : IsFractionalPacking Gᶜ wB)
    (hzeroR : ∀ e ∈ G.edgeSet,
      e ∈ packingPairFinset (monochromaticRedPart G P) →
        fractionalEdgeLoad G wR e = 0)
    (hzeroB : ∀ e ∈ Gᶜ.edgeSet,
      e ∈ packingPairFinset (monochromaticBluePart G P) →
        fractionalEdgeLoad Gᶜ wB e = 0) :
    ∃ uR uB : Finset α → ℝ,
      IsFractionalPacking G uR ∧ IsFractionalPacking Gᶜ uB ∧
      fractionalCoveredSize G uR + fractionalCoveredSize Gᶜ uB =
        fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB +
          3 * (P.card : ℝ) := by
  let PR := monochromaticRedPart G P
  let PB := monochromaticBluePart G P
  let uR := addTriangleWeight (integralPackingWeight PR) wR
  let uB := addTriangleWeight (integralPackingWeight PB) wB
  have hPR : EdgeDisjoint PR := edgeDisjoint_monochromaticRedPart hP
  have hPB : EdgeDisjoint PB := edgeDisjoint_monochromaticBluePart hP
  have huR : IsFractionalPacking G uR :=
    isFractionalPacking_add_packingWeight_of_zero_load
      G PR hPR wR hwR (by
        intro e heG heP
        exact hzeroR e (SimpleGraph.mem_edgeFinset.mp heG)
          (by simpa only [PR] using heP))
  have huB : IsFractionalPacking Gᶜ uB :=
    isFractionalPacking_add_packingWeight_of_zero_load
      Gᶜ PB hPB wB hwB (by
        intro e heG heP
        apply hzeroB e
        · induction e using Sym2.inductionOn with
          | hf a b =>
              simpa [SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet] using heG
        · simpa only [PB] using heP)
  have hPRtri : ∀ t ∈ PR, G.IsNClique 3 t := by
    intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).2
  have hPBtri : ∀ t ∈ PB, Gᶜ.IsNClique 3 t := by
    intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).2
  have hcard : PR.card + PB.card = P.card :=
    card_monochromaticRedPart_add_bluePart hP
  refine ⟨uR, uB, huR, huB, ?_⟩
  rw [show fractionalCoveredSize G uR =
      3 * (PR.card : ℝ) + fractionalCoveredSize G wR by
        exact fractionalCoveredSize_add_packingWeight G PR hPRtri wR,
    show fractionalCoveredSize Gᶜ uB =
      3 * (PB.card : ℝ) + fractionalCoveredSize Gᶜ wB by
        exact fractionalCoveredSize_add_packingWeight Gᶜ PB hPBtri wB]
  have hcardReal : (PR.card : ℝ) + (PB.card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- A residual two-colour packing which reserves the edges of `P` and whose
integral splice with `P` strictly exceeds the stated upper threshold. -/
def HasReservedResidualPacking
    (G : SimpleGraph α) (P : Finset (Finset α)) (q : ℝ) : Prop :=
  ∃ wR wB : Finset α → ℝ,
    IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
    (∀ e ∈ G.edgeSet,
      e ∈ packingPairFinset (monochromaticRedPart G P) →
        fractionalEdgeLoad G wR e = 0) ∧
    (∀ e ∈ Gᶜ.edgeSet,
      e ∈ packingPairFinset (monochromaticBluePart G P) →
        fractionalEdgeLoad Gᶜ wB e = 0) ∧
    q < fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB +
      3 * (P.card : ℝ)

/-- Conditional pure-blow-up extension endpoint.  All finite pattern and
packing-splice reasoning is discharged here: downstream only has to build a
reserved residual packing for the concrete two triangles supplied by a bad
transversal. -/
theorem isPentagonBlowup_of_upper_of_reserved_badPatterns
    {n : ℕ} {H : SimpleGraph (Fin n)}
    {G : SimpleGraph (Fin (n + 1))} {blob : Fin n → Fin 5} {q : ℝ}
    (hHG : IsInitialVertexExtension H G)
    (hH : IsPentagonBlowup H blob)
    (hupper : FractionalCoveredSizeAtMost G q)
    (hreserved : ∀ v : PentagonOldTransversal blob,
      pentagonBadPattern
        (pentagonAdjacencyPattern G (Fin.last n)
          (fun i ↦ (v i).1.castSucc)) = true →
      ∀ P : Finset (Finset (Fin (n + 1))),
        IsMonochromaticPacking G P → P.card = 2 →
        (∀ t ∈ P, Fin.last n ∈ t) →
        HasReservedResidualPacking G P q) :
    ∃ blob' : Fin (n + 1) → Fin 5, IsPentagonBlowup G blob' := by
  rcases pentagonBlowup_initialExtension_dichotomy hHG hH with
    hblowup | ⟨v, hvbad, P, hP, hPcard, hthrough⟩
  · exact hblowup
  · obtain ⟨wR, wB, hwR, hwB, hzeroR, hzeroB, hstrict⟩ :=
      hreserved v hvbad P hP hPcard hthrough
    obtain ⟨uR, uB, huR, huB, hsize⟩ :=
      exists_twoColorPacking_add_monochromaticPacking
        hP wR wB hwR hwB hzeroR hzeroB
    have hle := hupper uR uB huR huB
    unfold twoColorCoveredSize at hle
    rw [hsize] at hle
    exact (not_lt_of_ge hle hstrict).elim

/-- Before the terminal order, the preceding structural conclusion is an
`IsPentagonExceptional` witness. -/
theorem isPentagonExceptional_of_upper_of_reserved_badPatterns
    {n : ℕ} {H : SimpleGraph (Fin n)}
    {G : SimpleGraph (Fin (n + 1))} {blob : Fin n → Fin 5} {q : ℝ}
    (hn : n < 25)
    (hHG : IsInitialVertexExtension H G)
    (hH : IsPentagonBlowup H blob)
    (hupper : FractionalCoveredSizeAtMost G q)
    (hreserved : ∀ v : PentagonOldTransversal blob,
      pentagonBadPattern
        (pentagonAdjacencyPattern G (Fin.last n)
          (fun i ↦ (v i).1.castSucc)) = true →
      ∀ P : Finset (Finset (Fin (n + 1))),
        IsMonochromaticPacking G P → P.card = 2 →
        (∀ t ∈ P, Fin.last n ∈ t) →
        HasReservedResidualPacking G P q) :
    IsPentagonExceptional G := by
  refine ⟨?_, Or.inl ?_⟩
  · simp only [Fintype.card_fin]
    omega
  · exact isPentagonBlowup_of_upper_of_reserved_badPatterns
      hHG hH hupper hreserved

end

end Erdos76
