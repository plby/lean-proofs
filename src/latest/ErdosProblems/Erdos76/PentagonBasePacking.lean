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
import ErdosProblems.Erdos76.PentagonTableConsequences
import ErdosProblems.Erdos76.LPDuality

/-!
# The ten two-blob packings in a pentagon blow-up

This module starts the assembly of Proposition 7.4.  The construction in
`PentagonTwoBlob` is deliberately stated on the ambient graph, so we first
record its exact vertex support.  This is the fact needed to add the five
red and five blue two-blob weights without creating hidden edge load on an
unrelated blob pair.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

open LPDuality

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The complete-cross Proposition 7.2(a) weight is supported on the union
of its two blobs. -/
lemma proposition72aWeight_eq_zero_of_not_subset_union
    {A B t : Finset α} (hAB : Disjoint A B) (ht : ¬t ⊆ A ∪ B) :
    proposition72aWeight A B t = 0 := by
  classical
  have hF : t ∉ twoOneTriangleFamily A B := by
    intro htF
    exact ht ((mem_powersetCard.mp
      (twoOneTriangleFamily_subset_powersetCard_union hAB htF)).1)
  have hQ : t ∉ twoOneTriangleFamily B A := by
    intro htQ
    have htBA := (mem_powersetCard.mp
      (twoOneTriangleFamily_subset_powersetCard_union hAB.symm htQ)).1
    exact ht (by simpa [union_comm] using htBA)
  simp [proposition72aWeight, addTriangleWeight,
    constantTriangleFamilyWeight, hF, hQ]

/-- Restricting the two-blob weight to actual triangles preserves its
two-blob vertex support. -/
lemma zeroExtend_proposition72aWeight_eq_zero_of_not_subset_union
    {G : SimpleGraph α} {A B t : Finset α} (hAB : Disjoint A B)
    (ht : ¬t ⊆ A ∪ B) :
    zeroExtendTriangleWeight G (proposition72aWeight A B) t = 0 := by
  classical
  unfold zeroExtendTriangleWeight
  split
  · exact proposition72aWeight_eq_zero_of_not_subset_union hAB ht
  · rfl

/-- Consequently an edge outside the two-blob vertex union receives no
load from the restricted Proposition 7.2(a) weight. -/
lemma fractionalEdgeLoad_zeroExtend_proposition72aWeight_eq_zero
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B)
    {e : Sym2 α} (he : ¬e.toFinset ⊆ A ∪ B) :
    fractionalEdgeLoad G
        (zeroExtendTriangleWeight G (proposition72aWeight A B)) e = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  apply zeroExtend_proposition72aWeight_eq_zero_of_not_subset_union hAB
  intro htUnion
  apply he
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv := Finset.mk_mem_sym2_iff.mp (mem_filter.mp ht).2
      intro x hx
      rw [Sym2.toFinset_mk_eq] at hx
      rcases mem_insert.mp hx with rfl | hx
      · exact htUnion huv.1
      · have hxv : x = v := by simpa using hx
        exact hxv ▸ htUnion huv.2

/-- The ambient restricted weight used for one unordered pair of blobs. -/
def pentagonPairWeight
    (G : SimpleGraph α) (blob : α → Fin 5) (i j : Fin 5) :
    Finset α → ℝ :=
  zeroExtendTriangleWeight G
    (proposition72aWeight (pentagonBlobFinset blob i)
      (pentagonBlobFinset blob j))

lemma pentagonPairWeight_comm
    (G : SimpleGraph α) (blob : α → Fin 5) (i j : Fin 5) :
    pentagonPairWeight G blob i j = pentagonPairWeight G blob j i := by
  simp only [pentagonPairWeight, proposition72aWeight_comm]

/-- A pair weight is a fractional packing whenever the two blob sizes are
at least two and differ by at most two.  The cross colour is supplied by the
caller (red for adjacent labels, blue for distance-two labels). -/
theorem isFractionalPacking_pentagonPairWeight
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    (hij : i ≠ j)
    (hi : 2 ≤ (pentagonBlobFinset blob i).card)
    (hj : 2 ≤ (pentagonBlobFinset blob j).card)
    (hijCard : (pentagonBlobFinset blob i).card ≤
      (pentagonBlobFinset blob j).card + 2)
    (hjiCard : (pentagonBlobFinset blob j).card ≤
      (pentagonBlobFinset blob i).card + 2)
    (hcross : ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob j, G.Adj u v) :
    IsFractionalPacking G (pentagonPairWeight G blob i j) := by
  classical
  have hdis := pentagonBlobFinset_disjoint blob hij
  rcases le_total (pentagonBlobFinset blob i).card
      (pentagonBlobFinset blob j).card with hle | hle
  · exact (proposition72a_twoBlobPacking hdis hi hle hjiCard hcross).1
  · rw [pentagonPairWeight_comm]
    exact (proposition72a_twoBlobPacking hdis.symm hj hle hijCard
      (fun v hv u hu ↦ (hcross u hu v hv).symm)).1

/-- An actual edge internal to the first blob receives load exactly one
half from its pair weight. -/
lemma fractionalEdgeLoad_pentagonPairWeight_of_subset_left
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    (hij : i ≠ j)
    (hj : 0 < (pentagonBlobFinset blob j).card)
    (hcross : ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob j, G.Adj u v)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset)
    (he : e.toFinset ⊆ pentagonBlobFinset blob i) :
    fractionalEdgeLoad G (pentagonPairWeight G blob i j) e = 1 / 2 := by
  rw [pentagonPairWeight, fractionalEdgeLoad_zeroExtend le_rfl]
  exact fractionalEdgeLoad_proposition72aWeight_of_subset_left
    (pentagonBlobFinset_disjoint blob hij) hcross hj heG he

/-- Symmetric exact internal load for the second blob. -/
lemma fractionalEdgeLoad_pentagonPairWeight_of_subset_right
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    (hij : i ≠ j)
    (hi : 0 < (pentagonBlobFinset blob i).card)
    (hcross : ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob j, G.Adj u v)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset)
    (he : e.toFinset ⊆ pentagonBlobFinset blob j) :
    fractionalEdgeLoad G (pentagonPairWeight G blob i j) e = 1 / 2 := by
  rw [pentagonPairWeight, fractionalEdgeLoad_zeroExtend le_rfl]
  exact fractionalEdgeLoad_proposition72aWeight_of_subset_right
    (pentagonBlobFinset_disjoint blob hij) hcross hi heG he

/-- An edge whose endpoints are not both in the two participating blobs has
zero load in the pair weight. -/
lemma fractionalEdgeLoad_pentagonPairWeight_eq_zero
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    (hij : i ≠ j) {e : Sym2 α}
    (he : ¬e.toFinset ⊆
      pentagonBlobFinset blob i ∪ pentagonBlobFinset blob j) :
    fractionalEdgeLoad G (pentagonPairWeight G blob i j) e = 0 := by
  exact fractionalEdgeLoad_zeroExtend_proposition72aWeight_eq_zero
    (pentagonBlobFinset_disjoint blob hij) he

/-! ## A uniform edge-capacity description -/

/-- The capacity charged to an edge by one two-blob packing: one half on an
internal edge of either blob, one on a cross edge of the pair, and zero
outside the pair. -/
def pentagonPairEdgeCap (blob : α → Fin 5) (i j : Fin 5)
    (e : Sym2 α) : ℝ :=
  if e.toFinset ⊆ pentagonBlobFinset blob i then 1 / 2
  else if e.toFinset ⊆ pentagonBlobFinset blob j then 1 / 2
  else if e.toFinset ⊆
      pentagonBlobFinset blob i ∪ pentagonBlobFinset blob j then 1
  else 0

/-- Every feasible two-blob weight is bounded by its simple combinatorial
edge capacity. -/
lemma fractionalEdgeLoad_pentagonPairWeight_le_cap
    {G : SimpleGraph α} {blob : α → Fin 5} {i j : Fin 5}
    (hij : i ≠ j)
    (hi : 2 ≤ (pentagonBlobFinset blob i).card)
    (hj : 2 ≤ (pentagonBlobFinset blob j).card)
    (hijCard : (pentagonBlobFinset blob i).card ≤
      (pentagonBlobFinset blob j).card + 2)
    (hjiCard : (pentagonBlobFinset blob j).card ≤
      (pentagonBlobFinset blob i).card + 2)
    (hcross : ∀ u ∈ pentagonBlobFinset blob i,
      ∀ v ∈ pentagonBlobFinset blob j, G.Adj u v)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) :
    fractionalEdgeLoad G (pentagonPairWeight G blob i j) e ≤
      pentagonPairEdgeCap blob i j e := by
  classical
  unfold pentagonPairEdgeCap
  split_ifs with heI heJ heIJ
  · rw [fractionalEdgeLoad_pentagonPairWeight_of_subset_left hij
      (by omega) hcross heG heI]
  · rw [fractionalEdgeLoad_pentagonPairWeight_of_subset_right hij
      (by omega) hcross heG heJ]
  · exact (isFractionalPacking_pentagonPairWeight hij hi hj
      hijCard hjiCard hcross).2 e heG
  · rw [fractionalEdgeLoad_pentagonPairWeight_eq_zero hij heIJ]

/-- The five adjacent blob pairs charge total capacity at most one to every
non-diagonal unordered vertex pair.  This is the finite pentagon incidence
calculation behind the red half of Proposition 7.4. -/
lemma sum_pentagonPairEdgeCap_next_le_one
    (blob : α → Fin 5) {e : Sym2 α} (he : ¬e.IsDiag) :
    (∑ i : Fin 5, pentagonPairEdgeCap blob i (pentagonNext i) e) ≤ 1 := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv : u ≠ v := by
        simpa [Sym2.mk_isDiag_iff] using he
      generalize hu : blob u = iu
      generalize hv : blob v = iv
      fin_cases iu <;> fin_cases iv <;>
        simp [Fin.sum_univ_succ, pentagonPairEdgeCap,
          mem_pentagonBlobFinset, pentagonNext, Sym2.toFinset_mk_eq,
          subset_iff, hu, hv] <;> norm_num

/-- The same capacity calculation for the five distance-two blob pairs,
used for the blue half of Proposition 7.4. -/
lemma sum_pentagonPairEdgeCap_skip_le_one
    (blob : α → Fin 5) {e : Sym2 α} (he : ¬e.IsDiag) :
    (∑ i : Fin 5, pentagonPairEdgeCap blob i (pentagonSkip i) e) ≤ 1 := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv : u ≠ v := by
        simpa [Sym2.mk_isDiag_iff] using he
      generalize hu : blob u = iu
      generalize hv : blob v = iv
      fin_cases iu <;> fin_cases iv <;>
        simp [Fin.sum_univ_succ, pentagonPairEdgeCap,
          mem_pentagonBlobFinset, pentagonSkip, Sym2.toFinset_mk_eq,
          subset_iff, hu, hv] <;> norm_num

/-! ## The red and blue five-pair sums -/

/-- Sum of the five adjacent-blob two-blob weights. -/
def pentagonRedBaseWeight (G : SimpleGraph α) (blob : α → Fin 5) :
    Finset α → ℝ :=
  fun t ↦ ∑ i : Fin 5, pentagonPairWeight G blob i (pentagonNext i) t

/-- Sum of the five distance-two-blob two-blob weights. -/
def pentagonBlueBaseWeight (G : SimpleGraph α) (blob : α → Fin 5) :
    Finset α → ℝ :=
  fun t ↦ ∑ i : Fin 5, pentagonPairWeight G blob i (pentagonSkip i) t

lemma fractionalSize_sum_fin_five (G : SimpleGraph α)
    (w : Fin 5 → Finset α → ℝ) :
    fractionalSize G (fun t ↦ ∑ i : Fin 5, w i t) =
      ∑ i : Fin 5, fractionalSize G (w i) := by
  simp only [fractionalSize]
  rw [sum_comm]

/-- The five adjacent pair weights form a red fractional packing in any
`B₁`-sized pentagon blow-up. -/
theorem isFractionalPacking_pentagonRedBaseWeight
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    IsFractionalPacking G (pentagonRedBaseWeight G blob) := by
  classical
  have hpair : ∀ i : Fin 5,
      IsFractionalPacking G
        (pentagonPairWeight G blob i (pentagonNext i)) := by
    intro i
    exact isFractionalPacking_pentagonPairWeight
      (pentagonNext_ne i).symm
      (pentagonB1Sizes_lower_bound hsizes i)
      (pentagonB1Sizes_lower_bound hsizes (pentagonNext i))
      (pentagonB1Sizes_pair_bound hsizes i (pentagonNext i))
      (pentagonB1Sizes_pair_bound hsizes (pentagonNext i) i)
      (pentagonBlowup_next_cross hG i)
  constructor
  · intro t ht
    exact sum_nonneg fun i _hi ↦ (hpair i).1 t ht
  · intro e heG
    change fractionalEdgeLoad G
      (fun t ↦ ∑ i : Fin 5,
        pentagonPairWeight G blob i (pentagonNext i) t) e ≤ 1
    rw [fractionalEdgeLoad_sum]
    calc
      (∑ i : Fin 5,
          fractionalEdgeLoad G
            (pentagonPairWeight G blob i (pentagonNext i)) e) ≤
          ∑ i : Fin 5,
            pentagonPairEdgeCap blob i (pentagonNext i) e := by
        apply sum_le_sum
        intro i _hi
        exact fractionalEdgeLoad_pentagonPairWeight_le_cap
          (pentagonNext_ne i).symm
          (pentagonB1Sizes_lower_bound hsizes i)
          (pentagonB1Sizes_lower_bound hsizes (pentagonNext i))
          (pentagonB1Sizes_pair_bound hsizes i (pentagonNext i))
          (pentagonB1Sizes_pair_bound hsizes (pentagonNext i) i)
          (pentagonBlowup_next_cross hG i) heG
      _ ≤ 1 := sum_pentagonPairEdgeCap_next_le_one blob
        (G.not_isDiag_of_mem_edgeFinset heG)

/-- The five distance-two pair weights form a blue fractional packing. -/
theorem isFractionalPacking_pentagonBlueBaseWeight
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    IsFractionalPacking Gᶜ (pentagonBlueBaseWeight Gᶜ blob) := by
  classical
  have hpair : ∀ i : Fin 5,
      IsFractionalPacking Gᶜ
        (pentagonPairWeight Gᶜ blob i (pentagonSkip i)) := by
    intro i
    exact isFractionalPacking_pentagonPairWeight
      (pentagonSkip_ne i).symm
      (pentagonB1Sizes_lower_bound hsizes i)
      (pentagonB1Sizes_lower_bound hsizes (pentagonSkip i))
      (pentagonB1Sizes_pair_bound hsizes i (pentagonSkip i))
      (pentagonB1Sizes_pair_bound hsizes (pentagonSkip i) i)
      (pentagonBlowup_skip_cross_compl hG i)
  constructor
  · intro t ht
    exact sum_nonneg fun i _hi ↦ (hpair i).1 t ht
  · intro e heG
    have heND : ¬e.IsDiag := by
      induction e using Sym2.inductionOn with
      | hf u v =>
          have huv : Gᶜ.Adj u v := by
            simpa [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using heG
          simpa [Sym2.mk_isDiag_iff] using huv.ne
    change fractionalEdgeLoad Gᶜ
      (fun t ↦ ∑ i : Fin 5,
        pentagonPairWeight Gᶜ blob i (pentagonSkip i) t) e ≤ 1
    rw [fractionalEdgeLoad_sum]
    calc
      (∑ i : Fin 5,
          fractionalEdgeLoad Gᶜ
            (pentagonPairWeight Gᶜ blob i (pentagonSkip i)) e) ≤
          ∑ i : Fin 5,
            pentagonPairEdgeCap blob i (pentagonSkip i) e := by
        apply sum_le_sum
        intro i _hi
        exact fractionalEdgeLoad_pentagonPairWeight_le_cap
          (pentagonSkip_ne i).symm
          (pentagonB1Sizes_lower_bound hsizes i)
          (pentagonB1Sizes_lower_bound hsizes (pentagonSkip i))
          (pentagonB1Sizes_pair_bound hsizes i (pentagonSkip i))
          (pentagonB1Sizes_pair_bound hsizes (pentagonSkip i) i)
          (pentagonBlowup_skip_cross_compl hG i) heG
      _ ≤ 1 := sum_pentagonPairEdgeCap_skip_le_one blob heND

/-! ## Exact objective value (Proposition 7.4(a)) -/

lemma sum_comp_pentagonNext (f : Fin 5 → ℝ) :
    (∑ i : Fin 5, f (pentagonNext i)) = ∑ i : Fin 5, f i := by
  simp [Fin.sum_univ_succ, pentagonNext]
  ring

lemma sum_comp_pentagonSkip (f : Fin 5 → ℝ) :
    (∑ i : Fin 5, f (pentagonSkip i)) = ∑ i : Fin 5, f i := by
  simp [Fin.sum_univ_succ, pentagonSkip]
  ring

/-- Exact total triangle weight in the red five-pair sum. -/
lemma fractionalSize_pentagonRedBaseWeight
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    fractionalSize G (pentagonRedBaseWeight G blob) =
      ∑ i : Fin 5, ((blobPairFinset G
        (pentagonBlobFinset blob i)).card : ℝ) := by
  classical
  rw [show pentagonRedBaseWeight G blob =
      (fun t ↦ ∑ i : Fin 5,
        pentagonPairWeight G blob i (pentagonNext i) t) by rfl,
    fractionalSize_sum_fin_five]
  calc
    (∑ i : Fin 5,
        fractionalSize G
          (pentagonPairWeight G blob i (pentagonNext i))) =
        ∑ i : Fin 5,
          (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2 +
            ((blobPairFinset G
              (pentagonBlobFinset blob (pentagonNext i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _hi
      exact fractionalSize_proposition72a_restricted
        (pentagonBlobFinset_disjoint blob (pentagonNext_ne i).symm)
        (by have h := pentagonB1Sizes_lower_bound hsizes i; omega)
        (by
          have h := pentagonB1Sizes_lower_bound hsizes (pentagonNext i)
          omega)
        (pentagonBlowup_next_cross hG i)
    _ = ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
      rw [sum_add_distrib]
      rw [sum_comp_pentagonNext (fun i ↦
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) / 2)]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

/-- Exact total triangle weight in the blue five-pair sum. -/
lemma fractionalSize_pentagonBlueBaseWeight
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    fractionalSize Gᶜ (pentagonBlueBaseWeight Gᶜ blob) =
      ∑ i : Fin 5, ((blobPairFinset Gᶜ
        (pentagonBlobFinset blob i)).card : ℝ) := by
  classical
  rw [show pentagonBlueBaseWeight Gᶜ blob =
      (fun t ↦ ∑ i : Fin 5,
        pentagonPairWeight Gᶜ blob i (pentagonSkip i) t) by rfl,
    fractionalSize_sum_fin_five]
  calc
    (∑ i : Fin 5,
        fractionalSize Gᶜ
          (pentagonPairWeight Gᶜ blob i (pentagonSkip i))) =
        ∑ i : Fin 5,
          (((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ) / 2 +
            ((blobPairFinset Gᶜ
              (pentagonBlobFinset blob (pentagonSkip i))).card : ℝ) / 2) := by
      apply sum_congr rfl
      intro i _hi
      exact fractionalSize_proposition72a_restricted
        (pentagonBlobFinset_disjoint blob (pentagonSkip_ne i).symm)
        (by have h := pentagonB1Sizes_lower_bound hsizes i; omega)
        (by
          have h := pentagonB1Sizes_lower_bound hsizes (pentagonSkip i)
          omega)
        (pentagonBlowup_skip_cross_compl hG i)
    _ = ∑ i : Fin 5,
        ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ) := by
      rw [sum_add_distrib]
      rw [sum_comp_pentagonSkip (fun i ↦
        ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ) / 2)]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring

private lemma isClique_compl_iff_not_isClique_of_card_two
    (G : SimpleGraph α) {p : Finset α} (hp : p.card = 2) :
    Gᶜ.IsClique (p : Set α) ↔ ¬G.IsClique (p : Set α) := by
  classical
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hp
  rw [SimpleGraph.isClique_compl]
  simp only [coe_insert, coe_singleton]
  constructor
  · intro hind hclique
    exact hind (by simp) (by simp) huv
      ((SimpleGraph.isClique_pair.mp hclique) huv)
  · intro hnclique
    have hnuv : ¬G.Adj u v := by
      intro hadj
      exact hnclique (SimpleGraph.isClique_pair.mpr fun _hne ↦ hadj)
    intro a ha b hb hab
    have ha' : a = u ∨ a = v := by simpa using ha
    have hb' : b = u ∨ b = v := by simpa using hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (hab rfl).elim
    · exact hnuv
    · exact fun h ↦ hnuv h.symm
    · exact (hab rfl).elim

/-- The actual red and blue internal pairs partition all unordered pairs
inside a blob. -/
lemma card_blobPairFinset_add_compl
    (G : SimpleGraph α) (A : Finset α) :
    (blobPairFinset G A).card + (blobPairFinset Gᶜ A).card = A.card.choose 2 := by
  classical
  have hdis : Disjoint (blobPairFinset G A) (blobPairFinset Gᶜ A) := by
    apply disjoint_left.mpr
    intro p hpG hpB
    have hpCard : p.card = 2 := (mem_blobPairFinset.mp hpG).2.1
    exact (isClique_compl_iff_not_isClique_of_card_two G hpCard).mp
      (mem_blobPairFinset.mp hpB).2.2 (mem_blobPairFinset.mp hpG).2.2
  have hunion : blobPairFinset G A ∪ blobPairFinset Gᶜ A =
      A.powersetCard 2 := by
    ext p
    constructor
    · intro hp
      rcases mem_union.mp hp with hpG | hpB
      · exact mem_powersetCard.mpr
          ⟨(mem_blobPairFinset.mp hpG).1,
            (mem_blobPairFinset.mp hpG).2.1⟩
      · exact mem_powersetCard.mpr
          ⟨(mem_blobPairFinset.mp hpB).1,
            (mem_blobPairFinset.mp hpB).2.1⟩
    · intro hp
      rcases mem_powersetCard.mp hp with ⟨hpA, hpCard⟩
      by_cases hpG : G.IsClique (p : Set α)
      · exact mem_union_left _ (mem_blobPairFinset.mpr ⟨hpA, hpCard, hpG⟩)
      · exact mem_union_right _ (mem_blobPairFinset.mpr
          ⟨hpA, hpCard,
            (isClique_compl_iff_not_isClique_of_card_two G hpCard).mpr hpG⟩)
  rw [← card_union_of_disjoint hdis, hunion, card_powersetCard]

/-- Proposition 7.4(a), in the exact objective normalization used by the
stability induction. -/
theorem pentagonBlowup_basePacking
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    IsFractionalPacking G (pentagonRedBaseWeight G blob) ∧
      IsFractionalPacking Gᶜ (pentagonBlueBaseWeight Gᶜ blob) ∧
      fractionalCoveredSize G (pentagonRedBaseWeight G blob) +
          fractionalCoveredSize Gᶜ (pentagonBlueBaseWeight Gᶜ blob) =
        3 * ∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ) := by
  classical
  refine ⟨isFractionalPacking_pentagonRedBaseWeight hG hsizes,
    isFractionalPacking_pentagonBlueBaseWeight hG hsizes, ?_⟩
  rw [fractionalCoveredSize, fractionalCoveredSize,
    fractionalSize_pentagonRedBaseWeight hG hsizes,
    fractionalSize_pentagonBlueBaseWeight hG hsizes]
  push_cast
  calc
    3 * (∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
        3 * (∑ i : Fin 5,
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) =
      3 * ((∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
        ∑ i : Fin 5,
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) := by ring
    _ = 3 * ∑ i : Fin 5,
        (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) +
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) := by
      rw [sum_add_distrib]
    _ = 3 * ∑ i : Fin 5,
        ((pentagonBlobFinset blob i).card.choose 2 : ℝ) := by
      apply congrArg (fun z : ℝ ↦ 3 * z)
      apply sum_congr rfl
      intro i _hi
      exact_mod_cast card_blobPairFinset_add_compl G
        (pentagonBlobFinset blob i)

/-! ## The matching edge-cover upper bound

Every monochromatic triangle in a pentagon blow-up contains an edge internal
to one of the five blobs: after contracting the blobs, the red and blue
cross-edge graphs are respectively a five-cycle and its complement, and both
are triangle-free.  Giving every internal edge dual weight one therefore
proves the reverse inequality in Proposition 7.4(a).
-/

/-- The graph-independent dual weight which charges one for every blob
containing both endpoints of the edge.  For a nondiagonal pair at most one
summand can be nonzero, but the summed definition makes the objective
calculation particularly transparent. -/
def pentagonInternalEdgeCover (blob : α → Fin 5) (e : Sym2 α) : ℝ :=
  ∑ i : Fin 5,
    if e.toFinset ⊆ pentagonBlobFinset blob i then 1 else 0

lemma pentagonInternalEdgeCover_nonneg (blob : α → Fin 5) (e : Sym2 α) :
    0 ≤ pentagonInternalEdgeCover blob e := by
  classical
  unfold pentagonInternalEdgeCover
  exact sum_nonneg fun i _hi ↦ by
    split_ifs <;> norm_num

/-- A red triangle in a pentagon blow-up has an internal blob edge. -/
lemma pentagonBlowup_redTriangle_has_internal_edge
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) {t : Finset α}
    (ht : G.IsNClique 3 t) :
    ∃ e : Sym2 α, e ∈ G.edgeSet ∧ e ∈ t.sym2 ∧
      ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
  have habAdj : G.Adj a b :=
    ht.isClique (by simp) (by simp) hab
  have hacAdj : G.Adj a c :=
    ht.isClique (by simp) (by simp) hac
  have hbcAdj : G.Adj b c :=
    ht.isClique (by simp) (by simp) hbc
  by_cases habBlob : blob a = blob b
  · refine ⟨s(a, b), ?_, by simp, blob a, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using habAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, habBlob]
  by_cases hacBlob : blob a = blob c
  · refine ⟨s(a, c), ?_, by simp, blob a, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using hacAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, hacBlob]
  by_cases hbcBlob : blob b = blob c
  · refine ⟨s(b, c), ?_, by simp, blob b, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using hbcAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, hbcBlob]
  have habCycle : (SimpleGraph.cycleGraph 5).Adj (blob a) (blob b) :=
    (hG.2 habBlob).mp habAdj
  have hacCycle : (SimpleGraph.cycleGraph 5).Adj (blob a) (blob c) :=
    (hG.2 hacBlob).mp hacAdj
  have hbcCycle : (SimpleGraph.cycleGraph 5).Adj (blob b) (blob c) :=
    (hG.2 hbcBlob).mp hbcAdj
  generalize haLabel : blob a = ia at habCycle hacCycle
  generalize hbLabel : blob b = ib at habCycle hbcCycle
  generalize hcLabel : blob c = ic at hacCycle hbcCycle
  fin_cases ia <;> fin_cases ib <;> fin_cases ic <;>
    simp [cycleGraph5_adj_iff_next, pentagonNext] at habCycle hacCycle hbcCycle

/-- A blue triangle in a pentagon blow-up has an internal blob edge. -/
lemma pentagonBlowup_blueTriangle_has_internal_edge
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) {t : Finset α}
    (ht : Gᶜ.IsNClique 3 t) :
    ∃ e : Sym2 α, e ∈ Gᶜ.edgeSet ∧ e ∈ t.sym2 ∧
      ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
  have habAdj : Gᶜ.Adj a b :=
    ht.isClique (by simp) (by simp) hab
  have hacAdj : Gᶜ.Adj a c :=
    ht.isClique (by simp) (by simp) hac
  have hbcAdj : Gᶜ.Adj b c :=
    ht.isClique (by simp) (by simp) hbc
  by_cases habBlob : blob a = blob b
  · refine ⟨s(a, b), ?_, by simp, blob a, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using habAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, habBlob]
  by_cases hacBlob : blob a = blob c
  · refine ⟨s(a, c), ?_, by simp, blob a, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using hacAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, hacBlob]
  by_cases hbcBlob : blob b = blob c
  · refine ⟨s(b, c), ?_, by simp, blob b, ?_⟩
    · simpa [SimpleGraph.mem_edgeSet] using hbcAdj
    · simp [Sym2.toFinset_mk_eq, subset_iff, hbcBlob]
  have habCycle : (SimpleGraph.cycleGraph 5)ᶜ.Adj (blob a) (blob b) := by
    rw [SimpleGraph.compl_adj]
    exact ⟨habBlob, fun h ↦ habAdj.2 ((hG.2 habBlob).mpr h)⟩
  have hacCycle : (SimpleGraph.cycleGraph 5)ᶜ.Adj (blob a) (blob c) := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hacBlob, fun h ↦ hacAdj.2 ((hG.2 hacBlob).mpr h)⟩
  have hbcCycle : (SimpleGraph.cycleGraph 5)ᶜ.Adj (blob b) (blob c) := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hbcBlob, fun h ↦ hbcAdj.2 ((hG.2 hbcBlob).mpr h)⟩
  rw [cycleGraph5_compl_adj_iff_skip] at habCycle hacCycle hbcCycle
  generalize haLabel : blob a = ia at habCycle hacCycle
  generalize hbLabel : blob b = ib at habCycle hbcCycle
  generalize hcLabel : blob c = ic at hacCycle hbcCycle
  fin_cases ia <;> fin_cases ib <;> fin_cases ic <;>
    simp [pentagonSkip] at habCycle hacCycle hbcCycle

/-- If every graph triangle has an internal blob edge, the internal-edge
weight is a feasible fractional edge cover.  Stating this with an atomic
graph parameter also keeps the proof independent of the particular
decidability instance used to form a complement graph. -/
lemma isFractionalEdgeCover_pentagonInternal_of_triangles
    {H : SimpleGraph α} {blob : α → Fin 5}
    (htri : ∀ {t : Finset α}, H.IsNClique 3 t →
      ∃ e : Sym2 α, e ∈ H.edgeSet ∧ e ∈ t.sym2 ∧
        ∃ i : Fin 5, e.toFinset ⊆ pentagonBlobFinset blob i) :
    IsFractionalEdgeCover H (pentagonInternalEdgeCover blob) := by
  classical
  constructor
  · intro e _he
    exact pentagonInternalEdgeCover_nonneg blob e
  · intro t ht
    obtain ⟨e, heG, het, i, hei⟩ :=
      htri (SimpleGraph.mem_cliqueFinset_iff.mp ht)
    calc
      1 ≤ pentagonInternalEdgeCover blob e := by
        unfold pentagonInternalEdgeCover
        let f : Fin 5 → ℝ := fun j ↦
          if e.toFinset ⊆ pentagonBlobFinset blob j then 1 else 0
        change 1 ≤ ∑ j : Fin 5, f j
        have hfi : f i = 1 := by simp [f, hei]
        rw [← hfi]
        apply single_le_sum
        · intro j _hj
          simp only [f]
          split_ifs <;> norm_num
        · exact mem_univ i
      _ ≤ ∑ f ∈ H.edgeFinset.filter (fun f ↦ f ∈ t.sym2),
          pentagonInternalEdgeCover blob f := by
        apply single_le_sum
        · intro f _hf
          exact pentagonInternalEdgeCover_nonneg blob f
        · exact mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr heG, het⟩

/-- The internal-edge dual weight covers every red triangle of a pentagon
blow-up. -/
lemma isFractionalEdgeCover_pentagonInternal_red
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) :
    IsFractionalEdgeCover G (pentagonInternalEdgeCover blob) := by
  apply isFractionalEdgeCover_pentagonInternal_of_triangles
  exact fun ht ↦ pentagonBlowup_redTriangle_has_internal_edge hG ht

/-- The same internal-edge dual weight covers every blue triangle. -/
lemma isFractionalEdgeCover_pentagonInternal_blue
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) :
    IsFractionalEdgeCover Gᶜ (pentagonInternalEdgeCover blob) := by
  apply isFractionalEdgeCover_pentagonInternal_of_triangles
  exact fun ht ↦ pentagonBlowup_blueTriangle_has_internal_edge hG ht

/-- Passing from unordered graph edges to their two-element endpoint sets
identifies the internal edges with `blobPairFinset`. -/
lemma card_filter_edgeFinset_internal_eq_blobPairFinset
    (G : SimpleGraph α) (A : Finset α) :
    (G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ A)).card =
      (blobPairFinset G A).card := by
  classical
  let E := G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ A)
  have hInjective : Function.Injective (Sym2.toFinset : Sym2 α → Finset α) := by
    intro e f hef
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]
  have hImage : E.image Sym2.toFinset = blobPairFinset G A := by
    ext p
    constructor
    · intro hp
      obtain ⟨e, heE, rfl⟩ := mem_image.mp hp
      have heG : e ∈ G.edgeFinset := (mem_filter.mp heE).1
      refine mem_blobPairFinset.mpr ⟨(mem_filter.mp heE).2,
        Sym2.card_toFinset_of_not_isDiag e
          (G.not_isDiag_of_mem_edgeFinset heG), ?_⟩
      induction e using Sym2.inductionOn with
      | hf u v =>
          rw [Sym2.toFinset_mk_eq]
          simp only [Finset.coe_insert, Finset.coe_singleton]
          apply SimpleGraph.isClique_pair.mpr
          intro huv
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
    · intro hp
      rcases mem_blobPairFinset.mp hp with ⟨hpA, hpCard, hpClique⟩
      obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hpCard
      refine mem_image.mpr ⟨s(u, v), ?_, Sym2.toFinset_mk_eq⟩
      rw [mem_filter]
      constructor
      · have hpCliqueSet : G.IsClique ({u, v} : Set α) := by
          simpa only [Finset.coe_insert, Finset.coe_singleton] using hpClique
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          (SimpleGraph.isClique_pair.mp hpCliqueSet huv)
      · simpa [Sym2.toFinset_mk_eq] using hpA
  calc
    E.card = (E.image Sym2.toFinset).card :=
      (card_image_of_injective E hInjective).symm
    _ = (blobPairFinset G A).card := congrArg card hImage

/-- The objective of the internal-edge cover is exactly the number of
actual graph edges internal to the five blobs. -/
lemma sum_pentagonInternalEdgeCover
    (G : SimpleGraph α) (blob : α → Fin 5) :
    (∑ e ∈ G.edgeFinset, pentagonInternalEdgeCover blob e) =
      ∑ i : Fin 5,
        ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
  classical
  simp only [pentagonInternalEdgeCover]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _hi
  calc
    (∑ e ∈ G.edgeFinset,
        if e.toFinset ⊆ pentagonBlobFinset blob i then 1 else 0) =
      ∑ e ∈ G.edgeFinset.filter
          (fun e ↦ e.toFinset ⊆ pentagonBlobFinset blob i), (1 : ℝ) := by
        rw [sum_filter]
    _ = ((G.edgeFinset.filter
          (fun e ↦ e.toFinset ⊆ pentagonBlobFinset blob i)).card : ℝ) := by
        simp
    _ = ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
        exact_mod_cast card_filter_edgeFinset_internal_eq_blobPairFinset G
          (pentagonBlobFinset blob i)

/-- Weak duality bounds every red fractional packing by the red internal
edge count. -/
theorem fractionalSize_pentagonBlowup_le_internal_red
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) :
    fractionalSize G w ≤ ∑ i : Fin 5,
      ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) := by
  rw [← sum_pentagonInternalEdgeCover G blob]
  exact fractionalSize_le_edgeCover_sum G w
    (pentagonInternalEdgeCover blob) hw
    (isFractionalEdgeCover_pentagonInternal_red hG)

/-- The analogous weak-duality bound for blue fractional packings. -/
theorem fractionalSize_pentagonBlowup_le_internal_blue
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob) {w : Finset α → ℝ}
    (hw : IsFractionalPacking Gᶜ w) :
    fractionalSize Gᶜ w ≤ ∑ i : Fin 5,
      ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ) := by
  rw [← sum_pentagonInternalEdgeCover Gᶜ blob]
  exact fractionalSize_le_edgeCover_sum Gᶜ w
    (pentagonInternalEdgeCover blob) hw
    (isFractionalEdgeCover_pentagonInternal_blue hG)

/-- The reverse inequality in Proposition 7.4(a): no two-colour fractional
packing of a pentagon blow-up can exceed three times the total number of
internal vertex pairs. -/
theorem twoColorCoveredSize_pentagonBlowup_le
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    {wR wB : Finset α → ℝ}
    (hwR : IsFractionalPacking G wR)
    (hwB : IsFractionalPacking Gᶜ wB) :
    fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB ≤
      3 * ∑ i : Fin 5,
        ((pentagonBlobFinset blob i).card.choose 2 : ℕ) := by
  rw [fractionalCoveredSize, fractionalCoveredSize]
  push_cast
  have hR := fractionalSize_pentagonBlowup_le_internal_red hG hwR
  have hB := fractionalSize_pentagonBlowup_le_internal_blue hG hwB
  calc
    3 * fractionalSize G wR + 3 * fractionalSize Gᶜ wB ≤
        3 * (∑ i : Fin 5,
          ((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ)) +
        3 * (∑ i : Fin 5,
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) := by
      gcongr
    _ = 3 * ∑ i : Fin 5,
        (((blobPairFinset G (pentagonBlobFinset blob i)).card : ℝ) +
          ((blobPairFinset Gᶜ (pentagonBlobFinset blob i)).card : ℝ)) := by
      rw [sum_add_distrib]
      ring
    _ = 3 * ∑ i : Fin 5,
        ((pentagonBlobFinset blob i).card.choose 2 : ℝ) := by
      apply congrArg (fun z : ℝ ↦ 3 * z)
      apply sum_congr rfl
      intro i _hi
      exact_mod_cast card_blobPairFinset_add_compl G
        (pentagonBlobFinset blob i)

/-- Proposition 7.4(a) as an exact optimum statement: the explicit ten
two-blob packings attain the universal dual upper bound. -/
theorem pentagonBlowup_basePacking_optimal
    {G : SimpleGraph α} {blob : α → Fin 5}
    (hG : IsPentagonBlowup G blob)
    (hsizes : PentagonB1Sizes
      (fun i ↦ (pentagonBlobFinset blob i).card)) :
    IsFractionalPacking G (pentagonRedBaseWeight G blob) ∧
      IsFractionalPacking Gᶜ (pentagonBlueBaseWeight Gᶜ blob) ∧
      fractionalCoveredSize G (pentagonRedBaseWeight G blob) +
          fractionalCoveredSize Gᶜ (pentagonBlueBaseWeight Gᶜ blob) =
        3 * ∑ i : Fin 5,
          ((pentagonBlobFinset blob i).card.choose 2 : ℕ) ∧
      ∀ wR wB : Finset α → ℝ,
        IsFractionalPacking G wR → IsFractionalPacking Gᶜ wB →
        fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB ≤
          fractionalCoveredSize G (pentagonRedBaseWeight G blob) +
            fractionalCoveredSize Gᶜ (pentagonBlueBaseWeight Gᶜ blob) := by
  rcases pentagonBlowup_basePacking hG hsizes with ⟨hR, hB, hsize⟩
  refine ⟨hR, hB, hsize, ?_⟩
  intro wR wB hwR hwB
  rw [hsize]
  exact twoColorCoveredSize_pentagonBlowup_le hG hwR hwB

end

end Erdos76
