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
import ErdosProblems.Erdos76.GruslysLetzter

/-!
# Fractional triangle packings between two blobs

This module begins the human Section 7 argument of Gruslys--Letzter.  The
family `twoOneTriangleFamily A B` consists of triples with two vertices in
`A` and one in `B`.  Giving every such triple weight `1/(2|B|)` covers every
pair in `A` to weight `1/2`.  Adding the construction with the roles of the
two blobs reversed proves Proposition 7.2(a).
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Triples having two vertices in `A` and one in `B`, presented as the
union of the complete clique stars with attachment vertex in `B`. -/
def twoOneTriangleFamily (A B : Finset α) : Finset (Finset α) :=
  B.biUnion fun z ↦ cliqueStarTriangleFamily z A

lemma mem_twoOneTriangleFamily_iff {A B : Finset α} {t : Finset α} :
    t ∈ twoOneTriangleFamily A B ↔
      ∃ z ∈ B, ∃ p ∈ A.powersetCard 2, t = insert z p := by
  classical
  simp only [twoOneTriangleFamily, mem_biUnion, cliqueStarTriangleFamily,
    mem_image]
  aesop

lemma twoOneTriangleFamily_subset_powersetCard_union
    {A B : Finset α} (hAB : Disjoint A B) :
    twoOneTriangleFamily A B ⊆ (A ∪ B).powersetCard 3 := by
  classical
  intro t ht
  obtain ⟨z, hzB, p, hp, rfl⟩ := mem_twoOneTriangleFamily_iff.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  apply mem_powersetCard.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hxp
    · exact mem_union_right A hzB
    · exact mem_union_left B (hpA hxp)
  · have hzp : z ∉ p := by
      intro hzp
      exact Finset.disjoint_left.mp hAB (hpA hzp) hzB
    simp [hzp, hpcard]

lemma twoOneTriangleFamily_inter_base_card
    {A B : Finset α} (hAB : Disjoint A B)
    {t : Finset α} (ht : t ∈ twoOneTriangleFamily A B) :
    (t ∩ A).card = 2 := by
  classical
  obtain ⟨z, hzB, p, hp, rfl⟩ := mem_twoOneTriangleFamily_iff.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  have hzA : z ∉ A := fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB
  have hpinter : p ∩ A = p := inter_eq_left.mpr hpA
  simp [hzA, hpinter, hpcard]

lemma twoOneTriangleFamily_inter_attachment_card
    {A B : Finset α} (hAB : Disjoint A B)
    {t : Finset α} (ht : t ∈ twoOneTriangleFamily A B) :
    (t ∩ B).card = 1 := by
  classical
  obtain ⟨z, hzB, p, hp, rfl⟩ := mem_twoOneTriangleFamily_iff.mp ht
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hpB : Disjoint p B := hAB.mono_left hpA
  have hpinter : p ∩ B = ∅ := disjoint_iff_inter_eq_empty.mp hpB
  simp [hzB, hpinter]

lemma twoOneTriangleFamily_pairwiseDisjoint_stars
    {A B : Finset α} (hAB : Disjoint A B) :
    (B : Set α).PairwiseDisjoint fun z ↦ cliqueStarTriangleFamily z A := by
  classical
  intro z hzB w hwB hzw
  apply Finset.disjoint_left.mpr
  intro t htz htw
  obtain ⟨p, hp, htp⟩ := mem_image.mp htz
  obtain ⟨q, hq, htq⟩ := mem_image.mp htw
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hqA : q ⊆ A := (mem_powersetCard.mp hq).1
  have hwA : w ∉ A := fun hwA ↦ Finset.disjoint_left.mp hAB hwA hwB
  have hwp : w ∉ p := fun hwp ↦ hwA (hpA hwp)
  have hwt : w ∈ t := by rw [← htq]; simp
  rw [← htp] at hwt
  have hwz : w = z := by
    rcases mem_insert.mp hwt with hwz | hwq'
    · exact hwz
    · exact (hwp hwq').elim
  exact hzw hwz.symm

lemma card_twoOneTriangleFamily
    {A B : Finset α} (hAB : Disjoint A B) :
    (twoOneTriangleFamily A B).card = B.card * A.card.choose 2 := by
  classical
  unfold twoOneTriangleFamily
  rw [card_biUnion (twoOneTriangleFamily_pairwiseDisjoint_stars hAB)]
  calc
    (∑ z ∈ B, (cliqueStarTriangleFamily z A).card) =
        ∑ _z ∈ B, A.card.choose 2 := by
      apply sum_congr rfl
      intro z hzB
      rw [card_cliqueStarTriangleFamily]
      exact fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB
    _ = B.card * A.card.choose 2 := by simp

/-- Every member of a two-one family is a graph triangle when both blobs
are cliques and all cross pairs are graph edges. -/
lemma twoOneTriangleFamily_isNClique
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B)
    (hA : G.IsClique (A : Set α))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∀ t ∈ twoOneTriangleFamily A B, G.IsNClique 3 t := by
  classical
  intro t ht
  obtain ⟨z, hzB, p, hp, rfl⟩ := mem_twoOneTriangleFamily_iff.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hpcard
  have haA : a ∈ A := hpA (by simp)
  have hbA : b ∈ A := hpA (by simp)
  have hzA : z ∉ A := fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB
  have hza : z ≠ a := fun h ↦ hzA (h ▸ haA)
  have hzb : z ≠ b := fun h ↦ hzA (h ▸ hbA)
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, by simp [hza, hzb, hab]⟩
  simpa [hza, hzb, hab] using
    And.intro (hA haA hbA hab)
      (And.intro (hcross a haA z hzB).symm
        (hcross b hbA z hzB).symm)

/-- Exact load formula for a constant-weight finite triangle family. -/
lemma fractionalEdgeLoad_constantTriangleFamilyWeight
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ}
    (htri : ∀ t ∈ F, G.IsNClique 3 t) (e : Sym2 α) :
    fractionalEdgeLoad G (constantTriangleFamilyWeight F d) e =
      (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) * (d : ℝ)⁻¹ := by
  classical
  unfold fractionalEdgeLoad
  rw [← sum_subset
    (s₁ := F.filter fun t ↦ e ∈ t.sym2)
    (s₂ := (G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2)]
  · calc
      (∑ t ∈ F with e ∈ t.sym2, constantTriangleFamilyWeight F d t) =
          ∑ _t ∈ F.filter (fun t ↦ e ∈ t.sym2), (d : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro t ht
        simp [constantTriangleFamilyWeight, (mem_filter.mp ht).1]
      _ = (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) *
          (d : ℝ)⁻¹ := by simp
  · intro t ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    exact mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr (htri t htF), het⟩
  · intro t htG htF
    have htNot : t ∉ F := by
      intro ht
      exact htF (mem_filter.mpr ⟨ht, (mem_filter.mp htG).2⟩)
    simp [constantTriangleFamilyWeight, htNot]

/-- The exact constant-family load formula only needs the members incident
with the edge under consideration to be graph triangles.  This form is what
allows a complete two-blob packing to be restricted to a graph whose edges
inside the blobs are arbitrary. -/
lemma fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ} {e : Sym2 α}
    (htri : ∀ t ∈ F, e ∈ t.sym2 → G.IsNClique 3 t) :
    fractionalEdgeLoad G (constantTriangleFamilyWeight F d) e =
      (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) * (d : ℝ)⁻¹ := by
  classical
  unfold fractionalEdgeLoad
  rw [← sum_subset
    (s₁ := F.filter fun t ↦ e ∈ t.sym2)
    (s₂ := (G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2)]
  · calc
      (∑ t ∈ F with e ∈ t.sym2, constantTriangleFamilyWeight F d t) =
          ∑ _t ∈ F.filter (fun t ↦ e ∈ t.sym2), (d : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro t ht
        simp [constantTriangleFamilyWeight, (mem_filter.mp ht).1]
      _ = (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) *
          (d : ℝ)⁻¹ := by simp
  · intro t ht
    rcases mem_filter.mp ht with ⟨htF, het⟩
    exact mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr (htri t htF het), het⟩
  · intro t htG htF
    have htNot : t ∉ F := by
      intro ht
      exact htF (mem_filter.mpr ⟨ht, (mem_filter.mp htG).2⟩)
    simp [constantTriangleFamilyWeight, htNot]

/-- Restrict a packing of a supergraph to the triangles of a subgraph.
Loads can only decrease because all weights are nonnegative. -/
lemma IsFractionalPacking.restrictToSubgraph {G K : SimpleGraph α}
    (hGK : G ≤ K) {w : Finset α → ℝ} (hw : IsFractionalPacking K w) :
    IsFractionalPacking G (zeroExtendTriangleWeight G w) := by
  classical
  constructor
  · intro t htG
    rw [zeroExtendTriangleWeight_of_mem htG]
    exact hw.nonneg_on (SimpleGraph.cliqueFinset_mono K hGK htG)
  · intro e heG
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl]
    apply (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
      (hw.edgeLoad_le_one (SimpleGraph.edgeFinset_mono hGK heG))
    · intro t ht
      rcases mem_filter.mp ht with ⟨htG, het⟩
      exact mem_filter.mpr
        ⟨SimpleGraph.cliqueFinset_mono K hGK htG, het⟩
    · intro t htK _htG
      exact hw.nonneg_on (mem_filter.mp htK).1

private lemma card_filter_cliqueStar_le_one_of_edge_subset_base
    {z : α} {A : Finset α} (hzA : z ∉ A) (e : Sym2 α)
    (hecard : e.toFinset.card = 2) (heA : e.toFinset ⊆ A) :
    ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro t ht u hu
  rcases mem_filter.mp ht with ⟨htStar, het⟩
  rcases mem_filter.mp hu with ⟨huStar, heu⟩
  obtain ⟨p, hp, htp⟩ := mem_image.mp htStar
  obtain ⟨q, hq, huq⟩ := mem_image.mp huStar
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hqA : q ⊆ A := (mem_powersetCard.mp hq).1
  have hpcard : p.card = 2 := (mem_powersetCard.mp hp).2
  have hqcard : q.card = 2 := (mem_powersetCard.mp hq).2
  have heP : e.toFinset ⊆ p := by
    intro x hxe
    have hxt : x ∈ t := (mem_sym2_iff.mp het) x (by simpa using hxe)
    rw [← htp] at hxt
    rcases mem_insert.mp hxt with hxz | hxp
    · subst x
      exact (hzA (heA hxe)).elim
    · exact hxp
  have heQ : e.toFinset ⊆ q := by
    intro x hxe
    have hxu : x ∈ u := (mem_sym2_iff.mp heu) x (by simpa using hxe)
    rw [← huq] at hxu
    rcases mem_insert.mp hxu with hxz | hxq
    · subst x
      exact (hzA (heA hxe)).elim
    · exact hxq
  have hpEq : p = e.toFinset :=
    (eq_of_subset_of_card_le heP (by omega)).symm
  have hqEq : q = e.toFinset :=
    (eq_of_subset_of_card_le heQ (by omega)).symm
  rw [← htp, ← huq, hpEq, hqEq]

lemma card_filter_twoOne_le_attachment_of_edge_subset_base
    {A B : Finset α} (hAB : Disjoint A B) (e : Sym2 α)
    (hecard : e.toFinset.card = 2) (heA : e.toFinset ⊆ A) :
    ((twoOneTriangleFamily A B).filter fun t ↦ e ∈ t.sym2).card ≤ B.card := by
  classical
  rw [twoOneTriangleFamily, filter_biUnion]
  calc
    (B.biUnion fun z ↦
        (cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤
        ∑ z ∈ B,
          ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card :=
      card_biUnion_le
    _ ≤ ∑ _z ∈ B, 1 := by
      apply sum_le_sum
      intro z hzB
      exact card_filter_cliqueStar_le_one_of_edge_subset_base
        (fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB) e hecard heA
    _ = B.card := by simp

lemma filter_twoOne_of_edge_subset_base
    {A B : Finset α} (hAB : Disjoint A B) (e : Sym2 α)
    (hecard : e.toFinset.card = 2) (heA : e.toFinset ⊆ A) :
    (twoOneTriangleFamily A B).filter (fun t ↦ e ∈ t.sym2) =
      B.image (fun z ↦ insert z e.toFinset) := by
  classical
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htFamily, het⟩
    obtain ⟨z, hzB, p, hp, htp⟩ := mem_twoOneTriangleFamily_iff.mp htFamily
    have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
    have hpcard : p.card = 2 := (mem_powersetCard.mp hp).2
    have heP : e.toFinset ⊆ p := by
      intro x hxe
      have hxt : x ∈ t := (mem_sym2_iff.mp het) x (by simpa using hxe)
      rw [htp] at hxt
      rcases mem_insert.mp hxt with hxz | hxp
      · subst x
        exact (Finset.disjoint_left.mp hAB (heA hxe) hzB).elim
      · exact hxp
    have hpEq : p = e.toFinset :=
      (eq_of_subset_of_card_le heP (by omega)).symm
    exact mem_image.mpr ⟨z, hzB, by simpa [htp, hpEq]⟩
  · intro ht
    obtain ⟨z, hzB, rfl⟩ := mem_image.mp ht
    have hePow : e.toFinset ∈ A.powersetCard 2 :=
      mem_powersetCard.mpr ⟨heA, hecard⟩
    apply mem_filter.mpr
    refine ⟨mem_twoOneTriangleFamily_iff.mpr
      ⟨z, hzB, e.toFinset, hePow, rfl⟩, ?_⟩
    apply mem_sym2_iff.mpr
    intro x hxe
    exact mem_insert_of_mem (by simpa using hxe)

lemma card_filter_twoOne_eq_attachment_of_edge_subset_base
    {A B : Finset α} (hAB : Disjoint A B) (e : Sym2 α)
    (hecard : e.toFinset.card = 2) (heA : e.toFinset ⊆ A) :
    ((twoOneTriangleFamily A B).filter fun t ↦ e ∈ t.sym2).card = B.card := by
  classical
  rw [filter_twoOne_of_edge_subset_base hAB e hecard heA]
  apply card_image_of_injOn
  intro z hzB w hwB hzw
  have hzE : z ∉ e.toFinset := fun hzE ↦
    Finset.disjoint_left.mp hAB (heA hzE) hzB
  have hwE : w ∉ e.toFinset := fun hwE ↦
    Finset.disjoint_left.mp hAB (heA hwE) hwB
  change insert z e.toFinset = insert w e.toFinset at hzw
  have hzmem : z ∈ insert w e.toFinset := by
    rw [← hzw]
    exact mem_insert_self _ _
  rcases mem_insert.mp hzmem with h | h
  · exact h
  · exact (hzE h).elim

lemma card_filter_twoOne_eq_zero_of_edge_subset_attachment
    {A B : Finset α} (hAB : Disjoint A B) (e : Sym2 α)
    (hecard : e.toFinset.card = 2) (heB : e.toFinset ⊆ B) :
    ((twoOneTriangleFamily A B).filter fun t ↦ e ∈ t.sym2).card = 0 := by
  classical
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases mem_filter.mp ht with ⟨htFamily, het⟩
  have heT : e.toFinset ⊆ t := by
    intro x hxe
    exact (mem_sym2_iff.mp het) x (by simpa using hxe)
  have heInter : e.toFinset ⊆ t ∩ B := fun x hxe ↦
    mem_inter.mpr ⟨heT hxe, heB hxe⟩
  have hinter := twoOneTriangleFamily_inter_attachment_card hAB htFamily
  have := card_le_card heInter
  omega

lemma card_filter_twoOne_le_base_pred_of_not_subset_base
    {A B : Finset α} (hAB : Disjoint A B) (hAcard : 2 ≤ A.card)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (heA : ¬ e.toFinset ⊆ A) :
    ((twoOneTriangleFamily A B).filter fun t ↦ e ∈ t.sym2).card ≤
      A.card - 1 := by
  classical
  by_cases hempty :
      ((twoOneTriangleFamily A B).filter fun t ↦ e ∈ t.sym2) = ∅
  · rw [hempty]
    simp
  obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.mpr hempty
  rcases mem_filter.mp ht with ⟨htFamily, het⟩
  obtain ⟨z, hzB, p, hp, htp⟩ := mem_twoOneTriangleFamily_iff.mp htFamily
  obtain ⟨x, hxe, hxA⟩ : ∃ x ∈ e.toFinset, x ∉ A := by
    simpa [Finset.subset_iff] using heA
  have hxT : x ∈ t :=
    (mem_sym2_iff.mp het) x (by simpa using hxe)
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hxz : x = z := by
    rw [htp] at hxT
    rcases mem_insert.mp hxT with hxz | hxp
    · exact hxz
    · exact (hxA (hpA hxp)).elim
  have hsub :
      (twoOneTriangleFamily A B).filter (fun u ↦ e ∈ u.sym2) ⊆
        (cliqueStarTriangleFamily z A).filter (fun u ↦ e ∈ u.sym2) := by
    intro u hu
    rcases mem_filter.mp hu with ⟨huFamily, heu⟩
    obtain ⟨w, hwB, q, hq, huq⟩ :=
      mem_twoOneTriangleFamily_iff.mp huFamily
    have hxU : x ∈ u :=
      (mem_sym2_iff.mp heu) x (by simpa using hxe)
    have hqA : q ⊆ A := (mem_powersetCard.mp hq).1
    have hxw : x = w := by
      rw [huq] at hxU
      rcases mem_insert.mp hxU with hxw | hxq
      · exact hxw
      · exact (hxA (hqA hxq)).elim
    have hwz : w = z := hxw.symm.trans hxz
    have hzu : insert z q = u := by
      calc
        insert z q = insert w q := congrArg (fun y ↦ insert y q) hwz.symm
        _ = u := huq.symm
    exact mem_filter.mpr ⟨by exact mem_image.mpr ⟨q, hq, hzu⟩, heu⟩
  exact (card_le_card hsub).trans
    (card_filter_cliqueStarTriangleFamily_le hAcard
      (fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB) e hecard)

private lemma cast_mul_inv_two_mul_le_half {c b : ℕ}
    (hb : 0 < b) (hcb : c ≤ b) :
    (c : ℝ) * (((2 * b : ℕ) : ℝ))⁻¹ ≤ 1 / 2 := by
  have hd : (0 : ℝ) < ((2 * b : ℕ) : ℝ) := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hd]
  have hcbR : (c : ℝ) ≤ b := by exact_mod_cast hcb
  push_cast
  linarith

private lemma two_blob_cross_load_bound {a b : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 2) :
    ((a - 1 : ℕ) : ℝ) * (((2 * b : ℕ) : ℝ))⁻¹ +
        ((b - 1 : ℕ) : ℝ) * (((2 * a : ℕ) : ℝ))⁻¹ ≤ 1 := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbaR : (b : ℝ) ≤ a + 2 := by exact_mod_cast hba
  have ha0 : (a : ℝ) ≠ 0 := by linarith
  have hb0 : (b : ℝ) ≠ 0 := by linarith
  have hda : (0 : ℝ) < 2 * a := by positivity
  have hdb : (0 : ℝ) < 2 * b := by linarith
  have hx0 : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr habR
  have hx2 : (b : ℝ) - a ≤ 2 := by linarith
  have hxprod : 0 ≤ ((b : ℝ) - a) * (2 - ((b : ℝ) - a)) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx2)
  have hxsq : ((b : ℝ) - a) ^ 2 ≤ 4 := by nlinarith
  have habSum : (4 : ℝ) ≤ a + b := by linarith
  rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b)]
  push_cast
  rw [inv_eq_one_div, inv_eq_one_div]
  have hform :
      ((a : ℝ) - 1) * (1 / (2 * b)) +
          ((b : ℝ) - 1) * (1 / (2 * a)) =
        (((a : ℝ) - 1) * (2 * a) + ((b : ℝ) - 1) * (2 * b)) /
          ((2 * b) * (2 * a)) := by
    field_simp [ha0, hb0]
  rw [hform, div_le_one (mul_pos hdb hda)]
  nlinarith

/-- The explicit weight in Proposition 7.2(a).  The first summand uses
triples with two vertices in `A`, the second triples with two in `B`. -/
def proposition72aWeight (A B : Finset α) : Finset α → ℝ :=
  addTriangleWeight
    (constantTriangleFamilyWeight (twoOneTriangleFamily A B) (2 * B.card))
    (constantTriangleFamilyWeight (twoOneTriangleFamily B A) (2 * A.card))

/-- Proposition 7.2(a) of Gruslys--Letzter.  Between two disjoint cliques of
sizes differing by at most two, all cross pairs being edges, there is an
explicit fractional packing of cross triangles.  Its total triangle weight
is half the number of internal pairs. -/
theorem proposition72a_completeTwoBlobPacking
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B)
    (hAcard : 2 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 2)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    IsFractionalPacking G (proposition72aWeight A B) ∧
      fractionalSize G (proposition72aWeight A B) =
        (((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)) / 2 := by
  classical
  let F := twoOneTriangleFamily A B
  let Q := twoOneTriangleFamily B A
  let wF := constantTriangleFamilyWeight F (2 * B.card)
  let wQ := constantTriangleFamilyWeight Q (2 * A.card)
  have hBcard : 2 ≤ B.card := hAcard.trans hAleB
  have htriF : ∀ t ∈ F, G.IsNClique 3 t :=
    twoOneTriangleFamily_isNClique hAB hA hcross
  have htriQ : ∀ t ∈ Q, G.IsNClique 3 t :=
    twoOneTriangleFamily_isNClique hAB.symm hB
      (fun b hb a ha ↦ (hcross a ha b hb).symm)
  have hpack : IsFractionalPacking G (addTriangleWeight wF wQ) := by
    constructor
    · intro t ht
      simp only [addTriangleWeight, wF, wQ, constantTriangleFamilyWeight]
      split <;> split <;> positivity
    · intro e heG
      have hecard : e.toFinset.card = 2 :=
        SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
      rw [show addTriangleWeight wF wQ = (fun t ↦ wF t + wQ t) by rfl,
        fractionalEdgeLoad_add,
        fractionalEdgeLoad_constantTriangleFamilyWeight htriF,
        fractionalEdgeLoad_constantTriangleFamilyWeight htriQ]
      by_cases heA : e.toFinset ⊆ A
      · have hcF := card_filter_twoOne_le_attachment_of_edge_subset_base
          hAB e hecard heA
        have hcQ := card_filter_twoOne_eq_zero_of_edge_subset_attachment
          hAB.symm e hecard heA
        have hcFR :
            ((((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ)) *
                (((2 * B.card : ℕ) : ℝ))⁻¹ ≤ 1 / 2 :=
          cast_mul_inv_two_mul_le_half (by omega)
            (by simpa only [F] using hcF)
        rw [show (Q.filter fun t ↦ e ∈ t.sym2).card = 0 by
          simpa only [Q] using hcQ]
        simp only [Nat.cast_zero, zero_mul]
        linarith
      · by_cases heB : e.toFinset ⊆ B
        · have hcF := card_filter_twoOne_eq_zero_of_edge_subset_attachment
            hAB e hecard heB
          have hcQ := card_filter_twoOne_le_attachment_of_edge_subset_base
            hAB.symm e hecard heB
          have hcQR :
              ((((Q.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ)) *
                  (((2 * A.card : ℕ) : ℝ))⁻¹ ≤ 1 / 2 :=
            cast_mul_inv_two_mul_le_half (by omega)
              (by simpa only [Q] using hcQ)
          rw [show (F.filter fun t ↦ e ∈ t.sym2).card = 0 by
            simpa only [F] using hcF]
          simp only [Nat.cast_zero, zero_mul]
          linarith
        · have hcF := card_filter_twoOne_le_base_pred_of_not_subset_base
            hAB hAcard e hecard heA
          have hcQ := card_filter_twoOne_le_base_pred_of_not_subset_base
            hAB.symm hBcard e hecard heB
          have hcFR :
              ((((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ)) *
                  (((2 * B.card : ℕ) : ℝ))⁻¹ ≤
                ((A.card - 1 : ℕ) : ℝ) *
                  (((2 * B.card : ℕ) : ℝ))⁻¹ := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast (by simpa only [F] using hcF)
            · positivity
          have hcQR :
              ((((Q.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ)) *
                  (((2 * A.card : ℕ) : ℝ))⁻¹ ≤
                ((B.card - 1 : ℕ) : ℝ) *
                  (((2 * A.card : ℕ) : ℝ))⁻¹ := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast (by simpa only [Q] using hcQ)
            · positivity
          exact (add_le_add hcFR hcQR).trans
            (two_blob_cross_load_bound hAcard hAleB hBle)
  refine ⟨by simpa only [proposition72aWeight, F, Q, wF, wQ] using hpack, ?_⟩
  rw [show proposition72aWeight A B = addTriangleWeight wF wQ by rfl,
    fractionalSize_addTriangleWeight,
    fractionalSize_constantTriangleFamilyWeight htriF,
    fractionalSize_constantTriangleFamilyWeight htriQ,
    show F.card = B.card * A.card.choose 2 by
      simpa only [F] using card_twoOneTriangleFamily hAB,
    show Q.card = A.card * B.card.choose 2 by
      simpa only [Q] using card_twoOneTriangleFamily hAB.symm]
  have hAposR : (0 : ℝ) < A.card := by positivity
  have hBposR : (0 : ℝ) < B.card := by positivity
  push_cast
  field_simp

lemma proposition72aWeight_comm (A B : Finset α) :
    proposition72aWeight A B = proposition72aWeight B A := by
  classical
  funext t
  simp only [proposition72aWeight, addTriangleWeight]
  ring

private lemma insert_edge_isNClique_of_cross
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) (heA : e.toFinset ⊆ A)
    {z : α} (hzB : z ∈ B) :
    G.IsNClique 3 (insert z e.toFinset) := by
  classical
  induction e using Sym2.inductionOn with
  | hf a b =>
      have habG : G.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      have hab : a ≠ b := habG.ne
      have haA : a ∈ A := heA (by simp [hab])
      have hbA : b ∈ A := heA (by simp [hab])
      have hzA : z ∉ A := fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB
      have hza : z ≠ a := fun h ↦ hzA (h ▸ haA)
      have hzb : z ≠ b := fun h ↦ hzA (h ▸ hbA)
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, by simp [Sym2.toFinset_mk_eq, hab, hza, hzb]⟩
      rw [coe_insert, SimpleGraph.isClique_insert]
      constructor
      · rw [Sym2.toFinset_mk_eq, coe_insert, coe_singleton]
        exact Set.pairwise_pair.mpr (fun _ ↦ ⟨habG, habG.symm⟩)
      · intro x hx hzx
        have hx' : x = a ∨ x = b := by
          simpa [Sym2.toFinset_mk_eq] using hx
        rcases hx' with hxa | hxb
        · simpa [hxa] using (hcross a haA z hzB).symm
        · simpa [hxb] using (hcross b hbA z hzB).symm

/-- Every actual internal edge of the first blob has load exactly `1/2` in
the Proposition 7.2(a) weight, even when all other internal blob pairs have
arbitrary colours. -/
lemma fractionalEdgeLoad_proposition72aWeight_of_subset_left
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hBpos : 0 < B.card)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) (heA : e.toFinset ⊆ A) :
    fractionalEdgeLoad G (proposition72aWeight A B) e = 1 / 2 := by
  classical
  let F := twoOneTriangleFamily A B
  let Q := twoOneTriangleFamily B A
  have hecard : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
  have htriF : ∀ t ∈ F, e ∈ t.sym2 → G.IsNClique 3 t := by
    intro t htF het
    have htFilter : t ∈ F.filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htF, het⟩
    have hfilter := filter_twoOne_of_edge_subset_base hAB e hecard heA
    change F.filter (fun u ↦ e ∈ u.sym2) = _ at hfilter
    rw [hfilter] at htFilter
    obtain ⟨z, hzB, rfl⟩ := mem_image.mp htFilter
    exact insert_edge_isNClique_of_cross hAB hcross heG heA hzB
  have hQzero : (Q.filter fun t ↦ e ∈ t.sym2).card = 0 := by
    simpa only [Q] using
      card_filter_twoOne_eq_zero_of_edge_subset_attachment hAB.symm e hecard heA
  have htriQ : ∀ t ∈ Q, e ∈ t.sym2 → G.IsNClique 3 t := by
    intro t htQ het
    have htFilter : t ∈ Q.filter (fun u ↦ e ∈ u.sym2) :=
      mem_filter.mpr ⟨htQ, het⟩
    have hEmpty : Q.filter (fun u ↦ e ∈ u.sym2) = ∅ := card_eq_zero.mp hQzero
    rw [hEmpty] at htFilter
    simp at htFilter
  have hFcard : (F.filter fun t ↦ e ∈ t.sym2).card = B.card := by
    simpa only [F] using
      card_filter_twoOne_eq_attachment_of_edge_subset_base hAB e hecard heA
  rw [proposition72aWeight,
    show addTriangleWeight
        (constantTriangleFamilyWeight (twoOneTriangleFamily A B) (2 * B.card))
        (constantTriangleFamilyWeight (twoOneTriangleFamily B A) (2 * A.card)) =
      (fun t ↦
        constantTriangleFamilyWeight (twoOneTriangleFamily A B) (2 * B.card) t +
        constantTriangleFamilyWeight (twoOneTriangleFamily B A) (2 * A.card) t) by rfl,
    fractionalEdgeLoad_add,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriF,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident htriQ,
    hFcard, hQzero]
  have hBposR : (0 : ℝ) < B.card := by exact_mod_cast hBpos
  push_cast
  field_simp
  norm_num

/-- Symmetric exact-load statement for an internal edge of the second blob. -/
lemma fractionalEdgeLoad_proposition72aWeight_of_subset_right
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hApos : 0 < A.card)
    {e : Sym2 α} (heG : e ∈ G.edgeFinset) (heB : e.toFinset ⊆ B) :
    fractionalEdgeLoad G (proposition72aWeight A B) e = 1 / 2 := by
  rw [proposition72aWeight_comm]
  exact fractionalEdgeLoad_proposition72aWeight_of_subset_left hAB.symm
    (fun b hb a ha ↦ (hcross a ha b hb).symm) hApos heG heB

/-- Proposition 7.2(a) with arbitrary colours inside the two blobs.  The
complete-graph weight is simply restricted to the graph's actual triangles;
the two preceding lemmas record the exact internal loads which survive that
restriction. -/
theorem proposition72a_twoBlobPacking
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B)
    (hAcard : 2 ≤ A.card) (hAleB : A.card ≤ B.card)
    (hBle : B.card ≤ A.card + 2)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    IsFractionalPacking G
        (zeroExtendTriangleWeight G (proposition72aWeight A B)) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ A →
        fractionalEdgeLoad G
          (zeroExtendTriangleWeight G (proposition72aWeight A B)) e = 1 / 2) ∧
      (∀ e ∈ G.edgeFinset, e.toFinset ⊆ B →
        fractionalEdgeLoad G
          (zeroExtendTriangleWeight G (proposition72aWeight A B)) e = 1 / 2) := by
  classical
  have hTopA : (⊤ : SimpleGraph α).IsClique (A : Set α) := by
    intro a ha b hb hab
    simpa using hab
  have hTopB : (⊤ : SimpleGraph α).IsClique (B : Set α) := by
    intro a ha b hb hab
    simpa using hab
  have hTopCross : ∀ a ∈ A, ∀ b ∈ B, (⊤ : SimpleGraph α).Adj a b := by
    intro a ha b hb
    have hab : a ≠ b := by
      intro h
      exact Finset.disjoint_left.mp hAB ha (h ▸ hb)
    simpa using hab
  have hTop := proposition72a_completeTwoBlobPacking
    (G := (⊤ : SimpleGraph α)) hAB hAcard hAleB hBle
    hTopA hTopB hTopCross
  refine ⟨hTop.1.restrictToSubgraph le_top, ?_, ?_⟩
  · intro e heG heA
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl]
    exact fractionalEdgeLoad_proposition72aWeight_of_subset_left
      hAB hcross (by omega) heG heA
  · intro e heG heB
    rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl]
    exact fractionalEdgeLoad_proposition72aWeight_of_subset_right
      hAB hcross (by omega) heG heB

/-! ## Exact size of the restricted complete-cross construction -/

/-- Actual graph edges internal to a blob, represented by their two-element
vertex sets. -/
def blobPairFinset (G : SimpleGraph α) (A : Finset α) : Finset (Finset α) :=
  A.powersetCard 2 |>.filter fun p ↦ G.IsClique (p : Set α)

@[simp] lemma mem_blobPairFinset {G : SimpleGraph α} {A p : Finset α} :
    p ∈ blobPairFinset G A ↔ p ⊆ A ∧ p.card = 2 ∧ G.IsClique (p : Set α) := by
  simp [blobPairFinset, and_assoc]

private lemma cliqueStar_filter_eq_blobPairs_image
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    {z : α} (hzB : z ∈ B) :
    (cliqueStarTriangleFamily z A).filter
        (fun t ↦ G.IsNClique 3 t) =
      (blobPairFinset G A).image fun p ↦ insert z p := by
  classical
  ext t
  constructor
  · intro ht
    rcases mem_filter.mp ht with ⟨htStar, htClique⟩
    obtain ⟨p, hp, rfl⟩ := mem_image.mp htStar
    rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
    have hpClique : G.IsClique (p : Set α) :=
      htClique.1.subset (by intro x hx; exact mem_insert_of_mem hx)
    exact mem_image.mpr
      ⟨p, mem_blobPairFinset.mpr ⟨hpA, hpcard, hpClique⟩, rfl⟩
  · intro ht
    obtain ⟨p, hpGraph, rfl⟩ := mem_image.mp ht
    rcases mem_blobPairFinset.mp hpGraph with ⟨hpA, hpcard, hpClique⟩
    have hzA : z ∉ A := fun hzA ↦ Finset.disjoint_left.mp hAB hzA hzB
    have hzp : z ∉ p := fun hzp ↦ hzA (hpA hzp)
    apply mem_filter.mpr
    refine ⟨mem_image.mpr
      ⟨p, mem_powersetCard.mpr ⟨hpA, hpcard⟩, rfl⟩, ?_⟩
    rw [SimpleGraph.isNClique_iff, coe_insert,
      SimpleGraph.isClique_insert_of_notMem (by simpa using hzp)]
    refine ⟨⟨hpClique, ?_⟩, by simp [hzp, hpcard]⟩
    intro a ha
    exact (hcross a (hpA ha) z hzB).symm

private lemma card_image_insert_of_not_mem
    {z : α} {P : Finset (Finset α)} (hz : ∀ p ∈ P, z ∉ p) :
    (P.image fun p ↦ insert z p).card = P.card := by
  classical
  apply card_image_of_injOn
  intro p hp q hq hpq
  calc
    p = (insert z p).erase z := by simp [hz p hp]
    _ = (insert z q).erase z := congrArg (fun r ↦ r.erase z) hpq
    _ = q := by simp [hz q hq]

lemma card_filter_twoOne_isNClique
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ((twoOneTriangleFamily A B).filter fun t ↦ G.IsNClique 3 t).card =
      B.card * (blobPairFinset G A).card := by
  classical
  rw [twoOneTriangleFamily, filter_biUnion]
  have hdis : (B : Set α).PairwiseDisjoint fun z ↦
      (cliqueStarTriangleFamily z A).filter (fun t ↦ G.IsNClique 3 t) := by
    intro z hzB w hwB hzw
    exact (twoOneTriangleFamily_pairwiseDisjoint_stars hAB hzB hwB hzw).mono
      (filter_subset _ _) (filter_subset _ _)
  rw [card_biUnion hdis]
  calc
    (∑ z ∈ B,
        ((cliqueStarTriangleFamily z A).filter
          (fun t ↦ G.IsNClique 3 t)).card) =
        ∑ _z ∈ B, (blobPairFinset G A).card := by
      apply sum_congr rfl
      intro z hzB
      rw [cliqueStar_filter_eq_blobPairs_image hAB hcross hzB]
      apply card_image_insert_of_not_mem
      intro p hp hzP
      exact Finset.disjoint_left.mp hAB
        ((mem_blobPairFinset.mp hp).1 hzP) hzB
    _ = B.card * (blobPairFinset G A).card := by simp

lemma fractionalSize_zeroExtend_constantTriangleFamilyWeight
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ} :
    fractionalSize G
        (zeroExtendTriangleWeight G (constantTriangleFamilyWeight F d)) =
      ((((F.filter fun t ↦ G.IsNClique 3 t).card : ℕ) : ℝ)) * (d : ℝ)⁻¹ := by
  classical
  unfold fractionalSize
  calc
    (∑ t ∈ G.cliqueFinset 3,
        zeroExtendTriangleWeight G (constantTriangleFamilyWeight F d) t) =
        ∑ t ∈ G.cliqueFinset 3,
          constantTriangleFamilyWeight F d t := by
      apply sum_congr rfl
      intro t ht
      rw [zeroExtendTriangleWeight_of_mem ht]
    _ = ∑ _t ∈ F.filter (fun t ↦ G.IsNClique 3 t), (d : ℝ)⁻¹ := by
      rw [← sum_subset
        (s₁ := F.filter fun t ↦ G.IsNClique 3 t)
        (s₂ := G.cliqueFinset 3)]
      · apply sum_congr rfl
        intro t ht
        simp [constantTriangleFamilyWeight, (mem_filter.mp ht).1]
      · intro t ht
        exact SimpleGraph.mem_cliqueFinset_iff.mpr (mem_filter.mp ht).2
      · intro t htG htFiltered
        have htF : t ∉ F := by
          intro htF
          exact htFiltered (mem_filter.mpr
            ⟨htF, SimpleGraph.mem_cliqueFinset_iff.mp htG⟩)
        simp [constantTriangleFamilyWeight, htF]
    _ = ((((F.filter fun t ↦ G.IsNClique 3 t).card : ℕ) : ℝ)) *
        (d : ℝ)⁻¹ := by simp

lemma zeroExtend_addTriangleWeight (G : SimpleGraph α)
    (w u : Finset α → ℝ) :
    zeroExtendTriangleWeight G (addTriangleWeight w u) =
      addTriangleWeight (zeroExtendTriangleWeight G w)
        (zeroExtendTriangleWeight G u) := by
  classical
  funext t
  by_cases ht : t ∈ G.cliqueFinset 3 <;>
    simp [zeroExtendTriangleWeight, addTriangleWeight, ht]

/-- Exact triangle-weight size of Proposition 7.2(a) after restriction to
arbitrary internal colours.  Each actual internal pair is covered to weight
one half, and every supported triangle contains exactly one such pair. -/
lemma fractionalSize_proposition72a_restricted
    {G : SimpleGraph α} {A B : Finset α}
    (hAB : Disjoint A B) (hApos : 0 < A.card) (hBpos : 0 < B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    fractionalSize G
        (zeroExtendTriangleWeight G (proposition72aWeight A B)) =
      ((blobPairFinset G A).card : ℝ) / 2 +
        ((blobPairFinset G B).card : ℝ) / 2 := by
  classical
  rw [proposition72aWeight, zeroExtend_addTriangleWeight,
    fractionalSize_addTriangleWeight,
    fractionalSize_zeroExtend_constantTriangleFamilyWeight,
    fractionalSize_zeroExtend_constantTriangleFamilyWeight,
    card_filter_twoOne_isNClique hAB hcross,
    card_filter_twoOne_isNClique hAB.symm
      (fun b hb a ha ↦ (hcross a ha b hb).symm)]
  have hAposR : (0 : ℝ) < A.card := by exact_mod_cast hApos
  have hBposR : (0 : ℝ) < B.card := by exact_mod_cast hBpos
  push_cast
  field_simp

end

end Erdos76
