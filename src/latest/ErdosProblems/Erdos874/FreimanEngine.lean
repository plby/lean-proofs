/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import ErdosProblems.Erdos874.FreimanDimension
import ErdosProblems.Erdos874.FreimanThreeKMinusFour
import ErdosProblems.Erdos874.LongProgression
import ErdosProblems.Erdos874.NearIndexFiber
import ErdosProblems.Erdos874.ProgressionExtraction
import ErdosProblems.Erdos874.RestrictedGrowth
import ErdosProblems.Erdos874.RestrictedSums

/-!
# The restricted-sum progression engine for Erdős Problem 874

This file fixes a precise, finite interface for the inverse-additive input in
Deshouillers--Freiman.  In particular, a progression in this file always has
nonzero common difference, so the number of its displayed terms really is its
cardinality.

The fully elementary front end of the engine is also recorded.  If
`|4^∧ B| < 6|B|` and `|B| ≥ 8`, then the fourth layer has two distinct
four-element representations; cancelling their common elements produces a
nonempty disjoint balanced additive relation.  The conversion of the resulting
large family of relations into a long progression is the substantive Freiman
inverse theorem.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A proper finite-arithmetic-progression interface -/

/-- `S` contains the `L` distinct terms
`a, a + q, ..., a + (L - 1)q`, for some positive integer `q`. -/
def EngineContainsAP (S : Finset ℤ) (L : ℕ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ContainsAP S (q : ℤ) L

/-- A proper progression contained in a finset cannot have more terms than
the finset has elements. -/
theorem EngineContainsAP.length_le_card {S : Finset ℤ} {L : ℕ}
    (h : EngineContainsAP S L) :
    L ≤ S.card := by
  obtain ⟨q, hq, a, ha⟩ := h
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← arithmeticProgression_card (a := a) hqz L]
  exact Finset.card_le_card ha

/-- Shortening a contained progression preserves containment. -/
theorem EngineContainsAP.mono {S : Finset ℤ} {L M : ℕ}
    (h : EngineContainsAP S M) (hLM : L ≤ M) :
    EngineContainsAP S L := by
  obtain ⟨q, hq, hAP⟩ := h
  exact ⟨q, hq, hAP.of_length_le hLM⟩

/-! ## Exact greedy packing at the endpoint -/

/-- Endpoint-sharp form of greedy pair packing.  Unlike the convenient
`v`-parameter version in `RestrictedGrowth`, this only asks for `2n`
representations (rather than `2n+1`): before the last choice only
`2(n-1)` vertices have been used.  The one-unit saving is useful when a
single vertex is reserved to absorb a floor-rounding remainder. -/
theorem nsmul_subset_restrictedSumset_two_mul_of_pair_card_ge :
    ∀ {B S : Finset ℤ} (n : ℕ),
      (∀ z ∈ S, 2 * n ≤ (pairRepresentations B z).card) →
      n • S ⊆ restrictedSumset (2 * n) B := by
  intro B S n
  induction n with
  | zero =>
      intro hrich z hz
      simpa [restrictedSumset_zero] using hz
  | succ n ih =>
      intro hrich z hz
      rw [succ_nsmul] at hz
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz
      have hrich' : ∀ w ∈ S, 2 * n ≤ (pairRepresentations B w).card := by
        intro w hw
        exact (by omega : 2 * n ≤ 2 * (n + 1)).trans (hrich w hw)
      have hx' := ih hrich' hx
      obtain ⟨U, hUB, hUcard, hUsum⟩ := mem_restrictedSumset.mp hx'
      have hUcardLt : U.card < (pairRepresentations B y).card := by
        rw [hUcard]
        have := hrich y hy
        omega
      obtain ⟨P, hPrep, hPU⟩ := exists_pairRepresentation_disjoint hUcardLt
      obtain ⟨hPB, hPcard, hPsum⟩ := mem_pairRepresentations.mp hPrep
      apply mem_restrictedSumset.mpr
      refine ⟨P ∪ U, Finset.union_subset hPB hUB, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hPU, hPcard, hUcard]
        omega
      · rw [Finset.sum_union hPU, hPsum, hUsum]
        omega

/-- Removing a finite reserve destroys at most one representation per
reserved vertex. -/
lemma card_pairRepresentations_le_sdiff_add_card
    (B : Finset ℤ) (z : ℤ) (R : Finset ℤ) :
    (pairRepresentations B z).card ≤
      (pairRepresentations (B \ R) z).card + R.card := by
  have hcover : pairRepresentations B z ⊆
      pairRepresentations (B \ R) z ∪
        intersectingPairRepresentations B z R := by
    intro P hP
    by_cases hPR : Disjoint P R
    · apply Finset.mem_union_left
      obtain ⟨hPB, hPcard, hPsum⟩ := mem_pairRepresentations.mp hP
      apply mem_pairRepresentations.mpr
      refine ⟨?_, hPcard, hPsum⟩
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨hPB hx, fun hxR ↦ Finset.disjoint_left.mp hPR hx hxR⟩
    · apply Finset.mem_union_right
      obtain ⟨x, hxP, hxR⟩ := Finset.not_disjoint_iff.mp hPR
      exact Finset.mem_biUnion.mpr
        ⟨x, hxR, Finset.mem_filter.mpr ⟨hP, hxP⟩⟩
  calc
    (pairRepresentations B z).card ≤
        (pairRepresentations (B \ R) z ∪
          intersectingPairRepresentations B z R).card :=
      Finset.card_le_card hcover
    _ ≤ (pairRepresentations (B \ R) z).card +
        (intersectingPairRepresentations B z R).card := Finset.card_union_le _ _
    _ ≤ (pairRepresentations (B \ R) z).card + R.card := by
      gcongr
      exact card_intersectingPairRepresentations_le B z R

/-- Reserving one element translates an `r`-restricted layer of the remaining
set into the `(r+1)`-restricted layer of the original set. -/
lemma affineImage_one_restrictedSumset_erase_subset
    {B : Finset ℤ} {b : ℤ} (hb : b ∈ B) (r : ℕ) :
    affineImage b 1 (restrictedSumset r (B.erase b)) ⊆
      restrictedSumset (r + 1) B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_affineImage.mp hx
  obtain ⟨U, hUB, hUcard, hUsum⟩ := mem_restrictedSumset.mp hy
  have hbU : b ∉ U := by
    intro hbU
    exact (Finset.mem_erase.mp (hUB hbU)).1 rfl
  apply mem_restrictedSumset.mpr
  refine ⟨insert b U, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hb
    · exact (Finset.mem_erase.mp (hUB hz)).2
  · rw [Finset.card_insert_of_notMem hbU, hUcard]
  · rw [Finset.sum_insert hbU, hUsum]
    ring

/-- Reserving an arbitrary finite block translates a restricted layer of its
complement into the correspondingly higher layer. -/
lemma affineImage_sum_restrictedSumset_sdiff_subset
    {B R : Finset ℤ} (hRB : R ⊆ B) (r : ℕ) :
    affineImage (∑ x ∈ R, x) 1 (restrictedSumset r (B \ R)) ⊆
      restrictedSumset (R.card + r) B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_affineImage.mp hx
  obtain ⟨U, hUB, hUcard, hUsum⟩ := mem_restrictedSumset.mp hy
  have hRU : Disjoint R U := by
    apply Finset.disjoint_left.mpr
    intro z hzR hzU
    exact (Finset.mem_sdiff.mp (hUB hzU)).2 hzR
  apply mem_restrictedSumset.mpr
  refine ⟨R ∪ U, Finset.union_subset hRB ?_, ?_, ?_⟩
  · intro z hzU
    exact (Finset.mem_sdiff.mp (hUB hzU)).1
  · rw [Finset.card_union_of_disjoint hRU, hUcard]
  · rw [Finset.sum_union hRU, hUsum]
    ring

/-- A proper progression survives the one-element reserve construction. -/
lemma EngineContainsAP.reserve_one {B : Finset ℤ} {b : ℤ} (hb : b ∈ B)
    {r L : ℕ} (hAP : EngineContainsAP (restrictedSumset r (B.erase b)) L) :
    EngineContainsAP (restrictedSumset (r + 1) B) L := by
  obtain ⟨q, hq, hcontains⟩ := hAP
  refine ⟨q, hq, ?_⟩
  have himage : ContainsAP
      (affineImage b 1 (restrictedSumset r (B.erase b))) (q : ℤ) L := by
    simpa using hcontains.affineImage b 1
  exact himage.mono (affineImage_one_restrictedSumset_erase_subset hb r)

/-- Proper progressions survive translation by an arbitrary reserved block. -/
lemma EngineContainsAP.reserve {B R : Finset ℤ} (hRB : R ⊆ B)
    {r L : ℕ} (hAP : EngineContainsAP (restrictedSumset r (B \ R)) L) :
    EngineContainsAP (restrictedSumset (R.card + r) B) L := by
  obtain ⟨q, hq, hcontains⟩ := hAP
  refine ⟨q, hq, ?_⟩
  have himage : ContainsAP
      (affineImage (∑ x ∈ R, x) 1 (restrictedSumset r (B \ R)))
        (q : ℤ) L := by
    simpa using hcontains.affineImage (∑ x ∈ R, x) 1
  exact himage.mono (affineImage_sum_restrictedSumset_sdiff_subset hRB r)

/-! ## Exact public statement of the deep engine -/

/-- The conclusion supplied by fixed constants `c₁,c₂`: the
`⌊c₁|B|⌋`-restricted layer contains a proper progression of at least
`c₂|B|²` terms. -/
def HasLongRestrictedSumProgression (c₁ c₂ : ℝ) (B : Finset ℤ) : Prop :=
  ∃ L : ℕ,
    c₂ * (B.card : ℝ) ^ 2 ≤ (L : ℝ) ∧
      EngineContainsAP (restrictedSumset ⌊c₁ * (B.card : ℝ)⌋₊ B) L

/-- The precise quantifier order of the Deshouillers--Freiman restricted-sum
progression engine.  This is a proposition, not an assumed theorem: clients
must provide a kernel-checked inhabitant before using the inverse theorem. -/
def RestrictedSumProgressionEngine (lambda : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∃ n₁ : ℕ, ∀ B : Finset ℤ, n₁ ≤ B.card →
      ((restrictedSumset 4 B).card : ℝ) ≤ lambda * (B.card : ℝ) →
      HasLongRestrictedSumProgression c₁ c₂ B

/-- The engine assertion is downward closed in the fourth-layer coefficient. -/
theorem RestrictedSumProgressionEngine.mono {lambda mu : ℝ}
    (hengine : RestrictedSumProgressionEngine lambda) (hmu : mu ≤ lambda) :
    RestrictedSumProgressionEngine mu := by
  obtain ⟨c₁, c₂, hc₁, hc₂, n₁, h⟩ := hengine
  refine ⟨c₁, c₂, hc₁, hc₂, n₁, ?_⟩
  intro B hB hfour
  apply h B hB
  exact hfour.trans (mul_le_mul_of_nonneg_right hmu (by positivity))

/-! ## The explicit Deshouillers--Freiman engine at `29/5` -/

/-- The natural floor in the public real-valued formulation is the expected
integer quotient. -/
lemma floor_two_div_million_mul_card (B : Finset ℤ) :
    ⌊(2 / 1000000 : ℝ) * (B.card : ℝ)⌋₊ = B.card / 500000 := by
  rw [show (2 / 1000000 : ℝ) * (B.card : ℝ) =
      (B.card : ℝ) / 500000 by ring]
  exact Nat.floor_div_eq_div B.card 500000

/-- Explicit finite form of the corrected DF95 Proposition 4.  The fourth
restricted layer bound with coefficient `29/5` forces a proper progression
in the `⌊2|B|/10⁶⌋`-restricted layer, with at least `|B|²/10⁸` terms.

The proof uses the safe near-index count in `NearIndexFiber`, the genuine
integer `3k-4` theorem, the dense-model progression lemma, endpoint-sharp
greedy packing, and a reserve of at most three elements to absorb every floor
and parity remainder. -/
theorem exists_long_restrictedSumset_AP_of_small_four
    (B : Finset ℤ) (hB : 100000000 ≤ B.card)
    (hfour : 5 * (restrictedSumset 4 B).card ≤ 29 * B.card) :
    ∃ ell : ℕ, B.card ^ 2 ≤ 100000000 * ell ∧
      EngineContainsAP (restrictedSumset (B.card / 500000) B) ell := by
  let S := dfPopularPairSums B
  have hpopular99 : 99 * B.card < 50 * S.card := by
    simpa [S] using card_dfPopularPairSums_large_of_small_four hB hfour
  have hpopular49 : 49 * B.card < 25 * S.card := by omega
  have hsubset : S + S ⊆ restrictedSumset 4 B := by
    dsimp [S]
    exact add_dfPopularPairSums_subset_four (by omega)
  obtain ⟨start, step, hmodel, hdense⟩ :=
    exists_dense_AP_container_of_popular_pair_sums
      (B := B) (S := S) (L := B.card) (by omega)
        hpopular49 hsubset hfour
  have hScard : 1000 ≤ S.card := by omega
  let h := B.card / 1000000
  let t := h / 2
  let r := B.card / 500000
  let k := r - 4 * t
  have hbase : 4 * t ≤ r := by
    dsimp [t, h, r]
    omega
  have hk : k ≤ 3 := by
    dsimp [k, t, h, r]
    omega
  have hkB : k ≤ B.card := hk.trans (by omega)
  obtain ⟨R, hRB, hRcard⟩ := Finset.exists_subset_card_eq hkB
  obtain ⟨ell, hell, hordinary⟩ :=
    exists_long_even_sum_progression_of_dense_AP S hmodel hScard hdense
      (t := t)
  have hrichErase : ∀ z ∈ S,
      4 * t ≤ (pairRepresentations (B \ R) z).card := by
    intro z hz
    have hrich := dfPopularPairSums_pair_rich B z (by simpa [S] using hz)
    have hloss := card_pairRepresentations_le_sdiff_add_card B z R
    have hrUpper : r ≤ 2 * h + 1 := by
      dsimp [r, h]
      omega
    dsimp [dfPairMultiplicity] at hrich
    rw [hRcard] at hloss
    dsimp [k] at hloss
    omega
  have hpacking : (2 * t) • S ⊆ restrictedSumset (4 * t) (B \ R) := by
    have hrichErase' : ∀ z ∈ S,
        2 * (2 * t) ≤ (pairRepresentations (B \ R) z).card := by
      intro z hz
      simpa only [show 2 * (2 * t) = 4 * t by omega] using hrichErase z hz
    have h := nsmul_subset_restrictedSumset_two_mul_of_pair_card_ge
      (B := B \ R) (S := S) (2 * t) hrichErase'
    simpa only [show 2 * (2 * t) = 4 * t by omega] using h
  have hbaseAP : EngineContainsAP
      (restrictedSumset (4 * t) (B \ R)) ell := by
    exact ⟨step, hmodel.step_pos, hordinary.mono hpacking⟩
  have hreserved : EngineContainsAP
      (restrictedSumset (R.card + 4 * t) B) ell :=
    hbaseAP.reserve hRB
  have hlayer : R.card + 4 * t = r := by
    rw [hRcard]
    dsimp [k]
    omega
  have hfinalAP : EngineContainsAP
      (restrictedSumset (B.card / 500000) B) ell := by
    simpa [r, hlayer] using hreserved
  have hfloorScale :
      50 * B.card ≤ 99 * 1000000 * (2 * t) := by
    dsimp [t, h]
    omega
  have hsquare : B.card ^ 2 ≤ 1000000 * (2 * t * S.card) := by
    nlinarith
  have hlength : B.card ^ 2 ≤ 100000000 * ell := by
    nlinarith
  exact ⟨ell, hlength, hfinalAP⟩

/-- The kernel-checked restricted-sum progression engine at the exact
coefficient `29/5`, with concrete constants `c₁ = 2/10⁶`,
`c₂ = 1/10⁸`, and threshold `10⁸`. -/
theorem restrictedSumProgressionEngine_29_div_5 :
    RestrictedSumProgressionEngine (29 / 5 : ℝ) := by
  refine ⟨2 / 1000000, 1 / 100000000, by norm_num, by norm_num,
    100000000, ?_⟩
  intro B hB hfourReal
  have hfourNat :
      5 * (restrictedSumset 4 B).card ≤ 29 * B.card := by
    have h : (5 : ℝ) * (restrictedSumset 4 B).card ≤
        29 * (B.card : ℝ) := by
      nlinarith
    exact_mod_cast h
  obtain ⟨ell, hell, hAP⟩ :=
    exists_long_restrictedSumset_AP_of_small_four B hB hfourNat
  refine ⟨ell, ?_, ?_⟩
  · have hellReal : (B.card : ℝ) ^ 2 ≤ 100000000 * ell := by
      exact_mod_cast hell
    nlinarith
  · simpa [floor_two_div_million_mul_card] using hAP

/-! ## The elementary `< 6` relation-producing front end -/

/-- A real-coefficient fourth-layer bound with coefficient below six gives a
strict integral bound by `6|B|`. -/
lemma card_four_lt_six_mul_of_real_bound {lambda : ℝ} {B : Finset ℤ}
    (hlambda : lambda < 6)
    (hB : B.Nonempty)
    (hfour : ((restrictedSumset 4 B).card : ℝ) ≤
      lambda * (B.card : ℝ)) :
    (restrictedSumset 4 B).card < 6 * B.card := by
  have hcard : (0 : ℝ) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hB
  have hlt : ((restrictedSumset 4 B).card : ℝ) <
      6 * (B.card : ℝ) :=
    hfour.trans_lt (mul_lt_mul_of_pos_right hlambda hcard)
  exact_mod_cast hlt

/-- Kernel-checked part of the `lambda < 6` engine: small fourth restricted
sumset produces a nonempty disjoint balanced relation. -/
theorem exists_disjoint_balanced_relation_of_real_small_four
    {lambda : ℝ} (hlambda : lambda < 6) {B : Finset ℤ}
    (hB : 8 ≤ B.card)
    (hfour : ((restrictedSumset 4 B).card : ℝ) ≤
      lambda * (B.card : ℝ)) :
    Nonempty (DisjointBalancedRelation B) := by
  exact exists_disjoint_balanced_relation_of_small_four_restrictedSumset hB
    (card_four_lt_six_mul_of_real_bound hlambda
      (Finset.card_pos.mp (by omega)) hfour)

/-! ## A sharp-lower-bound reduction below coefficient four -/

/-- The elementary restricted-sum lower bound is already enough to rule out
the hypotheses of the progression engine for every fixed coefficient below
four.  It is stated with the exact lower bound as an argument so this module
does not duplicate the order-embedding proof from `RestrictedSums`. -/
theorem restrictedSumProgressionEngine_of_lt_four_of_lower_bound
    {lambda : ℝ} (hlambda : lambda < 4)
    (hlower : ∀ B : Finset ℤ, 4 ≤ B.card →
      4 * (B.card - 4) + 1 ≤ (restrictedSumset 4 B).card) :
    RestrictedSumProgressionEngine lambda := by
  have hgap : 0 < (4 : ℝ) - lambda := sub_pos.mpr hlambda
  obtain ⟨n, hn⟩ := exists_nat_gt (15 / ((4 : ℝ) - lambda))
  refine ⟨1, 1, by norm_num, by norm_num, max 4 n, ?_⟩
  intro B hB hfour
  have hB4 : 4 ≤ B.card := (le_max_left 4 n).trans hB
  have hlower' := hlower B hB4
  have hnat : 4 * B.card - 15 ≤ (restrictedSumset 4 B).card := by
    omega
  have hrealLower : (4 : ℝ) * B.card - 15 ≤
      ((restrictedSumset 4 B).card : ℝ) := by
    have h15 : 15 ≤ 4 * B.card := by omega
    have hcast : (((4 * B.card - 15 : ℕ) : ℝ)) =
        (4 : ℝ) * B.card - 15 := by
      rw [Nat.cast_sub h15]
      norm_num
    rw [← hcast]
    exact_mod_cast hnat
  have hupper : (4 - lambda) * (B.card : ℝ) ≤ 15 := by
    nlinarith
  have hnB : n ≤ B.card := (le_max_right 4 n).trans hB
  have hnReal : (15 / ((4 : ℝ) - lambda)) < (B.card : ℝ) :=
    hn.trans_le (by exact_mod_cast hnB)
  have : 15 < (4 - lambda) * (B.card : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hnReal hgap
    have hcancel : (4 - lambda) * (15 / (4 - lambda)) = 15 := by
      field_simp
    rwa [hcancel] at hmul
  exfalso
  linarith

/-- Assumption-free specialization of the progression engine below the sharp
coefficient four.  In this range the hypotheses are eventually inconsistent;
the nonvacuous inverse-additive range is `4 ≤ lambda < 6`. -/
theorem restrictedSumProgressionEngine_of_lt_four
    {lambda : ℝ} (hlambda : lambda < 4) :
    RestrictedSumProgressionEngine lambda := by
  apply restrictedSumProgressionEngine_of_lt_four_of_lower_bound hlambda
  intro B hB
  exact card_restrictedSumset_lower_bound B 4 hB

end

end Erdos874
