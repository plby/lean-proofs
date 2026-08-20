import ErdosProblems.Erdos746.ExpansionPointwise
import ErdosProblems.Erdos746.ExpansionRangeBounds

/-!
# Exact finite range sums for Erdős 746

These definitions partition (with harmless endpoint overlap) the possible
cardinalities of a bad set.  The theorems below connect the exact binomial
layer `expansionBinomialUnionTerm` to the abstract summation lemmas.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos746

noncomputable section

def smallExpansionIndices (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun s ↦
    (s : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2

def mediumExpansionIndices (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun s ↦
    (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ) ∧
      (s : ℝ) ≤ (n : ℝ) / (c * Real.log (n : ℝ))

def largeLinearExpansionIndices (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun s ↦
    (n : ℝ) / (c * Real.log (n : ℝ)) ≤ (s : ℝ) ∧
      12 * s ≤ n

def largeLogExpansionIndices (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun s ↦
    (n : ℝ) / 12 ≤ (s : ℝ) ∧ (s : ℝ) ≤ (n : ℝ) / 4

lemma mem_smallExpansionIndices {n s : ℕ} :
    s ∈ smallExpansionIndices n ↔
      1 ≤ s ∧ s ≤ n ∧
        (s : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
  simp [smallExpansionIndices, and_assoc]

lemma mem_mediumExpansionIndices {c : ℝ} {n s : ℕ} :
    s ∈ mediumExpansionIndices c n ↔
      1 ≤ s ∧ s ≤ n ∧
        (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ) ∧
        (s : ℝ) ≤ (n : ℝ) / (c * Real.log (n : ℝ)) := by
  simp [mediumExpansionIndices, and_assoc]

lemma mem_largeLinearExpansionIndices {c : ℝ} {n s : ℕ} :
    s ∈ largeLinearExpansionIndices c n ↔
      1 ≤ s ∧ s ≤ n ∧
        (n : ℝ) / (c * Real.log (n : ℝ)) ≤ (s : ℝ) ∧ 12 * s ≤ n := by
  simp [largeLinearExpansionIndices, and_assoc]

lemma mem_largeLogExpansionIndices {n s : ℕ} :
    s ∈ largeLogExpansionIndices n ↔
      1 ≤ s ∧ s ≤ n ∧
        (n : ℝ) / 12 ≤ (s : ℝ) ∧ (s : ℝ) ≤ (n : ℝ) / 4 := by
  simp [largeLogExpansionIndices, and_assoc]

@[simp]
lemma expansionBinomialUnionTerm_zero (c : ℝ) (n : ℕ) :
    expansionBinomialUnionTerm c n 0 = 0 := by
  simp [expansionBinomialUnionTerm, binomialLowerTail]

/-- Every positive size at most `floor(n/4)` belongs to at least one of the
four analytic ranges.  Endpoint overlap is intentional and harmless. -/
theorem expansion_range_cover (c : ℝ) {n s : ℕ}
    (hs : s ∈ Finset.range (n / 4 + 1)) :
    s = 0 ∨ s ∈ smallExpansionIndices n ∨
      s ∈ mediumExpansionIndices c n ∨
      s ∈ largeLinearExpansionIndices c n ∨
      s ∈ largeLogExpansionIndices n := by
  have hsQuarter : s ≤ n / 4 := by
    have := Finset.mem_range.mp hs
    omega
  have hsn : s ≤ n := hsQuarter.trans (Nat.div_le_self n 4)
  by_cases hs0 : s = 0
  · exact Or.inl hs0
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  by_cases hsmall : (s : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2
  · exact Or.inr <| Or.inl <| mem_smallExpansionIndices.mpr
      ⟨hs1, hsn, hsmall⟩
  have hmediumLower : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ) :=
    le_of_lt (lt_of_not_ge hsmall)
  by_cases hmedium : (s : ℝ) ≤ (n : ℝ) / (c * Real.log (n : ℝ))
  · exact Or.inr <| Or.inr <| Or.inl <| mem_mediumExpansionIndices.mpr
      ⟨hs1, hsn, hmediumLower, hmedium⟩
  have hlargeLower : (n : ℝ) / (c * Real.log (n : ℝ)) ≤ (s : ℝ) :=
    le_of_lt (lt_of_not_ge hmedium)
  by_cases hlinear : 12 * s ≤ n
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      mem_largeLinearExpansionIndices.mpr ⟨hs1, hsn, hlargeLower, hlinear⟩
  have htwelveNat : n < 12 * s := Nat.lt_of_not_ge hlinear
  have htwelve : (n : ℝ) / 12 ≤ (s : ℝ) := by
    have htwelveR : (n : ℝ) < 12 * (s : ℝ) := by exact_mod_cast htwelveNat
    norm_num at htwelveR ⊢
    linarith
  have hfourNat : 4 * s ≤ n := by omega
  have hquarter : (s : ℝ) ≤ (n : ℝ) / 4 := by
    have hfourR : 4 * (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfourNat
    norm_num at hfourR ⊢
    linarith
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    mem_largeLogExpansionIndices.mpr ⟨hs1, hsn, htwelve, hquarter⟩

lemma sum_union_le_add_sum {A B : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ x ∈ B, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  let C := B \ A
  have hEq : A ∪ B = A ∪ C := by
    ext x
    simp [C]
  rw [hEq, Finset.sum_union Finset.disjoint_sdiff]
  exact add_le_add_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun x hxB _ ↦ hf x hxB)) _

/-- The exact total union-bound sum is bounded by the four range sums. -/
theorem expansion_total_sum_le_range_sums {c : ℝ} {n : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    (∑ s ∈ Finset.range (n / 4 + 1), expansionBinomialUnionTerm c n s) ≤
      (∑ s ∈ smallExpansionIndices n, expansionBinomialUnionTerm c n s) +
      (∑ s ∈ mediumExpansionIndices c n, expansionBinomialUnionTerm c n s) +
      (∑ s ∈ largeLinearExpansionIndices c n, expansionBinomialUnionTerm c n s) +
      ∑ s ∈ largeLogExpansionIndices n, expansionBinomialUnionTerm c n s := by
  let S := smallExpansionIndices n
  let M := mediumExpansionIndices c n
  let L := largeLinearExpansionIndices c n
  let H := largeLogExpansionIndices n
  let U := {0} ∪ (S ∪ (M ∪ (L ∪ H)))
  have hsubset : Finset.range (n / 4 + 1) ⊆ U := by
    intro s hs
    rcases expansion_range_cover c hs with rfl | hsS | hsM | hsL | hsH
    · simp [U]
    · simp [U, S, hsS]
    · simp [U, M, hsM]
    · simp [U, L, hsL]
    · simp [U, H, hsH]
  have hnonneg : ∀ s, 0 ≤ expansionBinomialUnionTerm c n s :=
    fun _ ↦ expansionBinomialUnionTerm_nonneg hp0 hp1
  have htoU :
      (∑ s ∈ Finset.range (n / 4 + 1), expansionBinomialUnionTerm c n s) ≤
        ∑ s ∈ U, expansionBinomialUnionTerm c n s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun s _ _ ↦ hnonneg s)
  have hLH := sum_union_le_add_sum
    (A := L) (B := H) (f := fun s ↦ expansionBinomialUnionTerm c n s)
    (fun s _ ↦ hnonneg s)
  have hMLH := sum_union_le_add_sum
    (A := M) (B := L ∪ H) (f := fun s ↦ expansionBinomialUnionTerm c n s)
    (fun s _ ↦ hnonneg s)
  have hSMLH := sum_union_le_add_sum
    (A := S) (B := M ∪ (L ∪ H))
    (f := fun s ↦ expansionBinomialUnionTerm c n s)
    (fun s _ ↦ hnonneg s)
  have hzero := sum_union_le_add_sum
    (A := {0}) (B := S ∪ (M ∪ (L ∪ H)))
    (f := fun s ↦ expansionBinomialUnionTerm c n s) (fun s _ ↦ hnonneg s)
  calc
    (∑ s ∈ Finset.range (n / 4 + 1), expansionBinomialUnionTerm c n s) ≤
        ∑ s ∈ U, expansionBinomialUnionTerm c n s := htoU
    _ ≤ (∑ s ∈ {0}, expansionBinomialUnionTerm c n s) +
        ∑ s ∈ S ∪ (M ∪ (L ∪ H)), expansionBinomialUnionTerm c n s := by
      simpa [U] using hzero
    _ ≤ (∑ s ∈ {0}, expansionBinomialUnionTerm c n s) +
        ((∑ s ∈ S, expansionBinomialUnionTerm c n s) +
          ∑ s ∈ M ∪ (L ∪ H), expansionBinomialUnionTerm c n s) := by
      exact add_le_add_right hSMLH _
    _ ≤ (∑ s ∈ {0}, expansionBinomialUnionTerm c n s) +
        ((∑ s ∈ S, expansionBinomialUnionTerm c n s) +
          ((∑ s ∈ M, expansionBinomialUnionTerm c n s) +
            ∑ s ∈ L ∪ H, expansionBinomialUnionTerm c n s)) := by
      exact add_le_add_right (add_le_add_right hMLH _) _
    _ ≤ (∑ s ∈ {0}, expansionBinomialUnionTerm c n s) +
        ((∑ s ∈ S, expansionBinomialUnionTerm c n s) +
          ((∑ s ∈ M, expansionBinomialUnionTerm c n s) +
            ((∑ s ∈ L, expansionBinomialUnionTerm c n s) +
              ∑ s ∈ H, expansionBinomialUnionTerm c n s))) := by
      exact add_le_add_right (add_le_add_right (add_le_add_right hLH _) _) _
    _ = (∑ s ∈ smallExpansionIndices n, expansionBinomialUnionTerm c n s) +
        (∑ s ∈ mediumExpansionIndices c n, expansionBinomialUnionTerm c n s) +
        (∑ s ∈ largeLinearExpansionIndices c n, expansionBinomialUnionTerm c n s) +
        ∑ s ∈ largeLogExpansionIndices n, expansionBinomialUnionTerm c n s := by
      simp [S, M, L, H]
      ring

lemma card_filtered_Icc_one_le (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.Icc 1 n).filter P).card ≤ n := by
  calc
    ((Finset.Icc 1 n).filter P).card ≤ (Finset.Icc 1 n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp [Nat.card_Icc]

lemma card_mediumExpansionIndices_le (c : ℝ) (n : ℕ) :
    (mediumExpansionIndices c n).card ≤ n :=
  card_filtered_Icc_one_le _ n

lemma card_largeLinearExpansionIndices_le (c : ℝ) (n : ℕ) :
    (largeLinearExpansionIndices c n).card ≤ n :=
  card_filtered_Icc_one_le _ n

lemma card_largeLogExpansionIndices_le (n : ℕ) :
    (largeLogExpansionIndices n).card ≤ n :=
  card_filtered_Icc_one_le _ n

/-! ## Discharging the pointwise hypotheses -/

/-- Equation (5) holds uniformly throughout the explicitly defined small
range. -/
theorem eventually_smallExpansion_pointwise {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcδ : 1 + δ ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤
        (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s := by
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have hlogTwo := tendsto_log_nat_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  have hlogDelta := tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop (16 / δ))
  have hlogCDelta := tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop (16 * c / δ))
  filter_upwards [hp, hlogTwo, hlogDelta, hlogCDelta, eventually_ge_atTop 2]
      with n hpN hlogTwoN hlogDeltaN hlogCDeltaN hn
  intro s hsMem
  have hsData := mem_smallExpansionIndices.mp hsMem
  have hs : 1 ≤ s := hsData.1
  have hsn : s ≤ n := hsData.2.1
  have hsUpper := hsData.2.2
  have hnR : (0 : ℝ) < n := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlogSq : 0 < Real.log (n : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hsLogSq : (s : ℝ) * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) :=
    (le_div_iff₀ hlogSq).1 hsUpper
  have hdeltaSq : 16 / δ ≤ Real.log (n : ℝ) ^ 2 := by
    have hone : 1 ≤ Real.log (n : ℝ) := by linarith
    have hlogSelf : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ Real.log (n : ℝ) by positivity)
        (show 0 ≤ Real.log (n : ℝ) - 1 by linarith)]
    exact hlogDeltaN.trans hlogSelf
  have hsSmall : (s : ℝ) ≤ (δ / 16) * (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left hdeltaSq (show 0 ≤ (s : ℝ) by positivity)
    have hscaled : (16 / δ) * (s : ℝ) ≤ (n : ℝ) := by
      rw [mul_comm]
      exact this.trans hsLogSq
    have hscaledδ := mul_le_mul_of_nonneg_left hscaled hδ.le
    have h16 : 16 * (s : ℝ) ≤ δ * (n : ℝ) := by
      calc
        16 * (s : ℝ) = δ * ((16 / δ) * (s : ℝ)) := by
          field_simp [ne_of_gt hδ]
        _ ≤ δ * (n : ℝ) := hscaledδ
    nlinarith
  have hpS : rangeOneProbability c n * (s : ℝ) ≤ δ / 16 := by
    have hfirst : rangeOneProbability c n * (s : ℝ) ≤
        c / Real.log (n : ℝ) := by
      unfold rangeOneProbability
      rw [show (c * Real.log (n : ℝ) / (n : ℝ)) * (s : ℝ) =
          (c * (s : ℝ) * Real.log (n : ℝ)) / (n : ℝ) by ring]
      rw [div_le_div_iff₀ hnR hlog]
      have hm := mul_le_mul_of_nonneg_left hsLogSq hc.le
      nlinarith
    have hsecond : c / Real.log (n : ℝ) ≤ δ / 16 := by
      rw [div_le_iff₀ hlog]
      have hcd := (div_le_iff₀ hδ).1 hlogCDeltaN
      nlinarith
    exact hfirst.trans hsecond
  have hmeanLower := rangeOneMean_ge_small (c := c) (δ := δ)
    hcδ hδ hδ1 (by omega) hsn hpN.1 hpN.2 hsSmall hpS
  have hmeanUpper := rangeOneMean_le_mul_log (c := c) (s := s)
    (by omega) hpN.1 hpN.2
  have hmeanTwo : ((2 * s : ℕ) : ℝ) ≤ rangeOneMean c n s := by
    have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hlogMul : 2 * (s : ℝ) ≤ (s : ℝ) * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlogTwoN hs0
      linarith
    have hcoeff : 1 ≤ 1 + δ / 2 := by linarith
    have hterm0 : 0 ≤ (s : ℝ) * Real.log (n : ℝ) := by positivity
    calc
      ((2 * s : ℕ) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
      _ ≤ (s : ℝ) * Real.log (n : ℝ) := hlogMul
      _ ≤ (1 + δ / 2) * ((s : ℝ) * Real.log (n : ℝ)) :=
        le_mul_of_one_le_left hterm0 hcoeff
      _ = (1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ rangeOneMean c n s := hmeanLower
  exact expansionBinomialUnionTerm_le_small_envelope hδ hc.le (by omega) hs
    hpN.1 hpN.2 hmeanLower hmeanUpper hmeanTwo

/-- Equation (6) holds uniformly throughout the explicitly defined medium
range. -/
theorem eventually_mediumExpansion_pointwise {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ s ∈ mediumExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)) := by
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have hlogLarge := tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop (8 / c))
  have habsorb := eventually_medium_polynomial_absorbed hc
  filter_upwards [hp, hlogLarge, habsorb, eventually_ge_atTop 2]
      with n hpN hlogLargeN habsorbN hn
  intro s hsMem
  have hsData := mem_mediumExpansionIndices.mp hsMem
  have hs : 1 ≤ s := hsData.1
  have hsn : s ≤ n := hsData.2.1
  have hsLower := hsData.2.2.1
  have hsUpper := hsData.2.2.2
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hclog : 0 < c * Real.log (n : ℝ) := mul_pos hc hlog
  have hcLogLarge : 8 ≤ c * Real.log (n : ℝ) := by
    have := (div_le_iff₀ hc).1 hlogLargeN
    nlinarith
  have hsCLog : (s : ℝ) * (c * Real.log (n : ℝ)) ≤ (n : ℝ) :=
    (le_div_iff₀ hclog).1 hsUpper
  have hcLogMul : 8 * (s : ℝ) ≤
      (s : ℝ) * (c * Real.log (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hcLogLarge (Nat.cast_nonneg s)
    nlinarith
  have hsHalfR : 2 * (s : ℝ) ≤ (n : ℝ) := by
    linarith
  have hsHalf : 2 * s ≤ n := by exact_mod_cast hsHalfR
  have hps : rangeOneProbability c n * (s : ℝ) ≤ 1 := by
    unfold rangeOneProbability
    rw [show (c * Real.log (n : ℝ) / (n : ℝ)) * (s : ℝ) =
        ((s : ℝ) * (c * Real.log (n : ℝ))) / (n : ℝ) by ring,
      div_le_one hnR]
    exact hsCLog
  have hmeanLower := rangeOneMean_ge_medium (c := c) (s := s)
    (by omega) hsHalf hpN.1 hpN.2 hps
  have hmeanUpper := rangeOneMean_le_mul_log (c := c) (s := s)
    (by omega) hpN.1 hpN.2
  have hmeanTwo : ((2 * s : ℕ) : ℝ) ≤ rangeOneMean c n s := by
    have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hscaled : 2 * (s : ℝ) ≤
        c / 4 * (s : ℝ) * Real.log (n : ℝ) := by
      nlinarith [hcLogMul]
    calc
      ((2 * s : ℕ) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
      _ ≤ c / 4 * (s : ℝ) * Real.log (n : ℝ) := hscaled
      _ ≤ rangeOneMean c n s := hmeanLower
  exact expansionBinomialUnionTerm_le_medium_envelope hc (by omega) hs
    hpN.1 hpN.2 hmeanLower hmeanUpper hmeanTwo hsLower habsorbN

/-- The logarithmic absorption used in the first half of Range III. -/
theorem eventually_large_linear_log_absorbed {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.exp 1 * c * Real.log (n : ℝ)) ≤
        c * Real.log (n : ℝ) / 20 := by
  have hinv : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop
  have hconst : Tendsto (fun n : ℕ ↦
      (1 + Real.log c) / Real.log (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun n : ℕ ↦ (1 + Real.log c) * (Real.log (n : ℝ))⁻¹) atTop
        (nhds ((1 + Real.log c) * 0)))
  have hratio : Tendsto (fun n : ℕ ↦
      (1 + Real.log c) / Real.log (n : ℝ) +
        Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    simpa using hconst.add tendsto_loglog_div_log_nat
  have hratio' : Tendsto (fun n : ℕ ↦
      Real.log (Real.exp 1 * c * Real.log (n : ℝ)) /
        Real.log (n : ℝ)) atTop (nhds 0) := by
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero 1) hc.ne') hlog.ne',
      Real.log_mul (Real.exp_ne_zero 1) hc.ne', Real.log_exp]
    ring
  have hsmall := hratio'.eventually (Iio_mem_nhds (show 0 < c / 20 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmallN hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have := (div_lt_iff₀ hlog).1 hsmallN
  nlinarith

/-- The two pointwise estimates in Range III hold uniformly on their
explicit index sets. -/
theorem eventually_largeExpansion_pointwise {c : ℝ} (hc : 0 < c) :
    (∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLinearExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-largeLinearCoefficient * (n : ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLogExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 -
          c * (n : ℝ) * Real.log (n : ℝ) / 16)) := by
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have habs := eventually_large_linear_log_absorbed hc
  constructor
  · filter_upwards [hp, habs, eventually_ge_atTop 2] with n hpN habsN hn
    intro s hsMem
    have hsData := mem_largeLinearExpansionIndices.mp hsMem
    have hs : 1 ≤ s := hsData.1
    have hsLower := hsData.2.2.1
    have htwelve := hsData.2.2.2
    have hthree : 3 * s ≤ n := by omega
    convert expansionBinomialUnionTerm_le_large_linear hc hn hs hthree htwelve
        hpN.1 hpN.2 hsLower habsN using 1 <;>
      simp only [largeLinearCoefficient] <;> ring
  · filter_upwards [hp, eventually_ge_atTop 2] with n hpN hn
    intro s hsMem
    have hsData := mem_largeLogExpansionIndices.mp hsMem
    have hs : 1 ≤ s := hsData.1
    have htwelve := hsData.2.2.1
    have hquarter := hsData.2.2.2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hthreeR : 3 * (s : ℝ) ≤ (n : ℝ) := by
      nlinarith
    have hthree : 3 * s ≤ n := by exact_mod_cast hthreeR
    exact expansionBinomialUnionTerm_le_large_log hc hn hs hthree htwelve hquarter
      hpN.1 hpN.2

/-- Exact Range-I sum convergence, assuming the concrete pointwise estimate
eventually holds. -/
theorem tendsto_smallExpansionSum_zero_of_pointwise
    {c δ : ℝ} (hδ : 0 < δ)
    (hprob : ∀ᶠ n : ℕ in atTop, rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ᶠ n : ℕ in atTop, ∀ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤
        (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s) :
    Tendsto (fun n ↦ ∑ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm c n s) atTop (nhds 0) := by
  apply tendsto_small_range_sum_zero (Real.exp 3 * c ^ 2 / 4) δ (by positivity) hδ
      smallExpansionIndices (expansionBinomialUnionTerm c)
  · intro n s hs
    exact ⟨(mem_smallExpansionIndices.mp hs).1, (mem_smallExpansionIndices.mp hs).2.1⟩
  · filter_upwards [hprob] with n hp
    exact fun s _ ↦ expansionBinomialUnionTerm_nonneg hp.1 hp.2
  · exact hpoint

/-- Exact Range-II sum convergence from its concrete pointwise envelope. -/
theorem tendsto_mediumExpansionSum_zero_of_pointwise
    {c : ℝ} (hc : 0 < c)
    (hprob : ∀ᶠ n : ℕ in atTop, rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ᶠ n : ℕ in atTop, ∀ s ∈ mediumExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ))) :
    Tendsto (fun n ↦ ∑ s ∈ mediumExpansionIndices c n,
      expansionBinomialUnionTerm c n s) atTop (nhds 0) := by
  apply tendsto_medium_range_sum_zero hc (mediumExpansionIndices c)
      (expansionBinomialUnionTerm c)
  · exact card_mediumExpansionIndices_le c
  · intro n s hs
    exact (mem_mediumExpansionIndices.mp hs).2.2.1
  · filter_upwards [hprob] with n hp
    exact fun s _ ↦ expansionBinomialUnionTerm_nonneg hp.1 hp.2
  · exact hpoint

/-- Exact Range-III sum convergence from its two concrete pointwise
envelopes. -/
theorem tendsto_largeExpansionSum_zero_of_pointwise
    {c : ℝ} (hc : 0 < c)
    (hprob : ∀ᶠ n : ℕ in atTop, rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1)
    (hlinear : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLinearExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-largeLinearCoefficient * (n : ℝ)))
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLogExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 -
          c * (n : ℝ) * Real.log (n : ℝ) / 16)) :
    Tendsto (fun n ↦
      (∑ s ∈ largeLinearExpansionIndices c n, expansionBinomialUnionTerm c n s) +
      ∑ s ∈ largeLogExpansionIndices n, expansionBinomialUnionTerm c n s)
      atTop (nhds 0) := by
  apply tendsto_large_range_sum_zero hc (largeLinearExpansionIndices c)
      largeLogExpansionIndices (expansionBinomialUnionTerm c)
      (expansionBinomialUnionTerm c)
  · exact card_largeLinearExpansionIndices_le c
  · exact card_largeLogExpansionIndices_le
  · filter_upwards [hprob] with n hp
    exact fun s _ ↦ expansionBinomialUnionTerm_nonneg hp.1 hp.2
  · filter_upwards [hprob] with n hp
    exact fun s _ ↦ expansionBinomialUnionTerm_nonneg hp.1 hp.2
  · exact hlinear
  · exact hlog

/-- End-to-end finite summation of all four analytic pieces. -/
theorem tendsto_allExpansionRangeSums_zero_of_pointwise
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hprob : ∀ᶠ n : ℕ in atTop, rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ∀ᶠ n : ℕ in atTop, ∀ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤
        (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s)
    (hmedium : ∀ᶠ n : ℕ in atTop, ∀ s ∈ mediumExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)))
    (hlinear : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLinearExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-largeLinearCoefficient * (n : ℝ)))
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLogExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 -
          c * (n : ℝ) * Real.log (n : ℝ) / 16)) :
    Tendsto (fun n ↦
      (∑ s ∈ smallExpansionIndices n, expansionBinomialUnionTerm c n s) +
      (∑ s ∈ mediumExpansionIndices c n, expansionBinomialUnionTerm c n s) +
      (∑ s ∈ largeLinearExpansionIndices c n, expansionBinomialUnionTerm c n s) +
      ∑ s ∈ largeLogExpansionIndices n, expansionBinomialUnionTerm c n s)
      atTop (nhds 0) := by
  have hs := tendsto_smallExpansionSum_zero_of_pointwise hδ hprob hsmall
  have hm := tendsto_mediumExpansionSum_zero_of_pointwise hc hprob hmedium
  have hl := tendsto_largeExpansionSum_zero_of_pointwise hc hprob hlinear hlog
  simpa [add_assoc] using (hs.add hm).add hl

/-- Concrete Range-I sum limit for `c = 1+δ`. -/
theorem tendsto_smallExpansionSum_zero {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n ↦ ∑ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm (1 + δ) n s) atTop (nhds 0) := by
  exact tendsto_smallExpansionSum_zero_of_pointwise hδ
    (eventually_rangeOneProbability_mem_Icc (by linarith : 0 < (1 + δ : ℝ)))
    (eventually_smallExpansion_pointwise (by linarith) hδ hδ1 le_rfl)

/-- Concrete Range-II sum limit for `c = 1+δ`. -/
theorem tendsto_mediumExpansionSum_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n ↦ ∑ s ∈ mediumExpansionIndices (1 + δ) n,
      expansionBinomialUnionTerm (1 + δ) n s) atTop (nhds 0) := by
  have hc : 0 < (1 + δ : ℝ) := by linarith
  exact tendsto_mediumExpansionSum_zero_of_pointwise hc
    (eventually_rangeOneProbability_mem_Icc hc)
    (eventually_mediumExpansion_pointwise hc)

/-- Concrete Range-III sum limit for `c = 1+δ`. -/
theorem tendsto_largeExpansionSum_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n ↦
      (∑ s ∈ largeLinearExpansionIndices (1 + δ) n,
        expansionBinomialUnionTerm (1 + δ) n s) +
      ∑ s ∈ largeLogExpansionIndices n,
        expansionBinomialUnionTerm (1 + δ) n s) atTop (nhds 0) := by
  have hc : 0 < (1 + δ : ℝ) := by linarith
  have hpoint := eventually_largeExpansion_pointwise hc
  exact tendsto_largeExpansionSum_zero_of_pointwise hc
    (eventually_rangeOneProbability_mem_Icc hc) hpoint.1 hpoint.2

/-- All four concrete range sums tend to zero. -/
theorem tendsto_allExpansionRangeSums_zero {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n ↦
      (∑ s ∈ smallExpansionIndices n,
        expansionBinomialUnionTerm (1 + δ) n s) +
      (∑ s ∈ mediumExpansionIndices (1 + δ) n,
        expansionBinomialUnionTerm (1 + δ) n s) +
      (∑ s ∈ largeLinearExpansionIndices (1 + δ) n,
        expansionBinomialUnionTerm (1 + δ) n s) +
      ∑ s ∈ largeLogExpansionIndices n,
        expansionBinomialUnionTerm (1 + δ) n s) atTop (nhds 0) := by
  have hc : 0 < (1 + δ : ℝ) := by linarith
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have hlarge := eventually_largeExpansion_pointwise hc
  exact tendsto_allExpansionRangeSums_zero_of_pointwise hc hδ hp
    (eventually_smallExpansion_pointwise hc hδ hδ1 le_rfl)
    (eventually_mediumExpansion_pointwise hc) hlarge.1 hlarge.2

/-- The exact union-bound sum tends to zero whenever the four concrete
pointwise envelopes hold.  This is the adapter-neutral final summation
statement used by the graph-probability layer. -/
theorem tendsto_totalExpansionBinomialUnionTerm_zero_of_pointwise
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hprob : ∀ᶠ n : ℕ in atTop,
      rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ∀ᶠ n : ℕ in atTop, ∀ s ∈ smallExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤
        (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s)
    (hmedium : ∀ᶠ n : ℕ in atTop, ∀ s ∈ mediumExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)))
    (hlinear : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLinearExpansionIndices c n,
      expansionBinomialUnionTerm c n s ≤
        Real.exp (-largeLinearCoefficient * (n : ℝ)))
    (hlog : ∀ᶠ n : ℕ in atTop, ∀ s ∈ largeLogExpansionIndices n,
      expansionBinomialUnionTerm c n s ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 -
          c * (n : ℝ) * Real.log (n : ℝ) / 16)) :
    Tendsto (fun n ↦ ∑ s ∈ Finset.range (n / 4 + 1),
      expansionBinomialUnionTerm c n s) atTop (nhds 0) := by
  have hranges := tendsto_allExpansionRangeSums_zero_of_pointwise
    hc hδ hprob hsmall hmedium hlinear hlog
  apply squeeze_zero'
  · filter_upwards [hprob] with n hp
    exact Finset.sum_nonneg fun s _ ↦ expansionBinomialUnionTerm_nonneg hp.1 hp.2
  · filter_upwards [hprob] with n hp
    exact expansion_total_sum_le_range_sums hp.1 hp.2
  · exact hranges

/-- General concrete range-sum theorem.  The small-range slack `δ` may be
strictly smaller than `c - 1`; this is needed when the target edge-density
constant is more than two. -/
theorem tendsto_allExpansionRangeSums_zero_general {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmargin : 1 + δ ≤ c) :
    Tendsto (fun n ↦
      (∑ s ∈ smallExpansionIndices n,
        expansionBinomialUnionTerm c n s) +
      (∑ s ∈ mediumExpansionIndices c n,
        expansionBinomialUnionTerm c n s) +
      (∑ s ∈ largeLinearExpansionIndices c n,
        expansionBinomialUnionTerm c n s) +
      ∑ s ∈ largeLogExpansionIndices n,
        expansionBinomialUnionTerm c n s) atTop (nhds 0) := by
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have hlarge := eventually_largeExpansion_pointwise hc
  exact tendsto_allExpansionRangeSums_zero_of_pointwise hc hδ hp
    (eventually_smallExpansion_pointwise hc hδ hδ1 hmargin)
    (eventually_mediumExpansion_pointwise hc) hlarge.1 hlarge.2

/-- The exact generalized expansion union-bound sum tends to zero. -/
theorem tendsto_totalExpansionBinomialUnionTerm_zero_general {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmargin : 1 + δ ≤ c) :
    Tendsto (fun n ↦ ∑ s ∈ Finset.range (n / 4 + 1),
      expansionBinomialUnionTerm c n s) atTop (nhds 0) := by
  have hp := eventually_rangeOneProbability_mem_Icc hc
  have hlarge := eventually_largeExpansion_pointwise hc
  exact tendsto_totalExpansionBinomialUnionTerm_zero_of_pointwise hc hδ hp
    (eventually_smallExpansion_pointwise hc hδ hδ1 hmargin)
    (eventually_mediumExpansion_pointwise hc) hlarge.1 hlarge.2

/-- The exact expansion union-bound sum at density constant `1+δ` tends
to zero. -/
theorem tendsto_totalExpansionBinomialUnionTerm_zero {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n ↦ ∑ s ∈ Finset.range (n / 4 + 1),
      expansionBinomialUnionTerm (1 + δ) n s) atTop (nhds 0) := by
  exact tendsto_totalExpansionBinomialUnionTerm_zero_general
    (by linarith) hδ hδ1 le_rfl

end

end Erdos746
