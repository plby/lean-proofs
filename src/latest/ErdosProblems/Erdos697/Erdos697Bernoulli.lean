/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Sharp finite Bernoulli tail estimates for Erdős Problem 697

The CRT model in the main argument gives independent, non-identically
distributed Bernoulli variables.  The lemmas below prove Chernoff bounds
directly as identities and inequalities between finite sums over a
powerset.  The cutoff ratios are arbitrary fixed `r < 1` and `r > 1`;
this flexibility is what preserves Hall's sharp constant.
-/

open scoped BigOperators

namespace Erdos697.Bernoulli

noncomputable section

/-- The probability weight of the subset `T` in the independent Bernoulli
model indexed by `s`.  The definition is meaningful for every `T`; all
applications restrict to `T ⊆ s`. -/
def weight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (T : Finset ι) : ℝ :=
  (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)

theorem weight_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {T : Finset ι} (hT : T ∈ s.powerset) : 0 ≤ weight s p T := by
  have hsub : T ⊆ s := Finset.mem_powerset.mp hT
  exact mul_nonneg
    (Finset.prod_nonneg (fun i hi => hp0 i (hsub hi)))
    (Finset.prod_nonneg (fun i hi => by
      have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
      linarith [hp1 i his]))

/-- The independent Bernoulli weights sum to one. -/
theorem sum_weight_powerset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) :
    (∑ T ∈ s.powerset, weight s p T) = 1 := by
  unfold weight
  calc
    (∑ T ∈ s.powerset,
        (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)) =
        ∏ i ∈ s, (p i + (1 - p i)) := by
          rw [Finset.prod_add]
    _ = 1 := by simp

/-- Exact probability-generating-function identity. -/
theorem sum_pow_card_mul_weight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (a : ℝ) :
    (∑ T ∈ s.powerset, a ^ T.card * weight s p T) =
      ∏ i ∈ s, ((1 - p i) + p i * a) := by
  unfold weight
  calc
    (∑ T ∈ s.powerset,
        a ^ T.card * ((∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i))) =
        ∏ i ∈ s, (p i * a + (1 - p i)) := by
          rw [Finset.prod_add]
          apply Finset.sum_congr rfl
          intro T _
          have hprod_mul :
              (∏ i ∈ T, p i * a) =
                (∏ i ∈ T, p i) * a ^ T.card := by
            rw [Finset.prod_mul_distrib]
            simp [Finset.prod_const]
          rw [hprod_mul]
          ring
    _ = ∏ i ∈ s, ((1 - p i) + p i * a) := by
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- A lower-tail Chernoff bound at every fixed proportion `r < 1` of the
mean.  The explicit coefficient multiplying `EW` is strictly negative;
see `lower_exponent_neg`. -/
theorem lower_tail_chernoff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW r : ℝ} (hEW : EW = ∑ i ∈ s, p i)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hK : (K : ℝ) ≤ r * EW) :
    (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T) ≤
      Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
  classical
  let t : ℝ := (1 - r) / (2 * r)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := 1 / (1 + t) - 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have honept : 0 < 1 + t := by linarith
  have ha_le : a ≤ 1 / (1 + t) := by
    have hexp : 1 + t ≤ Real.exp t := by
      simpa [add_comm] using Real.add_one_le_exp t
    have hinv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ :=
      inv_anti₀ honept hexp
    simpa [a, Real.exp_neg, one_div] using hinv
  have hb_nonpos : b ≤ 0 := by
    dsimp [b]
    have : 1 / (1 + t) ≤ 1 := (div_le_one₀ honept).2 (by linarith)
    linarith
  have hfactor_nonneg : ∀ i ∈ s, 0 ≤ (1 - p i) + p i * a := by
    intro i hi
    nlinarith [hp0 i hi, hp1 i hi,
      mul_nonneg (hp0 i hi) ha_nonneg]
  have hfactor_le : ∀ i ∈ s,
      (1 - p i) + p i * a ≤ Real.exp (b * p i) := by
    intro i hi
    have hpa : p i * a ≤ p i * (1 / (1 + t)) :=
      mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
    calc
      (1 - p i) + p i * a
          ≤ (1 - p i) + p i * (1 / (1 + t)) := by linarith
      _ = 1 + b * p i := by dsimp [b]; ring
      _ = b * p i + 1 := by ring
      _ ≤ Real.exp (b * p i) := Real.add_one_le_exp _
  have hgen_le :
      (∑ T ∈ s.powerset, a ^ T.card * weight s p T) ≤
        Real.exp (b * EW) := by
    rw [sum_pow_card_mul_weight]
    calc
      ∏ i ∈ s, ((1 - p i) + p i * a)
          ≤ ∏ i ∈ s, Real.exp (b * p i) :=
            Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (b * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, ← hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T) ≤
        Real.exp (t * (K : ℝ)) *
          (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T)
          ≤ ∑ T ∈ s.powerset.filter (fun T => T.card < K),
              Real.exp (t * (K : ℝ)) *
                (a ^ T.card * weight s p T) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTpowerset : T ∈ s.powerset :=
              (Finset.mem_filter.mp hT).1
            have hTcard : T.card ≤ K :=
              Nat.le_of_lt (Finset.mem_filter.mp hT).2
            have hscale :
                1 ≤ Real.exp (t * (K : ℝ)) * a ^ T.card := by
              dsimp [a]
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.one_le_exp
              have hcast : (T.card : ℝ) ≤ K := by exact_mod_cast hTcard
              nlinarith
            have hwT : 0 ≤ weight s p T :=
              weight_nonneg s p hp0 hp1 hTpowerset
            calc
              weight s p T
                  ≤ (Real.exp (t * (K : ℝ)) * a ^ T.card) *
                      weight s p T := le_mul_of_one_le_left hwT hscale
              _ = Real.exp (t * (K : ℝ)) *
                    (a ^ T.card * weight s p T) := by ring
      _ = Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset.filter (fun T => T.card < K),
              a ^ T.card * weight s p T) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro T hT
                exact (Finset.mem_filter.mp hT).1
              · intro T hTpowerset _
                exact mul_nonneg (pow_nonneg ha_nonneg _)
                  (weight_nonneg s p hp0 hp1 hTpowerset)
            · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T)
        ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := htail_le_gen
    _ ≤ Real.exp (t * (K : ℝ)) * Real.exp (b * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp (t * (K : ℝ) + b * EW) := by rw [Real.exp_add]
    _ ≤ Real.exp ((r * t + b) * EW) := by
      apply Real.exp_le_exp.mpr
      have hEW_nonneg : 0 ≤ EW := by
        rw [hEW]
        exact Finset.sum_nonneg (fun i hi => hp0 i hi)
      nlinarith
    _ = Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
      rfl

/-- The coefficient in `lower_tail_chernoff` is negative. -/
theorem lower_exponent_neg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * ((1 - r) / (2 * r)) +
        (1 / (1 + ((1 - r) / (2 * r))) - 1) < 0 := by
  have hrne : r ≠ 0 := hr0.ne'
  have hrpne : r + 1 ≠ 0 := by linarith
  have h1rpne : 1 + r ≠ 0 := by linarith
  have hdenform :
      1 + (1 - r) / (2 * r) = (r + 1) / (2 * r) := by
    field_simp [hrne]
    ring
  have heq :
      r * ((1 - r) / (2 * r)) +
          (1 / (1 + ((1 - r) / (2 * r))) - 1) =
        -((1 - r) ^ 2) / (2 * (r + 1)) := by
    rw [hdenform]
    field_simp [hrne, hrpne, h1rpne]
    ring
  rw [heq]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos (sub_pos.mpr hr1)))
    (mul_pos (by norm_num) (by linarith))

/-- An upper-tail Chernoff bound at every fixed proportion `r > 1` of the
mean.  The explicit coefficient multiplying `EW` is strictly negative;
see `upper_exponent_neg`. -/
theorem upper_tail_chernoff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW r : ℝ} (hEW : EW = ∑ i ∈ s, p i)
    (hr : 1 < r)
    (hK : r * EW ≤ (K : ℝ)) :
    (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T) ≤
      Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
            (1 / (1 - ((r - 1) / (2 * r))) - 1)) * EW) := by
  classical
  let t : ℝ := (r - 1) / (2 * r)
  let a : ℝ := Real.exp t
  let b : ℝ := 1 / (1 - t) - 1
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_lt_one : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity : 0 < 2 * r)]
    linarith
  have hone_sub_t : 0 < 1 - t := sub_pos.mpr ht_lt_one
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have ha_le : a ≤ 1 / (1 - t) := by
    have hexp : 1 - t ≤ Real.exp (-t) := by
      convert Real.add_one_le_exp (-t) using 1 <;> ring
    have hinv : (Real.exp (-t))⁻¹ ≤ (1 - t)⁻¹ :=
      inv_anti₀ hone_sub_t hexp
    simpa [a, Real.exp_neg, one_div] using hinv
  have hfactor_nonneg : ∀ i ∈ s, 0 ≤ (1 - p i) + p i * a := by
    intro i hi
    nlinarith [hp0 i hi, hp1 i hi,
      mul_nonneg (hp0 i hi) ha_nonneg]
  have hfactor_le : ∀ i ∈ s,
      (1 - p i) + p i * a ≤ Real.exp (b * p i) := by
    intro i hi
    have hpa : p i * a ≤ p i * (1 / (1 - t)) :=
      mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
    calc
      (1 - p i) + p i * a
          ≤ (1 - p i) + p i * (1 / (1 - t)) := by linarith
      _ = 1 + b * p i := by dsimp [b]; ring
      _ = b * p i + 1 := by ring
      _ ≤ Real.exp (b * p i) := Real.add_one_le_exp _
  have hgen_le :
      (∑ T ∈ s.powerset, a ^ T.card * weight s p T) ≤
        Real.exp (b * EW) := by
    rw [sum_pow_card_mul_weight]
    calc
      ∏ i ∈ s, ((1 - p i) + p i * a)
          ≤ ∏ i ∈ s, Real.exp (b * p i) :=
            Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (b * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, ← hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T) ≤
        Real.exp (-(t * (K : ℝ))) *
          (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T)
          ≤ ∑ T ∈ s.powerset.filter (fun T => K ≤ T.card),
              Real.exp (-(t * (K : ℝ))) *
                (a ^ T.card * weight s p T) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTpowerset : T ∈ s.powerset :=
              (Finset.mem_filter.mp hT).1
            have hTcard : K ≤ T.card := (Finset.mem_filter.mp hT).2
            have hscale :
                1 ≤ Real.exp (-(t * (K : ℝ))) * a ^ T.card := by
              dsimp [a]
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.one_le_exp
              have hcast : (K : ℝ) ≤ T.card := by exact_mod_cast hTcard
              nlinarith
            have hwT : 0 ≤ weight s p T :=
              weight_nonneg s p hp0 hp1 hTpowerset
            calc
              weight s p T
                  ≤ (Real.exp (-(t * (K : ℝ))) * a ^ T.card) *
                      weight s p T := le_mul_of_one_le_left hwT hscale
              _ = Real.exp (-(t * (K : ℝ))) *
                    (a ^ T.card * weight s p T) := by ring
      _ = Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card),
              a ^ T.card * weight s p T) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro T hT
                exact (Finset.mem_filter.mp hT).1
              · intro T hTpowerset _
                exact mul_nonneg (pow_nonneg ha_nonneg _)
                  (weight_nonneg s p hp0 hp1 hTpowerset)
            · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T)
        ≤ Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := htail_le_gen
    _ ≤ Real.exp (-(t * (K : ℝ))) * Real.exp (b * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp (-(t * (K : ℝ)) + b * EW) := by rw [Real.exp_add]
    _ ≤ Real.exp ((-(r * t) + b) * EW) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
            (1 / (1 - ((r - 1) / (2 * r))) - 1)) * EW) := by
      rfl

/-- The coefficient in `upper_tail_chernoff` is negative. -/
theorem upper_exponent_neg {r : ℝ} (hr : 1 < r) :
    (-(r * ((r - 1) / (2 * r)))) +
        (1 / (1 - ((r - 1) / (2 * r))) - 1) < 0 := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hrne : r ≠ 0 := hr0.ne'
  have hrpne : r + 1 ≠ 0 := by linarith
  have h1rpne : 1 + r ≠ 0 := by linarith
  have hdenform :
      1 - (r - 1) / (2 * r) = (r + 1) / (2 * r) := by
    field_simp [hrne]
    ring
  have heq :
      (-(r * ((r - 1) / (2 * r)))) +
          (1 / (1 - ((r - 1) / (2 * r))) - 1) =
        -((r - 1) ^ 2) / (2 * (r + 1)) := by
    rw [hdenform]
    field_simp [hrne, hrpne, h1rpne]
    ring
  rw [heq]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos (sub_pos.mpr hr)))
    (mul_pos (by norm_num) (by linarith))

/-! ## Odds factorization -/

def odds {I : Type*} (p : I → ℝ) (i : I) : ℝ :=
  p i / (1 - p i)

def zeroBase {I : Type*} (s : Finset I) (p : I → ℝ) : ℝ :=
  ∏ i ∈ s, (1 - p i)

theorem weight_eq_zeroBase_mul_prod_odds
    {I : Type*} [DecidableEq I]
    (s T : Finset I) (p : I → ℝ) (hT : T ⊆ s)
    (hp1 : ∀ i ∈ s, p i < 1) :
    weight s p T = zeroBase s p * ∏ i ∈ T, odds p i := by
  have hdisj : Disjoint T (s \ T) := Finset.disjoint_sdiff
  have hunion : T ∪ (s \ T) = s := Finset.union_sdiff_of_subset hT
  have hsplit : zeroBase s p =
      (∏ i ∈ T, (1 - p i)) * ∏ i ∈ s \ T, (1 - p i) := by
    unfold zeroBase
    rw [← Finset.prod_union hdisj, hunion]
  have hcancel :
      (∏ i ∈ T, (1 - p i)) * ∏ i ∈ T, odds p i =
        ∏ i ∈ T, p i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hiS := hT hi
    have hne : 1 - p i ≠ 0 := (sub_pos.mpr (hp1 i hiS)).ne'
    unfold odds
    field_simp
  unfold weight
  rw [hsplit]
  calc
    (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i) =
        ((∏ i ∈ T, (1 - p i)) * ∏ i ∈ T, odds p i) *
          ∏ i ∈ s \ T, (1 - p i) := by rw [hcancel]
    _ = ((∏ i ∈ T, (1 - p i)) *
          ∏ i ∈ s \ T, (1 - p i)) *
            ∏ i ∈ T, odds p i := by ring

theorem zeroBase_nonneg {I : Type*} [DecidableEq I]
    (s : Finset I) (p : I → ℝ) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    0 ≤ zeroBase s p := by
  unfold zeroBase
  exact Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hp1 i hi)

theorem zeroBase_le_one {I : Type*} [DecidableEq I]
    (s : Finset I) (p : I → ℝ) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i ≤ 1) :
    zeroBase s p ≤ 1 := by
  unfold zeroBase
  exact Finset.prod_le_one (fun i hi => by linarith [hp1 i hi])
    (fun i hi => by linarith [hp0 i hi])

end

end Erdos697.Bernoulli
