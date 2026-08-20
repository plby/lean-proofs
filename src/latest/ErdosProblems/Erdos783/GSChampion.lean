import ErdosProblems.Erdos783.Erdos783Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos783

noncomputable section

def logAtanhPartial (x : ℝ) (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

def logAtanhUpper (x : ℝ) (n : ℕ) : ℝ :=
  logAtanhPartial x n + 2 * x ^ (2 * n + 1) / (1 - x ^ 2)

lemma logAtanhPartial_le_log_of_eq
    {q x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq : q = (1 + x) / (1 - x)) (n : ℕ) :
    logAtanhPartial x n ≤ Real.log q := by
  have h := Real.sum_range_le_log_div hx0 hx1 n
  rw [← hq] at h
  unfold logAtanhPartial
  linarith

lemma log_le_logAtanhUpper_of_eq
    {q x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq : q = (1 + x) / (1 - x)) (n : ℕ) :
    Real.log q ≤ logAtanhUpper x n := by
  have h := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [← hq] at h
  unfold logAtanhUpper logAtanhPartial
  calc
    Real.log q = 2 * (1 / 2 * Real.log q) := by ring
    _ ≤ 2 * ((∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * n + 1) / (1 - x ^ 2)) := by nlinarith
    _ = 2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1) +
        2 * x ^ (2 * n + 1) / (1 - x ^ 2) := by ring

lemma log_three_halves_bounds :
    (40541 / 100000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (40547 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (3 / 2 : ℝ)) (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 4
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (3 / 2 : ℝ)) (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 4
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_thirtyseven_twenty_bounds :
    (61518 / 100000 : ℝ) < Real.log (37 / 20) ∧
      Real.log (37 / 20) < (61520 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (37 / 20 : ℝ)) (x := (17 / 57 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 6
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (37 / 20 : ℝ)) (x := (17 / 57 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 6
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_eight_fifths_bounds :
    (47000 / 100000 : ℝ) < Real.log (8 / 5) ∧
      Real.log (8 / 5) < (47001 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (8 / 5 : ℝ)) (x := (3 / 13 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 5
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (8 / 5 : ℝ)) (x := (3 / 13 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 5
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_thirtythree_twentyfive_bounds :
    (27763 / 100000 : ℝ) < Real.log (33 / 25) ∧
      Real.log (33 / 25) < (27764 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (33 / 25 : ℝ)) (x := (4 / 29 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 4
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (33 / 25 : ℝ)) (x := (4 / 29 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 4
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_sixtynine_forty_bounds :
    (54522 / 100000 : ℝ) < Real.log (69 / 40) ∧
      Real.log (69 / 40) < (54523 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (69 / 40 : ℝ)) (x := (29 / 109 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 6
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (69 / 40 : ℝ)) (x := (29 / 109 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 6
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_fiftyseven_fifty_bounds :
    (13102 / 100000 : ℝ) < Real.log (57 / 50) ∧
      Real.log (57 / 50) < (13103 / 100000 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (57 / 50 : ℝ)) (x := (7 / 107 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 3
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (57 / 50 : ℝ)) (x := (7 / 107 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 3
  constructor <;> norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma dickmanRho_three_halves_div_thirtyseven_twenty :
    (57 / 37 : ℝ) <
      dickmanRho (3 / 2) / dickmanRho (37 / 20) := by
  rw [dickmanRho_eq_one_sub_log (by norm_num) (by norm_num),
    dickmanRho_eq_one_sub_log (by norm_num) (by norm_num)]
  have h15 := log_three_halves_bounds
  have h185 := log_thirtyseven_twenty_bounds
  have hden : 0 < 1 - Real.log (37 / 20) := by linarith
  rw [lt_div_iff₀ hden]
  norm_num at h15 h185 ⊢
  nlinarith

lemma dickmanRho_three_halves_ge_twenty_eight_twentyfive :
    (28 / 25 : ℝ) * dickmanRho (8 / 5) ≤
      dickmanRho (3 / 2) := by
  rw [dickmanRho_eq_one_sub_log (by norm_num) (by norm_num),
    dickmanRho_eq_one_sub_log (by norm_num) (by norm_num)]
  have h15 := log_three_halves_bounds
  have h16 := log_eight_fifths_bounds
  norm_num at h15 h16 ⊢
  nlinarith

lemma dickmanRho_thirtythree_twentyfive_div_sixtynine_forty :
    (109 / 69 : ℝ) <
      dickmanRho (33 / 25) / dickmanRho (69 / 40) := by
  rw [dickmanRho_eq_one_sub_log (by norm_num) (by norm_num),
    dickmanRho_eq_one_sub_log (by norm_num) (by norm_num)]
  have h132 := log_thirtythree_twentyfive_bounds
  have h1725 := log_sixtynine_forty_bounds
  have hden : 0 < 1 - Real.log (69 / 40) := by linarith
  rw [lt_div_iff₀ hden]
  norm_num at h132 h1725 ⊢
  nlinarith

lemma dickmanRho_thirtythree_twentyfive_ge_thirtyfour_twentyfive :
    (34 / 25 : ℝ) * dickmanRho (8 / 5) ≤
      dickmanRho (33 / 25) := by
  rw [dickmanRho_eq_one_sub_log (by norm_num) (by norm_num),
    dickmanRho_eq_one_sub_log (by norm_num) (by norm_num)]
  have h132 := log_thirtythree_twentyfive_bounds
  have h16 := log_eight_fifths_bounds
  norm_num at h132 h16 ⊢
  nlinarith

lemma dickmanRho_fiftyseven_fifty_div_eight_fifths :
    (13 / 8 : ℝ) <
      dickmanRho (57 / 50) / dickmanRho (8 / 5) := by
  rw [dickmanRho_eq_one_sub_log (by norm_num) (by norm_num),
    dickmanRho_eq_one_sub_log (by norm_num) (by norm_num)]
  have h114 := log_fiftyseven_fifty_bounds
  have h16 := log_eight_fifths_bounds
  have hden : 0 < 1 - Real.log (8 / 5) := by linarith
  rw [lt_div_iff₀ hden]
  norm_num at h114 h16 ⊢
  nlinarith

lemma gs_champion_corner_three_halves (eta : ℝ) (heta : 1 ≤ eta) :
    (3 / 2 : ℝ) ≥
      eta * (1 + 1 - 1 * eta) * ((13 / 5 : ℝ) - (3 / 2 : ℝ)⁻¹) +
        1 + eta - (13 / 5 : ℝ) := by
  norm_num [inv_eq_one_div]
  nlinarith [sq_nonneg (eta - (73 / 58 : ℝ))]

lemma gs_champion_corner_thirtythree_twentyfive
    (eta : ℝ) (heta : 1 ≤ eta) :
    (33 / 25 : ℝ) ≥
      eta * (1 + (28 / 25 : ℝ) - (28 / 25 : ℝ) * eta) *
          ((13 / 5 : ℝ) - (33 / 25 : ℝ)⁻¹) +
        1 + eta - (13 / 5 : ℝ) := by
  norm_num [inv_eq_one_div]
  nlinarith [sq_nonneg (eta - (6 / 5 : ℝ))]

lemma gs_champion_corner_fiftyseven_fifty
    (eta : ℝ) (heta : 1 ≤ eta) :
    (57 / 50 : ℝ) ≥
      eta * (1 + (34 / 25 : ℝ) - (34 / 25 : ℝ) * eta) *
          ((13 / 5 : ℝ) - (57 / 50 : ℝ)⁻¹) +
        1 + eta - (13 / 5 : ℝ) := by
  norm_num [inv_eq_one_div]
  nlinarith [sq_nonneg (eta - (27 / 25 : ℝ))]

def gsChampionDefect (a e c eta : ℝ) : ℝ :=
  a - (eta * (1 + c - c * eta) * (e - a⁻¹) + 1 + eta - e)

lemma gsChampionDefect_mono_coefficient
    {a e c₀ c eta : ℝ}
    (ha : 1 ≤ a) (he : 13 / 5 ≤ e)
    (hc : c₀ ≤ c) (heta : 1 ≤ eta) :
    gsChampionDefect a e c₀ eta ≤ gsChampionDefect a e c eta := by
  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hinvLe : a⁻¹ ≤ 1 := by
    exact (inv_le_one₀ haPos).2 ha
  have hlambda : 0 ≤ e - a⁻¹ := by
    norm_num at he
    linarith
  unfold gsChampionDefect
  have hprod : 0 ≤ eta * (c - c₀) * (eta - 1) * (e - a⁻¹) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hc))
      (sub_nonneg.mpr heta)) hlambda
  nlinarith

lemma gsChampionDefect_mono_endpoint
    {a e₀ e c eta : ℝ}
    (hc : 1 ≤ c) (heta : 1 ≤ eta) (he : e₀ ≤ e) :
    gsChampionDefect a e₀ c eta ≤ gsChampionDefect a e c eta := by
  unfold gsChampionDefect
  have hfactor :
      0 ≤ 1 - eta * (1 + c - c * eta) := by
    have h1 : 0 ≤ eta - 1 := sub_nonneg.mpr heta
    have h2 : 0 ≤ c * eta - 1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) hfactor]

lemma inv_sub_inv_le_sub_of_one_le
    {a₀ a : ℝ} (ha₀ : 1 ≤ a₀) (haa₀ : a₀ ≤ a) :
    a₀⁻¹ - a⁻¹ ≤ a - a₀ := by
  have ha₀pos : 0 < a₀ := lt_of_lt_of_le zero_lt_one ha₀
  have haPos : 0 < a := ha₀pos.trans_le haa₀
  rw [inv_sub_inv ha₀pos.ne' haPos.ne']
  have hdiff : 0 ≤ a - a₀ := sub_nonneg.mpr haa₀
  have hprod : 1 ≤ a₀ * a := by nlinarith
  rw [div_le_iff₀ (mul_pos ha₀pos haPos)]
  nlinarith [mul_nonneg hdiff (sub_nonneg.mpr hprod)]

lemma gsChampionDefect_mono_base
    {a₀ a e c eta : ℝ}
    (ha₀ : 1 ≤ a₀) (haa₀ : a₀ ≤ a)
    (hc : 1 ≤ c) (heta : 1 ≤ eta) :
    gsChampionDefect a₀ e c eta ≤ gsChampionDefect a e c eta := by
  have hinv := inv_sub_inv_le_sub_of_one_le ha₀ haa₀
  have hfactor : eta * (1 + c - c * eta) ≤ 1 := by
    have h1 : 0 ≤ eta - 1 := sub_nonneg.mpr heta
    have h2 : 0 ≤ c * eta - 1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  have hinvNonneg : 0 ≤ a₀⁻¹ - a⁻¹ := by
    have ha₀pos : 0 < a₀ := lt_of_lt_of_le zero_lt_one ha₀
    have haPos : 0 < a := ha₀pos.trans_le haa₀
    exact sub_nonneg.mpr ((inv_le_inv₀ haPos ha₀pos).2 haa₀)
  unfold gsChampionDefect
  have hmul := mul_le_mul_of_nonneg_right hfactor hinvNonneg
  nlinarith

lemma gsChampionDefect_of_corner
    {a₀ a e c₀ c eta : ℝ}
    (ha₀ : 1 ≤ a₀) (haa₀ : a₀ ≤ a)
    (he : 13 / 5 ≤ e) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c)
    (heta : 1 ≤ eta)
    (hcorner : 0 ≤ gsChampionDefect a₀ (13 / 5) c₀ eta) :
    0 ≤ gsChampionDefect a e c eta := by
  exact hcorner.trans
    ((gsChampionDefect_mono_base ha₀ haa₀ hc₀ heta).trans
      ((gsChampionDefect_mono_endpoint hc₀ heta he).trans
        (gsChampionDefect_mono_coefficient
          (ha₀.trans haa₀) he hc heta)))

lemma gsChampionDefect_of_large_coefficient
    {a e c eta : ℝ}
    (ha : 1 ≤ a) (he : 13 / 5 ≤ e) (heta : 1 ≤ eta)
    (hc : 1 + (e - a⁻¹)⁻¹ ≤ c) :
    0 ≤ gsChampionDefect a e c eta := by
  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hinvLe : a⁻¹ ≤ 1 := (inv_le_one₀ haPos).2 ha
  have hlambda : 0 < e - a⁻¹ := by
    norm_num at he
    linarith
  have hcLinear : (1 - c) * (e - a⁻¹) + 1 ≤ 0 := by
    have hc' : (e - a⁻¹)⁻¹ ≤ c - 1 := by linarith
    rw [inv_eq_one_div] at hc'
    have h := (div_le_iff₀ hlambda).mp hc'
    nlinarith
  have hdrop :
      eta * (1 + c - c * eta) * (e - a⁻¹) + 1 + eta - e ≤
        (e - a⁻¹) + 2 - e := by
    have hx : 0 ≤ eta - 1 := sub_nonneg.mpr heta
    have hcx : 0 ≤ c * (e - a⁻¹) * (eta - 1) := by
      have hc0 : 0 ≤ c := by
        have : 0 < 1 + (e - a⁻¹)⁻¹ := by positivity
        linarith
      positivity
    nlinarith [mul_nonneg hx (neg_nonneg.mpr hcLinear),
      mul_nonneg hx hcx]
  have hbase : 2 - a⁻¹ ≤ a := by
    rw [sub_le_iff_le_add]
    rw [← (mul_le_mul_iff_of_pos_left haPos)]
    field_simp [haPos.ne']
    nlinarith [sq_nonneg (a - 1)]
  unfold gsChampionDefect
  linarith

lemma dickmanRho_ratio_ge_of_bounds
    {a A B b k : ℝ}
    (ha0 : 0 ≤ a) (haA : a ≤ A)
    (hB0 : 0 ≤ B) (hBb : B ≤ b)
    (hk0 : 0 ≤ k) (hk : k * dickmanRho B ≤ dickmanRho A) :
    k ≤ dickmanRho a / dickmanRho b := by
  have hb0 : 0 ≤ b := hB0.trans hBb
  have hρb : 0 < dickmanRho b := dickmanRho_profile.2.2.1 b hb0
  rw [le_div_iff₀ hρb]
  calc
    k * dickmanRho b ≤ k * dickmanRho B :=
      mul_le_mul_of_nonneg_left
        (antitoneOn_dickmanRho_Ici_zero hB0 hb0 hBb) hk0
    _ ≤ dickmanRho A := hk
    _ ≤ dickmanRho a :=
      antitoneOn_dickmanRho_Ici_zero ha0 (ha0.trans haA) haA

lemma one_add_inv_scale_le_endpoint_ratio
    {a e : ℝ} (ha : 1 ≤ a) (he : 13 / 5 ≤ e) :
    1 + (e - a⁻¹)⁻¹ ≤ e / (e - 1) := by
  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hinvLe : a⁻¹ ≤ 1 := (inv_le_one₀ haPos).2 ha
  have hsmall : 0 < e - 1 := by norm_num at he ⊢; linarith
  have hlarge : 0 < e - a⁻¹ := by linarith
  have hden : e - 1 ≤ e - a⁻¹ := by linarith
  have hinv : (e - a⁻¹)⁻¹ ≤ (e - 1)⁻¹ :=
    (inv_le_inv₀ hlarge hsmall).2 hden
  calc
    1 + (e - a⁻¹)⁻¹ ≤ 1 + (e - 1)⁻¹ := by linarith
    _ = e / (e - 1) := by
      rw [inv_eq_one_div]
      field_simp [hsmall.ne']
      <;> ring

lemma endpoint_ratio_antitone
    {e₀ e : ℝ} (he₀ : 1 < e₀) (hee₀ : e₀ ≤ e) :
    e / (e - 1) ≤ e₀ / (e₀ - 1) := by
  have he : 1 < e := he₀.trans_le hee₀
  have hinv : (e - 1)⁻¹ ≤ (e₀ - 1)⁻¹ := by
    apply (inv_le_inv₀ (by linarith) (by linarith)).2
    linarith
  rw [show e / (e - 1) = 1 + (e - 1)⁻¹ by
      rw [inv_eq_one_div]; field_simp [ne_of_gt (by linarith : 0 < e - 1)] <;> ring,
    show e₀ / (e₀ - 1) = 1 + (e₀ - 1)⁻¹ by
      rw [inv_eq_one_div]; field_simp [ne_of_gt (by linarith : 0 < e₀ - 1)] <;> ring]
  linarith

/-- The exact rational, six-cell certificate for the numerical inequality in
Section 7 of Granville--Soundararajan.  This formulation is deliberately
separated from the integral argument which supplies `a`, `e`, and `eta`. -/
theorem dickmanChampionScalar
    {a e eta : ℝ}
    (he : 13 / 5 ≤ e) (ha : 1 ≤ a) (hae : a ≤ e - 1)
    (heta : 1 ≤ eta) :
    let c := dickmanRho a / dickmanRho (e - 1)
    a ≥ eta * (1 + c - c * eta) * (e - a⁻¹) + 1 + eta - e := by
  dsimp only
  let c := dickmanRho a / dickmanRho (e - 1)
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ e - 1 := by norm_num at he ⊢; linarith
  have hc0 : 0 ≤ c := by
    exact div_nonneg (dickmanRho_nonneg ha0) (dickmanRho_nonneg hb0)
  suffices hdef : 0 ≤ gsChampionDefect a e c eta by
    exact sub_nonneg.mp hdef
  by_cases ha15 : (3 / 2 : ℝ) ≤ a
  · have hc1 : 1 ≤ c := by
      have hρden : 0 < dickmanRho (e - 1) :=
        dickmanRho_profile.2.2.1 (e - 1) hb0
      rw [show c = dickmanRho a / dickmanRho (e - 1) by rfl,
        le_div_iff₀ hρden]
      simpa using antitoneOn_dickmanRho_Ici_zero ha0 hb0 hae
    apply gsChampionDefect_of_corner (a₀ := (3 / 2 : ℝ))
      (c₀ := 1) (by norm_num) ha15 he (by norm_num) hc1 heta
    simpa [gsChampionDefect] using gs_champion_corner_three_halves eta heta
  · have haLt15 : a < 3 / 2 := lt_of_not_ge ha15
    by_cases he285 : (57 / 20 : ℝ) ≤ e
    · have hkbase : (57 / 37 : ℝ) * dickmanRho (37 / 20) ≤
          dickmanRho (3 / 2) := by
        have hpos : 0 < dickmanRho (37 / 20) :=
          dickmanRho_profile.2.2.1 _ (by norm_num)
        exact (lt_div_iff₀ hpos).mp
          dickmanRho_three_halves_div_thirtyseven_twenty |>.le
      have hb : (37 / 20 : ℝ) ≤ e - 1 := by linarith
      have hkc : (57 / 37 : ℝ) ≤ c := by
        exact dickmanRho_ratio_ge_of_bounds ha0 haLt15.le (by norm_num) hb
          (by norm_num) hkbase
      have hratio : e / (e - 1) ≤ (57 / 37 : ℝ) := by
        have h := endpoint_ratio_antitone (e₀ := (57 / 20 : ℝ))
          (e := e) (by norm_num) he285
        norm_num at h ⊢
        exact h
      apply gsChampionDefect_of_large_coefficient ha he heta
      exact (one_add_inv_scale_le_endpoint_ratio ha he).trans
        (hratio.trans hkc)
    · have heLt285 : e < 57 / 20 := lt_of_not_ge he285
      by_cases ha132 : (33 / 25 : ℝ) ≤ a
      · have hkc : (28 / 25 : ℝ) ≤ c := by
          apply dickmanRho_ratio_ge_of_bounds ha0 haLt15.le (by norm_num)
            (show (8 / 5 : ℝ) ≤ e - 1 by linarith) (by norm_num)
          exact dickmanRho_three_halves_ge_twenty_eight_twentyfive
        apply gsChampionDefect_of_corner (a₀ := (33 / 25 : ℝ))
          (c₀ := (28 / 25 : ℝ)) (by norm_num) ha132 he
          (by norm_num) hkc heta
        simpa [gsChampionDefect] using
          gs_champion_corner_thirtythree_twentyfive eta heta
      · have haLt132 : a < 33 / 25 := lt_of_not_ge ha132
        by_cases he2725 : (109 / 40 : ℝ) ≤ e
        · have hkbase : (109 / 69 : ℝ) * dickmanRho (69 / 40) ≤
              dickmanRho (33 / 25) := by
            have hpos : 0 < dickmanRho (69 / 40) :=
              dickmanRho_profile.2.2.1 _ (by norm_num)
            exact (lt_div_iff₀ hpos).mp
              dickmanRho_thirtythree_twentyfive_div_sixtynine_forty |>.le
          have hb : (69 / 40 : ℝ) ≤ e - 1 := by linarith
          have hkc : (109 / 69 : ℝ) ≤ c := by
            exact dickmanRho_ratio_ge_of_bounds ha0 haLt132.le (by norm_num) hb
              (by norm_num) hkbase
          have hratio : e / (e - 1) ≤ (109 / 69 : ℝ) := by
            have h := endpoint_ratio_antitone (e₀ := (109 / 40 : ℝ))
              (e := e) (by norm_num) he2725
            norm_num at h ⊢
            exact h
          apply gsChampionDefect_of_large_coefficient ha he heta
          exact (one_add_inv_scale_le_endpoint_ratio ha he).trans
            (hratio.trans hkc)
        · have heLt2725 : e < 109 / 40 := lt_of_not_ge he2725
          by_cases ha114 : (57 / 50 : ℝ) ≤ a
          · have hkc : (34 / 25 : ℝ) ≤ c := by
              apply dickmanRho_ratio_ge_of_bounds ha0 haLt132.le (by norm_num)
                (show (8 / 5 : ℝ) ≤ e - 1 by linarith) (by norm_num)
              exact dickmanRho_thirtythree_twentyfive_ge_thirtyfour_twentyfive
            apply gsChampionDefect_of_corner (a₀ := (57 / 50 : ℝ))
              (c₀ := (34 / 25 : ℝ)) (by norm_num) ha114 he
              (by norm_num) hkc heta
            simpa [gsChampionDefect] using
              gs_champion_corner_fiftyseven_fifty eta heta
          · have haLt114 : a < 57 / 50 := lt_of_not_ge ha114
            have hkbase : (13 / 8 : ℝ) * dickmanRho (8 / 5) ≤
                dickmanRho (57 / 50) := by
              have hpos : 0 < dickmanRho (8 / 5) :=
                dickmanRho_profile.2.2.1 _ (by norm_num)
              exact (lt_div_iff₀ hpos).mp
                dickmanRho_fiftyseven_fifty_div_eight_fifths |>.le
            have hkc : (13 / 8 : ℝ) ≤ c := by
              exact dickmanRho_ratio_ge_of_bounds ha0 haLt114.le (by norm_num)
                (show (8 / 5 : ℝ) ≤ e - 1 by linarith) (by norm_num) hkbase
            have hratio : e / (e - 1) ≤ (13 / 8 : ℝ) := by
              have h := endpoint_ratio_antitone (e₀ := (13 / 5 : ℝ))
                (e := e) (by norm_num) he
              norm_num at h ⊢
              exact h
            apply gsChampionDefect_of_large_coefficient ha he heta
            exact (one_add_inv_scale_le_endpoint_ratio ha he).trans
              (hratio.trans hkc)

lemma gsChampionScalar_to_endpoint
    {a e c eta lambda EV : ℝ}
    (he : 1 ≤ e) (hetaA : eta ≤ a) (hEV0 : 0 ≤ EV)
    (hEV : EV ≤ eta * lambda)
    (hscalar :
      eta * (1 + c - c * eta) * lambda + 1 + eta - e ≤ a) :
    EV * (1 + c - c * eta) + 1 + eta - e ≤ a := by
  by_cases hf : 0 ≤ 1 + c - c * eta
  · have hmul := mul_le_mul_of_nonneg_right hEV hf
    nlinarith
  · have hf' : 1 + c - c * eta < 0 := lt_of_not_ge hf
    have hneg : EV * (1 + c - c * eta) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hEV0 hf'.le
    linarith

lemma gsChampionScaleAlgebra
    {u u₀ V e a c eta EV : ℝ}
    (he : 1 ≤ e) (hu₀ : 0 < u₀) (hV : 0 < V) (hEV : 0 < EV)
    (hu : u = e * u₀) (heta : eta = u₀ * EV / V)
    (hetaA : eta ≤ a)
    (hEVlambda : EV ≤ eta * (e - a⁻¹))
    (hscalar :
      eta * (1 + c - c * eta) * (e - a⁻¹) + 1 + eta - e ≤ a) :
    V / EV * (EV - e + 1) ≤
      c * (u * EV / e - V) + (V * a / EV - u₀) := by
  have hePos : 0 < e := zero_lt_one.trans_le he
  have hend := gsChampionScalar_to_endpoint he hetaA hEV.le hEVlambda hscalar
  have heta' : eta * V = u₀ * EV := by
    rw [heta]
    field_simp [hV.ne']
  rw [← (mul_le_mul_iff_of_pos_right hEV)]
  have huTerm : u * EV / e = u₀ * EV := by
    rw [hu]
    field_simp [hePos.ne']
    <;> ring
  rw [huTerm]
  field_simp [hEV.ne']
  have hUE : EV * u₀ = eta * V := by nlinarith [heta']
  rw [hUE]
  have hmul := mul_le_mul_of_nonneg_left hend hV.le
  ring_nf at hmul ⊢
  linarith

lemma gsChampionGapLower
    {Bu B₁ BV B₀ c u e V EV a u₀ : ℝ}
    (hc : 1 ≤ c) (hB₁V : B₁ ≤ BV)
    (hupperGap : u * EV / e - V ≤ Bu - BV)
    (hlowerGap : V * a / EV - u₀ ≤ BV - B₀) :
    c * (u * EV / e - V) + (V * a / EV - u₀) ≤
      c * (Bu - B₁) + (B₁ - B₀) := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hscaled := mul_le_mul_of_nonneg_left hupperGap hc0
  have hshift :
      c * (Bu - BV) + (BV - B₀) ≤
        c * (Bu - B₁) + (B₁ - B₀) := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hB₁V)
    nlinarith
  linarith

lemma gsChampionTauCondition
    {u u₀ V e a c eta EV B₀ B₁ BV Bu a₁ tau tau' : ℝ}
    (he : 1 ≤ e) (hu₀ : 0 < u₀) (hV : 0 < V) (hEV : 0 < EV)
    (hu : u = e * u₀) (heta : eta = u₀ * EV / V)
    (hetaA : eta ≤ a)
    (hEVlambda : EV ≤ eta * (e - a⁻¹))
    (hscalar :
      eta * (1 + c - c * eta) * (e - a⁻¹) + 1 + eta - e ≤ a)
    (hc : 1 ≤ c) (hB₁V : B₁ ≤ BV)
    (hupperGap : u * EV / e - V ≤ Bu - BV)
    (hlowerGap : V * a / EV - u₀ ≤ BV - B₀)
    (htau : tau + a₁ - e + 1 = EV / V * c * (Bu - B₁))
    (htau' : tau' = EV / V * (B₁ - B₀)) :
    EV - a₁ ≤ tau + tau' := by
  have hscale := gsChampionScaleAlgebra he hu₀ hV hEV hu heta
    hetaA hEVlambda hscalar
  have hgap := gsChampionGapLower hc hB₁V hupperGap hlowerGap
  have hmain : V / EV * (EV - e + 1) ≤
      c * (Bu - B₁) + (B₁ - B₀) := hscale.trans hgap
  have hVEV : 0 < V / EV := div_pos hV hEV
  have hidentity :
      V / EV * (tau + tau' + a₁ - e + 1) =
        c * (Bu - B₁) + (B₁ - B₀) := by
    rw [htau', show tau + EV / V * (B₁ - B₀) + a₁ - e + 1 =
        (tau + a₁ - e + 1) + EV / V * (B₁ - B₀) by ring,
      htau]
    field_simp [hV.ne', hEV.ne']
    <;> ring
  rw [← hidentity] at hmain
  apply (mul_le_mul_iff_of_pos_left hVEV).mp
  nlinarith [hmain]

lemma gsChampionIntegralPieces
    {rho : ℝ → ℝ}
    {lo mid EV endpoint I₁ I₂ I₃ u rhoe alpha : ℝ}
    (hloMid : lo ≤ mid) (hmidEnd : mid ≤ endpoint)
    (hloEV : lo ≤ EV) (hEVEnd : EV ≤ endpoint)
    (hrho : IntervalIntegrable rho volume lo endpoint)
    (hrho0 : ∀ t ∈ Icc lo endpoint, 0 ≤ rho t)
    (halpha : 0 ≤ alpha)
    (h₃ : u * rhoe - alpha * (∫ t : ℝ in lo..EV, rho t) ≤ I₃)
    (h₁ : alpha * (∫ t : ℝ in lo..mid, rho t) ≤ I₁)
    (h₂ : alpha * (∫ t : ℝ in mid..endpoint, rho t) ≤ I₂) :
    u * rhoe ≤ I₁ + I₂ + I₃ := by
  have hloEnd : lo ≤ endpoint := hloEV.trans hEVEnd
  have hrhoLeft : IntervalIntegrable rho volume lo mid := by
    apply hrho.mono_set
    rw [uIcc_of_le hloMid, uIcc_of_le hloEnd]
    exact Icc_subset_Icc le_rfl hmidEnd
  have hrhoRight : IntervalIntegrable rho volume mid endpoint := by
    apply hrho.mono_set
    rw [uIcc_of_le hmidEnd, uIcc_of_le hloEnd]
    exact Icc_subset_Icc hloMid le_rfl
  have hsplit :
      (∫ t : ℝ in lo..mid, rho t) +
          (∫ t : ℝ in mid..endpoint, rho t) =
        ∫ t : ℝ in lo..endpoint, rho t :=
    intervalIntegral.integral_add_adjacent_intervals hrhoLeft hrhoRight
  have hrhoBeforeEV : IntervalIntegrable rho volume lo EV := by
    apply hrho.mono_set
    rw [uIcc_of_le hloEV, uIcc_of_le hloEnd]
    exact Icc_subset_Icc le_rfl hEVEnd
  have hrhoTail : IntervalIntegrable rho volume EV endpoint := by
    apply hrho.mono_set
    rw [uIcc_of_le hEVEnd, uIcc_of_le hloEnd]
    exact Icc_subset_Icc hloEV le_rfl
  have hsplitEV :
      (∫ t : ℝ in lo..EV, rho t) +
          (∫ t : ℝ in EV..endpoint, rho t) =
        ∫ t : ℝ in lo..endpoint, rho t :=
    intervalIntegral.integral_add_adjacent_intervals hrhoBeforeEV hrhoTail
  have htail0 : 0 ≤ ∫ t : ℝ in EV..endpoint, rho t := by
    apply intervalIntegral.integral_nonneg hEVEnd
    intro t ht
    exact hrho0 t ⟨hloEV.trans ht.1, ht.2⟩
  have hscaledTail : 0 ≤ alpha * (∫ t : ℝ in EV..endpoint, rho t) :=
    mul_nonneg halpha htail0
  nlinarith

end
end Erdos783
