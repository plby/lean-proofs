import Arxiv.Arxiv2411_18291.SharpRandomTypicality
import Arxiv.Arxiv2411_18291.LocalTypicalityTails
import Mathlib.Data.Nat.Choose.Cast

/-! # Finite bounds for the separate density and neighborhood probabilities -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem geometric_test_count_le {x : ℝ} (hx : 9 ≤ x) (h : ℕ) :
    (∑ a ∈ range (h + 1), x ^ a) ≤ (9 / 8 : ℝ) * x ^ h := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [sum_range_succ, pow_succ x h]
    have hp := mul_nonneg (show 0 ≤ x - 9 by linarith only [hx])
      (pow_nonneg (show 0 ≤ x by linarith only [hx]) h)
    nlinarith only [ih, hp]

theorem faceFamilies_count_le_sharp {n r h : ℕ} (hn : 9 ≤ n) (hr : 1 ≤ r) :
    ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ) ≤
      (9 / 8 : ℝ) * (n : ℝ) ^ (r * h) := by
  have hnR : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (9 : ℝ) ≤ (n : ℝ) ^ r := by
    have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ n by linarith only [hnR]) hr
    exact hnR.trans (by simpa only [pow_one] using hh)
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ a ∈ range (h + 1), ((n : ℝ) ^ r) ^ a := by
      apply sum_le_sum
      intro a _
      exact_mod_cast (Nat.choose_le_pow (n.choose r) a).trans
        (Nat.pow_le_pow_left (Nat.choose_le_pow n r) a)
    _ ≤ (9 / 8 : ℝ) * ((n : ℝ) ^ r) ^ h := geometric_test_count_le hp h
    _ = _ := by rw [← pow_mul]

theorem choose_two_le_choose_half {n R : ℕ} (hR : 2 ≤ R) (hhalf : R ≤ n / 2) :
    n.choose 2 ≤ n.choose R := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ R hR ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem choose_lower_square {n R : ℕ} (hn : 3 ≤ n) (hR : 2 ≤ R) (hhalf : R ≤ n / 2) :
    (n : ℝ) ^ 2 / 3 ≤ n.choose R := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (n.choose 2 : ℝ) ≤ n.choose R := by
    exact_mod_cast choose_two_le_choose_half hR hhalf
  rw [Nat.cast_choose_two] at hc
  nlinarith only [hnR, hc]

theorem sharp_typicality_exponent_bounds {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    let δ := (n : ℝ) ^ (-(1 / 10 : ℝ))
    (n : ℝ) ^ (13 / 10 : ℝ) / (1769472 * (h : ℝ) ^ 2) ≤
        (p : ℝ) * n.choose (r + 1) * (δ / (512 * h)) ^ 2 / (2 + δ / (512 * h)) ∧
      (504063 / 1212416 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ) ≤
        ((n - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * ((63 / 64 : ℝ) * δ) ^ 2 /
          (2 + (63 / 64 : ℝ) * δ) := by
  dsimp only
  let δ := (n : ℝ) ^ (-(1 / 10 : ℝ))
  let c := δ / (512 * h : ℝ)
  let d := (63 / 64 : ℝ) * δ
  obtain ⟨hnNat, hhalf, hδhi, hroot⟩ := sharp_local_typicality_size hr hh hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith only [hhR]
  have hδ : 0 ≤ δ := Real.rpow_nonneg hn0.le _
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hch : c ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 512 * h)).mpr
    change δ ≤ _
    linarith only [hδhi, hhR]
  have hdh : 2 + d ≤ 37 / 16 := by
    dsimp only [d]
    change δ ≤ 5 / 16 at hδhi
    nlinarith only [hδhi, hδ]
  have hph : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ h := by
    have hm := pow_le_pow_left₀ (Real.rpow_nonneg hn0.le _) hp h
    rw [← Real.rpow_mul_natCast hn0.le] at hm
    have heq : -(1 / (2 * h : ℝ)) * h = -(1 / 2 : ℝ) := by field_simp
    rwa [heq] at hm
  have hpweak : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ p := by
    have hbeta : 1 / (2 * h : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * h)).mpr
      linarith only [hhR]
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hbeta)).trans hp
  have hchoose := choose_lower_square (by omega : 3 ≤ n) (by omega : 2 ≤ r + 1) hhalf
  have hmeanD : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ 2 / 3) ≤
      (p : ℝ) * n.choose (r + 1) :=
    mul_le_mul hpweak hchoose (by positivity) p.property.1
  have hpowerD : (n : ℝ) ^ (13 / 10 : ℝ) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ 2 * δ ^ 2 := by
    dsimp only [δ]
    rw [← Real.rpow_mul_natCast hn0.le,
      show (13 / 10 : ℝ) = (-(1 / 2) + 2) + (-(1 / 10)) * 2 by norm_num,
      Real.rpow_add hn0, Real.rpow_add hn0]
    norm_num
  have hpowerN : (n : ℝ) ^ (3 / 10 : ℝ) =
      n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * δ ^ 2 := by
    dsimp only [δ]
    rw [← Real.rpow_mul_natCast hn0.le,
      show (3 / 10 : ℝ) = (1 + -(1 / 2)) + (-(1 / 10)) * 2 by norm_num,
      Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
    norm_num
  constructor
  · change _ ≤ (p : ℝ) * n.choose (r + 1) * c ^ 2 / (2 + c)
    calc
      _ = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ 2 / 3)) * c ^ 2 /
          (9 / 4 : ℝ) := by rw [hpowerD]; dsimp only [c]; field_simp; ring
      _ ≤ ((p : ℝ) * n.choose (r + 1)) * c ^ 2 / (9 / 4 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmeanD (sq_nonneg c))
          (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by linarith only [hch])
  · have hhrR : (h * r : ℝ) ≤ n / 128 := by
      have hm := mul_le_mul_of_nonneg_right hδhi (show (0 : ℝ) ≤ (n : ℝ) / 128 by positivity)
      nlinarith only [hroot, hm, hn0]
    have hhr : h * r ≤ n := by
      have hs : (h * r : ℝ) ≤ n := by linarith only [hhrR, hn0]
      exact_mod_cast hs
    have hmeanlow : (127 / 128 : ℝ) * n ≤ (n - h * r : ℕ) := by
      rw [Nat.cast_sub hhr, Nat.cast_mul]
      linarith only [hhrR]
    have hmeanN : ((127 / 128 : ℝ) * n) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        ((n - h * r : ℕ) : ℝ) * (p : ℝ) ^ h :=
      mul_le_mul hmeanlow hph (by positivity) (by positivity)
    change _ ≤ ((n - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * d ^ 2 / (2 + d)
    calc
      _ = (((127 / 128 : ℝ) * n) * (n : ℝ) ^ (-(1 / 2 : ℝ))) * d ^ 2 /
          (37 / 16 : ℝ) := by rw [hpowerN]; dsimp only [d]; ring
      _ ≤ (((n - h * r : ℕ) : ℝ) * (p : ℝ) ^ h) * d ^ 2 / (37 / 16 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmeanN (sq_nonneg d))
          (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hdh

theorem separate_typicality_failure_bound_local {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    separateTypicalityFailureBound n r h p ((n : ℝ) ^ (-(1 / 10 : ℝ))) <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  obtain ⟨hD, hN⟩ := sharp_typicality_exponent_bounds hr hh hn p hp
  have hnNat := (sharp_local_typicality_size hr hh hn).1
  have hcount := faceFamilies_count_le_sharp (h := h) (by omega : 9 ≤ n) hr
  have hdegree : r * h + 1 ≤ (r + 1) * h := by nlinarith only [hh]
  have hk : 2 ≤ (r + 1) * h := by nlinarith only [hr, hh]
  have htailN := local_typicality_neighborhood_tail hk hdegree hn
  have htailD := local_typicality_density_tail hr hh hn
  have heD := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hD))
    (by norm_num : (0 : ℝ) ≤ 2)
  have heN := mul_le_mul hcount (Real.exp_le_exp.mpr (neg_le_neg hN))
    (Real.exp_pos _).le (by positivity : (0 : ℝ) ≤ (9 / 8 : ℝ) * (n : ℝ) ^ (r * h))
  unfold separateTypicalityFailureBound
  nlinarith only [heD, heN, htailD, htailN]

end Arxiv2411_18291
