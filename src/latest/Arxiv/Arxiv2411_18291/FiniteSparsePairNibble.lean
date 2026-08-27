import Arxiv.Arxiv2411_18291.GeneralPairNibble
import Arxiv.Arxiv2411_18291.ExplicitNibbleTail
import Arxiv.Arxiv2411_18291.ExplicitNibbleMargins

/-! # Finite sampling bounds for the sparse pair nibble -/

namespace Arxiv2411_18291

theorem pair_nibble_numerics_of_small_leave_paper_threshold {n : ℕ}
    (hn : paperSizeThreshold 2 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hp : (n : ℝ) ^ (-(ε / 6)) ≤ 1 / 3) :
    let c := (n : ℝ) ^ (-(ε / 2))
    0 < c ∧ c ≤ 1 / 4 ∧ (n : ℝ) ^ (-ε) ≤ c ∧
      9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n ∧
      ∀ D : ℝ, (n : ℝ) ^ (2 / 3 : ℝ) ≤ D →
        (n + 1 : ℝ) * (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1 := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt (by norm_num : 1 < 2)).le.trans hn
  have hρhi := paperRho_le_one_div_36 (by norm_num : 1 < 2)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hcoef (C : ℕ) (hC : C ≤ 2 ^ 24) (u v : ℝ)
      (hgap : paperRho 2 1 + u ≤ v) :
      (C : ℝ) * (n : ℝ) ^ u ≤ (n : ℝ) ^ v := by
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one] using
      paper_nibble_scaled_monomial (C := C) (j := 0) (d := 0)
        (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2) hn hC (by norm_num) (by norm_num) hgap
  have hcube : (n : ℝ) ^ (-(ε / 2)) = ((n : ℝ) ^ (-(ε / 6))) ^ 3 := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    ring
  have hp0 := Real.rpow_nonneg hn0.le (-(ε / 6))
  have hsmall : (n : ℝ) ^ (-(ε / 2)) ≤ 1 / 4 := by
    rw [hcube]
    have hh := pow_le_pow_left₀ hp0 hp 3
    norm_num at hh
    linarith only [hh]
  have hdecay : 9 * (n : ℝ) ^ (-(ε / 2)) ≤ (n : ℝ) ^ (-(ε / 6)) := by
    have hh := pow_le_pow_left₀ hp0 hp 2
    have hm := mul_le_mul_of_nonneg_right hh hp0
    rw [hcube]
    nlinarith only [hm]
  have hconst : (2 : ℝ) ≤ (n : ℝ) ^ (1 - ε / 6) := by
    simpa only [Real.rpow_zero, mul_one, Nat.cast_ofNat] using
      hcoef 2 (by norm_num) 0 (1 - ε / 6) (by linarith only [hρhi, hεhi])
  have hexponent := hcoef 24 (by norm_num) (1 / 10) (2 / 3 - ε)
    (by linarith only [hρhi, hεhi])
  let c := (n : ℝ) ^ (-(ε / 2))
  have hc : 0 < c := Real.rpow_pos_of_pos hn0 _
  have hc1 : c ≤ 1 := by change (n : ℝ) ^ (-(ε / 2)) ≤ 1; linarith only [hsmall]
  have herror : (n : ℝ) ^ (-ε) ≤ c :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hε])
  have hprod : (n : ℝ) ^ (-(ε / 6)) * n = (n : ℝ) ^ (1 - ε / 6) := by
    rw [show 1 - ε / 6 = -(ε / 6) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hleave : 9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n := by
    have h9 := mul_le_mul_of_nonneg_right hdecay hn0.le
    have h2 : (2 : ℝ) ≤ (n : ℝ) ^ (-(ε / 6)) * n := hconst.trans_eq hprod.symm
    have hp : (0 : ℝ) < (n : ℝ) ^ (-(ε / 6)) * n := by positivity
    dsimp only [c]
    nlinarith only [h9, h2, hp]
  refine ⟨hc, hsmall, herror, hleave, ?_⟩
  intro D hD
  have hid : (n : ℝ) ^ (2 / 3 : ℝ) * c ^ 2 = (n : ℝ) ^ ((2 / 3 : ℝ) - ε) := by
    dsimp only [c]
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  have hDprod := mul_le_mul_of_nonneg_right hD (sq_nonneg c)
  rw [hid] at hDprod
  have hcxi := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hn0.le (1 / 10 : ℝ))
  simp only [one_mul] at hcxi
  have hmargin : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (D / 2) * c ^ 2 / (4 * (1 + 2 * c)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + 2 * c))).mpr
    nlinarith only [hDprod, hexponent, hcxi]
  have hcount : 2 * (n + 1 : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by
    nlinarith only [hnR, sq_nonneg ((n : ℝ) - 1)]
  have htail' : 5 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 :=
    paper_nibble_tail_tenth_lt_one (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2) hn
  calc
    _ ≤ (n + 1 : ℝ) * (2 * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hmargin)) (by norm_num)) (by positivity)
    _ = (2 * (n + 1 : ℝ)) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by ring
    _ ≤ (5 * (n : ℝ) ^ 2) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ < 1 := htail'

theorem pair_nibble_numerics_paper_threshold {n : ℕ}
    (hn : paperSizeThreshold 2 1 ≤ n) {ε : ℝ}
    (hεlo : 6 * paperRho 2 1 ≤ ε) (hεhi : ε ≤ 2 / 5) :
    let c := (n : ℝ) ^ (-(ε / 2))
    0 < c ∧ c ≤ 1 / 4 ∧ (n : ℝ) ^ (-ε) ≤ c ∧
      9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n ∧
      ∀ D : ℝ, (n : ℝ) ^ (2 / 3 : ℝ) ≤ D →
        (n + 1 : ℝ) * (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1 := by
  have hρ := paperRho_pos (by norm_num : 1 < 2)
  apply pair_nibble_numerics_of_small_leave_paper_threshold hn
    (by linarith only [hεlo, hρ]) hεhi
  have hh := paper_nibble_scaled_monomial (C := 3) (j := 0) (d := 0)
    (by norm_num : 1 ≤ 1) (by norm_num : 1 < 2) hn
    (by norm_num) (by norm_num) (by norm_num) (u := -(ε / 6)) (v := 0)
    (by linarith only [hεlo])
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat,
    mul_one, Real.rpow_zero] at hh
  linarith only [hh]

end Arxiv2411_18291
