import Arxiv.Arxiv2411_18291.SparseColouredFocusing
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # Finite density powers after deleting a small edge fraction -/

noncomputable section

namespace Arxiv2411_18291

theorem density_pow_lower_relative_errors
    {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
    {K G : Hypergraph V r} {p δ ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (hδε : δ ≤ ε)
    (hsmall : 3 * ε ≤ 1)
    (hd : |density K - p| ≤ δ * p) (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤ ε * K.card) :
    (1 - 3 * (s : ℝ) * ε) * p ^ s ≤ density G ^ s := by
  have hδ1 : δ ≤ 1 := by linarith only [hδε, hsmall]
  have hprod : ε * δ ≤ ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hε
  have herr := density_subgraph_reference_error hGK hε hloss hd
  have hcoef : ε + δ + ε * δ ≤ 3 * ε := by linarith only [hδε, hprod]
  have hcmul := mul_le_mul_of_nonneg_right hcoef hp
  have hlow : (1 - 3 * ε) * p ≤ density G := by
    have hh := (abs_le.mp herr).1
    nlinarith only [hh, hcmul]
  have hbase : 0 ≤ 1 - 3 * ε := by linarith only [hsmall]
  have hbern := one_add_mul_sub_le_pow (by linarith only [hbase] : -1 ≤ 1 - 3 * ε) s
  have hhalf : 1 - 3 * (s : ℝ) * ε ≤ (1 - 3 * ε) ^ s := by
    nlinarith only [hbern]
  calc
    _ ≤ (1 - 3 * ε) ^ s * p ^ s := mul_le_mul_of_nonneg_right hhalf (pow_nonneg hp s)
    _ = ((1 - 3 * ε) * p) ^ s := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hbase hp) hlow s

theorem density_pow_lower_of_small_relative_errors
    {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}
    {K G : Hypergraph V r} {p δ ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (hδε : δ ≤ ε)
    (hsmall : 6 * ε ≤ 1) (hscaled : 6 * (s : ℝ) * ε ≤ 1)
    (hd : |density K - p| ≤ δ * p) (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤ ε * K.card) :
    (1 / 2 : ℝ) * p ^ s ≤ density G ^ s := by
  have hb := density_pow_lower_relative_errors hp hε hδε (by linarith only [hsmall])
    hd hGK hloss (s := s)
  have hc : (1 / 2 : ℝ) ≤ 1 - 3 * (s : ℝ) * ε := by linarith only [hscaled]
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg hp s)).trans hb

theorem paper_good_density_error_small {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    6 * (q.choose (r + 1) : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 := by
  have hc : 6 * q.choose (r + 1) ≤ (4 * q) ^ (q + 1) := by
    calc
      _ ≤ (4 * q) ^ 1 * (4 * q) ^ q := Nat.mul_le_mul
        (by simp only [pow_one]; omega)
        ((Nat.choose_le_two_pow q (r + 1)).trans (Nat.pow_le_pow_left (by omega) q))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hg : (4 * q : ℝ) ^ (q + 1) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
      (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    convert hh using 1
    congr 1
    ring
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hh := mul_le_mul_of_nonneg_right
    ((by exact_mod_cast hc : 6 * (q.choose (r + 1) : ℝ) ≤ (4 * q : ℝ) ^ (q + 1)).trans hg)
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 10)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
  exact hh

/-- The error remains small after taking every density power needed for
punctured q-clique counts; no factor such as `4^choose(q,r)` is lost. -/
theorem good_reference_density_power_paper_threshold {q r n s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hs : s ≤ q.choose (r + 1)) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s ≤ density G ^ s := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hδε : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαupper])
  have hε : 0 ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbig := paper_good_density_error_small hqr hn
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hsmall : 6 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 := by
    calc
      _ ≤ 6 * (q.choose (r + 1) : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 6)) hε
      _ ≤ _ := hbig
  have hscaled : 6 * (s : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs) (by norm_num : (0 : ℝ) ≤ 6)) hε).trans hbig
  exact density_pow_lower_of_small_relative_errors (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    hε hδε hsmall hscaled hd hGK hloss

theorem good_reference_density_lower_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G := by
  simpa only [pow_one] using good_reference_density_power_paper_threshold hqr hn
    (s := 1) (Nat.choose_pos hqr.le) K G hd hGK hloss

end Arxiv2411_18291
