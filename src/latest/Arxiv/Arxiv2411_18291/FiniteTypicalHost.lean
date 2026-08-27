import Arxiv.Arxiv2411_18291.FiniteTypicalHostNumerics

/-! # Constructing a typical host through the exchange size at n0 -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_typicalGraph_paper_host_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ p) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      |density K - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 8 : ℝ)) * p ∧
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h := by
  let c := (n : ℝ) ^ (-(1 / 8 : ℝ))
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlarge : (48 * (r * h) + 24 * h + 36 : ℝ) < (n : ℝ) ^ (1 / 40 : ℝ) := by
    have hc : (48 * (r * h) + 24 * h + 36 : ℝ) <
        (4 * q : ℝ) ^ (10 * (q + h)) := by
      exact_mod_cast reserve_tail_constant_lt (by omega : 2 ≤ q) hh (by omega : r ≤ q)
    exact hc.trans_le (paper_host_configuration_growth hqr hn hh hH)
  have hpowN : (n : ℝ) ^ (1 / 40 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 40 : ℝ) ≤ 1)
  have hsizeReal : (2 * (h * r) : ℝ) ≤ n := by
    have hnlarge := hlarge.trans_le hpowN
    nlinarith only [hnlarge, (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hsize : 2 * (h * r) ≤ n := by exact_mod_cast hsizeReal
  have hrh : r ≤ h * r := by simpa using Nat.mul_le_mul_right r hh
  have hnr : r + 1 ≤ n := by omega
  have hroot : (h * r : ℝ) ≤ c * n := by
    have hh : (h * r : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
      nlinarith only [hlarge, (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 40 : ℝ) ≤ 7 / 8)
    have heq : (n : ℝ) ^ (7 / 8 : ℝ) = c * n := by
      rw [show (7 / 8 : ℝ) = -(1 / 8) + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]
    exact hh.trans (heq ▸ hpow)
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnormal : (4 + 2 * h * 2 ^ h : ℝ) * c ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) :=
    paper_host_typicality_normalization hqr hn hh hH
  have herror1 : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hprod : (0 : ℝ) ≤ c * h * 2 ^ h := by positivity
  have hc1 : c ≤ 1 := by nlinarith only [hnormal, herror1, hprod]
  have hsmall : c * h * 2 ^ h ≤ 1 / 2 := by nlinarith only [hnormal, herror1, hc]
  have hfailure : typicalFailureBound n r h p c < 1 := by
    have hαh := paperAlpha_mul_configuration_le hqr hH
    have hexp : (1 / 2 : ℝ) ≤ 1 - paperAlpha q (r + 1) * h - 2 * (1 / 8) := by
      linarith only [hαh]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hexp
    calc
      _ ≤ 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
          Real.exp (-((n : ℝ) ^ (1 - paperAlpha q (r + 1) * h - 2 * (1 / 8)) / 12)) :=
        typicalFailureBound_power_le n r h hnNat hh hsize (by norm_num) p hp
      _ ≤ 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
          Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        linarith only [hpow]
      _ < 1 := paper_host_sampling_tail_lt_one hqr hn hh hH
  obtain ⟨K, hd, hT⟩ := exists_typicalGraph (V := Fin n) (r := r) (h := h) p hc hc1
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hroot) hsmall
    (by simpa only [Fintype.card_fin] using hfailure)
  exact ⟨K, hd, hT.mono hnormal le_rfl⟩

theorem exists_typicalGraph_paper_alpha_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  let p : unitInterval := ⟨(n : ℝ) ^ (-paperAlpha q (r + 1)),
    Real.rpow_nonneg (Nat.cast_nonneg n) _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (paperAlpha_pos hqr).le)⟩
  obtain ⟨K, hd, hT⟩ := exists_typicalGraph_paper_host_threshold hqr hn hh hH p le_rfl
  refine ⟨K, hT, hd.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ p.property.1
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : -(1 / 8 : ℝ) ≤ -(1 / 10))

end Arxiv2411_18291
