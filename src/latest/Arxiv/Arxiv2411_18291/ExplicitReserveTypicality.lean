import Arxiv.Arxiv2411_18291.ExplicitReserveTail

/-! # Typical graphs at the paper's reserve threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_typicalGraph_paper_reserve_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (p : unitInterval)
    (hp : (n : ℝ) ^ (-(2 * paperRho q (r + 1))) ≤ p) :
    ∃ G : Hypergraph (Fin n) (r + 1),
      |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 8 : ℝ)) * p ∧
      IsTypical G ((4 + 2 * q.choose (r + 1) * 2 ^ q.choose (r + 1)) *
        (n : ℝ) ^ (-(1 / 8 : ℝ))) (q.choose (r + 1)) := by
  let K := q.choose (r + 1)
  let ρ := paperRho q (r + 1)
  let c := (n : ℝ) ^ (-(1 / 8 : ℝ))
  have hK : 1 ≤ K := Nat.choose_pos hqr.le
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hρK : ρ * K ≤ 1 / 36 := paperRho_mul_choose_le hqr
  have hlarge : (48 * (r * K) + 24 * K + 36 : ℝ) < (n : ℝ) ^ ρ :=
    paper_reserve_tail_constant_lt_rpow hqr hn
  have hnρ : (n : ℝ) ^ ρ ≤ n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (show ρ ≤ 1 by linarith)
  have hsizeReal : (2 * (K * r) : ℝ) ≤ n := by
    have hh := hlarge.trans_le hnρ
    nlinarith only [hh, (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hsize : 2 * (K * r) ≤ n := by exact_mod_cast hsizeReal
  have hrK : r ≤ K * r := by simpa using Nat.mul_le_mul_right r hK
  have hnr : r + 1 ≤ n := by omega
  have hroot : (K * r : ℝ) ≤ c * n := by
    have hh : (K * r : ℝ) ≤ (n : ℝ) ^ ρ := by
      nlinarith only [hlarge, (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (show ρ ≤ 7 / 8 by linarith)
    have heq : (n : ℝ) ^ (7 / 8 : ℝ) = c * n := by
      rw [show (7 / 8 : ℝ) = -(1 / 8) + 1 by norm_num,
        Real.rpow_add hn0, Real.rpow_one]
    exact hh.trans (heq ▸ hpow)
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnormal : (4 + 2 * K * 2 ^ K : ℝ) * c ≤ 1 / 4 :=
    paper_reserve_normalization hqr hn
  have hprod : (0 : ℝ) ≤ c * K * 2 ^ K := by positivity
  have hc1 : c ≤ 1 := by nlinarith only [hnormal, hprod]
  have hsmall : c * K * 2 ^ K ≤ 1 / 2 := by nlinarith only [hnormal, hc]
  have hfailure : typicalFailureBound n r K p c < 1 := by
    have hexp : (1 / 2 : ℝ) ≤ 1 - (2 * ρ) * K - 2 * (1 / 8) := by
      nlinarith only [hρK]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hexp
    calc
      _ ≤ 2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K) *
          Real.exp (-((n : ℝ) ^ (1 - (2 * ρ) * K - 2 * (1 / 8)) / 12)) :=
        typicalFailureBound_power_le n r K hnNat hK hsize (by norm_num) p hp
      _ ≤ 2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K) *
          Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        linarith only [hpow]
      _ < 1 := paper_reserve_sampling_tail_lt_one hqr hn
  exact exists_typicalGraph p hc hc1
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hroot) hsmall
    (by simpa only [Fintype.card_fin] using hfailure)

end Arxiv2411_18291
