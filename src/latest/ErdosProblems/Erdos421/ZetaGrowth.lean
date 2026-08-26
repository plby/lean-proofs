import ErdosProblems.Erdos421.ZetaHeightBound
import ErdosProblems.Erdos421.ZetaHeightWeight

/-! # A height-dependent bound for the actual zeta function near Re(s) = 1 -/

namespace Erdos421

/-- A quantitative zeta growth bound in a strip of explicit width. This is
a bound on the actual function, not an assumed zero-free-region theorem. -/
theorem riemannZeta_near_one_growth_bound (R K : ℕ)
    (hK : 2 * R + 4 ≤ K) (hK8 : 8 ≤ K) (s : ℂ) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (ht : (2 : ℝ) ^ (R + 1) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤
      (1 + Real.log |s.im| / (((R : ℝ) + 1) * Real.log 2)) *
        (2 : ℝ) ^ (1 - s.re) * |s.im| ^ ((1 - s.re) / ((R : ℝ) + 1)) +
      zetaStripConstant R K + 9 := by
  have hb : (1 : ℝ) < 2 ^ (R + 1) := by
    exact_mod_cast Nat.one_lt_pow (by omega : R + 1 ≠ 0) (by omega : 1 < 2)
  obtain ⟨u, hu₁, hu₂⟩ := exists_nat_pow_near (hb.le.trans ht) hb
  have hu : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he, zero_add, pow_one] at hu₂
    exact (not_lt_of_ge ht) hu₂
  have hlo : ((2 ^ ((R + 1) * u) : ℕ) : ℝ) ≤ |s.im| := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_mul] using hu₁
  have hhi : |s.im| ≤ ((2 ^ ((R + 1) * (u + 1)) : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_mul] using hu₂.le
  have hδ := logarithmicSavingExponent_le_half R (by omega : 2 ≤ K)
  have hs : 0 < s.re := by linarith
  have h := riemannZeta_height_scale_bound hu R K hK hK8 s hs hs1 hstrip hlo hhi
  have hw := dyadic_initial_zeta_weight_bound u R (sub_nonneg.mpr hs1) hlo
  linarith

end Erdos421
