import Arxiv.Arxiv2411_18291.ExplicitBoostSize
import Arxiv.Arxiv2411_18291.ShiftedChooseBounds

/-! # Finite conversion from the Boost power scale to its binomial scale -/

namespace Arxiv2411_18291

theorem explicit_boost_binomial_numerics {q n : ℕ} (hq : 2 ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) :
    (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ 1 / 2 ∧
      4 * (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ d ≤ q, (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) * (n : ℝ) ^ d / d.factorial ≤
        (n.choose d : ℝ) := by
  have hqn := (boost_threshold_root_size_bounds hq hn).2.2
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hp1 := boost_threshold_rpow_lower (s := 1) hq hn
    (by norm_num : (0 : ℝ) ≤ 1 / 15) (by nlinarith only [hq1])
  simp only [pow_one] at hp1
  have hfour : (4 : ℝ) ≤ (n : ℝ) ^ (1 / 15 : ℝ) := by linarith only [hp1, hq1]
  have hscale : 4 * (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 15 : ℝ) * (n : ℝ) ^ (-(2 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hone : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by norm_num)
  refine ⟨by linarith only [hscale, hone], hscale, ?_⟩
  have hp2 := boost_threshold_rpow_lower (s := 2) hq hn
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (by nlinarith only [hq1])
  have hsize : (q : ℝ) ^ 2 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by
    have hh : q ^ 2 ≤ (4 * q) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact (by exact_mod_cast hh : (q : ℝ) ^ 2 ≤ (4 * q : ℝ) ^ 2).trans hp2
  intro d hd
  have hprod : (d : ℝ) * (0 + d) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) * n := by
    calc
      _ = (d : ℝ) ^ 2 := by ring
      _ ≤ (q : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hd 2
      _ ≤ _ := hsize
      _ = _ := by
        rw [show (3 / 5 : ℝ) = -(2 / 5) + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  simpa only [Nat.sub_zero] using shifted_choose_relative_lower n 0 d
    (Real.rpow_nonneg hn0.le _) (by omega) (by simpa only [Nat.cast_zero] using hprod)

end Arxiv2411_18291
