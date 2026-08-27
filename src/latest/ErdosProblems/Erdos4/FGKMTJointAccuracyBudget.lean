import ErdosProblems.Erdos4.TupleSurvivalBounds
import ErdosProblems.Erdos4.FGKMTQuantitativeTail

/-! A finite joint-survival budget with an explicit prime cutoff and variable test size. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical TupleSurvivalBounds

theorem exp_sub_one_le_of_half_budget {t ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : t ≤ ε / 2) : Real.exp t - 1 ≤ ε := by
  have hhalf : ε / 2 ≤ 2 * ε / (ε + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < ε + 2)).mpr
    have hs := mul_le_mul_of_nonneg_left hε1 hε0
    nlinarith
  have hlog := ht.trans (hhalf.trans (Real.le_log_one_add_of_nonneg hε0))
  calc
    _ ≤ Real.exp (Real.log (1 + ε)) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr hlog) 1
    _ = _ := by rw [Real.exp_log (by linarith : 0 < 1 + ε)]; ring

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem indexed_reciprocal_square_cutoff {K : ℕ} (hK : 0 < K)
    (hinj : Function.Injective ell) (hlarge : ∀ l, K < ell l) :
    (∑ l, 1 / (ell l : ℝ) ^ 2) ≤ 1 / (K : ℝ) := by
  have hh := finite_reciprocal_square_tail hK (Finset.univ.image ell) (by
    intro n hn
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hn
    exact hlarge l)
  rw [Finset.sum_image hinj.injOn] at hh
  simpa only [one_div] using hh

theorem accurate_of_prime_cutoff {K r Y : ℕ} {ε : ℝ}
    (hK : 0 < K) (hinj : Function.Injective ell) (hlarge : ∀ l, K < ell l)
    (hsize : 2 * r ≤ K) (hY : 1 ≤ Y) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbudget : 2 * (r : ℝ) ^ 2 / K +
      2 * (r : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) ≤ ε / 2) :
    Accurate ell Y r ε := by
  intro T hTr hT
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have htail := indexed_reciprocal_square_cutoff ell hK hinj hlarge
  have htail0 : 0 ≤ ∑ l, 1 / (ell l : ℝ) ^ 2 := Finset.sum_nonneg (fun l _ => by positivity)
  have hr : (T.card : ℝ) ≤ r := by exact_mod_cast hTr
  have hr2 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 2
  have hr3 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 3
  have hfirst : 2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) ≤ 2 * (r : ℝ) ^ 2 / K := by
    calc
      _ ≤ 2 * (r : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num)) htail0
      _ ≤ 2 * (r : ℝ) ^ 2 * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have hsecond : 2 * (T.card : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) ≤
      2 * (r : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr3 (by norm_num)) hlogY)
      (mul_nonneg hKpos.le hlog2.le)
  have hh := JointSurvivalEstimate.uniform_relative_error_le ell hinj T
    (fun l => (Nat.mul_le_mul_left 2 hTr).trans (hsize.trans (hlarge l).le)) hY hT hKpos
    (fun l => by exact_mod_cast (hlarge l).le)
  exact hh.trans (exp_sub_one_le_of_half_budget hε0 hε1 (by linarith))

end Erdos4.FGKMT
