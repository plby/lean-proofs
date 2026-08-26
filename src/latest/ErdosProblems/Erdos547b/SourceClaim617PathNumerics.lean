/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceDegreeFormBounds

/-!
# Integral postponed-path count for Claim 6.17

The actual source schedule pays the ceiling in `ceil (4 * rho * q)`.
The coarse eighth-order bound leaves room for the clean-parent loss.
-/

noncomputable section

namespace Erdos547b.ZhaoSourceClaim617PathNumerics

open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds

def postponedCount (α : ℚ) (q : ℕ) : ℕ := ⌈4 * (rho α : ℝ) * q⌉₊

theorem path_coefficient_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    13 * fourthRoot α ^ 2 + 3 * rho α / 5 ≤ 1 / 4 ∧
      4 * rho α ≤ 1 / 16 ∧ epsilon α ≤ 1 := by
  obtain ⟨_, hr0, he0, ht0, hd0, _, hg0, _⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, hepg⟩ := parameter_upper_bounds hα hα1
  have hrSmall : rho α ≤ 1 / 4000 := by
    dsimp only [rhoOne] at hrr1
    linarith only [hrr1, hα1]
  have he1 : eta α ≤ 1 := by linarith only [her, hrSmall]
  have he3 : eta α ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 3
  have htSmall : fourthRoot α ≤ 1 / 1000000 := by linarith only [hte3, he3]
  have ht1 : fourthRoot α ≤ 1 := by linarith only [htSmall]
  have ht2 : fourthRoot α ^ 2 ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 1
  exact ⟨by linarith only [ht2, htSmall, hrSmall],
    by linarith only [hrSmall],
    by linarith only [hepg, hgd, hdt, htSmall]⟩

theorem sixteen_le_order {α : ℚ} {M q : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ q) :
    16 ≤ q := by
  have hprod := orderThreshold_product hα horder
  have he0 := (parameter_pos hα).2.2.2.2.2.2.2
  have he1 := (path_coefficient_bounds hα hα1).2.2
  have he4 : epsilon α ^ 4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 4
  have hq := mul_le_mul_of_nonneg_right he4 (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  have hM : (1 : ℚ) ≤ ((M : ℚ) + 1) ^ 2 := by
    nlinarith only [(Nat.cast_nonneg M : (0 : ℚ) ≤ M), sq_nonneg (M : ℚ)]
  have hlarge : (16 : ℚ) ≤ q := by nlinarith only [hprod, hq, hM]
  exact_mod_cast hlarge

theorem postponedCount_lt_eighth {α : ℚ} {M q : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ q) :
    (postponedCount α q : ℝ) < (q : ℝ) / 8 := by
  have hr : (0 : ℝ) < rho α := by exact_mod_cast (parameter_pos hα).2.1
  have hsmall : 4 * (rho α : ℝ) ≤ 1 / 16 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (path_coefficient_bounds hα hα1).2.1
    norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] at h
    exact h
  have hq : (16 : ℝ) ≤ q := by exact_mod_cast sixteen_le_order hα hα1 horder
  have hmul := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hceil : (postponedCount α q : ℝ) < 4 * (rho α : ℝ) * q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith only [hmul, hceil, hq]

theorem eighth_lt_middles {q H L m c : ℕ} {t rho : ℝ}
    (hmajor : (q : ℝ) / 2 - 12 * t ^ 2 * q < H)
    (hlarge : (L : ℝ) < 3 * rho / 5 * q)
    (hcount : H ≤ 2 * (m + c) + L)
    (hparents : 3 * (c : ℝ) ≤ t ^ 2 * q)
    (hcoef : 13 * t ^ 2 + 3 * rho / 5 ≤ 1 / 4) :
    (q : ℝ) / 8 < m := by
  have hcountR : (H : ℝ) ≤ 2 * ((m : ℝ) + c) + L := by exact_mod_cast hcount
  have hcoefq := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hmajor, hlarge, hcountR, hparents, hcoefq,
    (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]

end Erdos547b.ZhaoSourceClaim617PathNumerics

#print axioms Erdos547b.ZhaoSourceClaim617PathNumerics.path_coefficient_bounds
#print axioms Erdos547b.ZhaoSourceClaim617PathNumerics.postponedCount_lt_eighth
#print axioms Erdos547b.ZhaoSourceClaim617PathNumerics.eighth_lt_middles
