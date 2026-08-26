import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Elementary numerical slack for permutation correction -/

namespace Erdos19

/-- A coarse factorial lower bound, directly from one nonnegative term of
the exponential series. Stirling's formula is unnecessary. -/
theorem div_exp_pow_le_factorial (s : ℕ) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hfact : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hexp : Real.exp (s : ℝ) = Real.exp 1 ^ s := by
    simpa only [mul_one] using Real.exp_nat_mul 1 s
  have h := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (s : ℝ)
    (show (0 : ℝ) ≤ s by positivity) s)
  rw [hexp] at h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) s)).mpr
  simpa only [mul_comm] using h

theorem twice_pow_lt_factorial {f s : ℕ} (hs : 0 < s) (hfs : 8 * f ≤ s) :
    (2 * f) ^ s < s.factorial := by
  by_cases hf : f = 0
  · simpa [hf, Nat.ne_of_gt hs] using Nat.factorial_pos s
  have hfpos : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf
  have hfsR : (8 : ℝ) * f ≤ s := by exact_mod_cast hfs
  have hbase : (2 : ℝ) * f < (s : ℝ) / Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).mpr
    have hmul := mul_lt_mul_of_pos_left Real.exp_one_lt_three
      (show (0 : ℝ) < 2 * f by positivity)
    nlinarith
  have hpow : ((2 : ℝ) * f) ^ s < (s.factorial : ℝ) :=
    (pow_lt_pow_left₀ hbase (by positivity) (Nat.ne_of_gt hs)).trans_le
      (div_exp_pow_le_factorial s)
  exact_mod_cast hpow

theorem square_le_two_pow {s : ℕ} (hs : 4 ≤ s) : s ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- A convenient entirely finite criterion: at most `s²` constraints, at most
`s/8` forbidden colors per object, and `s ≥ 4` suffice. -/
theorem mul_pow_lt_factorial_of_square_bound {m f s : ℕ}
    (hs : 4 ≤ s) (hm : m ≤ s ^ 2) (hf : 8 * f ≤ s) :
    m * f ^ s < s.factorial := by
  calc
    m * f ^ s ≤ 2 ^ s * f ^ s :=
      Nat.mul_le_mul_right _ (hm.trans (square_le_two_pow hs))
    _ = (2 * f) ^ s := (mul_pow _ _ _).symm
    _ < s.factorial := twice_pow_lt_factorial (by omega) hf

#print axioms mul_pow_lt_factorial_of_square_bound

end Erdos19
