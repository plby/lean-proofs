import ErdosProblems.Erdos1148.ZetaCharacterGeneralEstimate

/-! # The zeta-character estimate at arbitrary real cutoffs -/

namespace Erdos1148.DukeArithmetic

theorem realZetaConvolution_floor_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖weightedArithmeticPartialSum (realZetaConvolution χ) s ⌊x⌋₊ -
        (realZetaRegularized s * realDirichletValue χ s +
          x ^ (1 - s) / (1 - s) * realDirichletValue χ 1)‖ ≤
      76 * ((q : ℝ) / (1 - s)) * x ^ (1 / 2 - s) := by
  let Q := (q : ℝ) / (1 - s)
  let F := fun y : ℝ => realZetaRegularized s * realDirichletValue χ s +
    y ^ (1 - s) / (1 - s) * realDirichletValue χ 1
  have hs0 : 0 < s := by linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hfloor : 0 < ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have hfloor0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hfloor
  have hfloor1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfloor
  have hxy : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hq : (q : ℝ) ≤ Q := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - s)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hi := rpow_integral_short_interval_bounds hs0 hs1 hfloor0
    (Nat.floor_le hx0.le) (Nat.lt_floor_add_one x).le
  have hshift : ‖F (⌊x⌋₊ : ℝ) - F x‖ ≤ 4 * Q * x ^ (1 / 2 - s) := by
    rw [show F (⌊x⌋₊ : ℝ) - F x =
      -(((x ^ (1 - s) - (⌊x⌋₊ : ℝ) ^ (1 - s)) / (1 - s)) *
        realDirichletValue χ 1) by dsimp [F]; ring,
      norm_neg, norm_mul, Real.norm_of_nonneg hi.1]
    calc
      _ ≤ (⌊x⌋₊ : ℝ) ^ (-s) * (2 * q) :=
        mul_le_mul hi.2 (realDirichletValue_norm_le χ hχ zero_lt_one)
          (norm_nonneg _) (by positivity)
      _ ≤ (2 * x ^ (-s)) * (2 * q) := mul_le_mul_of_nonneg_right
        (rpow_neg_le_of_le_twice hx0 hfloor0 hxy hs0.le hs1.le) (by positivity)
      _ ≤ (2 * x ^ (1 / 2 - s)) * (2 * q) := by
        gcongr
        linarith
      _ ≤ (2 * x ^ (1 / 2 - s)) * (2 * Q) := by gcongr
      _ = _ := by ring
  have hbase : ‖weightedArithmeticPartialSum (realZetaConvolution χ) s ⌊x⌋₊ -
      F (⌊x⌋₊ : ℝ)‖ ≤ 72 * Q * x ^ (1 / 2 - s) := by
    calc
      _ ≤ 36 * Q * (⌊x⌋₊ : ℝ) ^ (1 / 2 - s) :=
        realZetaConvolution_nat_error_le χ hχ hs hs1 hfloor
      _ ≤ 36 * Q * (2 * x ^ (1 / 2 - s)) :=
        mul_le_mul_of_nonneg_left (nat_floor_rpow_error_le hx hs hs1.le)
          (by dsimp [Q]; positivity)
      _ = _ := by ring
  change ‖weightedArithmeticPartialSum (realZetaConvolution χ) s ⌊x⌋₊ - F x‖ ≤
    76 * Q * x ^ (1 / 2 - s)
  calc
    _ = ‖(weightedArithmeticPartialSum (realZetaConvolution χ) s ⌊x⌋₊ - F (⌊x⌋₊ : ℝ)) +
        (F (⌊x⌋₊ : ℝ) - F x)‖ := by congr 1; ring
    _ ≤ ‖weightedArithmeticPartialSum (realZetaConvolution χ) s ⌊x⌋₊ - F (⌊x⌋₊ : ℝ)‖ +
        ‖F (⌊x⌋₊ : ℝ) - F x‖ := norm_add_le _ _
    _ ≤ 72 * Q * x ^ (1 / 2 - s) + 4 * Q * x ^ (1 / 2 - s) := add_le_add hbase hshift
    _ = _ := by ring

end Erdos1148.DukeArithmetic
