import ErdosProblems.Erdos633b.RationalSides

/-! Exact rationality arguments for the doubled group-2 shape. All integer
coefficients below are either signed tile counts or nonnegative boundary
counts; zero boundary coefficients are handled explicitly. -/

namespace Erdos633b

namespace IsRational

theorem add {a b : ℝ} (ha : IsRational a) (hb : IsRational b) : IsRational (a + b) := by
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  exact ⟨q + r, by push_cast; rfl⟩

theorem sub {a b : ℝ} (ha : IsRational a) (hb : IsRational b) : IsRational (a - b) := by
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  exact ⟨q - r, by push_cast; rfl⟩

theorem natCast (m : ℕ) : IsRational (m : ℝ) := ⟨m, by push_cast; rfl⟩

theorem intCast (m : ℤ) : IsRational (m : ℝ) := ⟨m, by push_cast; rfl⟩

end IsRational

theorem groupTwoDouble_rational_parameters {x y k : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hconic : x ^ 2 + x * y + y ^ 2 = 1) (M L : ℤ) (hMpos : 0 < M) (hLpos : 0 < L)
    (hM : (M : ℝ) * (1 + x - y) = 3 * k * x * y)
    (hL : (L : ℝ) * (1 - x + y) = 3 * k * x * y) :
    IsRational (x - y) ∧ IsRational (x * y) ∧ IsRational k := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hden : (0 : ℝ) < (L : ℝ) + M := by positivity
  have hd : IsRational (x - y) := by
    refine ⟨((L : ℚ) - M) / ((L : ℚ) + M), ?_⟩
    push_cast
    apply (div_eq_iff hden.ne').mpr
    linear_combination hL - hM
  obtain ⟨q, hq⟩ := hd
  have hxy : IsRational (x * y) := by
    refine ⟨(1 - q ^ 2) / 3, ?_⟩
    push_cast
    rw [hq]
    nlinarith [hconic]
  have hx1 : x < 1 := by nlinarith [sq_nonneg y, mul_pos hx hy]
  have hy1 : y < 1 := by nlinarith [sq_nonneg x, mul_pos hx hy]
  have hp : 0 < 1 + x - y := by linarith
  have hm : 0 < 1 - (x - y) := by linarith
  refine ⟨⟨q, hq⟩, hxy, ?_⟩
  refine ⟨(M : ℚ) / (1 - q), ?_⟩
  push_cast
  rw [hq]
  apply (div_eq_iff hm.ne').mpr
  apply mul_right_cancel₀ hp.ne'
  linear_combination hM + k * hconic

/-- A rational sum of two actual boundary lengths forces rational short
sides, unless all short-side counts vanish. In that case their difference
forces the same conclusion. -/
theorem rational_pair_of_nonnegative_boundary_counts {x y k : ℝ}
    (hconic : x ^ 2 + x * y + y ^ 2 = 1) (hk : k ≠ 0) (hne : x ≠ y)
    (hd : IsRational (x - y)) (hxy : IsRational (x * y)) (hkr : IsRational k)
    (p q r p' q' r' : ℕ)
    (hX : k * (x * (x + 2 * y)) = p * x + q * y + r)
    (hY : k * (y * (2 * x + y)) = p' * x + q' * y + r') :
    IsRational x ∧ IsRational y := by
  have hu : IsRational (k * (1 + 3 * (x * y))) :=
    hkr.mul ((show IsRational (1 : ℝ) from ⟨1, by norm_num⟩).add
      ((show IsRational (3 : ℝ) from ⟨3, by norm_num⟩).mul hxy))
  have hsum : (p : ℝ) * x + q * y + r + (p' * x + q' * y + r') =
      k * (1 + 3 * (x * y)) := by
    linear_combination k * hconic - hX - hY
  have hxrat : IsRational x := by
    by_cases hA : p + q + p' + q' = 0
    · have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      have hp' : p' = 0 := by omega
      have hq' : q' = 0 := by omega
      simp only [hp, hq, hp', hq', Nat.cast_zero, zero_mul, zero_add] at hX hY
      have he : x + y = ((r : ℝ) - r') / (k * (x - y)) := by
        apply (eq_div_iff (mul_ne_zero hk (sub_ne_zero.mpr hne))).mpr
        linear_combination hX - hY
      have hs : IsRational (x + y) := by
        rw [he]
        exact ((IsRational.natCast r).sub (IsRational.natCast r')).div (hkr.mul hd)
      have he' : x = ((x + y) + (x - y)) / 2 := by ring
      rw [he']
      exact (hs.add hd).div (IsRational.natCast 2)
    · have hAr : (p : ℝ) + q + p' + q' ≠ 0 := by
        exact_mod_cast hA
      have he : x = (k * (1 + 3 * (x * y)) + ((q : ℝ) + q') * (x - y) -
          ((r : ℝ) + r')) / ((p : ℝ) + q + p' + q') := by
        apply (eq_div_iff hAr).mpr
        linear_combination hsum
      rw [he]
      exact ((hu.add (((IsRational.natCast q).add (IsRational.natCast q')).mul hd)).sub
        ((IsRational.natCast r).add (IsRational.natCast r'))).div
          ((((IsRational.natCast p).add (IsRational.natCast q)).add
            (IsRational.natCast p')).add (IsRational.natCast q'))
  refine ⟨hxrat, ?_⟩
  have he : y = x - (x - y) := by ring
  rw [he]
  exact hxrat.sub hd

end Erdos633b
