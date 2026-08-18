import Mathlib

/-!
# Numerical exponents in the Pham--Zakharov iteration

This file isolates the elementary real inequalities used when the subset-sum
dimension changes in the proof of the upper bound for Erdős problem 186.

The exponent in dimension one is exceptional: it is `1 / 4`.  Starting in
dimension two it is `(d - 1) / (d + 1)`.  We give the definition a harmless
value at dimension zero as well, although every result about the iteration
assumes that dimensions are positive.

The final two theorems are a quantitative form of Observation 15 in
Pham--Zakharov.  If `d' > d`, then a dimension rise gives a fixed saving in
the exponent.  The last theorem makes all smallness assumptions explicit:
`0 < ζ ≤ 1` and `0 ≤ ε ≤ ζ / (4 * (d' - d))` suffice, and the
saving is `ζ / 2`.
-/

namespace Erdos186

/-- The Pham--Zakharov exponent in dimension `d`.

Only positive dimensions occur in the argument.  At zero the displayed
rational formula gives `-1`; fixing the value to be zero makes the function
more convenient as a total function on `ℕ` without affecting any theorem
below. -/
noncomputable def pzExponent (d : ℕ) : ℝ :=
  if d = 0 then 0
  else if d = 1 then 1 / 4
  else ((d : ℝ) - 1) / ((d : ℝ) + 1)

@[simp]
theorem pzExponent_zero : pzExponent 0 = 0 := by
  simp [pzExponent]

@[simp]
theorem pzExponent_one : pzExponent 1 = 1 / 4 := by
  norm_num [pzExponent]

theorem pzExponent_eq_fraction {d : ℕ} (hd : 2 ≤ d) :
    pzExponent d = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  simp [pzExponent, show d ≠ 0 by omega, show d ≠ 1 by omega]

@[simp]
theorem pzExponent_two : pzExponent 2 = 1 / 3 := by
  rw [pzExponent_eq_fraction (by omega)]
  norm_num

@[simp]
theorem pzExponent_three : pzExponent 3 = 1 / 2 := by
  rw [pzExponent_eq_fraction (by omega)]
  norm_num

/-- The exponent is positive in every positive dimension. -/
theorem pzExponent_pos {d : ℕ} (hd : 1 ≤ d) : 0 < pzExponent d := by
  by_cases h1 : d = 1
  · subst d
    norm_num
  · rw [pzExponent_eq_fraction (by omega)]
    have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    exact div_pos (by linarith) (by positivity)

/-- Every finite-dimensional exponent is strictly smaller than one. -/
theorem pzExponent_lt_one {d : ℕ} (hd : 1 ≤ d) : pzExponent d < 1 := by
  by_cases h1 : d = 1
  · subst d
    norm_num
  · rw [pzExponent_eq_fraction (by omega)]
    have hden : 0 < (d : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hden]
    linarith

/-- The Pham--Zakharov exponents are strictly increasing among positive
dimensions. -/
theorem pzExponent_strictMono {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) :
    pzExponent d < pzExponent e := by
  by_cases h1 : d = 1
  · subst d
    rw [pzExponent_one, pzExponent_eq_fraction (by omega)]
    have hden : 0 < (e : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hden]
    have heR : (2 : ℝ) ≤ e := by exact_mod_cast (show 2 ≤ e by omega)
    norm_num
    linarith
  · rw [pzExponent_eq_fraction (by omega), pzExponent_eq_fraction (by omega)]
    have hdpos : 0 < (d : ℝ) + 1 := by positivity
    have hepos : 0 < (e : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ hdpos hepos]
    have hdeR : (d : ℝ) < e := by exact_mod_cast hde
    nlinarith

/-- Set-theoretic packaging of strict monotonicity on the positive
dimensions. -/
theorem pzExponent_strictMonoOn :
    StrictMonoOn pzExponent (Set.Ici 1) := by
  intro d hd e he hde
  exact pzExponent_strictMono hd hde

/-- Non-strict monotonicity, in the pairwise form most convenient for
rewriting estimates. -/
theorem pzExponent_mono {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    pzExponent d ≤ pzExponent e := by
  rcases hde.eq_or_lt with rfl | hde
  · rfl
  · exact (pzExponent_strictMono hd hde).le

/-- Set-theoretic packaging of monotonicity on the positive dimensions. -/
theorem pzExponent_monotoneOn :
    MonotoneOn pzExponent (Set.Ici 1) := by
  intro d hd e he hde
  exact pzExponent_mono hd hde

/-- In particular, every positive-dimensional exponent is at least `1 / 4`. -/
theorem one_div_four_le_pzExponent {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / 4 ≤ pzExponent d := by
  rcases eq_or_lt_of_le hd with rfl | hd
  · simp
  · exact (pzExponent_strictMono (d := 1) (e := d) (by omega) hd).le

/-- The unperturbed exponent expression occurring after a dimension rise is
at most one.  This is the discrete core of Observation 15. -/
theorem pzExponent_dimensionRise_base {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) :
    pzExponent e *
        (1 / pzExponent d - ((e - d : ℕ) : ℝ)) ≤ 1 := by
  by_cases hd1 : d = 1
  · subst d
    by_cases he2 : e = 2
    · subst e
      norm_num
    by_cases he3 : e = 3
    · subst e
      norm_num
    have he4 : 4 ≤ e := by omega
    have hb0 : 0 ≤ pzExponent e := (pzExponent_pos (by omega)).le
    have hb1 : pzExponent e ≤ 1 := (pzExponent_lt_one (by omega)).le
    have hk : (1 : ℝ) / pzExponent 1 - ((e - 1 : ℕ) : ℝ) ≤ 1 := by
      rw [pzExponent_one]
      norm_num
      exact_mod_cast (show 4 ≤ 1 + (e - 1) by omega)
    calc
      pzExponent e * (1 / pzExponent 1 - ↑(e - 1))
          ≤ pzExponent e * 1 := mul_le_mul_of_nonneg_left hk hb0
      _ ≤ 1 := by simpa using hb1
  · by_cases hd2 : d = 2
    · subst d
      by_cases he3 : e = 3
      · subst e
        norm_num
      have he4 : 4 ≤ e := by omega
      have hb0 : 0 ≤ pzExponent e := (pzExponent_pos (by omega)).le
      have hb1 : pzExponent e ≤ 1 := (pzExponent_lt_one (by omega)).le
      have hk : (1 : ℝ) / pzExponent 2 - ((e - 2 : ℕ) : ℝ) ≤ 1 := by
        rw [pzExponent_two]
        norm_num
        exact_mod_cast (show 3 ≤ 1 + (e - 2) by omega)
      calc
        pzExponent e * (1 / pzExponent 2 - ↑(e - 2))
            ≤ pzExponent e * 1 := mul_le_mul_of_nonneg_left hk hb0
        _ ≤ 1 := by simpa using hb1
    · have hd3 : 3 ≤ d := by omega
      have ha : (1 : ℝ) / pzExponent d ≤ 2 := by
        have hhalf : (1 : ℝ) / 2 ≤ pzExponent d := by
          rcases eq_or_lt_of_le hd3 with rfl | hdgt
          · simp
          · simpa using (pzExponent_strictMono (d := 3) (e := d) (by omega) hdgt).le
        have hapos := pzExponent_pos hd
        rw [one_div_le hapos (by norm_num)]
        nlinarith
      have hk_nat : 1 ≤ e - d := by omega
      have hk : (1 : ℝ) / pzExponent d - ((e - d : ℕ) : ℝ) ≤ 1 := by
        have hk_real : (1 : ℝ) ≤ ((e - d : ℕ) : ℝ) := by
          exact_mod_cast hk_nat
        linarith
      have hb0 : 0 ≤ pzExponent e := (pzExponent_pos (by omega)).le
      have hb1 : pzExponent e ≤ 1 := (pzExponent_lt_one (by omega)).le
      calc
        pzExponent e * (1 / pzExponent d - ↑(e - d))
            ≤ pzExponent e * 1 := mul_le_mul_of_nonneg_left hk hb0
        _ ≤ 1 := by simpa using hb1

/-- Quantitative Observation 15 with the perturbation cost exposed as a
hypothesis.  This version is useful when a caller has a sharper bound on
`ε` than the uniform corollary below requires. -/
theorem observation15_dimensionRise_of_perturbation {d e : ℕ} {ζ ε : ℝ}
    (hd : 1 ≤ d) (hde : d < e) (hζ : 0 < ζ)
    (hcost :
      ε * ((e - d : ℕ) : ℝ) * (pzExponent e + ζ) ≤ ζ / 2) :
    (pzExponent e + ζ) *
        (1 / (pzExponent d + ζ) -
          (1 - ε) * ((e - d : ℕ) : ℝ)) ≤
      1 - ζ / 2 := by
  let a := pzExponent d
  let b := pzExponent e
  let k : ℝ := ((e - d : ℕ) : ℝ)
  have ha : 0 < a := pzExponent_pos hd
  have hab : a ≤ b := (pzExponent_strictMono hd hde).le
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (show 1 ≤ e - d by omega)
  have haz : 0 < a + ζ := by positivity
  have hratio : (b + ζ) / (a + ζ) ≤ b / a := by
    rw [div_le_div_iff₀ haz ha]
    nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hab)]
  have hbase : b * (1 / a - k) ≤ 1 := by
    simpa [a, b, k] using pzExponent_dimensionRise_base hd hde
  change (b + ζ) * (1 / (a + ζ) - (1 - ε) * k) ≤ 1 - ζ / 2
  have hmain : (b + ζ) / (a + ζ) - k * (b + ζ) ≤ 1 - ζ := by
    calc
      (b + ζ) / (a + ζ) - k * (b + ζ)
          ≤ b / a - k * (b + ζ) := sub_le_sub_right hratio _
      _ = b * (1 / a - k) - k * ζ := by field_simp; ring
      _ ≤ 1 - ζ := by nlinarith
  dsimp [b, k] at hcost ⊢
  rw [one_div]
  ring_nf at hmain ⊢
  nlinarith

/-- A completely explicit uniform form of Observation 15.

For a rise from positive dimension `d` to `e`, `0 < ζ ≤ 1` and
`0 ≤ ε ≤ ζ / (4 * (e-d))` ensure a saving of `ζ / 2` in the
Pham--Zakharov exponent inequality. -/
theorem observation15_dimensionRise {d e : ℕ} {ζ ε : ℝ}
    (hd : 1 ≤ d) (hde : d < e) (hζ : 0 < ζ) (hζ_one : ζ ≤ 1)
    (hε : 0 ≤ ε)
    (hε_small :
      ε ≤ ζ / (4 * ((e - d : ℕ) : ℝ))) :
    (pzExponent e + ζ) *
        (1 / (pzExponent d + ζ) -
          (1 - ε) * ((e - d : ℕ) : ℝ)) ≤
      1 - ζ / 2 := by
  apply observation15_dimensionRise_of_perturbation hd hde hζ
  have hk : 0 < ((e - d : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < e - d by omega)
  have hb : pzExponent e + ζ ≤ 2 := by
    linarith [pzExponent_lt_one (show 1 ≤ e by omega)]
  have hmul :
      ε * ((e - d : ℕ) : ℝ) ≤ ζ / 4 := by
    calc
      ε * ((e - d : ℕ) : ℝ)
          ≤ (ζ / (4 * ((e - d : ℕ) : ℝ))) *
              ((e - d : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hε_small hk.le
      _ = ζ / 4 := by field_simp
  have hleft : 0 ≤ ε * ((e - d : ℕ) : ℝ) := mul_nonneg hε hk.le
  nlinarith [mul_nonneg hleft (sub_nonneg.mpr hb)]

end Erdos186
