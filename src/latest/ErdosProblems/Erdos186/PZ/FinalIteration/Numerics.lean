/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Numerical
import ErdosProblems.Erdos186.UpperPackaging

/-!
# Numerical bookkeeping for the final Pham--Zakharov iteration

The public finite box theorem is stated using `boxExponent`, while the
elementary dimension-change estimates were proved using `pzExponent`.  This
file identifies the two exponents in every positive dimension and transports
the numerical estimates needed by the final iteration.

It also isolates the comparison with the exponent `(d - 1) / (d + 1)` in the
convex-density lemma.  Here the subtraction is deliberately performed in
`ℕ` before coercion, exactly as it is in `boxExponent`.
-/

namespace Erdos186.PZ.FinalIteration

noncomputable section

/-! ## The two presentations of the Pham--Zakharov exponent -/

/-- In every positive dimension, the exponent in the public box statement is
the exponent used by the numerical iteration. -/
theorem boxExponent_eq_pzExponent {d : ℕ} (hd : 0 < d) :
    boxExponent d = pzExponent d := by
  by_cases hd1 : d = 1
  · subst d
    simp
  · have hd2 : 2 ≤ d := by omega
    rw [pzExponent_eq_fraction hd2]
    simp only [boxExponent, hd1, if_false]
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_add]
    norm_num

/-- The exceptional one-dimensional exponent. -/
@[simp]
theorem boxExponent_one_exact : boxExponent 1 = (1 : ℝ) / 4 := by
  exact Erdos186.boxExponent_one

/-- From dimension two onwards, `boxExponent` is literally the quotient with
natural subtraction used in the box theorem. -/
theorem boxExponent_eq_fraction {d : ℕ} (hd : 2 ≤ d) :
    boxExponent d =
      (((d - 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  simp [boxExponent, show d ≠ 1 by omega]

/-- The same formula with subtraction performed after coercion. -/
theorem boxExponent_eq_real_fraction {d : ℕ} (hd : 2 ≤ d) :
    boxExponent d = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  rw [boxExponent_eq_pzExponent (by omega)]
  exact pzExponent_eq_fraction hd

/-- The box exponent is positive in every positive dimension. -/
theorem boxExponent_pos {d : ℕ} (hd : 1 ≤ d) :
    0 < boxExponent d := by
  rw [boxExponent_eq_pzExponent (by omega)]
  exact pzExponent_pos hd

/-- Every finite-dimensional box exponent is strictly below one. -/
theorem boxExponent_lt_one {d : ℕ} (hd : 1 ≤ d) :
    boxExponent d < 1 := by
  rw [boxExponent_eq_pzExponent (by omega)]
  exact pzExponent_lt_one hd

/-- The box exponents are strictly increasing on the positive dimensions. -/
theorem boxExponent_strictMono {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) :
    boxExponent d < boxExponent e := by
  rw [boxExponent_eq_pzExponent (by omega),
    boxExponent_eq_pzExponent (by omega)]
  exact pzExponent_strictMono hd hde

/-- Set-theoretic packaging of strict monotonicity. -/
theorem boxExponent_strictMonoOn :
    StrictMonoOn boxExponent (Set.Ici 1) := by
  intro d hd e _ hde
  exact boxExponent_strictMono hd hde

/-- Pairwise non-strict monotonicity on positive dimensions. -/
theorem boxExponent_mono {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    boxExponent d ≤ boxExponent e := by
  rcases hde.eq_or_lt with rfl | hde
  · rfl
  · exact (boxExponent_strictMono hd hde).le

/-- Every positive-dimensional box exponent is at least the exceptional
one-dimensional value `1 / 4`. -/
theorem one_div_four_le_boxExponent {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / 4 ≤ boxExponent d := by
  rw [boxExponent_eq_pzExponent (by omega)]
  exact one_div_four_le_pzExponent hd

/-! ## Observation 15 in box-exponent notation -/

/-- The unperturbed exponent expression in a dimension rise is at most one. -/
theorem boxExponent_dimensionRise_base {d e : ℕ}
    (hd : 1 ≤ d) (hde : d < e) :
    boxExponent e *
        (1 / boxExponent d - ((e - d : ℕ) : ℝ)) ≤ 1 := by
  rw [boxExponent_eq_pzExponent (by omega),
    boxExponent_eq_pzExponent (by omega)]
  exact pzExponent_dimensionRise_base hd hde

/-- Observation 15 with the perturbation cost exposed as a hypothesis. -/
theorem observation15_boxExponent_of_perturbation
    {d e : ℕ} {ζ ε : ℝ}
    (hd : 1 ≤ d) (hde : d < e) (hζ : 0 < ζ)
    (hcost :
      ε * ((e - d : ℕ) : ℝ) * (boxExponent e + ζ) ≤ ζ / 2) :
    (boxExponent e + ζ) *
        (1 / (boxExponent d + ζ) -
          (1 - ε) * ((e - d : ℕ) : ℝ)) ≤
      1 - ζ / 2 := by
  rw [boxExponent_eq_pzExponent (by omega)] at hcost ⊢
  rw [boxExponent_eq_pzExponent (by omega)] at ⊢
  exact observation15_dimensionRise_of_perturbation hd hde hζ hcost

/-- The explicit uniform form of Observation 15, now stated entirely with
the exponent occurring in `PZBoxBound`. -/
theorem observation15_boxExponent {d e : ℕ} {ζ ε : ℝ}
    (hd : 1 ≤ d) (hde : d < e) (hζ : 0 < ζ) (hζ_one : ζ ≤ 1)
    (hε : 0 ≤ ε)
    (hε_small :
      ε ≤ ζ / (4 * ((e - d : ℕ) : ℝ))) :
    (boxExponent e + ζ) *
        (1 / (boxExponent d + ζ) -
          (1 - ε) * ((e - d : ℕ) : ℝ)) ≤
      1 - ζ / 2 := by
  rw [boxExponent_eq_pzExponent (by omega),
    boxExponent_eq_pzExponent (by omega)]
  exact observation15_dimensionRise hd hde hζ hζ_one hε hε_small

/-- A source-level uniform version of Observation 15.

If all dimensions are bounded by `D`, it suffices to choose `ε` once using
the smaller positive loss `ζ₀`.  The conclusion applies at every
`ζ ∈ [ζ₀, 1]` and retains the uniform saving `ζ₀ / 2`. -/
theorem observation15_boxExponent_uniform
    {d e D : ℕ} {ζ₀ ζ ε : ℝ}
    (hd : 1 ≤ d) (hde : d < e) (heD : e ≤ D)
    (hζ₀ : 0 < ζ₀) (hζ₀ζ : ζ₀ ≤ ζ) (hζ_one : ζ ≤ 1)
    (hε : 0 ≤ ε)
    (hε_small : ε ≤ ζ₀ / (4 * (D : ℝ))) :
    (boxExponent e + ζ) *
        (1 / (boxExponent d + ζ) -
          (1 - ε) * ((e - d : ℕ) : ℝ)) ≤
      1 - ζ₀ / 2 := by
  have hk_nat : 0 < e - d := by omega
  have hk : (0 : ℝ) < ((e - d : ℕ) : ℝ) := by exact_mod_cast hk_nat
  have hD_nat : 0 < D := by omega
  have hD : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD_nat
  have hkD_nat : e - d ≤ D := (Nat.sub_le e d).trans heD
  have hkD : (((e - d : ℕ) : ℝ) : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hkD_nat
  have hεD : ε * (4 * (D : ℝ)) ≤ ζ₀ := by
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (D : ℝ))).mp hε_small
  have hεkD : ε * (4 * ((e - d : ℕ) : ℝ)) ≤
      ε * (4 * (D : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hε
    nlinarith
  have hε_uniform :
      ε ≤ ζ / (4 * ((e - d : ℕ) : ℝ)) := by
    rw [le_div_iff₀ (by positivity :
      (0 : ℝ) < 4 * ((e - d : ℕ) : ℝ))]
    exact hεkD.trans (hεD.trans hζ₀ζ)
  have hζ : 0 < ζ := hζ₀.trans_le hζ₀ζ
  have hmain :=
    observation15_boxExponent hd hde hζ hζ_one hε hε_uniform
  linarith

/-! ## Convex-density and downward-dimension gaps -/

/-- The dimension-dependent exponent supplied by the convex-density lemma.
Natural subtraction is intentional: in dimension one this has value zero. -/
def convexDensityExponent (d : ℕ) : ℝ :=
  ((d - 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)

/-- In dimensions at least two, the convex-density exponent is exactly the
box exponent. -/
theorem convexDensityExponent_eq_boxExponent {d : ℕ} (hd : 2 ≤ d) :
    convexDensityExponent d = boxExponent d := by
  rw [boxExponent_eq_fraction hd]
  rfl

/-- In every positive dimension, the convex-density exponent is at most the
box exponent.  The one-dimensional branch is the exceptional comparison
`0 ≤ 1/4`; from dimension two onwards there is equality. -/
theorem convexDensityExponent_le_boxExponent {d : ℕ} (hd : 1 ≤ d) :
    convexDensityExponent d ≤ boxExponent d := by
  by_cases hd1 : d = 1
  · subst d
    norm_num [convexDensityExponent, boxExponent]
  · have hd2 : 2 ≤ d := by omega
    exact (convexDensityExponent_eq_boxExponent hd2).le

/-- Inline form of `convexDensityExponent_le_boxExponent`, useful at call
sites whose exponent is not named. -/
theorem convexDensityFraction_le_boxExponent {d : ℕ} (hd : 1 ≤ d) :
    (((d - 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤ boxExponent d := by
  exact convexDensityExponent_le_boxExponent hd

/-- A positive loss `ζ` leaves a strict saving over the bare convex-density
exponent. -/
theorem convexDensityExponent_lt_boxExponent_add {d : ℕ} {ζ : ℝ}
    (hd : 1 ≤ d) (hζ : 0 < ζ) :
    convexDensityExponent d < boxExponent d + ζ := by
  linarith [convexDensityExponent_le_boxExponent hd]

/-- If the error in the convex-density lemma is at most `ζ / 2`, then at
least `ζ / 2` of the target exponent remains as a saving. -/
theorem convexDensityExponent_add_error_add_half_zeta_le
    {d : ℕ} {ζ error : ℝ}
    (hd : 1 ≤ d) (herror : error ≤ ζ / 2) :
    convexDensityExponent d + error + ζ / 2 ≤ boxExponent d + ζ := by
  have hbase := convexDensityExponent_le_boxExponent hd
  linarith

/-- Equivalent subtraction form of the preceding `ζ / 2` saving. -/
theorem convexDensityExponent_add_error_le_sub_half_zeta
    {d : ℕ} {ζ error : ℝ}
    (hd : 1 ≤ d) (herror : error ≤ ζ / 2) :
    convexDensityExponent d + error ≤ boxExponent d + ζ - ζ / 2 := by
  linarith [convexDensityExponent_add_error_add_half_zeta_le hd herror]

/-- Inline form of the convex-density saving, retaining the natural-number
subtraction casts appearing in the analytic statement. -/
theorem convexDensityFraction_add_error_add_half_zeta_le
    {d : ℕ} {ζ error : ℝ}
    (hd : 1 ≤ d) (herror : error ≤ ζ / 2) :
    (((d - 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) + error + ζ / 2 ≤
      boxExponent d + ζ := by
  exact convexDensityExponent_add_error_add_half_zeta_le hd herror

/-- A downward change between positive dimensions has a strictly positive
box-exponent gap. -/
theorem boxExponent_downward_gap_pos {lower upper : ℕ}
    (hlower : 1 ≤ lower) (hdrop : lower < upper) :
    0 < boxExponent upper - boxExponent lower := by
  exact sub_pos.mpr (boxExponent_strictMono hlower hdrop)

/-- Existential packaging of the positive gain available at a downward
dimension change. -/
theorem exists_boxExponent_gain_of_dimensionDrop {lower upper : ℕ}
    (hlower : 1 ≤ lower) (hdrop : lower < upper) :
    ∃ gain : ℝ, 0 < gain ∧
      boxExponent lower + gain = boxExponent upper := by
  refine ⟨boxExponent upper - boxExponent lower,
    boxExponent_downward_gap_pos hlower hdrop, ?_⟩
  ring

end

end Erdos186.PZ.FinalIteration
