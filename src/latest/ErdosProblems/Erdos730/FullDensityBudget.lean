/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: exact logarithmic density budget

This module formalizes the final infinite-series and rational-arithmetic
certificate in the proposed positive-density proof of Erdős 730.  It does not
formalize the preceding analytic counting argument; its sole input is the
explicit series appearing in that argument.
-/

namespace Erdos730

/-- The rational function used to majorize
`log ((1+x)/(1-x))` on `0 < x < 1`. -/
noncomputable def atanhLogUpper (x : ℝ) : ℝ :=
  2 * (x + x ^ 3 / 3) + 2 * x ^ 5 / (5 * (1 - x ^ 2))

/-- Equation (123): a strict, completely explicit upper bound for the
logarithmic ratio. -/
theorem log_one_add_div_one_sub_lt_atanhLogUpper
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) < atanhLogUpper x := by
  let f : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1)
  let g : ℕ → ℝ := fun k ↦
    (2 / 5) * x ^ 5 * (x ^ 2) ^ k
  have habs : |x| < 1 := by simpa [abs_of_pos hx0] using hx1
  have hf : HasSum f (Real.log (1 + x) - Real.log (1 - x)) := by
    simpa [f, Nat.cast_add, Nat.cast_mul] using
      (Real.hasSum_log_sub_log_of_abs_lt_one habs)
  have hratio :
      Real.log ((1 + x) / (1 - x)) =
        Real.log (1 + x) - Real.log (1 - x) := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0.le).2 hx1
  have hgeom : Summable (fun k : ℕ ↦ (x ^ 2) ^ k) :=
    summable_geometric_of_lt_one hx2_nonneg hx2_lt
  have hg : Summable g := (hgeom.mul_left ((2 / 5) * x ^ 5))
  have hpow (k : ℕ) : x ^ (2 * (k + 2) + 1) = x ^ 5 * (x ^ 2) ^ k := by
    rw [show 2 * (k + 2) + 1 = 5 + 2 * k by omega, pow_add, pow_mul]
  have hle (k : ℕ) : f (k + 2) ≤ g k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hden : (5 : ℝ) ≤ 2 * (k : ℝ) + 5 := by linarith
    have hinv : 1 / (2 * (k : ℝ) + 5) ≤ (1 : ℝ) / 5 := by
      exact one_div_le_one_div_of_le (by norm_num) hden
    dsimp only [f, g]
    rw [show 2 * ((k + 2 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 5 by
      push_cast
      ring, hpow]
    have hxpow : 0 ≤ x ^ 5 := (pow_nonneg hx0.le 5)
    have hxgeom : 0 ≤ (x ^ 2) ^ k := pow_nonneg hx2_nonneg k
    calc
      2 * (1 / (2 * (k : ℝ) + 5)) * (x ^ 5 * (x ^ 2) ^ k) ≤
          2 * ((1 : ℝ) / 5) * (x ^ 5 * (x ^ 2) ^ k) := by
        gcongr
      _ = 2 / 5 * x ^ 5 * (x ^ 2) ^ k := by ring
  have hlt : f (1 + 2) < g 1 := by
    dsimp only [f, g]
    rw [show 2 * ((1 + 2 : ℕ) : ℝ) + 1 = 7 by norm_num, hpow]
    have hx5 : 0 < x ^ 5 := pow_pos hx0 5
    have hx2 : 0 < x ^ 2 := pow_pos hx0 2
    norm_num
    nlinarith [mul_pos hx5 hx2]
  have htail : (∑' k : ℕ, f (k + 2)) < ∑' k : ℕ, g k := by
    exact Summable.tsum_lt_tsum hle hlt
      ((summable_nat_add_iff 2).2 hf.summable) hg
  have hsplit := hf.summable.sum_add_tsum_nat_add 2
  have hg_sum :
      (∑' k : ℕ, g k) = (2 / 5) * x ^ 5 / (1 - x ^ 2) := by
    rw [show (∑' k : ℕ, g k) = (2 / 5) * x ^ 5 *
        (∑' k : ℕ, (x ^ 2) ^ k) by
      simp only [g, tsum_mul_left]]
    rw [tsum_geometric_of_lt_one hx2_nonneg hx2_lt]
    field_simp
  rw [hg_sum] at htail
  have hhead :
      (∑ k ∈ Finset.range 2, f k) = 2 * x + 2 * x ^ 3 / 3 := by
    norm_num [f, Finset.sum_range_succ]
    ring
  calc
    Real.log ((1 + x) / (1 - x)) =
        (∑ k ∈ Finset.range 2, f k) + ∑' k : ℕ, f (k + 2) := by
      rw [hratio, ← hf.tsum_eq, hsplit]
    _ < (2 * x + 2 * x ^ 3 / 3) +
        (2 / 5) * x ^ 5 / (1 - x ^ 2) := by
      rw [hhead]
      linarith
    _ = atanhLogUpper x := by
      rw [atanhLogUpper]
      field_simp

/-- Equation (124), written as a specialization of `atanhLogUpper`. -/
noncomputable def U (d : ℕ) : ℝ := atanhLogUpper (1 / (d : ℝ))

/-- Equation (125). -/
theorem log_succ_div_pred_lt_U {d : ℕ} (hd : 3 ≤ d) :
    Real.log (((d + 1 : ℕ) : ℝ) / (d - 1 : ℕ)) < U d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hx0 : (0 : ℝ) < 1 / d := one_div_pos.mpr hd0
  have hx1 : (1 : ℝ) / d < 1 := (div_lt_one hd0).2 (by linarith)
  have h := log_one_add_div_one_sub_lt_atanhLogUpper hx0 hx1
  have hd1 : 1 ≤ d := by omega
  have hratio :
      (((d + 1 : ℕ) : ℝ) / (d - 1 : ℕ)) =
        (1 + 1 / (d : ℝ)) / (1 - 1 / (d : ℝ)) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hd1, Nat.cast_one]
    field_simp
  rw [hratio, U]
  exact h

/-! ## Exact specializations of the logarithmic majorant -/

theorem U_three : U 3 = (1123 : ℝ) / 1620 := by
  norm_num [U, atanhLogUpper]

theorem U_five : U 5 = (3041 : ℝ) / 7500 := by
  norm_num [U, atanhLogUpper]

theorem U_seven : U 7 = (3947 : ℝ) / 13720 := by
  norm_num [U, atanhLogUpper]

theorem U_nine : U 9 = (97603 : ℝ) / 437400 := by
  norm_num [U, atanhLogUpper]

theorem U_eleven : U 11 = (24267 : ℝ) / 133100 := by
  norm_num [U, atanhLogUpper]

theorem U_thirteen : U 13 = (142241 : ℝ) / 922740 := by
  norm_num [U, atanhLogUpper]

theorem U_fifteen : U 15 = (757123 : ℝ) / 5670000 := by
  norm_num [U, atanhLogUpper]

/-- The logarithm in the `r`th density-series term is the specialization
`d = 2r+3` of equation (125). -/
theorem log_density_ratio_lt_U (r : ℕ) :
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) < U (2 * r + 3) := by
  have h := log_succ_div_pred_lt_U (d := 2 * r + 3) (by omega)
  convert h using 1
  congr 1
  push_cast
  field_simp
  ring

/-! ## The infinite density series -/

/-- The `r=0` term is set to zero, so this is exactly the series over
integers `r >= 1` from equation (103). -/
noncomputable def densityBudgetTerm (r : ℕ) : ℝ :=
  if r = 0 then 0
  else (1 / 4 : ℝ) ^ r * Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ))

/-- The series `S` in the density budget. -/
noncomputable def densityBudgetSeries : ℝ :=
  ∑' r : ℕ, densityBudgetTerm r

theorem densityBudgetTerm_nonneg (r : ℕ) : 0 ≤ densityBudgetTerm r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, hr]
  · have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
    have hratio : (1 : ℝ) ≤ (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) := by
      rw [le_div_iff₀ hden]
      push_cast
      linarith
    simp only [densityBudgetTerm, hr, if_false]
    exact mul_nonneg (pow_nonneg (by norm_num) r) (Real.log_nonneg hratio)

/-- The elementary upper bound `log ((r+2)/(r+1)) <= 1/(r+1)`. -/
theorem log_density_ratio_le_inv_succ (r : ℕ) :
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤ 1 / (r + 1 : ℕ) := by
  have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hpos : (0 : ℝ) < (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) := by positivity
  calc
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
        (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    _ = 1 / (r + 1 : ℕ) := by
      field_simp
      push_cast
      ring

theorem densityBudgetTerm_le_geometric (r : ℕ) :
    densityBudgetTerm r ≤ (1 / 4 : ℝ) ^ r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, hr]
  · have hlog := log_density_ratio_le_inv_succ r
    have hinv : (1 : ℝ) / (r + 1 : ℕ) ≤ 1 := by
      rw [div_le_one]
      · norm_num
      · positivity
    simp only [densityBudgetTerm, hr, if_false]
    calc
      (1 / 4 : ℝ) ^ r *
          Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
          (1 / 4 : ℝ) ^ r * 1 := by
        gcongr
        exact hlog.trans hinv
      _ = (1 / 4 : ℝ) ^ r := mul_one _

theorem densityBudgetTerm_summable : Summable densityBudgetTerm := by
  exact Summable.of_nonneg_of_le densityBudgetTerm_nonneg
    densityBudgetTerm_le_geometric
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- For `r >= 7`, the logarithm is at most `1/8`. -/
theorem densityBudgetTerm_le_eighth_geometric {r : ℕ} (hr : 7 ≤ r) :
    densityBudgetTerm r ≤ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ r := by
  have hr0 : r ≠ 0 := by omega
  have hden : (8 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast (show 8 ≤ r + 1 by omega)
  have hinv : (1 : ℝ) / (r + 1 : ℕ) ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hlog :
      Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤ 1 / 8 :=
    (log_density_ratio_le_inv_succ r).trans hinv
  simp only [densityBudgetTerm, hr0, if_false]
  calc
    (1 / 4 : ℝ) ^ r *
        Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
        (1 / 4 : ℝ) ^ r * (1 / 8) := by
      gcongr
    _ = (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ r := by ring

/-- Equation (126): the entire tail beginning at `r=7`. -/
theorem densityBudget_tail_le :
    (∑' n : ℕ, densityBudgetTerm (n + 7)) ≤ (1 : ℝ) / 98304 := by
  let g : ℕ → ℝ := fun n ↦ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ (n + 7)
  have hg : HasSum g ((1 : ℝ) / 98304) := by
    have hgeom := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    have hscaled := hgeom.mul_left ((1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7)
    have hfun : g = fun i ↦ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7 * (1 / 4 : ℝ) ^ i := by
      funext n
      simp only [g, pow_add]
      ring
    have hval : (1 : ℝ) / 98304 = (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7 * (1 - 1 / 4)⁻¹ := by
      norm_num
    rw [hfun, hval]
    exact hscaled
  calc
    (∑' n : ℕ, densityBudgetTerm (n + 7)) ≤ ∑' n : ℕ, g n := by
      exact ((summable_nat_add_iff 7).2 densityBudgetTerm_summable).tsum_le_tsum
        (fun n ↦ densityBudgetTerm_le_eighth_geometric (by omega)) hg.summable
    _ = (1 : ℝ) / 98304 := hg.tsum_eq

/-- The finite majorant used for indices `0,...,6`. -/
noncomputable def densityBudgetFiniteMajorant (r : ℕ) : ℝ :=
  if r = 0 then 0 else (1 / 4 : ℝ) ^ r * U (2 * r + 3)

theorem densityBudgetTerm_le_finiteMajorant (r : ℕ) :
    densityBudgetTerm r ≤ densityBudgetFiniteMajorant r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, densityBudgetFiniteMajorant, hr]
  · simp only [densityBudgetTerm, densityBudgetFiniteMajorant, hr, if_false]
    exact (mul_lt_mul_of_pos_left (log_density_ratio_lt_U r)
      (pow_pos (by norm_num) r)).le

theorem densityBudgetTerm_one_lt_finiteMajorant :
    densityBudgetTerm 1 < densityBudgetFiniteMajorant 1 := by
  simp only [densityBudgetTerm, densityBudgetFiniteMajorant, one_ne_zero, if_false]
  exact mul_lt_mul_of_pos_left (log_density_ratio_lt_U 1) (by norm_num)

/-- The exact rational evaluation of the six finite majorants together with
the geometric tail. -/
theorem densityBudget_finite_and_tail_certificate :
    (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) + (1 : ℝ) / 98304 =
      (11117760449158646497 : ℝ) / 89848527388139520000 := by
  norm_num [densityBudgetFiniteMajorant, U, atanhLogUpper, Finset.sum_range_succ]

/-- Equation (127): the exact strict upper bound for the series `S`. -/
theorem densityBudgetSeries_lt_certificate :
    densityBudgetSeries <
      (11117760449158646497 : ℝ) / 89848527388139520000 := by
  have hfinite :
      (∑ r ∈ Finset.range 7, densityBudgetTerm r) <
        ∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r := by
    exact Finset.sum_lt_sum
      (fun r _ ↦ densityBudgetTerm_le_finiteMajorant r)
      ⟨1, by simp, densityBudgetTerm_one_lt_finiteMajorant⟩
  have hsplit := densityBudgetTerm_summable.sum_add_tsum_nat_add 7
  rw [densityBudgetSeries, ← hsplit]
  calc
    (∑ r ∈ Finset.range 7, densityBudgetTerm r) +
        ∑' n : ℕ, densityBudgetTerm (n + 7) <
        (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) +
          ∑' n : ℕ, densityBudgetTerm (n + 7) := by
      gcongr
    _ ≤ (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) +
          (1 : ℝ) / 98304 := by
      gcongr
      exact densityBudget_tail_le
    _ = (11117760449158646497 : ℝ) / 89848527388139520000 :=
      densityBudget_finite_and_tail_certificate

/-! ## Final exact density budget -/

/-- Equation (128): the same logarithmic majorant at `d=3` bounds `log 2`. -/
theorem log_two_lt_U_three : Real.log 2 < U 3 := by
  have h := log_succ_div_pred_lt_U (d := 3) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Exact evaluation of the two rational upper bounds in equation (129). -/
theorem densityBudget_total_upper_identity :
    4 * ((11117760449158646497 : ℝ) / 89848527388139520000) +
        (2 / 3) * ((1123 : ℝ) / 1620) =
      (21498408212212214497 : ℝ) / 22462131847034880000 := by
  norm_num

/-- Equation (129), including both strict analytic inequalities. -/
theorem densityBudget_total_lt_exact :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 <
      (21498408212212214497 : ℝ) / 22462131847034880000 := by
  have hS := densityBudgetSeries_lt_certificate
  have hlog : Real.log 2 < (1123 : ℝ) / 1620 := by
    rw [← U_three]
    exact log_two_lt_U_three
  calc
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 <
        4 * ((11117760449158646497 : ℝ) / 89848527388139520000) +
          (2 / 3) * ((1123 : ℝ) / 1620) := by
      nlinarith
    _ = (21498408212212214497 : ℝ) / 22462131847034880000 :=
      densityBudget_total_upper_identity

/-- Equation (130): the target-minus-certificate difference, exactly. -/
theorem densityBudget_target_difference :
    (2393 : ℝ) / 2500 -
        (21498408212212214497 : ℝ) / 22462131847034880000 =
      (2344391769572639 : ℝ) / 22462131847034880000 := by
  norm_num

/-- Equation (121): the final logarithmic-series budget is below `2393/2500`. -/
theorem densityBudget_final_lt :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 < (2393 : ℝ) / 2500 := by
  exact densityBudget_total_lt_exact.trans (by norm_num)

end Erdos730
