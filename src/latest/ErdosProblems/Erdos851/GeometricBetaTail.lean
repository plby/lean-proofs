/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The geometric tail in the beta-100 boundary-chain estimate

This file isolates the numerical part of the beta-sieve argument.  The actual
boundary-chain estimate has the shape

`A * c^(κ*r) * (log A + κ*r*log c)^r / r!`,

where `κ ≤ 2`.  The same-parity Rosser stopping rule contributes `101/99`
over a two-position advance (and hence is covered by `(100/99)^2`), but this
helper deliberately uses the stronger, parity-free inflation
`c = (β+1)/(β-1) = 101/99` at every depth.  Unlike a fixed-constant
exponential-series bound, the base inside the `r`-th power grows linearly in
`r`.  The factorial still wins: the elementary lower bound implicit in the
exponential series leaves the geometric base

`c^2 * 3 * log c * exp 1 < 1/4`.

The results below give eventual termwise domination by `A * (1/4)^r`,
summability, explicit finite and infinite shifted-tail bounds, and tails below
an arbitrary positive tolerance.
-/

namespace Erdos851

open Filter
open scoped BigOperators Topology

namespace GeometricBetaTail

/-- A conservative per-depth beta-100 inflation factor `(β+1)/(β-1)`;
the same-parity application only incurs this factor every two positions. -/
noncomputable def inflation : ℝ := 101 / 99

/-- The numerical chain term occurring after the dimension estimate. -/
noncomputable def term (A : ℝ) (κ r : ℕ) : ℝ :=
  A * inflation ^ (κ * r) *
      (Real.log A + (κ * r : ℕ) * Real.log inflation) ^ r /
    (r.factorial : ℝ)

/-- The constant left after using `r^r / r! ≤ e^r`. -/
noncomputable def geometricBase : ℝ :=
  inflation ^ 2 * 3 * Real.log inflation * Real.exp 1

lemma inflation_pos : 0 < inflation := by
  norm_num [inflation]

lemma inflation_one_le : 1 ≤ inflation := by
  norm_num [inflation]

lemma log_inflation_pos : 0 < Real.log inflation := by
  exact Real.log_pos (by norm_num [inflation])

lemma log_inflation_le : Real.log inflation ≤ 2 / 99 := by
  calc
    Real.log inflation ≤ inflation - 1 :=
      Real.log_le_sub_one_of_pos inflation_pos
    _ = 2 / 99 := by norm_num [inflation]

/-- An explicit rational upper bound for the beta-100 geometric base. -/
lemma geometricBase_lt_explicit : geometricBase < 20402 / 107811 := by
  have hlog0 : 0 ≤ Real.log inflation := log_inflation_pos.le
  calc
    geometricBase =
        inflation ^ 2 * 3 * Real.log inflation * Real.exp 1 := rfl
    _ ≤ inflation ^ 2 * 3 * (2 / 99) * Real.exp 1 := by
      gcongr
      exact log_inflation_le
    _ < inflation ^ 2 * 3 * (2 / 99) * 3 := by
      exact mul_lt_mul_of_pos_left Real.exp_one_lt_three (by
        have : (0 : ℝ) < inflation := inflation_pos
        positivity)
    _ = 20402 / 107811 := by norm_num [inflation]

/-- The decisive beta-100 numerical inequality. -/
lemma geometricBase_lt_quarter : geometricBase < 1 / 4 :=
  geometricBase_lt_explicit.trans (by norm_num)

lemma geometricBase_nonneg : 0 ≤ geometricBase := by
  unfold geometricBase
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg inflation_pos.le 2) (by norm_num))
      log_inflation_pos.le)
    (Real.exp_pos 1).le

/-- The diagonal term of the exponential series gives
`r^r / r! ≤ (exp 1)^r`. -/
lemma self_pow_div_factorial_le_exp_one_pow (r : ℕ) :
    (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp 1 ^ r := by
  rw [← Real.exp_nat_mul, mul_one, Real.exp_eq_exp_ℝ,
    NormedSpace.exp_eq_tsum_div]
  exact Summable.le_tsum
    (show Summable (fun n : ℕ => (r : ℝ) ^ n / (n.factorial : ℝ)) from
      Real.summable_pow_div_factorial (r : ℝ))
    r (fun _ _ => by positivity)

/-- Once `log A ≤ r log c`, the true beta-chain term is bounded by the fixed
geometric base. -/
lemma term_le_geometricBase_pow
    {A : ℝ} {κ r : ℕ} (hA : 1 ≤ A) (hκ : κ ≤ 2)
    (hr : Real.log A ≤ (r : ℝ) * Real.log inflation) :
    term A κ r ≤ A * geometricBase ^ r := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogc0 : 0 ≤ Real.log inflation := log_inflation_pos.le
  have hκReal : (κ : ℝ) ≤ 2 := by exact_mod_cast hκ
  have hlinear :
      Real.log A + (κ * r : ℕ) * Real.log inflation ≤
        3 * (r : ℝ) * Real.log inflation := by
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) hlogc0]
  have hlinear0 :
      0 ≤ Real.log A + (κ * r : ℕ) * Real.log inflation := by
    positivity
  have hcκ : inflation ^ κ ≤ inflation ^ 2 :=
    pow_le_pow_right₀ inflation_one_le hκ
  have hcpow : inflation ^ (κ * r) ≤ (inflation ^ 2) ^ r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg inflation_pos.le κ) hcκ r
  have hbasepow :
      (Real.log A + (κ * r : ℕ) * Real.log inflation) ^ r ≤
        (3 * (r : ℝ) * Real.log inflation) ^ r :=
    pow_le_pow_left₀ hlinear0 hlinear r
  have hfactorial := self_pow_div_factorial_le_exp_one_pow r
  unfold term
  calc
    A * inflation ^ (κ * r) *
          (Real.log A + ↑(κ * r) * Real.log inflation) ^ r /
        (r.factorial : ℝ)
        ≤ A * (inflation ^ 2) ^ r *
          (3 * (r : ℝ) * Real.log inflation) ^ r /
        (r.factorial : ℝ) := by
          gcongr
    _ = A * (inflation ^ 2 * 3 * Real.log inflation) ^ r *
          ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ A * (inflation ^ 2 * 3 * Real.log inflation) ^ r *
          Real.exp 1 ^ r := by
      gcongr
    _ = A * geometricBase ^ r := by
      unfold geometricBase
      rw [mul_pow]
      ring

/-- The logarithmic threshold needed in `term_le_geometricBase_pow` is
eventually satisfied. -/
lemma eventually_log_le_nat_mul_log_inflation (A : ℝ) :
    ∀ᶠ r : ℕ in atTop,
      Real.log A ≤ (r : ℝ) * Real.log inflation := by
  have h := tendsto_natCast_atTop_atTop.const_mul_atTop log_inflation_pos
  simpa [mul_comm] using h.eventually_ge_atTop (Real.log A)

/-- The actual beta-100 chain term is eventually bounded by a quarter-ratio
geometric sequence, uniformly for every natural `κ ≤ 2`. -/
theorem eventually_term_le_quarter
    {A : ℝ} (hA : 1 ≤ A) {κ : ℕ} (hκ : κ ≤ 2) :
    ∀ᶠ r : ℕ in atTop, term A κ r ≤ A * (1 / 4 : ℝ) ^ r := by
  filter_upwards [eventually_log_le_nat_mul_log_inflation A] with r hr
  exact (term_le_geometricBase_pow hA hκ hr).trans <|
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ geometricBase_nonneg geometricBase_lt_quarter.le r)
      (zero_le_one.trans hA)

lemma term_nonneg {A : ℝ} (hA : 1 ≤ A) (κ r : ℕ) :
    0 ≤ term A κ r := by
  unfold term
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hbase :
      0 ≤ Real.log A + (κ * r : ℕ) * Real.log inflation :=
    add_nonneg (Real.log_nonneg hA)
      (mul_nonneg (by positivity) log_inflation_pos.le)
  exact div_nonneg
    (mul_nonneg (mul_nonneg hA0 (pow_nonneg inflation_pos.le (κ * r)))
      (pow_nonneg hbase r))
    (by positivity)

/-- The beta-chain numerical majorant is summable. -/
theorem summable_term {A : ℝ} (hA : 1 ≤ A) {κ : ℕ} (hκ : κ ≤ 2) :
    Summable (term A κ) := by
  apply ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left A).of_norm_bounded_eventually_nat
  filter_upwards [eventually_term_le_quarter hA hκ] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg hA κ r)]
  exact hr

lemma tsum_quarter_add (R : ℕ) :
    (∑' i : ℕ, (1 / 4 : ℝ) ^ (R + i)) =
      (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
  simp_rw [pow_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
  ring

/-- Explicit finite shifted-tail bound after the termwise geometric regime
has begun. -/
theorem sum_range_tail_le
    {A : ℝ} (hA : 1 ≤ A) {κ R : ℕ}
    (hR : ∀ r ≥ R, term A κ r ≤ A * (1 / 4 : ℝ) ^ r) (m : ℕ) :
    ∑ i ∈ Finset.range m, term A κ (R + i) ≤
      A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
  calc
    ∑ i ∈ Finset.range m, term A κ (R + i) ≤
        ∑ i ∈ Finset.range m, A * (1 / 4 : ℝ) ^ (R + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hR (R + i) (by omega)
    _ ≤ ∑' i : ℕ, A * (1 / 4 : ℝ) ^ (R + i) := by
      exact Summable.sum_le_tsum (Finset.range m) (fun _ _ => by positivity)
        (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)).comp_injective
            (add_right_injective R)).mul_left A)
    _ = A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
      rw [tsum_mul_left, tsum_quarter_add]
      ring

/-- Explicit infinite shifted-tail bound after the termwise geometric regime
has begun. -/
theorem tsum_tail_le
    {A : ℝ} (hA : 1 ≤ A) {κ R : ℕ} (hκ : κ ≤ 2)
    (hR : ∀ r ≥ R, term A κ r ≤ A * (1 / 4 : ℝ) ^ r) :
    (∑' i : ℕ, term A κ (R + i)) ≤
      A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
  calc
    (∑' i : ℕ, term A κ (R + i)) ≤
        ∑' i : ℕ, A * (1 / 4 : ℝ) ^ (R + i) := by
      exact Summable.tsum_le_tsum
        (fun i => hR (R + i) (by omega))
        ((summable_term hA hκ).comp_injective (add_right_injective R))
        (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)).comp_injective
            (add_right_injective R)).mul_left A)
    _ = A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
      rw [tsum_mul_left, tsum_quarter_add]
      ring

/-- A single sufficiently large starting depth makes every finite tail and
the infinite tail smaller than `eta`. -/
theorem exists_tails_lt
    {A eta : ℝ} (hA : 1 ≤ A) (heta : 0 < eta)
    {κ : ℕ} (hκ : κ ≤ 2) :
    ∃ R : ℕ,
      (∀ r ≥ R, term A κ r ≤ A * (1 / 4 : ℝ) ^ r) ∧
      (∀ m : ℕ, ∑ i ∈ Finset.range m, term A κ (R + i) < eta) ∧
      (∑' i : ℕ, term A κ (R + i)) < eta := by
  have hsmall : ∀ᶠ R : ℕ in atTop,
      A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R < eta := by
    have htend : Tendsto
        (fun R : ℕ => A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R)
        atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).const_mul
          (A * (4 / 3 : ℝ))
    exact (tendsto_order.1 htend).2 eta heta
  have hgeom := eventually_term_le_quarter hA hκ
  rw [eventually_atTop] at hsmall hgeom
  obtain ⟨Rsmall, hRsmall⟩ := hsmall
  obtain ⟨Rgeom, hRgeom⟩ := hgeom
  let R := max Rsmall Rgeom
  have hRbound : ∀ r ≥ R, term A κ r ≤ A * (1 / 4 : ℝ) ^ r := by
    intro r hr
    exact hRgeom r ((le_max_right Rsmall Rgeom).trans hr)
  have hRsmall' : A * (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R < eta :=
    hRsmall R ((le_max_left Rsmall Rgeom))
  refine ⟨R, hRbound, ?_, ?_⟩
  · intro m
    exact (sum_range_tail_le hA hRbound m).trans_lt hRsmall'
  · exact (tsum_tail_le hA hκ hRbound).trans_lt hRsmall'

end GeometricBetaTail

end Erdos851
