/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerLemma3Concrete
import ErdosProblems.Erdos240.BakerLemma4Concrete
import ErdosProblems.Erdos240.BakerLemma4LocalResidues
import ErdosProblems.Erdos240.BakerLemma4OuterContour
import ErdosProblems.Erdos240.BakerRationalExtrapolation
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerSourceMomentCancellation
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics
import ErdosProblems.Erdos240.BakerSourceRationalFixedHeightBudget
import ErdosProblems.Erdos240.BakerSourceRationalExactLiouville
import ErdosProblems.Erdos240.BakerSourceRationalHonestOuterBudget
import ErdosProblems.Erdos240.BakerSourceRationalSharpBudget
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.ExplicitHermiteBasis
import ErdosProblems.Erdos240.InterpolationProducts
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Concrete rational extrapolation (van der Poorten--Loxton, Lemma 5)

This file discharges the outer-contour part of source Lemma 5.  The
interpolation nodes are `1, ..., R`, each repeated `T` times, the target is
the nonintegral rational point `l / q`, and the outer contour is the circle
of radius `3R` about zero.

The displayed budget in `norm_at_rational_lt_of_hermite_bounds` contains
exactly the three estimates used in the source:

* `(R!)^T` for the nodal product at the rational target;
* `(2R)^(R*T)` for the nodal product on the outer circle;
* `2R` for the distance from the target to that circle.

The final source-shaped theorem specializes to the corrected
`BakerSourceState.LevelState`: only the Delta factor is level-scaled, while
the exponential retains the unscaled interpolation variable.  Its outer
growth and target lower alternatives are supplied by concrete Lemma 3, and
its small normalized jets are converted to Hermite-polynomial bounds by
concrete Lemma 4.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerLemma5Concrete

open Complex Finset Metric Polynomial
open BakerLemma3 BakerLemma3Concrete
open BakerLemma4Concrete
open BakerSourceState
open BakerSourceMomentCancellation
open BakerSourceOversizedConstantNumerics
open Erdos240.BakerSourcePositiveStageGrowth
open ExplicitHermiteBasis
open HermiteInterpolation InterpolationProducts

/-! ### The factorial-cancelled local circles for a rational target

For a nonintegral target `l/q`, the circle about an integral node has radius
`1/(2q)`.  The centre factor contributes exactly this radius, whereas all
other integral-node factors retain half their integral separation.  Thus the
only new loss compared with the integral version of equation (9) is one
factor of `q` per Hermite multiplicity; importantly, there is no factorial or
`R log R` loss. -/

/-- On a circle of radius at most `1/2` about `r`, a node strictly to the
left is separated by at least half its integral distance. -/
theorem rationalLocalCircle_left_factor_lower {z : ℂ} {r i q : ℕ}
    (hq : 0 < q) (hi : i < r - 1)
    (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    ((r - (i + 1) : ℕ) : ℝ) / 2 ≤
      ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hzhalf : ‖z - (r : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    rw [hz]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)
      (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hir : i + 1 < r := by omega
  have hdist : ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ ≤
      ‖((r : ℕ) : ℂ) - z‖ + ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
    calc
      ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ =
          ‖(((r : ℕ) : ℂ) - z) + (z - ((i + 1 : ℕ) : ℂ))‖ := by
        congr 1 <;> ring
      _ ≤ ‖((r : ℕ) : ℂ) - z‖ + ‖z - ((i + 1 : ℕ) : ℂ)‖ :=
        norm_add_le _ _
  rw [norm_sub_rev ((r : ℕ) : ℂ) z] at hdist
  have hcast : ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ =
      ((r - (i + 1) : ℕ) : ℝ) := by
    rw [show ((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ) =
        (((r - (i + 1) : ℕ) : ℝ) : ℂ) by
      norm_num [Nat.cast_sub (Nat.le_of_lt hir)]]
    simp
  rw [hcast] at hdist
  have hone : (1 : ℝ) ≤ (r - (i + 1) : ℕ) := by
    exact_mod_cast (show 1 ≤ r - (i + 1) by omega)
  nlinarith

/-- The analogous half-separation for a node to the right of the centre. -/
theorem rationalLocalCircle_right_factor_lower {z : ℂ} {r j q : ℕ}
    (hq : 0 < q) (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    ((j + 1 : ℕ) : ℝ) / 2 ≤
      ‖z - ((r + j + 1 : ℕ) : ℂ)‖ := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hzhalf : ‖z - (r : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    rw [hz]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)
      (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hdist : ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ ≤
      ‖((r + j + 1 : ℕ) : ℂ) - z‖ + ‖z - (r : ℂ)‖ := by
    calc
      ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ =
          ‖(((r + j + 1 : ℕ) : ℂ) - z) + (z - (r : ℂ))‖ := by
        congr 1 <;> ring
      _ ≤ ‖((r + j + 1 : ℕ) : ℂ) - z‖ + ‖z - (r : ℂ)‖ :=
        norm_add_le _ _
  rw [norm_sub_rev ((r + j + 1 : ℕ) : ℂ) z] at hdist
  have hcast : ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ =
      ((j + 1 : ℕ) : ℝ) := by
    rw [show ((r + j + 1 : ℕ) : ℂ) - (r : ℂ) =
        (((j + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))]
  rw [hcast] at hdist
  have hone : (1 : ℝ) ≤ (j + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  nlinarith

/-- Exact factorial lower bound for the rational local circle. -/
theorem rationalLocalCircle_denominator_lower {R r q : ℕ}
    (hq : 0 < q) (hr : 1 ≤ r) (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    (1 / (2 * (q : ℝ))) * (1 / 2 : ℝ) ^ (R - 1) *
        (r - 1).factorial * (R - r).factorial ≤
      ∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
  have hsplit : R = (r - 1) + 1 + (R - r) := by omega
  have hprod :
      (∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖) =
        (∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖) *
          ‖z - (r : ℂ)‖ *
          (∏ j ∈ range (R - r),
            ‖z - ((r + j + 1 : ℕ) : ℂ)‖) := by
    conv_lhs => rw [hsplit, prod_range_add, prod_range_succ]
    simp only [Nat.sub_add_cancel hr]
  rw [hprod]
  have hleft :
      (1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial ≤
        ∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
    rw [show (1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial =
      ∏ i ∈ range (r - 1), (((r - (i + 1) : ℕ) : ℝ) / 2) by
        simp_rw [div_eq_mul_inv]
        rw [prod_mul_distrib]
        have hprodsub :
            (∏ i ∈ range (r - 1), ((r - (i + 1) : ℕ) : ℝ)) =
              ∏ i ∈ range (r - 1), (((r - 1) - i : ℕ) : ℝ) := by
          apply prod_congr rfl
          intro i hi
          have hi' := mem_range.mp hi
          exact_mod_cast (show r - (i + 1) = (r - 1) - i by omega)
        rw [hprodsub, prod_range_cast_sub_eq_factorial]
        simp [mul_comm]]
    apply prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact rationalLocalCircle_left_factor_lower hq (mem_range.mp hi) hz
  have hright :
      (1 / 2 : ℝ) ^ (R - r) * (R - r).factorial ≤
        ∏ j ∈ range (R - r), ‖z - ((r + j + 1 : ℕ) : ℂ)‖ := by
    rw [show (1 / 2 : ℝ) ^ (R - r) * (R - r).factorial =
      ∏ j ∈ range (R - r), (((j + 1 : ℕ) : ℝ) / 2) by
        simp_rw [div_eq_mul_inv]
        rw [prod_mul_distrib, prod_range_cast_add_one_eq_factorial]
        simp [mul_comm]]
    apply prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact rationalLocalCircle_right_factor_lower hq hz
  have hpow :
      (1 / 2 : ℝ) ^ (R - 1) =
        (1 / 2 : ℝ) ^ (r - 1) * (1 / 2 : ℝ) ^ (R - r) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (1 / (2 * (q : ℝ))) * (1 / 2 : ℝ) ^ (R - 1) *
        (r - 1).factorial * (R - r).factorial =
      ((1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial) *
        (1 / (2 * (q : ℝ))) *
        ((1 / 2 : ℝ) ^ (R - r) * (R - r).factorial) := by
          rw [hpow]
          ring
    _ ≤ (∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖) *
          ‖z - (r : ℂ)‖ *
          (∏ j ∈ range (R - r),
            ‖z - ((r + j + 1 : ℕ) : ℂ)‖) := by
      rw [hz]
      exact mul_le_mul (mul_le_mul hleft le_rfl (by positivity) (by positivity))
        hright (by positivity) (by positivity)

/-- The factorial cancellation for a nonintegral rational target, before
raising to the Hermite multiplicity. -/
theorem rationalLocalCircle_nodal_base_ratio_bound
    {R r l q : ℕ} (hq : 0 < q) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hlR : l ≤ q * R) {z : ℂ}
    (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    ‖(∏ i ∈ range R,
          ((l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ))) /
        (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)))‖ ≤
      (q : ℝ) * (2 : ℝ) ^ (3 * R) := by
  rw [norm_div, norm_prod, norm_prod]
  have hden := rationalLocalCircle_denominator_lower hq hr hrR hz
  have hbasePos : 0 <
      (1 / (2 * (q : ℝ))) * (1 / 2 : ℝ) ^ (R - 1) *
        (r - 1).factorial * (R - r).factorial := by positivity
  have hden0 : 0 < ∏ i ∈ range R,
      ‖z - ((i + 1 : ℕ) : ℂ)‖ := hbasePos.trans_le hden
  rw [div_le_iff₀ hden0]
  have hnum : (∏ i ∈ range R,
      ‖(l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ)‖) ≤
      (R.factorial : ℝ) := by
    have h := norm_integralNodalProduct_ratCast_le_factorial_pow
      (l := l) (q := q) (R := R) (S := 1) hq hlR
    rw [integralNodalProduct, norm_prod] at h
    have hcast : ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) =
        (l : ℂ) / (q : ℂ) := by norm_num
    rw [hcast] at h
    simpa only [pow_one] using h
  have hfac := factorial_le_localCircle_factor_times_pow hr hrR
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hR : 1 ≤ R := hr.trans hrR
  have hbaseEq :
      (1 / (2 * (q : ℝ))) * (1 / 2 : ℝ) ^ (R - 1) =
        (1 / (q : ℝ)) * (1 / 2 : ℝ) ^ R := by
    rw [show R = (R - 1) + 1 by omega, pow_add]
    norm_num
    ring
  calc
    ∏ i ∈ range R,
        ‖(l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ)‖ ≤
        (R.factorial : ℝ) := hnum
    _ ≤ (2 : ℝ) ^ (2 * R) * (r - 1).factorial *
        (R - r).factorial := hfac
    _ = ((q : ℝ) * (2 : ℝ) ^ (3 * R)) *
        ((1 / (2 * (q : ℝ))) * (1 / 2 : ℝ) ^ (R - 1) *
          (r - 1).factorial * (R - r).factorial) := by
      rw [hbaseEq]
      rw [show (1 / 2 : ℝ) ^ R =
          ((2 : ℝ) ^ R)⁻¹ by rw [one_div, inv_pow]]
      have hpow : (2 : ℝ) ^ (3 * R) =
          (2 : ℝ) ^ (2 * R) * (2 : ℝ) ^ R := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp [hqR.ne']
    _ ≤ ((q : ℝ) * (2 : ℝ) ^ (3 * R)) *
        ∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
      gcongr

/-- Powered form of the rational local-circle quotient.  Its logarithmic
loss is linear in `R*T`: `q^T * 2^(3RT)`. -/
theorem rationalLocalCircle_nodal_ratio_bound
    {R T r l q : ℕ} (hq : 0 < q) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hlR : l ≤ q * R) {z : ℂ}
    (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    ‖(∏ i ∈ range R,
          ((l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ T) /
        (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ T)‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T := by
  rw [Finset.prod_pow, Finset.prod_pow, ← div_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (rationalLocalCircle_nodal_base_ratio_bound hq hr hrR hlR hz) T

/-- Rational-target version of the local residue kernel in source equation
(9). -/
def rationalLocalCircleKernel
    (R T r l q m : ℕ) (z : ℂ) : ℂ :=
  ((∏ i ∈ range R,
        ((l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ T) /
      (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ T) *
    (z - (r : ℂ)) ^ m) /
      (z - (l : ℂ) / (q : ℂ))

/-- The target is at least the local radius away from every point of the
small circle.  The assumption `q ∤ l` is used exactly here. -/
theorem rationalLocalCircle_target_separation
    {r l q : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l) {z : ℂ}
    (hz : ‖z - (r : ℂ)‖ = 1 / (2 * (q : ℝ))) :
    1 / (2 * (q : ℝ)) ≤ ‖z - (l : ℂ) / (q : ℂ)‖ := by
  have hcentres := BakerRationalExtrapolation.one_div_le_norm_rational_sub_nat
    (r := r) hq hnmid
  have htriangle :
      ‖(l : ℂ) / (q : ℂ) - (r : ℂ)‖ ≤
        ‖z - (l : ℂ) / (q : ℂ)‖ + ‖z - (r : ℂ)‖ := by
    calc
      ‖(l : ℂ) / (q : ℂ) - (r : ℂ)‖ =
          ‖((l : ℂ) / (q : ℂ) - z) + (z - (r : ℂ))‖ := by
        congr 1 <;> ring
      _ ≤ ‖(l : ℂ) / (q : ℂ) - z‖ + ‖z - (r : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖z - (l : ℂ) / (q : ℂ)‖ + ‖z - (r : ℂ)‖ := by
        rw [norm_sub_rev]
  rw [hz] at htriangle
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by
    field_simp
  rw [hhalf] at hcentres
  linarith

/-- After normalizing the small-circle integral by `2*pi*i`, its radius
cancels the lower bound for the distance to the rational target. -/
theorem norm_normalized_rationalLocalCircleKernel_integral_le
    {R T r l q m : ℕ} (hq : 0 < q) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hlR : l ≤ q * R) (hnmid : ¬ q ∣ l) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C((r : ℂ), (1 / (2 * (q : ℝ)))),
          rationalLocalCircleKernel R T r l q m z‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T := by
  let rho : ℝ := 1 / (2 * (q : ℝ))
  let B : ℝ := ((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho_le_one : rho ≤ 1 := by
    dsimp [rho]
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * q)]
    nlinarith [hq1]
  have hkernel : ∀ z ∈ sphere (r : ℂ) rho,
      ‖rationalLocalCircleKernel R T r l q m z‖ ≤
        (2 * (q : ℝ)) * B := by
    intro z hzSphere
    have hz : ‖z - (r : ℂ)‖ = rho := by
      simpa [mem_sphere, dist_eq_norm] using hzSphere
    have hratio := rationalLocalCircle_nodal_ratio_bound
      (T := T) hq hr hrR hlR (by simpa only [rho] using hz)
    have htarget := rationalLocalCircle_target_separation hq hnmid
      (by simpa only [rho] using hz)
    have hpowSmall : ‖(z - (r : ℂ)) ^ m‖ ≤ 1 := by
      rw [norm_pow, hz]
      exact pow_le_one₀ hrho.le hrho_le_one
    rw [rationalLocalCircleKernel, norm_div, norm_mul]
    calc
      ‖((∏ i ∈ range R,
          ((l : ℂ) / (q : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ T) /
          (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ T))‖ *
          ‖(z - (r : ℂ)) ^ m‖ /
          ‖z - (l : ℂ) / (q : ℂ)‖ ≤
        (B * 1) / rho := by
          exact div_le_div₀ (by positivity : 0 ≤ B * 1)
            (mul_le_mul hratio hpowSmall (norm_nonneg _) (by positivity))
            hrho htarget
      _ = (2 * (q : ℝ)) * B := by
        dsimp [rho]
        field_simp
  have hIntegral :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      hrho.le hkernel
  have hcancel : rho * ((2 * (q : ℝ)) * B) = B := by
    dsimp [rho]
    field_simp
  simpa only [smul_eq_mul, hcancel, rho, B] using hIntegral

/-- The full sum of local corrections.  The number `R*T` of terms costs
one further power of two, leaving a completely linear contour exponent. -/
theorem norm_sum_normalized_rationalLocalCircleKernel_integral_le
    {R T l q : ℕ} (hq : 0 < q) (hlR : l ≤ q * R)
    (hnmid : ¬ q ∣ l) {delta : ℝ} (hdelta : 0 ≤ delta)
    (c : Fin R → Fin T → ℂ) (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
      (2 : ℝ) ^ (R * T) *
        (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) * delta := by
  let B : ℝ := ((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T
  have hterm : ∀ r : Fin R, ∀ m : Fin T,
      ‖c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
        delta * B := by
    intro r m
    rw [norm_mul]
    apply mul_le_mul (hc r m)
      (norm_normalized_rationalLocalCircleKernel_integral_le
        (T := T) (m := m.1) hq (by omega) (by omega) hlR hnmid)
      (norm_nonneg _) hdelta
  calc
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
      ∑ r : Fin R, ∑ m : Fin T,
        ‖c r m *
          ((2 * Real.pi * I : ℂ)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
              rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ := by
        exact (norm_sum_le _ _).trans (sum_le_sum fun r _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _r : Fin R, ∑ _m : Fin T, delta * B := by
      gcongr with r _ m _
      exact hterm r m
    _ = (R * T : ℕ) * (delta * B) := by simp; ring
    _ ≤ (2 : ℝ) ^ (R * T) * (delta * B) := by
      gcongr
      exact_mod_cast nat_le_two_pow_for_localCircle (R * T)
    _ = (2 : ℝ) ^ (R * T) * B * delta := by ring
    _ = (2 : ℝ) ^ (R * T) *
        (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) * delta := by rfl

/-- Exponential form of the rational local-circle estimate.  A normalized
jet bound spending `2/3` of the source exponent and a contour loss spending
`1/6` leave the required half-exponent decay.  The contour factor is kept in
the literal form proved above, so no hidden logarithm or factorial estimate
enters this statement. -/
theorem norm_sum_normalized_rationalLocalCircleKernel_integral_le_exp
    {R T l q : ℕ} (hq : 0 < q) (hlR : l ≤ q * R)
    (hnmid : ¬ q ∣ l) {A delta : ℝ} (hA : 0 ≤ A)
    (hdelta : 0 ≤ delta) (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (R * T) *
          (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) ≤
        Real.exp ((1 / 6) * A))
    (c : Fin R → Fin T → ℂ) (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
      Real.exp (-(1 / 2) * A) := by
  calc
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
        (2 : ℝ) ^ (R * T) *
          (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) * delta :=
      norm_sum_normalized_rationalLocalCircleKernel_integral_le
        hq hlR hnmid hdelta c hc
    _ ≤ Real.exp ((1 / 6) * A) * Real.exp (-(2 / 3) * A) := by
      exact mul_le_mul hcontour hsmall hdelta (by positivity)
    _ = Real.exp (-(1 / 2) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The sharper bookkeeping used by source Lemma 5.  The exact rational
local-circle factor spends only `E / 12`; combined with the normalized-jet
estimate `exp (-2E/3)`, the polynomial value retains `7E/12` of decay. -/
theorem norm_sum_normalized_rationalLocalCircleKernel_integral_le_exp_seven_twelfths
    {R T l q : ℕ} (hq : 0 < q) (hlR : l ≤ q * R)
    (hnmid : ¬ q ∣ l) {E delta : ℝ} (hE : 0 ≤ E)
    (hdelta : 0 ≤ delta) (hsmall : delta ≤ Real.exp (-2 * E / 3))
    (hcontour :
      (2 : ℝ) ^ (R * T) *
          (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) ≤
        Real.exp (E / 12))
    (c : Fin R → Fin T → ℂ) (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
      Real.exp (-7 * E / 12) := by
  calc
    ‖∑ r : Fin R, ∑ m : Fin T, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (q : ℝ)))),
            rationalLocalCircleKernel R T (r.1 + 1) l q m.1 z)‖ ≤
        (2 : ℝ) ^ (R * T) *
          (((q : ℝ) * (2 : ℝ) ^ (3 * R)) ^ T) * delta :=
      norm_sum_normalized_rationalLocalCircleKernel_integral_le
        hq hlR hnmid hdelta c hc
    _ ≤ Real.exp (E / 12) * Real.exp (-2 * E / 3) := by
      exact mul_le_mul hcontour hsmall hdelta (by positivity)
    _ = Real.exp (-7 * E / 12) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Direct outer-contour estimate for a rational target.  Every repeated
nodal factor contributes `1/2`; the outer radius divided by the
target-to-circle gap contributes only `3/2`. -/
theorem norm_normalized_rationalOuterKernel_integral_le
    {R T q l : ℕ} (hq : 0 < q) (hR : 0 < R) (hlR : l ≤ q * R)
    (f : ℂ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hfunction : ∀ z ∈ sphere (0 : ℂ) (3 * (R : ℝ)), ‖f z‖ ≤ B) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, (3 * (R : ℝ))),
          BakerLemma4Concrete.localEntireKernel R T
            ((l : ℂ) / (q : ℂ)) f z‖ ≤
      (3 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (R * T) * B) := by
  let rho : ℝ := 3 * (R : ℝ)
  let decay : ℝ := (1 / 2 : ℝ) ^ (R * T)
  let M : ℝ := decay * B / (2 * (R : ℝ))
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have htargetNorm : ‖(l : ℂ) / (q : ℂ)‖ ≤ (R : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast,
      div_le_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)]
    exact_mod_cast (by simpa only [mul_comm] using hlR)
  have hkernel : ∀ z ∈ sphere (0 : ℂ) rho,
      ‖BakerLemma4Concrete.localEntireKernel R T
          ((l : ℂ) / (q : ℂ)) f z‖ ≤ M := by
    intro z hz
    have hzNorm : ‖z‖ = 3 * (R : ℝ) := by
      simpa only [rho, mem_sphere, dist_zero_right] using hz
    have hratio :=
      BakerRationalExtrapolation.norm_integerNodeProduct_div_pow_le_two_inv_pow_mul
        hq hR hlR (show 3 * (R : ℝ) ≤ ‖z‖ by rw [hzNorm]) (T := T)
    have hgap : 2 * (R : ℝ) ≤ ‖z - (l : ℂ) / (q : ℂ)‖ := by
      have hrev : ‖z‖ - ‖(l : ℂ) / (q : ℂ)‖ ≤
          ‖z - (l : ℂ) / (q : ℂ)‖ := norm_sub_norm_le z _
      linarith
    have hgapPos : 0 < ‖z - (l : ℂ) / (q : ℂ)‖ :=
      (mul_pos (by norm_num) hRreal).trans_le hgap
    have hratio' :
        ‖(BakerRationalExtrapolation.integerNodeProduct R
              ((l : ℂ) / (q : ℂ)) /
            BakerRationalExtrapolation.integerNodeProduct R z) ^ T‖ ≤
          decay := by simpa only [decay] using hratio
    have hnodal :
        ‖(BakerLemma4Concrete.localNodalPolynomial R T).eval
              ((l : ℂ) / (q : ℂ)) /
            (BakerLemma4Concrete.localNodalPolynomial R T).eval z‖ ≤
          decay := by
      simpa only [BakerLemma4Concrete.localNodalPolynomial_eval,
        BakerRationalExtrapolation.integerNodeProduct, Finset.prod_pow,
        div_pow] using hratio'
    rw [BakerLemma4Concrete.localEntireKernel, norm_div, norm_mul]
    calc
      ‖(BakerLemma4Concrete.localNodalPolynomial R T).eval
              ((l : ℂ) / (q : ℂ)) /
            (BakerLemma4Concrete.localNodalPolynomial R T).eval z‖ *
          ‖f z‖ / ‖z - (l : ℂ) / (q : ℂ)‖ ≤
          (decay * B) / (2 * (R : ℝ)) := by
        exact div_le_div₀ (mul_nonneg (pow_nonneg (by norm_num) _) hB)
          (mul_le_mul hnodal (hfunction z (by simpa only [rho] using hz))
            (norm_nonneg _) (pow_nonneg (by norm_num) _))
          (mul_pos (by norm_num) hRreal) hgap
      _ = M := rfl
  have hint :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      hrho.le hkernel
  have hcalc : rho * M = (3 / 2 : ℝ) * (decay * B) := by
    dsimp only [rho, M]
    field_simp
  simpa only [smul_eq_mul, rho, M, decay, hcalc] using hint

/-- Hermite's exact contour remainder for an arbitrary complex target,
rewritten in the source outer-kernel notation.  The local-residue module
states this first for natural targets; the proof itself only uses that the
target lies inside the contour, which is the form required at `l/q`. -/
theorem normalized_outerCircleIntegral_entireKernel_sub_polynomial_complex
    {R T : ℕ} (hT : 1 ≤ T) (x : ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) {c : ℂ} {rho : ℝ}
    (hxball : x ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho),
          BakerLemma4Concrete.localEntireKernel R T x f z -
            BakerLemma4Concrete.localPolynomialKernel R T x
              (polynomial f (integralNodes R T)) z) =
      f x - (polynomial f (integralNodes R T)).eval x := by
  let Q : ℂ[X] := polynomial f (integralNodes R T)
  have hrho : 0 < rho := dist_nonneg.trans_lt hxball
  have hnodesList : ∀ a ∈ integralNodes R T, a ∈ Metric.ball c rho := by
    intro a ha
    rcases mem_integralNodes_iff_data.mp ha with ⟨i, hi, _hT, rfl⟩
    exact hnodes ⟨i, hi⟩
  have hrem := HermiteInterpolation.remainder_eq_nodeProduct_mul_circleIntegral
    hf (integralNodes R T) hrho hxball hnodesList
  have hFcircle : ∀ z ∈ Metric.sphere c rho,
      (BakerLemma4Concrete.localNodalPolynomial R T).eval z ≠ 0 := by
    intro z hz
    rw [BakerLemma4Concrete.localNodalPolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply pow_ne_zero
    rw [sub_ne_zero]
    exact Metric.sphere_disjoint_ball.ne_of_mem hz
      (hnodes ⟨i, Finset.mem_range.mp hi⟩)
  have htargetCircle : ∀ z ∈ Metric.sphere c rho, z - x ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hz hxball)
  have hpoint : ∀ z ∈ Metric.sphere c rho,
      BakerLemma4Concrete.localEntireKernel R T x f z -
          BakerLemma4Concrete.localPolynomialKernel R T x Q z =
        (BakerLemma4Concrete.localNodalPolynomial R T).eval x *
          ((z - x)⁻¹ *
            (((BakerLemma4Concrete.localNodalPolynomial R T).eval z)⁻¹ *
              (f z - Q.eval z))) := by
    intro z hz
    unfold BakerLemma4Concrete.localEntireKernel
      BakerLemma4Concrete.localPolynomialKernel
    field_simp [hFcircle z hz, htargetCircle z hz]
  have hintegral :
      (∮ z in C(c, rho),
        BakerLemma4Concrete.localEntireKernel R T x f z -
          BakerLemma4Concrete.localPolynomialKernel R T x Q z) =
        (BakerLemma4Concrete.localNodalPolynomial R T).eval x *
          (∮ z in C(c, rho),
            (z - x)⁻¹ *
              (((BakerLemma4Concrete.localNodalPolynomial R T).eval z)⁻¹ *
                (f z - Q.eval z))) := by
    rw [circleIntegral.integral_congr hrho.le hpoint]
    exact circleIntegral.integral_const_mul
      ((BakerLemma4Concrete.localNodalPolynomial R T).eval x)
      (fun z : ℂ => (z - x)⁻¹ *
        (((BakerLemma4Concrete.localNodalPolynomial R T).eval z)⁻¹ *
          (f z - Q.eval z))) c rho
  rw [hintegral]
  simp_rw [← BakerLemma4Concrete.localNodalPolynomial_eval_eq_nodeProduct R T]
    at hrem
  calc
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        ((BakerLemma4Concrete.localNodalPolynomial R T).eval x *
          (∮ z in C(c, rho),
            (z - x)⁻¹ *
              (((BakerLemma4Concrete.localNodalPolynomial R T).eval z)⁻¹ *
                (f z - Q.eval z)))) =
      (BakerLemma4Concrete.localNodalPolynomial R T).eval x *
        ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            (z - x)⁻¹ *
              (((BakerLemma4Concrete.localNodalPolynomial R T).eval z)⁻¹ *
                (f z - Q.eval z)))) := by ring
    _ = f x - (polynomial f (integralNodes R T)).eval x := by
      simpa only [Q] using hrem.symm

/-- Exact arbitrary-target source contour identity.  The Hermite polynomial
has zero outer integral, so the target value is its polynomial value plus
the outer integral of the original entire function. -/
theorem entire_eval_eq_hermitePolynomial_add_outer_complex
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (x : ℂ)
    {c : ℂ} {rho : ℝ} (hxball : x ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    f x = (polynomial f (integralNodes R T)).eval x +
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho),
          BakerLemma4Concrete.localEntireKernel R T x f z) := by
  let Q : ℂ[X] := polynomial f (integralNodes R T)
  have hQdeg : Q ∈ Polynomial.degreeLT ℂ (R * T) :=
    polynomial_integralNodes_mem_degreeLT f R T
  have hpoly :=
    BakerLemma4Concrete.normalized_outerCircleIntegral_localPolynomialKernel_complex_eq_zero
      hR hT x Q hQdeg hxball hnodes
  have hsub :=
    normalized_outerCircleIntegral_entireKernel_sub_polynomial_complex
      hT x f hf hxball hnodes
  have hfint : CircleIntegrable
      (BakerLemma4Concrete.localEntireKernel R T x f) c rho :=
    BakerLemma4Concrete.circleIntegrable_localEntireKernel_of_nodes_mem_ball
      hxball hnodes hf.continuous.continuousOn
  have hQint : CircleIntegrable
      (BakerLemma4Concrete.localPolynomialKernel R T x Q) c rho := by
    simpa only [BakerLemma4Concrete.localEntireKernel_polynomial] using
      BakerLemma4Concrete.circleIntegrable_localEntireKernel_of_nodes_mem_ball
        hxball hnodes Q.differentiable.continuous.continuousOn
  rw [circleIntegral.integral_sub hfint hQint, mul_sub, hpoly, sub_zero] at hsub
  rw [hsub]
  ring

/-- At every repeated integral node, the Hasse jet of the Hermite
interpolant is the normalized analytic jet of the original entire
function. -/
theorem hasseDeriv_hermitePolynomial_eval_integralNode
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R T : ℕ}
    (r : Fin R) (m : Fin T) :
    (hasseDeriv m.1 (polynomial f (integralNodes R T))).eval
        ((r.1 + 1 : ℕ) : ℂ) =
      iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ) := by
  rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
  obtain ⟨after, hsplit⟩ := integralNodes_eq_append_replicate_append (S := T) r
  rw [hsplit]
  rw [HermiteInterpolation.iteratedDeriv_eval_polynomial_eq_of_replicate_block
    hf (integralNodes r.1 T) after ((r.1 + 1 : ℕ) : ℂ) T m.1 m.2]

/-- Factorial-cancelled rational evaluation of the Hermite interpolant.
This is the finite-dimensional part of source Lemma 5, with a loss whose
logarithm is linear in `R*T`. -/
theorem norm_hermitePolynomial_eval_ratCast_le_of_normalized_jets
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R T q l : ℕ} (hR : 0 < R) (hT : 0 < T)
    (hq : 0 < q) (hnmid : ¬ q ∣ l) (hlR : l ≤ q * R)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hjet : ∀ r : Fin R, ∀ m : Fin T,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta) :
    ‖(polynomial f (integralNodes R T)).eval
        ((l : ℂ) / (q : ℂ))‖ ≤
      (q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) * delta := by
  let P : ℂ[X] := polynomial f (integralNodes R T)
  have hPdeg : P.natDegree < R * T := by
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]
      exact Nat.mul_pos hR hT
    · have hd := Polynomial.mem_degreeLT.mp
        (polynomial_integralNodes_mem_degreeLT f R T)
      rw [Polynomial.degree_eq_natDegree hP0] at hd
      exact_mod_cast hd
  apply ExplicitHermiteBasis.norm_eval_ratCast_le_of_hasse
    hq hnmid hlR hPdeg hdelta
  intro r m
  rw [show P = polynomial f (integralNodes R T) by rfl,
    hasseDeriv_hermitePolynomial_eval_integralNode hf r m]
  exact hjet r m



/-- The source auxiliary function is entire in its interpolation variable.
Although its coefficients contain powered-Delta factors evaluated at the
same variable, these are polynomial functions, so the statement follows
termwise. -/
theorem differentiable_vdplF
    {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    Differentiable ℂ
      (fun z ↦ vdplF coord support p h b bLast logAlpha q N z m) := by
  classical
  simp only [vdplF, ExponentialPolynomial.ordinaryDerivative, pow_zero, mul_one,
    sourceCoefficient, auxiliaryFactor, scaledArgument, poweredDeltaHasseEval,
    Polynomial.eval₂_eq_eval_map]
  fun_prop

/-- Lower bound for the repeated nodal product on the circle `|z|=3R`. -/
def outerNodalLower (R T : ℕ) : ℝ :=
  (2 * (R : ℝ)) ^ (R * T)

/-- The explicit outer-contour contribution to the rational interpolation
estimate. -/
def outerRemainderBudget (R T : ℕ) (outerFunction outerPolynomial : ℝ) : ℝ :=
  (R.factorial : ℝ) ^ T *
    ((3 * (R : ℝ)) *
      (((outerFunction + outerPolynomial) / outerNodalLower R T) /
        (2 * (R : ℝ))))

theorem outerNodalLower_pos {R T : ℕ} (hR : 0 < R) :
    0 < outerNodalLower R T := by
  unfold outerNodalLower
  positivity

/-- Every repeated integral interpolation node lies strictly inside the
circle of radius `3R`. -/
theorem integralNodes_mem_outerBall {R T : ℕ} (hR : 0 < R) :
    ∀ a ∈ integralNodes R T, a ∈ ball (0 : ℂ) (3 * (R : ℝ)) := by
  intro a ha
  simp only [integralNodes, List.mem_flatMap, List.mem_range,
    List.mem_replicate] at ha
  obtain ⟨i, hiR, hT, rfl⟩ := ha
  simp only [mem_ball, dist_zero_right, norm_natCast]
  have hi : i + 1 ≤ R := by omega
  have hRr : ((i + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hi
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  linarith

/-- A rational target in `[0,R]` is strictly inside the circle of radius
`3R`, and in fact is at distance at most `R` from its centre. -/
theorem rationalPoint_mem_outerBall {q l R : ℕ} (hq : 0 < q)
    (hR : 0 < R) (hlR : l ≤ q * R) :
    (l : ℂ) / (q : ℂ) ∈ ball (0 : ℂ) (3 * (R : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htarget : (l : ℝ) / (q : ℝ) ≤ R := by
    rw [div_le_iff₀ hqR]
    exact_mod_cast (by simpa [mul_comm] using hlR)
  have hnonneg : (0 : ℝ) ≤ (l : ℝ) / (q : ℝ) := by positivity
  have hcast :
      (l : ℂ) / (q : ℂ) = (((l : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [mem_ball, dist_zero_right, hcast, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg]
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  linarith

/-- A rational target with numerator at most `q*R` has norm at most `R`. -/
theorem norm_rationalPoint_le {q l R : ℕ} (hq : 0 < q)
    (hlR : l ≤ q * R) :
    ‖(l : ℂ) / (q : ℂ)‖ ≤ (R : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htarget : (l : ℝ) / (q : ℝ) ≤ R := by
    rw [div_le_iff₀ hqR]
    exact_mod_cast (by simpa [mul_comm] using hlR)
  have hnonneg : (0 : ℝ) ≤ (l : ℝ) / (q : ℝ) := by positivity
  have hcast :
      (l : ℂ) / (q : ℂ) = (((l : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact htarget

/-- The target-to-contour radial gap is at least `2R`. -/
theorem two_mul_R_le_outerRadius_sub_dist {q l R : ℕ} (hq : 0 < q)
    (hlR : l ≤ q * R) :
    2 * (R : ℝ) ≤
      3 * (R : ℝ) - dist ((l : ℂ) / (q : ℂ)) (0 : ℂ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htarget : (l : ℝ) / (q : ℝ) ≤ R := by
    rw [div_le_iff₀ hqR]
    exact_mod_cast (by simpa [mul_comm] using hlR)
  have hnonneg : (0 : ℝ) ≤ (l : ℝ) / (q : ℝ) := by positivity
  have hcast :
      (l : ℂ) / (q : ℂ) = (((l : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [dist_zero_right, hcast, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg]
  linarith

/-- On the outer circle, the repeated nodal product has its source lower
bound `(2R)^(R*T)`. -/
theorem outerNodalLower_le_nodeProductNorm {R T : ℕ} (hR : 0 < R) :
    ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
      outerNodalLower R T ≤ nodeProductNorm (integralNodes R T) w := by
  intro w hw
  rw [← norm_nodeProduct, hermite_nodeProduct_integralNodes]
  unfold outerNodalLower integralNodalProduct
  have hnorm : ‖w‖ = 3 * (R : ℝ) := by
    simpa [mem_sphere, dist_zero_right] using hw
  have hprod := pow_card_le_norm_prod_pow (𝕜 := ℂ)
    (s := range R) (f := fun i ↦ w - ((i + 1 : ℕ) : ℂ))
    (B := 2 * (R : ℝ)) T (by positivity) (fun i hi ↦ by
      exact two_mul_le_norm_sub_natCast_of_norm_eq_three_mul
        (show i + 1 ≤ R by exact Nat.succ_le_iff.mpr (mem_range.mp hi)) hnorm)
  simpa only [card_range] using hprod

/-- At a rational target in `[0,R]`, the repeated nodal product is at most
`(R!)^T`. -/
theorem nodeProductNorm_rational_le_factorial_pow
    {q l R T : ℕ} (hq : 0 < q) (hlR : l ≤ q * R) :
    nodeProductNorm (integralNodes R T) ((l : ℂ) / (q : ℂ)) ≤
      (R.factorial : ℝ) ^ T := by
  rw [← norm_nodeProduct, hermite_nodeProduct_integralNodes]
  have hcast :
      (l : ℂ) / (q : ℂ) = ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) := by
    norm_num
  rw [hcast]
  exact norm_integralNodalProduct_ratCast_le_factorial_pow hq hlR

/-- Quantitative rational interpolation on the outer circle.

`hpolyTarget` and `hpolyOuter` are the outputs of the small-jet Hermite
polynomial estimate.  Everything after those finite-dimensional estimates
is proved here, including all nodal-product and Cauchy-denominator losses. -/
theorem norm_at_rational_lt_of_hermite_bounds
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q l R T : ℕ} (hq : 0 < q) (hR : 0 < R) (hlR : l ≤ q * R)
    {outerFunction outerPolynomial polynomialTarget lower : ℝ}
    (houterFunction : 0 ≤ outerFunction)
    (houterPolynomial : 0 ≤ outerPolynomial)
    (hfunction : ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
      ‖f w‖ ≤ outerFunction)
    (hpolyOuter : ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
      ‖(polynomial f (integralNodes R T)).eval w‖ ≤ outerPolynomial)
    (hpolyTarget :
      ‖(polynomial f (integralNodes R T)).eval
        ((l : ℂ) / (q : ℂ))‖ ≤ polynomialTarget)
    (hbudget : polynomialTarget +
      outerRemainderBudget R T outerFunction outerPolynomial < lower) :
    ‖f ((l : ℂ) / (q : ℂ))‖ < lower := by
  let nodes := integralNodes R T
  let target : ℂ := (l : ℂ) / (q : ℂ)
  let radius : ℝ := 3 * (R : ℝ)
  let D : ℝ := outerNodalLower R T
  let B : ℝ := (outerFunction + outerPolynomial) / D
  have hD : 0 < D := outerNodalLower_pos hR
  have hB : 0 ≤ B := div_nonneg (add_nonneg houterFunction houterPolynomial) hD.le
  have htarget : target ∈ ball (0 : ℂ) radius :=
    rationalPoint_mem_outerBall hq hR hlR
  have hnodes : ∀ a ∈ nodes, a ∈ ball (0 : ℂ) radius :=
    integralNodes_mem_outerBall hR
  have hboundary : ∀ w ∈ sphere (0 : ℂ) radius,
      ‖f w - (polynomial f nodes).eval w‖ / nodeProductNorm nodes w ≤ B := by
    exact BakerIntegralExtrapolation.boundary_div_nodeProductNorm_le
      hD hfunction hpolyOuter (outerNodalLower_le_nodeProductNorm hR)
  have hrem := norm_remainder_le_of_boundary_div_nodeProductNorm
    hf nodes (by dsimp [radius]; positivity) htarget hB hnodes hboundary
  have htargetProduct : nodeProductNorm nodes target ≤
      (R.factorial : ℝ) ^ T :=
    nodeProductNorm_rational_le_factorial_pow hq hlR
  have hgap : 2 * (R : ℝ) ≤ radius - dist target (0 : ℂ) :=
    two_mul_R_le_outerRadius_sub_dist hq hlR
  have hgapPos : 0 < radius - dist target (0 : ℂ) := by
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    exact (mul_pos (by norm_num) hRreal).trans_le hgap
  have htwoRPos : 0 < 2 * (R : ℝ) := by positivity
  have hquotient :
      radius * (B / (radius - dist target (0 : ℂ))) ≤
        radius * (B / (2 * (R : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_left hB htwoRPos hgap
  have hremBudget :
      nodeProductNorm nodes target *
          (radius * (B / (radius - dist target (0 : ℂ)))) ≤
        outerRemainderBudget R T outerFunction outerPolynomial := by
    calc
      nodeProductNorm nodes target *
          (radius * (B / (radius - dist target (0 : ℂ)))) ≤
          (R.factorial : ℝ) ^ T *
            (radius * (B / (radius - dist target (0 : ℂ)))) := by
              exact mul_le_mul_of_nonneg_right htargetProduct (by positivity)
      _ ≤ (R.factorial : ℝ) ^ T *
            (radius * (B / (2 * (R : ℝ)))) := by
              exact mul_le_mul_of_nonneg_left hquotient (by positivity)
      _ = outerRemainderBudget R T outerFunction outerPolynomial := by
        rfl
  have hwhole :
      ‖f target‖ ≤
        ‖(polynomial f nodes).eval target‖ + ‖f target - (polynomial f nodes).eval target‖ := by
    calc
      ‖f target‖ = ‖(polynomial f nodes).eval target +
          (f target - (polynomial f nodes).eval target)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  calc
    ‖f ((l : ℂ) / (q : ℂ))‖ = ‖f target‖ := rfl
    _ ≤ ‖(polynomial f nodes).eval target‖ +
        ‖f target - (polynomial f nodes).eval target‖ := hwhole
    _ ≤ polynomialTarget + outerRemainderBudget R T
        outerFunction outerPolynomial :=
      add_le_add hpolyTarget (hrem.trans hremBudget)
    _ < lower := hbudget

/-- Concrete Lemma 5 assembly for an arbitrary entire auxiliary family.

Unlike `BakerRationalExtrapolation.vdpl_lemma5`, this theorem does not take
the decisive strict upper estimate as a hypothesis.  It proves that estimate
from the outer growth, the two Hermite-polynomial bounds, and the displayed
factorial/product budget.  The divisibility split is then performed by the
checked rational-grid lemma, and `Snext ≤ S` retains the next derivative
budget. -/
theorem rational_extrapolation_next_budget_of_hermite_bounds
    {n q R S Snext T : ℕ} {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hR : 0 < R) (hnext : Snext ≤ S)
    (lower outerFunction outerPolynomial polynomialTarget :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 R S)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hpolyOuter : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
          ‖(polynomial (fun z ↦ F z m) (integralNodes R T)).eval w‖ ≤
            outerPolynomial l m)
    (hpolyTarget : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ‖(polynomial (fun z ↦ F z m) (integralNodes R T)).eval
          ((l : ℂ) / (q : ℂ))‖ ≤ polynomialTarget l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        polynomialTarget l m +
          outerRemainderBudget R T (outerFunction l m) (outerPolynomial l m) <
            lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q R Snext := by
  have hall : VanishesOn G q R S := by
    apply BakerRationalExtrapolation.vdpl_lemma5_of_interpolation_lt_lower
      hq lower hint
    · intro l hl hlR hnmid m hm
      exact norm_at_rational_lt_of_hermite_bounds (hFdiff m) hq hR
        (show l ≤ q * R by
          exact hlR.trans (Nat.le_mul_of_pos_left R hq))
        (houterFunction l m) (houterPolynomial l m)
        (hfunction l hl hlR hnmid m hm)
        (hpolyOuter l hl hlR hnmid m hm)
        (hpolyTarget l hl hlR hnmid m hm)
        (hbudget l hl hlR hnmid m hm)
    · exact hlower
  exact hall.mono le_rfl hnext

/-- Lemma 5 with the Hermite-polynomial estimates derived from small jets.

The target polynomial bound is the literal evaluation norm of the inverse
confluent jet map.  On the outer circle the caller proves only the displayed
real comparison with `outerPolynomial`; the polynomial estimate itself is a
theorem, not an assumption. -/
theorem rational_extrapolation_next_budget_of_small_jets
    {n q R S Snext T : ℕ} {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hR : 0 < R) (hnext : Snext ≤ S)
    (lower outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 R S)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ i : Fin R, ∀ k : Fin T,
          ‖iteratedDeriv k.1 (fun z ↦ F z m)
            ((i.1 + 1 : ℕ) : ℂ)‖ ≤ jetBound l m)
    (houterJetConstant : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (R : ℝ)),
          hermiteJetConstant R T w * jetBound l m ≤ outerPolynomial l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ R → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        hermiteJetConstant R T ((l : ℂ) / (q : ℂ)) * jetBound l m +
          outerRemainderBudget R T (outerFunction l m) (outerPolynomial l m) <
            lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ R →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q R Snext := by
  let polynomialTarget : ℕ → VDPLMultiIndex n → ℝ := fun l m ↦
    hermiteJetConstant R T ((l : ℂ) / (q : ℂ)) * jetBound l m
  apply rational_extrapolation_next_budget_of_hermite_bounds hq hR hnext
    lower outerFunction outerPolynomial polynomialTarget hint hFdiff
    houterFunction houterPolynomial hfunction
  · intro l hl hlR hnmid m hm w hw
    exact (norm_polynomial_integralNodes_eval_le_of_small_jets
      (hFdiff m) (hjetBound l m) (hsmallJets l hl hlR hnmid m hm)).trans
        (houterJetConstant l hl hlR hnmid m hm w hw)
  · intro l hl hlR hnmid m hm
    exact norm_polynomial_integralNodes_eval_le_of_small_jets
      (hFdiff m) (hjetBound l m) (hsmallJets l hl hlR hnmid m hm)
  · exact hbudget
  · exact hlower

/-- Source-faithful two-radius form of rational extrapolation.

`nodeR` is the number of integral interpolation nodes, whereas `targetR` is
the largest numerator on the rational grid.  The source has
`targetR ≤ q * nodeR`; these radii are not definitionally equal.  Keeping
them separate prevents the common (and quantitatively serious) error of
interpolating at too few integral nodes. -/
theorem rational_extrapolation_twoRadii_next_budget_of_small_jets
    {n q nodeR targetR S Snext T : ℕ}
    {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hnodeR : 0 < nodeR) (htarget : targetR ≤ q * nodeR)
    (hnext : Snext ≤ S)
    (lower outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 nodeR S)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ i : Fin nodeR, ∀ k : Fin T,
          ‖iteratedDeriv k.1 (fun z ↦ F z m)
            ((i.1 + 1 : ℕ) : ℂ)‖ ≤ jetBound l m)
    (houterJetConstant : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          hermiteJetConstant nodeR T w * jetBound l m ≤ outerPolynomial l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        hermiteJetConstant nodeR T ((l : ℂ) / (q : ℂ)) * jetBound l m +
          outerRemainderBudget nodeR T (outerFunction l m) (outerPolynomial l m) <
            lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ targetR →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q targetR Snext := by
  have hall : VanishesOn G q targetR S := by
    intro l hl hlTarget m hm
    by_cases hdiv : q ∣ l
    · have hqle : q ≤ l := Nat.le_of_dvd (Nat.zero_lt_of_lt hl) hdiv
      have hquotPos : 0 < l / q := Nat.div_pos hqle hq
      have hlqNode : l / q ≤ nodeR := by
        apply Nat.div_le_of_le_mul
        exact hlTarget.trans htarget
      have hz := hint (l / q) hquotPos hlqNode m hm
      simp only [Nat.cast_one, div_one] at hz
      rwa [Nat.cast_div hdiv (by exact_mod_cast hq.ne')] at hz
    · rcases hlower l hl hlTarget m hm with hzero | hlow
      · exact hzero
      · exfalso
        apply (not_lt_of_ge hlow)
        exact norm_at_rational_lt_of_hermite_bounds (hFdiff m) hq hnodeR
          (hlTarget.trans htarget)
          (houterFunction l m) (houterPolynomial l m)
          (hfunction l hl hlTarget hdiv m hm)
          (fun w hw ↦
            (norm_polynomial_integralNodes_eval_le_of_small_jets
                (z := w) (hFdiff m) (hjetBound l m)
                (hsmallJets l hl hlTarget hdiv m hm)).trans
              (houterJetConstant l hl hlTarget hdiv m hm w hw))
          (norm_polynomial_integralNodes_eval_le_of_small_jets
            (hFdiff m) (hjetBound l m)
            (hsmallJets l hl hlTarget hdiv m hm))
          (hbudget l hl hlTarget hdiv m hm)
  exact hall.mono le_rfl hnext

/-- Source-faithful two-radius extrapolation from normalized (Hasse) jets.

This is the version used by the source estimate (10): its input is
`f^(k)(r) / k!`, rather than the unnormalised ordinary derivative.  The
Hermite polynomial bounds on both the outer circle and the rational target
are derived by the normalized finite-dimensional estimate from concrete
Lemma 4. -/
theorem rational_extrapolation_twoRadii_next_budget_of_normalized_jets
    {n q nodeR targetR S Snext T : ℕ}
    {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hnodeR : 0 < nodeR) (htarget : targetR ≤ q * nodeR)
    (hnext : Snext ≤ S)
    (lower outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 nodeR S)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ i : Fin nodeR, ∀ k : Fin T,
          ‖iteratedDeriv k.1 (fun z ↦ F z m)
              ((i.1 + 1 : ℕ) : ℂ) /
              (k.1.factorial : ℂ)‖ ≤ jetBound l m)
    (houterJetConstant : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          hasseHermiteJetConstant nodeR T w * jetBound l m ≤
            outerPolynomial l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        hasseHermiteJetConstant nodeR T
              ((l : ℂ) / (q : ℂ)) * jetBound l m +
            outerRemainderBudget nodeR T
              (outerFunction l m) (outerPolynomial l m) <
          lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ targetR →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q targetR Snext := by
  have hall : VanishesOn G q targetR S := by
    intro l hl hlTarget m hm
    by_cases hdiv : q ∣ l
    · have hqle : q ≤ l := Nat.le_of_dvd (Nat.zero_lt_of_lt hl) hdiv
      have hquotPos : 0 < l / q := Nat.div_pos hqle hq
      have hlqNode : l / q ≤ nodeR := by
        apply Nat.div_le_of_le_mul
        exact hlTarget.trans htarget
      have hz := hint (l / q) hquotPos hlqNode m hm
      simp only [Nat.cast_one, div_one] at hz
      rwa [Nat.cast_div hdiv (by exact_mod_cast hq.ne')] at hz
    · rcases hlower l hl hlTarget m hm with hzero | hlow
      · exact hzero
      · exfalso
        apply (not_lt_of_ge hlow)
        exact norm_at_rational_lt_of_hermite_bounds (hFdiff m) hq hnodeR
          (hlTarget.trans htarget)
          (houterFunction l m) (houterPolynomial l m)
          (hfunction l hl hlTarget hdiv m hm)
          (fun w hw ↦
            (norm_polynomial_integralNodes_eval_le_of_small_normalized_jets
                (z := w) (hFdiff m) (hjetBound l m)
                (hsmallJets l hl hlTarget hdiv m hm)).trans
              (houterJetConstant l hl hlTarget hdiv m hm w hw))
          (norm_polynomial_integralNodes_eval_le_of_small_normalized_jets
            (hFdiff m) (hjetBound l m)
            (hsmallJets l hl hlTarget hdiv m hm))
          (hbudget l hl hlTarget hdiv m hm)
  exact hall.mono le_rfl hnext

/-- Two-radius rational extrapolation with the Hermite polynomial eliminated
in favour of the closed-form Cramer bound from concrete Lemma 4.

On the outer circle the monomial radius is `3*nodeR`; at the rational target
it is `nodeR`.  Thus every remaining hypothesis is an explicit inequality
between source parameter expressions. -/
theorem rational_extrapolation_twoRadii_next_budget_of_coarse_normalized_jets
    {n q nodeR targetR S Snext T : ℕ}
    {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hnodeR : 0 < nodeR) (htarget : targetR ≤ q * nodeR)
    (hnext : Snext ≤ S)
    (lower outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 nodeR S)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        ∀ i : Fin nodeR, ∀ k : Fin T,
          ‖iteratedDeriv k.1 (fun z ↦ F z m)
              ((i.1 + 1 : ℕ) : ℂ) /
              (k.1.factorial : ℂ)‖ ≤ jetBound l m)
    (houterCoarse : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        coarseHasseEvaluationBound nodeR T (3 * (nodeR : ℝ)) *
            jetBound l m ≤ outerPolynomial l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        coarseHasseEvaluationBound nodeR T (nodeR : ℝ) * jetBound l m +
            outerRemainderBudget nodeR T
              (outerFunction l m) (outerPolynomial l m) <
          lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ targetR →
      ∀ m, VDPLMultiIndex.weight m ≤ S →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q targetR Snext := by
  have houterRho : (1 : ℝ) ≤ 3 * (nodeR : ℝ) := by
    have hnodeReal : (1 : ℝ) ≤ nodeR := by exact_mod_cast hnodeR
    linarith
  have htargetRho : (1 : ℝ) ≤ (nodeR : ℝ) := by exact_mod_cast hnodeR
  have hall : VanishesOn G q targetR S := by
    intro l hl hlTarget m hm
    by_cases hdiv : q ∣ l
    · have hqle : q ≤ l := Nat.le_of_dvd (Nat.zero_lt_of_lt hl) hdiv
      have hquotPos : 0 < l / q := Nat.div_pos hqle hq
      have hlqNode : l / q ≤ nodeR := by
        apply Nat.div_le_of_le_mul
        exact hlTarget.trans htarget
      have hz := hint (l / q) hquotPos hlqNode m hm
      simp only [Nat.cast_one, div_one] at hz
      rwa [Nat.cast_div hdiv (by exact_mod_cast hq.ne')] at hz
    · rcases hlower l hl hlTarget m hm with hzero | hlow
      · exact hzero
      · exfalso
        apply (not_lt_of_ge hlow)
        exact norm_at_rational_lt_of_hermite_bounds (hFdiff m) hq hnodeR
          (hlTarget.trans htarget)
          (houterFunction l m) (houterPolynomial l m)
          (hfunction l hl hlTarget hdiv m hm)
          (fun w hw ↦
            (norm_polynomial_integralNodes_eval_le_coarse_of_small_normalized_jets
                (z := w) (rho := 3 * (nodeR : ℝ)) (hFdiff m)
                houterRho
                (by
                  have hwNorm : ‖w‖ = 3 * (nodeR : ℝ) := by
                    simpa [mem_sphere, dist_zero_right] using hw
                  exact hwNorm.le)
                (hjetBound l m)
                (hsmallJets l hl hlTarget hdiv m hm)).trans
              (houterCoarse l hl hlTarget hdiv m hm))
          ((norm_polynomial_integralNodes_eval_le_coarse_of_small_normalized_jets
              (z := (l : ℂ) / (q : ℂ)) (rho := (nodeR : ℝ))
              (hFdiff m) htargetRho
              (norm_rationalPoint_le hq (hlTarget.trans htarget))
              (hjetBound l m)
              (hsmallJets l hl hlTarget hdiv m hm)))
          (hbudget l hl hlTarget hdiv m hm)
  exact hall.mono le_rfl hnext

/-- Full-budget two-radius rational extrapolation from a stronger integral
seed.  This is the budget layout used literally in source Lemma 5: the
terminal Lemma 4 seed is available through `Sseed`, whereas the rational
conclusion and every analytic estimate use the smaller `Sout`. -/
theorem rational_extrapolation_twoRadii_full_budget_of_coarse_normalized_jets
    {n q nodeR targetR Sseed Sout T : ℕ}
    {F G : ℂ → VDPLMultiIndex n → ℂ}
    (hq : 0 < q) (hnodeR : 0 < nodeR) (htarget : targetR ≤ q * nodeR)
    (hseedBudget : Sout ≤ Sseed)
    (lower outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex n → ℝ)
    (hint : VanishesOn G 1 nodeR Sseed)
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hfunction : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ Sout →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          ‖F w m‖ ≤ outerFunction l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ Sout →
        ∀ i : Fin nodeR, ∀ k : Fin T,
          ‖iteratedDeriv k.1 (fun z ↦ F z m)
              ((i.1 + 1 : ℕ) : ℂ) /
              (k.1.factorial : ℂ)‖ ≤ jetBound l m)
    (houterCoarse : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ Sout →
        coarseHasseEvaluationBound nodeR T (3 * (nodeR : ℝ)) *
            jetBound l m ≤ outerPolynomial l m)
    (hbudget : ∀ l, 1 ≤ l → l ≤ targetR → ¬ q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ Sout →
        coarseHasseEvaluationBound nodeR T (nodeR : ℝ) * jetBound l m +
            outerRemainderBudget nodeR T
              (outerFunction l m) (outerPolynomial l m) <
          lower l m)
    (hlower : ∀ l, 1 ≤ l → l ≤ targetR →
      ∀ m, VDPLMultiIndex.weight m ≤ Sout →
        G ((l : ℂ) / (q : ℂ)) m = 0 ∨
          lower l m ≤ ‖F ((l : ℂ) / (q : ℂ)) m‖) :
    VanishesOn G q targetR Sout := by
  apply rational_extrapolation_twoRadii_next_budget_of_coarse_normalized_jets
    hq hnodeR htarget (S := Sout) (Snext := Sout) le_rfl lower
      outerFunction outerPolynomial jetBound (hint.mono le_rfl hseedBudget)
      hFdiff houterFunction houterPolynomial hjetBound hfunction hsmallJets
      houterCoarse hbudget hlower

/-! ## Corrected source-state specialization -/

/-- The auxiliary integer `S` used inside source Lemma 5, before its
one-third Hermite multiplicity loss. -/
def sourceRationalS {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (N : ℕ) : ℕ :=
  ⌊P.levelScale N / 6⌋₊

/-- The repeated-node multiplicity `floor(S/3)+1` in source Lemma 5. -/
def sourceRationalMultiplicity {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) : ℕ :=
  sourceRationalS P N / 3 + 1

theorem sourceRationalMultiplicity_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    0 < sourceRationalMultiplicity P N := by
  unfold sourceRationalMultiplicity
  omega

theorem sourceRationalS_eq_Slevel_div_six {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    sourceRationalS P N = P.Slevel N / 6 := by
  unfold sourceRationalS VDPLParameters.Slevel
  exact Nat.floor_div_natCast (P.levelScale N) 6

theorem sourceSstep_eq_Slevel_div_nine {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    P.Sstep N = P.Slevel N / 9 := by
  unfold VDPLParameters.Sstep VDPLParameters.Slevel
  exact Nat.floor_div_natCast (P.levelScale N) 9

/-- Exact floor accounting behind source equation (10): a base index in the
`1/9` output rectangle plus every derivative order below `S/3+1` remains in
the terminal Lemma 4 rectangle `S=floor(levelScale/6)`. -/
theorem sourceSstep_add_jet_le_sourceRationalS {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (k : Fin (sourceRationalMultiplicity P N)) :
    P.Sstep N + k.1 ≤ sourceRationalS P N := by
  have hsplit := P.Sstep_add_levelScale_div_six_floor_div_three_le N
  have hk : k.1 ≤ sourceRationalS P N / 3 := by
    have := k.isLt
    unfold sourceRationalMultiplicity at this
    omega
  have hadd : P.Sstep N + k.1 ≤
      P.Sstep N + sourceRationalS P N / 3 := Nat.add_le_add_left hk _
  exact hadd.trans (by simpa only [sourceRationalS] using hsplit)

theorem sourceSstep_le_sourceRationalS {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    P.Sstep N ≤ sourceRationalS P N := by
  unfold VDPLParameters.Sstep sourceRationalS
  apply Nat.floor_mono
  have hscale := P.levelScale_pos N
  nlinarith

/-- The integral node radius produced by the terminal Lemma 4 step.  By
`lemmaFourRadius_terminal` this is exactly
`floor(16*q^N*h*k^(1/2))`, the source's `mu=1` specialization. -/
def sourceRationalNodeRadius {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) : ℕ :=
  P.lemmaFourRadius N (3 * (P.rank + 1))

theorem sourceRationalNodeRadius_eq_floor {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    sourceRationalNodeRadius P N =
      ⌊16 * ((P.q ^ N : ℕ) : ℝ) * P.h * P.k ^ (1 / 2 : ℝ)⌋₊ := by
  exact P.lemmaFourRadius_terminal N

/-- The parameter ledger absorbs the complete rational local-circle loss,
including both floors and the extra `+1` in the multiplicity, into one
twelfth of the normalized Lemma-3 source exponent. -/
theorem source_localCircleFactor_le_exp_sourceExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N) :
    (2 : ℝ) ^
        (sourceRationalNodeRadius P N * sourceRationalMultiplicity P N) *
      ((P.q : ℝ) *
        (2 : ℝ) ^ (3 * sourceRationalNodeRadius P N)) ^
          sourceRationalMultiplicity P N ≤
      Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
  have h := P.lemmaFive_localCircleFactor_le_exp_twelfth hN
  have hexponent :
      sourceExponent P (P.C * Real.log P.OmegaOld) =
        P.C * P.Omega * Real.log P.OmegaOld *
          Real.log (P.Bsrc : ℝ) := by
    unfold sourceExponent VDPLParameters.Omega
    ring
  rw [hexponent]
  simpa only [sourceRationalNodeRadius_eq_floor,
    sourceRationalMultiplicity, sourceRationalS,
    VDPLParameters.lemmaFiveLocalRadius,
    VDPLParameters.lemmaFiveLocalMultiplicity] using h

/-- Monotone form of the source local-circle estimate for the enlarged
fixed-family logarithmic-form constant.  This is the form consumed by the
strong equation-(7)--(8) jet estimate. -/
theorem source_localCircleFactor_le_exp_oversizedExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    {C₀ : ℝ} (hC : P.C ≤ C₀) :
    (2 : ℝ) ^
        (sourceRationalNodeRadius P N * sourceRationalMultiplicity P N) *
      ((P.q : ℝ) *
        (2 : ℝ) ^ (3 * sourceRationalNodeRadius P N)) ^
          sourceRationalMultiplicity P N ≤
      Real.exp
        (sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) := by
  refine (source_localCircleFactor_le_exp_sourceExponent_div_twelve
    P hN).trans ?_
  apply Real.exp_le_exp.mpr
  have hmono := sourceExponent_mono_normalized P hC
  linarith

/-- The terminal integral radius already contains the full next rational
numerator range. -/
theorem targetRadius_le_sourceRationalNodeRadius {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    P.R (N + 1) ≤ sourceRationalNodeRadius P N := by
  rw [sourceRationalNodeRadius_eq_floor]
  apply Nat.le_floor
  have hq := P.q_le_k_rpow_epsilon
  have hhalf : P.epsilon ≤ (1 / 2 : ℝ) := by
    rw [P.epsilon_eq]
    have hrank : (1 : ℝ) ≤ (P.rank : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    have hden : (2 : ℝ) ≤ 6 * (P.rank + 1 : ℝ) := by nlinarith
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
  have hkhalf : P.k ^ P.epsilon ≤ P.k ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hhalf
  have hfac : (0 : ℝ) ≤ 16 * ((P.q ^ N : ℕ) : ℝ) * P.h := by positivity
  calc
    (P.R (N + 1) : ℝ) =
        (16 * ((P.q ^ N : ℕ) : ℝ) * P.h) * P.q := by
      unfold VDPLParameters.R
      rw [pow_succ]
      push_cast
      ring
    _ ≤ (16 * ((P.q ^ N : ℕ) : ℝ) * P.h) * P.k ^ P.epsilon :=
      mul_le_mul_of_nonneg_left hq hfac
    _ ≤ (16 * ((P.q ^ N : ℕ) : ℝ) * P.h) * P.k ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hkhalf hfac

theorem sourceRationalNodeRadius_pos {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    0 < sourceRationalNodeRadius P N :=
  (P.R_pos (N + 1)).trans_le (targetRadius_le_sourceRationalNodeRadius P N)

/-- Fully specialized local-circle summation bound for source Lemma 5.  The
target range, rational separation, exact terminal radius/multiplicity, and
all contour-factor arithmetic are discharged here. -/
theorem norm_source_rationalLocalCircle_sum_le_exp_neg_seven_twelfths
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N l : ℕ} (hN : P.LevelOK N)
    (hl : l ≤ P.R (N + 1)) (hnmid : ¬ P.q ∣ l)
    {C₀ : ℝ} (hC : P.C ≤ C₀)
    (c : Fin (sourceRationalNodeRadius P N) →
      Fin (sourceRationalMultiplicity P N) → ℂ)
    (hc : ∀ r m, ‖c r m‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3)) :
    ‖∑ r : Fin (sourceRationalNodeRadius P N),
        ∑ m : Fin (sourceRationalMultiplicity P N), c r m *
          ((2 * Real.pi * I : ℂ)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / (2 * (P.q : ℝ)))),
              rationalLocalCircleKernel
                (sourceRationalNodeRadius P N)
                (sourceRationalMultiplicity P N) (r.1 + 1) l P.q m.1 z)‖ ≤
      Real.exp
        (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) := by
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  have hq : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hq1 : 1 ≤ P.q := hq
  have hlNode : l ≤ sourceRationalNodeRadius P N :=
    hl.trans (targetRadius_le_sourceRationalNodeRadius P N)
  have hlqNode : l ≤ P.q * sourceRationalNodeRadius P N := by
    exact hlNode.trans (by nlinarith)
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold sourceExponent
    have hC0 : 0 < C₀ := P.C_pos.trans_le hC
    exact (mul_pos
      (mul_pos (mul_pos (mul_pos hC0 P.log_OmegaOld_pos)
        P.OmegaOld_pos) P.log_newHeight_pos) (log_Bsrc_pos P)).le
  apply norm_sum_normalized_rationalLocalCircleKernel_integral_le_exp_seven_twelfths
    hq hlqNode hnmid hE (Real.exp_pos _).le le_rfl
    (source_localCircleFactor_le_exp_oversizedExponent_div_twelve P hN hC)
    c hc

/-- Terminal Lemma-4 vanishing, equation (7), and the exact `/9 + /18 ≤ /6`
budget give all normalized jets used in source Lemma 5.  This theorem keeps
the pointwise Lemma-3 comparison as a single uniform `delta`; the growth of
the differentiated row operation is the explicit, state-independent power
of `sourceJetCoefficientBound`. -/
theorem terminal_normalized_jets_le
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤ delta)
    (m : VDPLMultiIndex P.rank) (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    (i : Fin (sourceRationalNodeRadius P N))
    (j : Fin (sourceRationalMultiplicity P N)) :
    ‖iteratedDeriv j.1 (fun w ↦ BakerSourceState.f state b bLast w m)
        (((i.1 + 1 : ℕ) : ℂ)) / (j.1.factorial : ℂ)‖ ≤
      (sourceJetCoefficientBound P (sourceRationalS P N)) ^ j.1 * delta := by
  have hseed : VanishesOn (BakerSourceState.g state b bLast) 1
      (sourceRationalNodeRadius P N) (sourceRationalS P N) := by
    exact hint.mono le_rfl (by
      exact (P.levelScale_div_six_floor_le_terminalBudget hN))
  have hmj : VDPLMultiIndex.weight m + j.1 ≤ sourceRationalS P N := by
    exact (Nat.add_le_add_right hm j.1).trans
      (sourceSstep_add_jet_le_sourceRationalS P N j)
  have hjet :=
    norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
      state b hbLast hseed (fun _ ↦ delta) (fun _ ↦ hdelta)
      (show 1 ≤ i.1 + 1 by omega) (show i.1 + 1 ≤ sourceRationalNodeRadius P N by omega)
      (fun m' hm' ↦ hpoint i m' hm') m hmj
  exact hjet.trans
    (jetErrorIterate_const_div_factorial_le_pow P N bLast hbLast
      (sourceRationalS P N) j.1 hdelta (toSourceMultiIndex P m)
      (by simpa [weight_toSourceMultiIndex] using hmj))

/-- Source equation (10) with all factorial and derivative-budget losses
absorbed.  A pointwise `exp (-3E/4)` comparison error on the terminal
`/6` simplex gives `exp (-2E/3)` normalized jets throughout the exact
Lemma-5 rectangle. -/
theorem terminal_normalized_jets_le_exp_neg_two_thirds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hjet : jetAbsorptionConstant P ≤ C₀)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank) (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    (i : Fin (sourceRationalNodeRadius P N))
    (j : Fin (sourceRationalMultiplicity P N)) :
    ‖iteratedDeriv j.1 (fun w ↦ BakerSourceState.f state b bLast w m)
        (((i.1 + 1 : ℕ) : ℂ)) / (j.1.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  let delta := Real.exp
    (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4)
  have hdelta : 0 ≤ delta := (Real.exp_pos _).le
  have hseed : VanishesOn (BakerSourceState.g state b bLast) 1
      (sourceRationalNodeRadius P N) (sourceRationalS P N) := by
    exact hint.mono le_rfl (P.levelScale_div_six_floor_le_terminalBudget hN)
  have hmj : VDPLMultiIndex.weight m + j.1 ≤ sourceRationalS P N := by
    exact (Nat.add_le_add_right hm j.1).trans
      (sourceSstep_add_jet_le_sourceRationalS P N j)
  have hbase :=
    norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
      state b hbLast hseed (fun _ ↦ delta) (fun _ ↦ hdelta)
      (show 1 ≤ i.1 + 1 by omega)
      (show i.1 + 1 ≤ sourceRationalNodeRadius P N by omega)
      (fun m' hm' ↦ by simpa only [delta] using hpoint i m' hm') m hmj
  refine hbase.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j.1 (fun _ ↦ delta) (fun _ ↦ hdelta) hjet
  · intro m' hm'
    exact le_rfl
  · simpa only [weight_toSourceMultiIndex] using
      (hmj.trans (by
        rw [sourceRationalS_eq_Slevel_div_six]
        exact Nat.div_le_self _ _))

theorem targetRadius_le_q_mul_sourceRationalNodeRadius {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    P.R (N + 1) ≤ P.q * sourceRationalNodeRadius P N := by
  exact (targetRadius_le_sourceRationalNodeRadius P N).trans
    (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt P.one_lt_q))

/-- `BakerSourceState.fSource` is definitionally the corrected split-scaled
function controlled by concrete Lemma 3. -/
theorem fSource_eq_vdplF {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    fSource state b bLast z m =
      vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q N z m := by
  rfl

/-- The corresponding definitional identification for the algebraic
companion. -/
theorem gSource_eq_vdplG {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    gSource state b bLast z m =
      vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q N z m := by
  rfl

/-- The corrected source-state analytic function is entire. -/
theorem differentiable_fSource {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    Differentiable ℂ (fun z ↦ fSource state b bLast z m) := by
  simpa only [fSource_eq_vdplF] using
    differentiable_vdplF (coordinatesForState state) state.support state.coeff
      P.h b bLast
      (oldLog P) P.q N m

/-- The complete explicit-Hermite evaluation loss at the rational target
uses only one forty-eighth of an oversized source exponent.  The factor
four is deliberately kept explicit: it is exactly the slack supplied by
the uniform source constant. -/
theorem source_explicitHermiteFactor_le_exp_oversizedExponent_div_fortyEight
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀) :
    (P.q : ℝ) ^ sourceRationalMultiplicity P N *
        (2 : ℝ) ^ ((4 * sourceRationalNodeRadius P N + 3) *
          sourceRationalMultiplicity P N) ≤
      Real.exp
        (sourceExponent P (C₀ * Real.log P.OmegaOld) / 48) := by
  have hfactor := P.lemmaFive_explicitHermiteFactor_le_exp_twelfth hN
  have hsource :
      sourceExponent P (P.C * Real.log P.OmegaOld) =
        P.C * P.Omega * Real.log P.OmegaOld *
          Real.log (P.Bsrc : ℝ) := by
    unfold sourceExponent VDPLParameters.Omega
    ring
  have hfactor' :
      (P.q : ℝ) ^ sourceRationalMultiplicity P N *
          (2 : ℝ) ^ ((4 * sourceRationalNodeRadius P N + 3) *
            sourceRationalMultiplicity P N) ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 12) := by
    rw [hsource]
    simpa only [sourceRationalNodeRadius_eq_floor,
      sourceRationalMultiplicity, sourceRationalS,
      VDPLParameters.lemmaFiveLocalRadius,
      VDPLParameters.lemmaFiveLocalMultiplicity] using hfactor
  refine hfactor'.trans (Real.exp_le_exp.mpr ?_)
  have hmono := sourceExponent_mono_normalized P hstruct
  rw [sourceExponent_four_mul] at hmono
  linarith

/-- The actual Hermite polynomial occurring in source Lemma 5 is already
smaller than `exp (-7E/12)` at every nonintegral rational target.  This is
the factorial-cancelled replacement for the unusable global adjugate
estimate: its loss is linear in the number of node/multiplicity pairs and
is therefore absorbed uniformly in the source height parameter. -/
theorem norm_source_hermitePolynomial_eval_ratCast_le_exp_neg_seven_twelfths
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    {l : ℕ} (hl : l ≤ P.R (N + 1)) (hnmid : ¬ P.q ∣ l)
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep N) :
    ‖(polynomial (fun z ↦ BakerSourceState.f state b bLast z m)
        (integralNodes (sourceRationalNodeRadius P N)
          (sourceRationalMultiplicity P N))).eval
        ((l : ℂ) / (P.q : ℂ))‖ ≤
      Real.exp
        (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) := by
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  have hC : P.C ≤ C₀ := by
    have hCpos := P.C_pos
    nlinarith
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold sourceExponent
    exact (mul_pos
      (mul_pos (mul_pos (mul_pos (P.C_pos.trans_le hC)
        P.log_OmegaOld_pos) P.OmegaOld_pos) P.log_newHeight_pos)
      (log_Bsrc_pos P)).le
  have hdiff : Differentiable ℂ
      (fun z ↦ BakerSourceState.f state b bLast z m) := by
    simpa only [BakerSourceState.f] using
      differentiable_fSource state b bLast (toSourceMultiIndex P m)
  have hR : 0 < sourceRationalNodeRadius P N :=
    sourceRationalNodeRadius_pos P N
  have hT : 0 < sourceRationalMultiplicity P N :=
    sourceRationalMultiplicity_pos P N
  have hq : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hlq : l ≤ P.q * sourceRationalNodeRadius P N :=
    hl.trans (targetRadius_le_q_mul_sourceRationalNodeRadius P N)
  have hpoly :=
    norm_hermitePolynomial_eval_ratCast_le_of_normalized_jets
      hdiff hR hT hq hnmid hlq (Real.exp_pos _).le
      (fun i j ↦ terminal_normalized_jets_le_exp_neg_two_thirds
        state b hbLast hN hint hjet hpoint m hm i j)
  have hfactor :=
    source_explicitHermiteFactor_le_exp_oversizedExponent_div_fortyEight
      P hN hstruct
  calc
    ‖(polynomial (fun z ↦ BakerSourceState.f state b bLast z m)
          (integralNodes (sourceRationalNodeRadius P N)
            (sourceRationalMultiplicity P N))).eval
          ((l : ℂ) / (P.q : ℂ))‖
        ≤ (P.q : ℝ) ^ sourceRationalMultiplicity P N *
            (2 : ℝ) ^ ((4 * sourceRationalNodeRadius P N + 3) *
              sourceRationalMultiplicity P N) * Real.exp (-2 * E / 3) := by
          simpa only [E] using hpoly
    _ ≤ Real.exp (E / 48) * Real.exp (-2 * E / 3) := by
          gcongr
    _ = Real.exp (-31 * E / 48) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-7 * E / 12) := by
          apply Real.exp_le_exp.mpr
          linarith

/-- The outer-contour part of source Lemma 5 after the exact `2^(-R*T)`
nodal-product decay.  This theorem deliberately accepts only the genuine
boundary growth statement; every geometric and parameter inequality is
discharged here. -/
theorem norm_source_rationalOuterKernel_integral_lt_exp_neg_twentySeven
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N l : ℕ} (hN : P.LevelOK N)
    (hl : l ≤ P.R (N + 1)) (f : ℂ → ℂ)
    (hboundary : ∀ z ∈ sphere (0 : ℂ)
        (3 * (sourceRationalNodeRadius P N : ℝ)),
      ‖f z‖ ≤ Real.exp
        (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C((0 : ℂ),
          3 * (sourceRationalNodeRadius P N : ℝ)),
          BakerLemma4Concrete.localEntireKernel
            (sourceRationalNodeRadius P N)
            (sourceRationalMultiplicity P N)
            ((l : ℂ) / (P.q : ℂ)) f z‖ <
      Real.exp (-(27 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  have hq : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hR : 0 < sourceRationalNodeRadius P N :=
    sourceRationalNodeRadius_pos P N
  have hlq : l ≤ P.q * sourceRationalNodeRadius P N :=
    hl.trans (targetRadius_le_q_mul_sourceRationalNodeRadius P N)
  have houter := norm_normalized_rationalOuterKernel_integral_le
    (T := sourceRationalMultiplicity P N)
    hq hR hlq f (Real.exp_pos _).le hboundary
  refine houter.trans_lt ?_
  have hdecay := P.lemmaFive_outerFactor_lt_exp_neg_twentySeven
    hN (Real.exp_pos _).le le_rfl
  simpa only [sourceRationalNodeRadius_eq_floor,
    sourceRationalMultiplicity, sourceRationalS,
    VDPLParameters.lemmaFiveLocalRadius,
    VDPLParameters.lemmaFiveLocalMultiplicity] using hdecay

/-- Sharp version of the outer estimate on the rational Liouville scale.
The exponent retains the actual radical-field degree `13^(oldRank+1)`;
the terminal `R*T` count dominates this scale by the source parameter
inequalities. -/
theorem norm_source_rationalOuterKernel_integral_lt_exp_neg_sharpScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N l : ℕ} (hN : P.LevelOK N)
    (hl : l ≤ P.R (N + 1)) (f : ℂ → ℂ)
    (hboundary : ∀ z ∈ sphere (0 : ℂ)
        (3 * (sourceRationalNodeRadius P N : ℝ)),
      ‖f z‖ ≤ Real.exp
        (2 * sourceHeightUnit P +
          24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1))) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C((0 : ℂ),
          3 * (sourceRationalNodeRadius P N : ℝ)),
          BakerLemma4Concrete.localEntireKernel
            (sourceRationalNodeRadius P N)
            (sourceRationalMultiplicity P N)
            ((l : ℂ) / (P.q : ℂ)) f z‖ <
      Real.exp (-((34 * (13 ^ (oldRank + 1) : ℝ) + 6) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  have hq : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hR : 0 < sourceRationalNodeRadius P N :=
    sourceRationalNodeRadius_pos P N
  have hlq : l ≤ P.q * sourceRationalNodeRadius P N :=
    hl.trans (targetRadius_le_q_mul_sourceRationalNodeRadius P N)
  have houter := norm_normalized_rationalOuterKernel_integral_le
    (T := sourceRationalMultiplicity P N)
    hq hR hlq f (Real.exp_pos _).le hboundary
  refine houter.trans_lt ?_
  have hdecay :=
    P.lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_honestAnalyticGrowth
    hN (Real.exp_pos _).le le_rfl
  simpa only [sourceRationalNodeRadius_eq_floor,
    sourceRationalMultiplicity, sourceRationalS,
    VDPLParameters.lemmaFiveLocalRadius,
    VDPLParameters.lemmaFiveLocalMultiplicity, sourceHeightUnit,
    add_comm] using hdecay

/-- Complete analytic upper estimate at a nonintegral rational-grid point.
The Hermite and outer-contour pieces are both source-instantiated; the only
analytic premise not internal to this theorem is the source-state boundary
growth on the literal outer circle. -/
theorem norm_source_f_ratCast_lt_hermite_add_outer_exponents
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    {l : ℕ} (hl : l ≤ P.R (N + 1)) (hnmid : ¬ P.q ∣ l)
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    (hboundary : ∀ z ∈ sphere (0 : ℂ)
        (3 * (sourceRationalNodeRadius P N : ℝ)),
      ‖BakerSourceState.f state b bLast z m‖ ≤ Real.exp
        (2 * sourceHeightUnit P +
          24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1))) :
    ‖BakerSourceState.f state b bLast
        ((l : ℂ) / (P.q : ℂ)) m‖ <
      Real.exp
          (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) +
        Real.exp (-((34 * (13 ^ (oldRank + 1) : ℝ) + 6) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  let R := sourceRationalNodeRadius P N
  let T := sourceRationalMultiplicity P N
  let x : ℂ := (l : ℂ) / (P.q : ℂ)
  let f : ℂ → ℂ := fun z ↦ BakerSourceState.f state b bLast z m
  have hR : 0 < R := sourceRationalNodeRadius_pos P N
  have hT : 0 < T := sourceRationalMultiplicity_pos P N
  have hq : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hlq : l ≤ P.q * R := by
    dsimp only [R]
    exact hl.trans (targetRadius_le_q_mul_sourceRationalNodeRadius P N)
  have hxnorm : ‖x‖ ≤ (R : ℝ) := by
    dsimp only [x]
    rw [norm_div, norm_natCast, norm_natCast]
    apply (div_le_iff₀ (by exact_mod_cast hq)).2
    exact_mod_cast (show l ≤ R * P.q by simpa [mul_comm] using hlq)
  have hxball : x ∈ Metric.ball (0 : ℂ) (3 * (R : ℝ)) := by
    rw [mem_ball, dist_zero_right]
    exact hxnorm.trans_lt (by
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
      linarith)
  have hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball (0 : ℂ) (3 * (R : ℝ)) := by
    intro r
    rw [mem_ball, dist_zero_right, Complex.norm_natCast]
    have hr : (r.1 + 1 : ℝ) ≤ R := by exact_mod_cast Nat.succ_le_iff.mpr r.2
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hlt : (r.1 + 1 : ℝ) < 3 * (R : ℝ) := by linarith
    simpa only [Nat.cast_add, Nat.cast_one] using hlt
  have hdiff : Differentiable ℂ f := by
    dsimp only [f]
    simpa only [BakerSourceState.f] using
      differentiable_fSource state b bLast (toSourceMultiIndex P m)
  have hid := entire_eval_eq_hermitePolynomial_add_outer_complex
    hR hT x hxball hnodes hdiff
  have hpoly :=
    norm_source_hermitePolynomial_eval_ratCast_le_exp_neg_seven_twelfths
      state b hbLast hN hint hstruct hjet hpoint hl hnmid m hm
  have houter :=
    norm_source_rationalOuterKernel_integral_lt_exp_neg_sharpScale
      P hN hl f (by simpa only [R, f] using hboundary)
  rw [show BakerSourceState.f state b bLast
      ((l : ℂ) / (P.q : ℂ)) m = f x by rfl, hid]
  exact (norm_add_le _ _).trans_lt
    (add_lt_add_of_le_of_lt (by simpa only [R, T, x, f] using hpoly)
      (by simpa only [R, T, x, f] using houter))

/-- Predicate-level source Lemma 5.  This exposes the exact two remaining
numerical interfaces while returning the literal full-`Sstep` upper bound
consumed by the induction assembly. -/
theorem rationalInterpolationUpperAtLevel_of_source_hermite_outer
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hboundary : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ z ∈ sphere (0 : ℂ)
          (3 * (sourceRationalNodeRadius P N : ℝ)),
          ‖BakerSourceState.f state b bLast z m‖ ≤ Real.exp
            (2 * sourceHeightUnit P +
              24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)))
    (hthreshold : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        Real.exp
            (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) +
          Real.exp (-((34 * (13 ^ (oldRank + 1) : ℝ) + 6) *
            ((P.h : ℝ) * P.k * P.Omega *
              Real.log P.OmegaOld))) ≤ lower l m) :
    BakerInduction.RationalInterpolationUpperAtLevel P
      (BakerSourceState.f state b bLast) lower N := by
  intro l hl1 hlR hnmid m hm
  exact (norm_source_f_ratCast_lt_hermite_add_outer_exponents
    state b hbLast hN hint hstruct hjet hpoint hlR hnmid m hm
      (hboundary l hl1 hlR hnmid m hm)).trans_le
        (hthreshold l hl1 hlR hnmid m hm)

/-- Exact source Lemma 5 on the full `Sstep` budget.  The local Hermite
term, the outer contour, and the sharp radical-degree Liouville threshold
are compared here, so the conclusion has no residual sum-to-threshold
hypothesis.  The remaining analytic inputs are the source-faithful row
error and growth estimates supplied by the algebraic majorant layer. -/
theorem rationalInterpolationUpperAtLevel_of_source_exactLiouville
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (hint : BakerInduction.IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hfixed :
      2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀)
    (hpoint : ∀ i : Fin (sourceRationalNodeRadius P N),
      ∀ m' : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m' ≤ sourceRationalS P N →
        ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m' -
          gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m'‖ ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hboundary : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ z ∈ sphere (0 : ℂ)
          (3 * (sourceRationalNodeRadius P N : ℝ)),
          ‖BakerSourceState.f state b bLast z m‖ ≤ Real.exp
            (2 * sourceHeightUnit P +
              24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        (BakerSourceAlgebraicLevelMajorant.levelAlgebraicExponentialMajorant
          P state b bLast ((l : ℂ) / (P.q : ℂ))
            (toSourceMultiIndex P m)).growth ≤
          Real.exp (2 *
            Erdos240.BakerSourceRationalLiouvilleLowerBounds.rationalHeightScale P)) :
    BakerInduction.RationalInterpolationUpperAtLevel P
      (BakerSourceState.f state b bLast)
      (fun l m ↦
        Erdos240.BakerLemma3Instantiation.stateRationalLiouvilleThreshold
          P N state b bLast l (toSourceMultiIndex P m)) N := by
  intro l hl1 hlR hnmid m hm
  have hupper := norm_source_f_ratCast_lt_hermite_add_outer_exponents
    state b hbLast hN hint hstruct hjet hpoint hlR hnmid m hm
      (hboundary l hl1 hlR hnmid m hm)
  have hsum := P.exp_neg_seven_twelfths_add_exactStrong_lt_exactWeak hfixed
  have hsum' :
      Real.exp (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) +
          Real.exp (-((34 * (13 ^ (oldRank + 1) : ℝ) + 6) *
            ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
        Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
    convert hsum using 1 <;> ring_nf
  have hmSource :
      VDPLMultiIndex.weight (toSourceMultiIndex P m) ≤ P.Sstep N := by
    simpa only [weight_toSourceMultiIndex] using hm
  have hlower :=
    Erdos240.BakerSourceRationalLiouvilleLowerBounds.exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold
        P hN state b bLast l hlR (toSourceMultiIndex P m) hmSource
          (hgrowth l hl1 hlR hnmid m hm)
  exact hupper.trans (hsum'.trans_le (by
    simpa only
      [Erdos240.BakerSourceRationalLiouvilleLowerBounds.rationalHeightScale]
      using hlower))

/-- Source auxiliary family at the fixed induction level `N`. -/
def sourceF {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fun z m ↦ vdplF coord support p h b bLast logAlpha q N z m

/-- Algebraic companion of `sourceF`. -/
def sourceG {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ) (q N : ℕ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fun z m ↦ vdplG coord support p h b bLast logAlpha logAlphaLast q N z m

/-- The explicit half-Liouville lower bound carried by a concrete Lemma 3
certificate. -/
def certificateLower
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    {coord : SourceCoordinates oldRank I} {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)} {radicalRank : ℕ}
    (A : AlgebraicCertificateInputs (K := K) coord support p h b bLast
      logAlpha logAlphaLast q N z m radicalRank) : ℝ :=
  ((A.conjugateBound ^ (13 ^ radicalRank - 1))⁻¹ / ‖A.scale‖) / 2

/-- **Concrete source Lemma 5 for the corrected coefficient state.**

The interpolation multiplicity is the literal source value
`floor(S/3)+1`, with `S=floor(levelScale/6)`.  The integral interpolation
radius is the terminal Lemma 4 value `floor(16*q^N*h*k^(1/2))`; it is kept
distinct from the rational target radius, and their required comparison is
proved above from the source parameter inequalities.

Both analytic inputs are outputs of concrete Lemma 3.  On the outer circle,
`SourceMajorants.norm_vdplF_le_growth` supplies the function bound.  At the
rational target, `quantitative_lemma3` supplies the algebraic-zero/Liouville
alternative with radical degree `13 ^ ((N+1)*rank)`.  The only remaining
quantitative hypotheses are explicit inequalities between the displayed
real majorants.  Every majorant and algebraic certificate is built from
`coordinatesForState state`.  With the corrected equation (3), those
coordinates contain only the old exponential indices: every old factor is
the ordinary two-argument polynomial `Delta(x;m_r)`, while only the head
factor is a powered Delta derivative.  Thus no canonical or active old-side
power is hidden in this endpoint. -/
theorem sourceState_lemma5_full_budget_of_coarse_normalized_jets
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {K : Type*} [Field K] [NumberField K]
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex (oldRank + 1) → ℝ)
    (hint : VanishesOn (BakerSourceState.g state b bLast)
      1 (sourceRationalNodeRadius P N) (sourceRationalS P N))
    (Mouter : ∀ l (m : VDPLMultiIndex (oldRank + 1)) (w : ℂ),
      SourceMajorants P (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q N w m)
    (houterGrowth : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w ∈ sphere (0 : ℂ) (3 * (sourceRationalNodeRadius P N : ℝ)),
          (Mouter l m w).growth ≤ outerFunction l m)
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ i : Fin (sourceRationalNodeRadius P N),
          ∀ k : Fin (sourceRationalMultiplicity P N),
          ‖iteratedDeriv k.1
              (fun z ↦ fSource state b bLast z m)
              ((i.1 + 1 : ℕ) : ℂ) /
              (k.1.factorial : ℂ)‖ ≤ jetBound l m)
    (houterCoarse : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        coarseHasseEvaluationBound (sourceRationalNodeRadius P N)
              (sourceRationalMultiplicity P N)
              (3 * (sourceRationalNodeRadius P N : ℝ)) *
            jetBound l m ≤ outerPolynomial l m)
    (Mtarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceMajorants P (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q N ((l : ℂ) / (P.q : ℂ)) m)
    (Btarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceNumericalConditions (Mtarget l m))
    (Atarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      AlgebraicCertificateInputs (K := K) (coordinatesForState state)
        state.support state.coeff
        P.h b bLast (oldLog P) (lastLog P) P.q N
        ((l : ℂ) / (P.q : ℂ)) m (oldRank + 1))
    (hbLast : bLast ≠ 0)
    (hsmall : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
          smallLinearFormBound P (Btarget l m).sourceConstant)
    (herrorToLiouville : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        errorEnvelope P (Btarget l m).sourceConstant
            (Btarget l m).errorMultiplier ≤
          certificateLower (K := K) (Atarget l m))
    (hbudget : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        coarseHasseEvaluationBound (sourceRationalNodeRadius P N)
              (sourceRationalMultiplicity P N)
              (sourceRationalNodeRadius P N : ℝ) * jetBound l m +
            outerRemainderBudget (sourceRationalNodeRadius P N)
              (sourceRationalMultiplicity P N)
              (outerFunction l m) (outerPolynomial l m) <
          certificateLower (K := K) (Atarget l m)) :
    VanishesOn (BakerSourceState.g state b bLast)
      P.q (P.R (N + 1)) (P.Sstep N) := by
  let lower : ℕ → VDPLMultiIndex (oldRank + 1) → ℝ := fun l m ↦
    certificateLower (K := K) (Atarget l m)
  have hintSource : VanishesOn (gSource state b bLast)
      1 (sourceRationalNodeRadius P N) (sourceRationalS P N) := by
    intro l hl hlR m hm
    let mRank := fromSourceMultiIndex P m
    have hmRank : VDPLMultiIndex.weight mRank ≤ sourceRationalS P N := by
      dsimp only [mRank]
      rw [weight_fromSourceMultiIndex]
      exact hm
    have hz := hint l hl hlR mRank hmRank
    simpa [BakerSourceState.g, mRank] using hz
  have hsource : VanishesOn (gSource state b bLast)
      P.q (P.R (N + 1)) (P.Sstep N) := by
    apply rational_extrapolation_twoRadii_full_budget_of_coarse_normalized_jets
      (F := fSource state b bLast) (G := gSource state b bLast)
      (Nat.zero_lt_of_lt P.one_lt_q) (sourceRationalNodeRadius_pos P N)
      (targetRadius_le_q_mul_sourceRationalNodeRadius P N)
      (sourceSstep_le_sourceRationalS P N) lower outerFunction outerPolynomial
      jetBound hintSource
    · exact differentiable_fSource state b bLast
    · exact houterFunction
    · exact houterPolynomial
    · exact hjetBound
    · intro l hl hlR hnmid m hm w hw
      rw [fSource_eq_vdplF]
      exact (Mouter l m w).norm_vdplF_le_growth.trans
        (houterGrowth l hl hlR hnmid m hm w hw)
    · exact hsmallJets
    · exact houterCoarse
    · exact hbudget
    · intro l hl hlR m hm
      have hlemma := quantitative_lemma3
        (Mtarget l m) (Btarget l m) (Atarget l m) hbLast
        (hsmall l hl hlR m hm) (herrorToLiouville l hl hlR m hm)
      change gSource state b bLast ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
        certificateLower (K := K) (Atarget l m) ≤
          ‖fSource state b bLast ((l : ℂ) / (P.q : ℂ)) m‖
      simpa only [gSource_eq_vdplG, fSource_eq_vdplF, certificateLower] using
        hlemma.2.2
  intro l hl hlR m hm
  have hz := hsource l hl hlR (toSourceMultiIndex P m)
    (by simpa [weight_toSourceMultiIndex] using hm)
  simpa [BakerSourceState.g] using hz

/-- Concrete source Lemma 5, with both analytic inputs taken from the
quantitative Lemma 3 layer.

For boundary points, `Mouter` consists of the literal coefficient, Delta,
exponential, amplification, and support estimates; `houterGrowth` is the
single real inequality placing their product under `outerFunction`.
At target points, `Mtarget`, `Btarget`, and `Atarget` are precisely the
source majorants, numerical conditions, and sharp-denominator algebraic
certificate consumed by `quantitative_lemma3`.

Thus the nonintegral branch is proved by Hermite interpolation, while the
integral branch is inherited from `hint`.  The conclusion retains exactly
`Slevel (N+1)`, using the checked floor inequality
`Slevel (N+1) ≤ Sstep N`. -/
theorem source_lemma5_nextLevel_of_hermite_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    (P : VDPLParameters ι)
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (N T radicalRank : ℕ)
    (outerFunction outerPolynomial polynomialTarget :
      ℕ → VDPLMultiIndex (oldRank + 1) → ℝ)
    (hint : VanishesOn
      (sourceG coord support p h b bLast logAlpha logAlphaLast P.q N)
      1 (P.R (N + 1)) (P.Sstep N))
    (Mouter : ∀ l (m : VDPLMultiIndex (oldRank + 1)) (w : ℂ),
      SourceMajorants P coord support p h b bLast logAlpha P.q N w m)
    (houterGrowth : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w ∈ sphere (0 : ℂ) (3 * (P.R (N + 1) : ℝ)),
          (Mouter l m w).growth ≤ outerFunction l m)
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hpolyOuter : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w ∈ sphere (0 : ℂ) (3 * (P.R (N + 1) : ℝ)),
          ‖(polynomial
              (fun z ↦ sourceF coord support p h b bLast logAlpha P.q N z m)
              (integralNodes (P.R (N + 1)) T)).eval w‖ ≤ outerPolynomial l m)
    (hpolyTarget : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖(polynomial
              (fun z ↦ sourceF coord support p h b bLast logAlpha P.q N z m)
              (integralNodes (P.R (N + 1)) T)).eval
            ((l : ℂ) / (P.q : ℂ))‖ ≤ polynomialTarget l m)
    (Mtarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceMajorants P coord support p h b bLast logAlpha P.q N
        ((l : ℂ) / (P.q : ℂ)) m)
    (Btarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceNumericalConditions (Mtarget l m))
    (Atarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      AlgebraicCertificateInputs (K := K) coord support p h b bLast logAlpha logAlphaLast
        P.q N ((l : ℂ) / (P.q : ℂ)) m radicalRank)
    (hbLast : bLast ≠ 0)
    (hsmall : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖logForm b bLast logAlpha logAlphaLast‖ ≤
          smallLinearFormBound P (Btarget l m).sourceConstant)
    (herrorToLiouville : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        errorEnvelope P (Btarget l m).sourceConstant
            (Btarget l m).errorMultiplier ≤
          certificateLower (K := K) (Atarget l m))
    (hbudget : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        polynomialTarget l m + outerRemainderBudget (P.R (N + 1)) T
            (outerFunction l m) (outerPolynomial l m) <
          certificateLower (K := K) (Atarget l m)) :
    VanishesOn
      (sourceG coord support p h b bLast logAlpha logAlphaLast P.q N)
      P.q (P.R (N + 1)) (P.Slevel (N + 1)) := by
  let F := sourceF coord support p h b bLast logAlpha P.q N
  let G := sourceG coord support p h b bLast logAlpha logAlphaLast P.q N
  let lower : ℕ → VDPLMultiIndex (oldRank + 1) → ℝ := fun l m ↦
    certificateLower (K := K) (Atarget l m)
  apply rational_extrapolation_next_budget_of_hermite_bounds
    (F := F) (G := G)
    (Nat.zero_lt_of_lt P.one_lt_q) (P.R_pos (N + 1))
    (P.Slevel_succ_le_Sstep N) lower outerFunction outerPolynomial polynomialTarget hint
  · intro m
    exact differentiable_vdplF coord support p h b bLast logAlpha P.q N m
  · exact houterFunction
  · exact houterPolynomial
  · intro l hl hlR hnmid m hm w hw
    exact (Mouter l m w).norm_vdplF_le_growth.trans
      (houterGrowth l hl hlR hnmid m hm w hw)
  · exact hpolyOuter
  · exact hpolyTarget
  · exact hbudget
  · intro l hl hlR m hm
    exact (quantitative_lemma3 (Mtarget l m) (Btarget l m) (Atarget l m)
      hbLast (hsmall l hl hlR m hm) (herrorToLiouville l hl hlR m hm)).2.2

/-- Final consumer-facing form of concrete source Lemma 5.  In contrast to
`source_lemma5_nextLevel_of_hermite_bounds`, no Hermite-polynomial value is
assumed: both its target and boundary estimates are derived from the small
ordinary jets at the integral nodes. -/
theorem source_lemma5_nextLevel_of_small_jets
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    (P : VDPLParameters ι)
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (N T radicalRank nodeR : ℕ)
    (hnodeR : 0 < nodeR)
    (htarget : P.R (N + 1) ≤ P.q * nodeR)
    (outerFunction outerPolynomial jetBound :
      ℕ → VDPLMultiIndex (oldRank + 1) → ℝ)
    (hint : VanishesOn
      (sourceG coord support p h b bLast logAlpha logAlphaLast P.q N)
      1 nodeR (P.Sstep N))
    (Mouter : ∀ l (m : VDPLMultiIndex (oldRank + 1)) (w : ℂ),
      SourceMajorants P coord support p h b bLast logAlpha P.q N w m)
    (houterGrowth : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          (Mouter l m w).growth ≤ outerFunction l m)
    (houterFunction : ∀ l m, 0 ≤ outerFunction l m)
    (houterPolynomial : ∀ l m, 0 ≤ outerPolynomial l m)
    (hjetBound : ∀ l m, 0 ≤ jetBound l m)
    (hsmallJets : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ i : Fin nodeR, ∀ k : Fin T,
          ‖iteratedDeriv k.1
              (fun z ↦ sourceF coord support p h b bLast logAlpha P.q N z m)
              ((i.1 + 1 : ℕ) : ℂ)‖ ≤ jetBound l m)
    (houterJetConstant : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w ∈ sphere (0 : ℂ) (3 * (nodeR : ℝ)),
          hermiteJetConstant nodeR T w * jetBound l m ≤
            outerPolynomial l m)
    (Mtarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceMajorants P coord support p h b bLast logAlpha P.q N
        ((l : ℂ) / (P.q : ℂ)) m)
    (Btarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      SourceNumericalConditions (Mtarget l m))
    (Atarget : ∀ l (m : VDPLMultiIndex (oldRank + 1)),
      AlgebraicCertificateInputs (K := K) coord support p h b bLast logAlpha logAlphaLast
        P.q N ((l : ℂ) / (P.q : ℂ)) m radicalRank)
    (hbLast : bLast ≠ 0)
    (hsmall : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ‖logForm b bLast logAlpha logAlphaLast‖ ≤
          smallLinearFormBound P (Btarget l m).sourceConstant)
    (herrorToLiouville : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        errorEnvelope P (Btarget l m).sourceConstant
            (Btarget l m).errorMultiplier ≤
          certificateLower (K := K) (Atarget l m))
    (hbudget : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) → ¬ P.q ∣ l →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        hermiteJetConstant nodeR T
              ((l : ℂ) / (P.q : ℂ)) * jetBound l m +
            outerRemainderBudget nodeR T
              (outerFunction l m) (outerPolynomial l m) <
          certificateLower (K := K) (Atarget l m)) :
    VanishesOn
      (sourceG coord support p h b bLast logAlpha logAlphaLast P.q N)
      P.q (P.R (N + 1)) (P.Slevel (N + 1)) := by
  let F := sourceF coord support p h b bLast logAlpha P.q N
  let G := sourceG coord support p h b bLast logAlpha logAlphaLast P.q N
  let lower : ℕ → VDPLMultiIndex (oldRank + 1) → ℝ := fun l m ↦
    certificateLower (K := K) (Atarget l m)
  apply rational_extrapolation_twoRadii_next_budget_of_small_jets
    (F := F) (G := G)
    (Nat.zero_lt_of_lt P.one_lt_q) hnodeR htarget
    (P.Slevel_succ_le_Sstep N) lower outerFunction outerPolynomial jetBound hint
  · intro m
    exact differentiable_vdplF coord support p h b bLast logAlpha P.q N m
  · exact houterFunction
  · exact houterPolynomial
  · exact hjetBound
  · intro l hl hlR hnmid m hm w hw
    exact (Mouter l m w).norm_vdplF_le_growth.trans
      (houterGrowth l hl hlR hnmid m hm w hw)
  · exact hsmallJets
  · exact houterJetConstant
  · exact hbudget
  · intro l hl hlR m hm
    exact (quantitative_lemma3 (Mtarget l m) (Btarget l m) (Atarget l m)
      hbLast (hsmall l hl hlR m hm) (herrorToLiouville l hl hlR m hm)).2.2

end Erdos240.BakerLemma5Concrete

#print axioms Erdos240.BakerLemma5Concrete.norm_at_rational_lt_of_hermite_bounds
#print axioms Erdos240.BakerLemma5Concrete.rational_extrapolation_next_budget_of_hermite_bounds
#print axioms Erdos240.BakerLemma5Concrete.rational_extrapolation_next_budget_of_small_jets
#print axioms Erdos240.BakerLemma5Concrete.rational_extrapolation_twoRadii_next_budget_of_normalized_jets
#print axioms Erdos240.BakerLemma5Concrete.rational_extrapolation_twoRadii_next_budget_of_coarse_normalized_jets
#print axioms Erdos240.BakerLemma5Concrete.norm_source_rationalLocalCircle_sum_le_exp_neg_seven_twelfths
#print axioms Erdos240.BakerLemma5Concrete.norm_normalized_rationalOuterKernel_integral_le
#print axioms Erdos240.BakerLemma5Concrete.entire_eval_eq_hermitePolynomial_add_outer_complex
#print axioms Erdos240.BakerLemma5Concrete.terminal_normalized_jets_le_exp_neg_two_thirds
#print axioms Erdos240.BakerLemma5Concrete.norm_source_hermitePolynomial_eval_ratCast_le_exp_neg_seven_twelfths
#print axioms Erdos240.BakerLemma5Concrete.norm_source_rationalOuterKernel_integral_lt_exp_neg_twentySeven
#print axioms Erdos240.BakerLemma5Concrete.norm_source_rationalOuterKernel_integral_lt_exp_neg_sharpScale
#print axioms Erdos240.BakerLemma5Concrete.norm_source_f_ratCast_lt_hermite_add_outer_exponents
#print axioms Erdos240.BakerLemma5Concrete.rationalInterpolationUpperAtLevel_of_source_hermite_outer
#print axioms Erdos240.BakerLemma5Concrete.rationalInterpolationUpperAtLevel_of_source_exactLiouville
#print axioms Erdos240.BakerLemma5Concrete.sourceState_lemma5_full_budget_of_coarse_normalized_jets
#print axioms Erdos240.BakerLemma5Concrete.source_lemma5_nextLevel_of_hermite_bounds
#print axioms Erdos240.BakerLemma5Concrete.source_lemma5_nextLevel_of_small_jets
