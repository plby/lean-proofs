import ErdosProblems.Erdos520.CaichWoverX
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Scalar summability for the aligned `W/x` auxiliary

The analytic part of the `W/x` estimate leaves a deterministic finite-test
budget.  On the aligned mesh every selected point has

`log log x >= ell^K / (3 * 2^K)`.

Consequently a sufficiently large fixed moment (depending only on `K` and
the root-exponential denominator `m`) beats both the polynomial threshold
and the exact test-point entropy.  This file records that scalar conclusion;
it introduces no arithmetic or probabilistic hypothesis.
-/

private theorem eventually_caichW_polynomial_le_exp
    {K : ℕ} (hK : 1 ≤ K) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ ell : ℕ in atTop,
      C * (ell : ℝ) ^ ((K : ℝ) / 2) ≤
        Real.exp (c * (ell : ℝ) ^ K) := by
  have ht : Tendsto (fun ell : ℕ ↦ (ell : ℝ) ^ K) atTop atTop :=
    (Filter.tendsto_pow_atTop (show K ≠ 0 by omega)).comp
      tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun ell : ℕ ↦
        Real.exp (c * (ell : ℝ) ^ K) / (ell : ℝ) ^ K)
      atTop atTop := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.rpow_natCast] using!
      (tendsto_exp_mul_div_rpow_atTop 1 c hc).comp ht
  filter_upwards [hratio.eventually (eventually_ge_atTop C),
      eventually_ge_atTop (1 : ℕ)] with ell hellRatio hell
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hKhalf : (K : ℝ) / 2 ≤ (K : ℝ) := by
    have : (0 : ℝ) ≤ K := by positivity
    linarith
  have hrpow : (ell : ℝ) ^ ((K : ℝ) / 2) ≤
      (ell : ℝ) ^ (K : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hellR hKhalf
  have hden : 0 < (ell : ℝ) ^ K := by positivity
  have hcross : C * (ell : ℝ) ^ K ≤
      Real.exp (c * (ell : ℝ) ^ K) := by
    rw [le_div_iff₀ hden] at hellRatio
    simpa only [Real.rpow_natCast] using! hellRatio
  exact (mul_le_mul_of_nonneg_left hrpow hC).trans (by
    simpa only [Real.rpow_natCast] using! hcross)

private theorem eventually_caichW_point_term_le_exp
    {K m r : ℕ} (hK : 1 ≤ K) (hgap :
      12 * (2 ^ K) * (2 * m + 2) ≤ r)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      caichAlignedWMoment r m C ell i /
          caichAlignedWSafeThreshold K ell ^ r ≤
        Real.exp
          (-(2 * (2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ K) := by
  let c : ℝ := 1 / (6 * (2 : ℝ) ^ K)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpoly := eventually_caichW_polynomial_le_exp hK hC hc
  filter_upwards [hpoly, eventually_ge_atTop (5 : ℕ)] with
      ell hpolyEll hell i hi
  let x : ℕ := alignedRootExpTestPoint m i
  let T : ℝ := (ell : ℝ) ^ K
  let Q : ℝ := (ell : ℝ) ^ ((K : ℝ) / 2)
  have hx : 1 < x := by
    simpa only [x] using! one_lt_alignedRootExpTestPoint_of_mem hi
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hloglogLower :
      (1 / (3 * (2 : ℝ) ^ K)) * T ≤
        Real.log (Real.log (x : ℝ)) := by
    simpa only [x, T, log₂] using!
      alignedRootExpTestPoint_log₂_scale_lower hK hi
  have hlogLower : Real.exp (2 * c * T) ≤ Real.log (x : ℝ) := by
    have hcEq : 2 * c = 1 / (3 * (2 : ℝ) ^ K) := by
      dsimp [c]
      ring
    exact (Real.le_log_iff_exp_le hlogx).mp (by
      simpa only [hcEq] using! hloglogLower)
  have hQpoly : C * Q ≤ Real.exp (c * T) := by
    simpa only [Q, T, c] using! hpolyEll
  have hbase : C * Q / Real.log (x : ℝ) ≤ Real.exp (-c * T) := by
    have hexpPos : 0 < Real.exp (2 * c * T) := Real.exp_pos _
    have hratio : Real.exp (c * T) / Real.log (x : ℝ) ≤
        Real.exp (c * T) / Real.exp (2 * c * T) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hexpPos hlogLower
    calc
      C * Q / Real.log (x : ℝ) ≤
          Real.exp (c * T) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right hQpoly hlogx.le
      _ ≤ Real.exp (c * T) / Real.exp (2 * c * T) := hratio
      _ = Real.exp (-c * T) := by
        rw [← Real.exp_sub]
        congr 1
        ring
  have hbaseNonneg : 0 ≤ C * Q / Real.log (x : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hbaseNonneg hbase r
  have hcoeff :
      (2 * (2 * m + 2 : ℕ) : ℝ) ≤ (r : ℝ) * c := by
    have hgapR :
        (12 * (2 ^ K) * (2 * m + 2) : ℕ) ≤ (r : ℝ) := by
      exact_mod_cast hgap
    dsimp [c]
    have hden : 0 < 6 * (2 : ℝ) ^ K := by positivity
    rw [show (r : ℝ) * (1 / (6 * (2 : ℝ) ^ K)) =
      (r : ℝ) / (6 * (2 : ℝ) ^ K) by ring]
    rw [le_div_iff₀ hden]
    calc
      (2 * (2 * m + 2 : ℕ) : ℝ) * (6 * (2 : ℝ) ^ K) =
          (12 * (2 ^ K) * (2 * m + 2) : ℕ) := by
        push_cast
        ring
      _ ≤ (r : ℝ) := hgapR
  have hexpCoeff :
      Real.exp (-(r : ℝ) * c * T) ≤
        Real.exp (-(2 * (2 * m + 2 : ℕ) : ℝ) * T) := by
    apply Real.exp_le_exp.mpr
    have hT : 0 ≤ T := by dsimp [T]; positivity
    nlinarith
  have hthreshold : caichAlignedWSafeThreshold K ell = 1 / Q := by
    unfold caichAlignedWSafeThreshold caichWAuxThreshold caichAuxiliaryPower
    rw [if_neg (by omega : ¬ ell < 5)]
  have htermEq :
      caichAlignedWMoment r m C ell i /
          caichAlignedWSafeThreshold K ell ^ r =
        (C * Q / Real.log (x : ℝ)) ^ r := by
    unfold caichAlignedWMoment
    rw [hthreshold]
    dsimp only [x]
    have hQ : Q ≠ 0 := by dsimp [Q]; positivity
    rw [← div_pow]
    congr 1
    field_simp [hQ]
  rw [htermEq]
  calc
    (C * Q / Real.log (x : ℝ)) ^ r ≤
        Real.exp (-c * T) ^ r := hpow
    _ = Real.exp (-(r : ℝ) * c * T) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(2 * (2 * m + 2 : ℕ) : ℝ) * T) :=
      hexpCoeff

/-- A sufficiently large fixed moment makes the exact aligned `W/x`
finite-union budget summable. -/
theorem caichWAlignedScalarSummability_of_largeMoment
    {K m r : ℕ} (hK : 1 ≤ K)
    (hgap : 12 * (2 ^ K) * (2 * m + 2) ≤ r)
    {C : ℝ} (hC : 0 ≤ C) :
    CaichWAlignedScalarSummability r K m C := by
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let moment : ℕ → ℕ → ℝ := fun ell i ↦
    if i ∈ tests ell then caichAlignedWMoment r m C ell i else 0
  have hpoint := eventually_caichW_point_term_le_exp hK hgap hC
  have hmajor : ∀ᶠ ell : ℕ in atTop,
      ‖caichAuxiliaryFiniteUnionMomentBudget tests moment
          (caichAlignedWSafeThreshold K) r ell‖ ≤
        Real.exp (-(ell : ℝ)) := by
    filter_upwards [hpoint, eventually_ge_atTop (1 : ℕ)] with
        ell hpointEll hell
    have htermNonneg : ∀ i ∈ tests ell,
        0 ≤ moment ell i / caichAlignedWSafeThreshold K ell ^ r := by
      intro i hi
      have hx : 1 < alignedRootExpTestPoint m i :=
        one_lt_alignedRootExpTestPoint_of_mem (by simpa only [tests] using! hi)
      have hlog : 0 < Real.log (alignedRootExpTestPoint m i : ℝ) :=
        Real.log_pos (by exact_mod_cast hx)
      unfold moment caichAlignedWMoment
      rw [if_pos hi]
      exact div_nonneg
        (pow_nonneg (div_nonneg hC hlog.le) r)
        (pow_nonneg (caichAlignedWSafeThreshold_pos K ell).le r)
    have hcostNonneg : 0 ≤ caichAuxiliaryFiniteUnionMomentBudget
        tests moment (caichAlignedWSafeThreshold K) r ell := by
      unfold caichAuxiliaryFiniteUnionMomentBudget
      exact Finset.sum_nonneg htermNonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hcostNonneg]
    let D : ℝ := (2 * m + 2 : ℕ)
    let T : ℝ := (ell : ℝ) ^ K
    have hcard := card_alignedRootExpTests_le_exp_entropy K m ell
    have hDT : ((tests ell).card : ℝ) ≤ Real.exp (D * T) := by
      simpa only [tests, D, T, Real.rpow_natCast] using! hcard
    have hlinear : (ell : ℝ) ≤ D * T := by
      have hellPow : (ell : ℝ) ≤ (ell : ℝ) ^ K := by
        have hnat : ell ≤ ell ^ K := le_self_pow₀ hell (show K ≠ 0 by omega)
        exact_mod_cast hnat
      have hD : (1 : ℝ) ≤ D := by
        dsimp [D]
        exact_mod_cast (show 1 ≤ 2 * m + 2 by omega)
      have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
      have hTmul : T ≤ D * T := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right hD hTnonneg
      exact hellPow.trans (by simpa only [T] using! hTmul)
    unfold caichAuxiliaryFiniteUnionMomentBudget
    calc
      (∑ i ∈ tests ell,
          moment ell i / caichAlignedWSafeThreshold K ell ^ r) ≤
          ∑ _i ∈ tests ell, Real.exp (-2 * D * T) := by
        gcongr with i hi
        unfold moment
        rw [if_pos hi]
        convert! hpointEll i (by simpa only [tests] using! hi) using 1 <;>
          dsimp only [D, T, tests] <;> ring
      _ = ((tests ell).card : ℝ) * Real.exp (-2 * D * T) := by simp
      _ ≤ Real.exp (D * T) * Real.exp (-2 * D * T) :=
        mul_le_mul_of_nonneg_right hDT (Real.exp_pos _).le
      _ = Real.exp (-D * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(ell : ℝ)) := by
        exact Real.exp_le_exp.mpr (by linarith)
  exact Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat hmajor

end Problem520
end Erdos
