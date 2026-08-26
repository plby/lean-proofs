import ErdosProblems.Erdos520.LTWFourthMoment
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Unconditional dyadic interpolation on the LTW mesh

This file supplies the maximal fourth-moment argument behind the
Lau--Tenenbaum--Wu interpolation step.  The recursion is the usual dyadic
decomposition, written directly for `fIntervalPrefixMax`.
-/

theorem integrable_fIntervalPrefixMax_pow_four (a L : ℕ) :
    Integrable (fun omega : Omega => fIntervalPrefixMax omega a L ^ 4) μ := by
  refine Integrable.of_bound
    ((measurable_fIntervalPrefixMax a L).pow_const 4).aestronglyMeasurable
    ((L : ℝ) ^ 4) ?_
  filter_upwards [] with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (fIntervalPrefixMax_nonneg omega a L) 4)]
  exact pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a L)
    (fIntervalPrefixMax_le omega a L) 4

private theorem max_pow_four_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ^ 4 ≤ x ^ 4 + y ^ 4 := by
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy]
    exact le_add_of_nonneg_left (pow_nonneg hx 4)
  · rw [max_eq_left (le_of_not_ge hxy)]
    exact le_add_of_nonneg_right (pow_nonneg hy 4)

/-- A fixed weighted fourth-power inequality.  The weights are chosen so
that the coefficient of the recursively occurring right half is close to
one. -/
private theorem add_pow_four_le_weighted {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 1331 * x ^ 4 + (1331 / 1000 : ℝ) * y ^ 4 := by
  have hquad : 0 ≤ 331 * y ^ 2 + 2620 * x * y + 13300 * x ^ 2 := by
    positivity
  have hnonneg : 0 ≤
      (y - 10 * x) ^ 2 *
        (331 * y ^ 2 + 2620 * x * y + 13300 * x ^ 2) :=
    mul_nonneg (sq_nonneg _) hquad
  nlinarith [hnonneg]

/-- Dyadic pointwise recursion for the fourth power of the interval
prefix maximum. -/
theorem fIntervalPrefixMax_pow_four_le_split (omega : Omega)
    (a L R : ℕ) :
    fIntervalPrefixMax omega a (L + R) ^ 4 ≤
      fIntervalPrefixMax omega a L ^ 4 +
        1331 * |fIntervalSum omega a L| ^ 4 +
        (1331 / 1000 : ℝ) *
          fIntervalPrefixMax omega (a + L) R ^ 4 := by
  let A := fIntervalPrefixMax omega a L
  let B := fIntervalPrefixMax omega (a + L) R
  let S := fIntervalSum omega a L
  have hA : 0 ≤ A := fIntervalPrefixMax_nonneg omega a L
  have hB : 0 ≤ B := fIntervalPrefixMax_nonneg omega (a + L) R
  have hSB : 0 ≤ |S| + B := add_nonneg (abs_nonneg _) hB
  have hsplit : fIntervalPrefixMax omega a (L + R) ≤
      max A (|S| + B) := fIntervalPrefixMax_le_split omega a L R
  calc
    fIntervalPrefixMax omega a (L + R) ^ 4 ≤
        max A (|S| + B) ^ 4 :=
      pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a (L + R)) hsplit 4
    _ ≤ A ^ 4 + (|S| + B) ^ 4 := max_pow_four_le_add hA hSB
    _ ≤ A ^ 4 +
        (1331 * |S| ^ 4 + (1331 / 1000 : ℝ) * B ^ 4) := by
      gcongr
      exact add_pow_four_le_weighted (abs_nonneg _) hB
    _ = fIntervalPrefixMax omega a L ^ 4 +
        1331 * |fIntervalSum omega a L| ^ 4 +
        (1331 / 1000 : ℝ) *
          fIntervalPrefixMax omega (a + L) R ^ 4 := by
      dsimp [A, B, S]
      ring

private theorem fIntervalPrefixMax_one (omega : Omega) (a : ℕ) :
    fIntervalPrefixMax omega a 1 = |fIntervalSum omega a 1| := by
  apply le_antisymm
  · unfold fIntervalPrefixMax
    apply Finset.sup'_le
    intro k hk
    have hk' : k ≤ 1 := Nat.le_of_lt_succ (by simpa using! hk)
    interval_cases k
    · simp [fIntervalSum]
    · rfl
  · exact abs_fIntervalSum_le_prefixMax omega a le_rfl

/-- The scalar fourth-moment budget used throughout the dyadic recursion. -/
noncomputable def ltwFourthMomentBudget (L x : ℕ) : ℝ :=
  Real.sqrt
    ((L : ℝ) ^ 3 *
      ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80))

theorem ltwFourthMomentBudget_nonneg (L x : ℕ) :
    0 ≤ ltwFourthMomentBudget L x := by
  exact Real.sqrt_nonneg _

private theorem fourteen_fifths_mul_ltwFourthMomentBudget_le_double
    (N x : ℕ) :
    (14 / 5 : ℝ) * ltwFourthMomentBudget N x ≤
      ltwFourthMomentBudget (N + N) x := by
  let A : ℝ := (x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80
  let B : ℝ := (N : ℝ) ^ 3 * A
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) (pow_nonneg (by positivity) 80)
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg (by positivity) 3) hA
  have hsqrtB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have htarget :
      (((N + N : ℕ) : ℝ) ^ 3 * A) = 8 * B := by
    dsimp [B]
    push_cast
    ring
  unfold ltwFourthMomentBudget
  change (14 / 5 : ℝ) * Real.sqrt B ≤
    Real.sqrt (((N + N : ℕ) : ℝ) ^ 3 * A)
  rw [Real.le_sqrt
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (mul_nonneg (pow_nonneg (by positivity) 3) hA)]
  rw [htarget]
  nlinarith

/-- The dyadic maximal fourth-moment estimate.  Its absolute constant is
deliberately generous; the important feature is the same `L^(3/2)` length
dependence as the one-interval estimate. -/
theorem integral_fIntervalPrefixMax_pow_four_pow_two_le_ltwBudget
    (a d x : ℕ) (hx : 3 ≤ x) (hax : a + 2 ^ d ≤ x) :
    (∫ omega, fIntervalPrefixMax omega a (2 ^ d) ^ 4 ∂μ) ≤
      4096 * ltwFourthMomentBudget (2 ^ d) x := by
  induction d generalizing a with
  | zero =>
      norm_num at hax ⊢
      simp_rw [fIntervalPrefixMax_one]
      calc
        (∫ omega, |fIntervalSum omega a 1| ^ 4 ∂μ) ≤
            ltwFourthMomentBudget 1 x := by
          simpa only [ltwFourthMomentBudget] using!
            integral_abs_fIntervalSum_pow_four_le_ltwBudget a 1 x hx hax
        _ ≤ 4096 * ltwFourthMomentBudget 1 x := by
          nlinarith [ltwFourthMomentBudget_nonneg 1 x]
  | succ d ih =>
      let N : ℕ := 2 ^ d
      have hpow : 2 ^ (d + 1) = N + N := by
        dsimp [N]
        rw [pow_succ]
        omega
      rw [hpow] at hax ⊢
      have hN : 0 < N := by
        dsimp [N]
        positivity
      have hleft : a + N ≤ x := by omega
      have hright : (a + N) + N ≤ x := by omega
      have hAint := integrable_fIntervalPrefixMax_pow_four a N
      have hSint : Integrable
          (fun omega : Omega => |fIntervalSum omega a N| ^ 4) μ := by
        simpa only [show 4 = 2 * 2 by norm_num] using!
          integrable_abs_fIntervalSum_pow 2 a N
      have hBint := integrable_fIntervalPrefixMax_pow_four (a + N) N
      have hRint : Integrable (fun omega : Omega =>
          fIntervalPrefixMax omega a N ^ 4 +
            1331 * |fIntervalSum omega a N| ^ 4 +
            (1331 / 1000 : ℝ) *
              fIntervalPrefixMax omega (a + N) N ^ 4) μ :=
        (hAint.add (hSint.const_mul _)).add (hBint.const_mul _)
      calc
        (∫ omega, fIntervalPrefixMax omega a (N + N) ^ 4 ∂μ) ≤
            ∫ omega,
              fIntervalPrefixMax omega a N ^ 4 +
                1331 * |fIntervalSum omega a N| ^ 4 +
                (1331 / 1000 : ℝ) *
                  fIntervalPrefixMax omega (a + N) N ^ 4 ∂μ := by
          exact integral_mono
            (integrable_fIntervalPrefixMax_pow_four a (N + N)) hRint
              (fun omega =>
                fIntervalPrefixMax_pow_four_le_split omega a N N)
        _ = (∫ omega, fIntervalPrefixMax omega a N ^ 4 ∂μ) +
              1331 * (∫ omega, |fIntervalSum omega a N| ^ 4 ∂μ) +
              (1331 / 1000 : ℝ) *
                (∫ omega,
                  fIntervalPrefixMax omega (a + N) N ^ 4 ∂μ) := by
          calc
            (∫ omega,
                fIntervalPrefixMax omega a N ^ 4 +
                  1331 * |fIntervalSum omega a N| ^ 4 +
                  (1331 / 1000 : ℝ) *
                    fIntervalPrefixMax omega (a + N) N ^ 4 ∂μ) =
                (∫ omega,
                  fIntervalPrefixMax omega a N ^ 4 +
                    1331 * |fIntervalSum omega a N| ^ 4 ∂μ) +
                ∫ omega, (1331 / 1000 : ℝ) *
                  fIntervalPrefixMax omega (a + N) N ^ 4 ∂μ := by
              exact integral_add (hAint.add (hSint.const_mul _))
                (hBint.const_mul _)
            _ = ((∫ omega, fIntervalPrefixMax omega a N ^ 4 ∂μ) +
                  ∫ omega, 1331 * |fIntervalSum omega a N| ^ 4 ∂μ) +
                ∫ omega, (1331 / 1000 : ℝ) *
                  fIntervalPrefixMax omega (a + N) N ^ 4 ∂μ := by
              rw [integral_add hAint (hSint.const_mul _)]
            _ = _ := by
              rw [integral_const_mul, integral_const_mul]
        _ ≤ 4096 * ltwFourthMomentBudget N x +
              1331 * ltwFourthMomentBudget N x +
              (1331 / 1000 : ℝ) *
                (4096 * ltwFourthMomentBudget N x) := by
          gcongr
          · exact ih (a := a) hleft
          · simpa only [ltwFourthMomentBudget] using!
              integral_abs_fIntervalSum_pow_four_le_ltwBudget a N x hx hleft
          · exact ih (a := a + N) hright
        _ ≤ 4096 * ((14 / 5 : ℝ) * ltwFourthMomentBudget N x) := by
          nlinarith [ltwFourthMomentBudget_nonneg N x]
        _ ≤ 4096 * ltwFourthMomentBudget (N + N) x := by
          gcongr
          exact fourteen_fifths_mul_ltwFourthMomentBudget_le_double N x

/-! ## Padding an arbitrary interval to a dyadic interval -/

def ltwDyadicDepth (L : ℕ) : ℕ := Nat.clog 2 L

def ltwDyadicLength (L : ℕ) : ℕ := 2 ^ ltwDyadicDepth L

theorem le_ltwDyadicLength (L : ℕ) : L ≤ ltwDyadicLength L := by
  exact Nat.le_pow_clog Nat.one_lt_two L

theorem ltwDyadicLength_le_two_mul {L : ℕ} (hL : 0 < L) :
    ltwDyadicLength L ≤ 2 * L := by
  by_cases hLone : L ≤ 1
  · have : L = 1 := by omega
    subst L
    simp [ltwDyadicLength, ltwDyadicDepth]
  · have hLtwo : 1 < L := by omega
    have hclog : 0 < Nat.clog 2 L := Nat.clog_pos Nat.one_lt_two hLtwo
    have hpred : 2 ^ (Nat.clog 2 L).pred < L :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two hLtwo
    unfold ltwDyadicLength ltwDyadicDepth
    rw [← Nat.succ_pred_eq_of_pos hclog, pow_succ]
    omega

/-- Arbitrary-length maximal fourth moment after zero-cost dyadic padding.
The ambient endpoint is the padded endpoint itself. -/
theorem integral_fIntervalPrefixMax_pow_four_le_ltwDyadicBudget
    (a L : ℕ) (hlarge : 3 ≤ a + ltwDyadicLength L) :
    (∫ omega, fIntervalPrefixMax omega a L ^ 4 ∂μ) ≤
      4096 * ltwFourthMomentBudget (ltwDyadicLength L)
        (a + ltwDyadicLength L) := by
  calc
    (∫ omega, fIntervalPrefixMax omega a L ^ 4 ∂μ) ≤
        ∫ omega,
          fIntervalPrefixMax omega a (ltwDyadicLength L) ^ 4 ∂μ := by
      exact integral_mono
        (integrable_fIntervalPrefixMax_pow_four a L)
        (integrable_fIntervalPrefixMax_pow_four a (ltwDyadicLength L))
        (fun omega => pow_le_pow_left₀
          (fIntervalPrefixMax_nonneg omega a L)
          (fIntervalPrefixMax_mono_length omega a (le_ltwDyadicLength L)) 4)
    _ ≤ 4096 * ltwFourthMomentBudget (ltwDyadicLength L)
          (a + ltwDyadicLength L) := by
      exact integral_fIntervalPrefixMax_pow_four_pow_two_le_ltwBudget
        a (ltwDyadicDepth L) (a + ltwDyadicLength L) hlarge (by
          simp only [ltwDyadicLength]
          exact le_rfl)

/-- Markov form of the padded dyadic maximal fourth moment. -/
theorem measureReal_fIntervalPrefixMax_gt_le_ltwDyadicBudget
    (a L : ℕ) (hlarge : 3 ≤ a + ltwDyadicLength L)
    {u : ℝ} (hu : 0 < u) :
    μ.real {omega | u < fIntervalPrefixMax omega a L} ≤
      (4096 * ltwFourthMomentBudget (ltwDyadicLength L)
          (a + ltwDyadicLength L)) / u ^ 4 := by
  exact measureReal_lt_le_natMoment
    (q := 4) (Y := fun omega => fIntervalPrefixMax omega a L)
    (by norm_num) (fun omega => fIntervalPrefixMax_nonneg omega a L) hu
    (integrable_fIntervalPrefixMax_pow_four a L)
    (integral_fIntervalPrefixMax_pow_four_le_ltwDyadicBudget a L hlarge)

/-! ## Probability wrapper on the exact LTW mesh -/

noncomputable def ltwDyadicInterpolationCost (i : ℕ) : ℝ :=
  let a := ltwRademacherTestPoint i
  let b := ltwRademacherTestPoint (i + 1)
  let L := b - a
  let P := ltwDyadicLength L
  (4096 * ltwFourthMomentBudget P (a + P)) /
    ltwInterpolationScale b ^ 4

theorem ltwDyadicInterpolationCost_nonneg (i : ℕ) :
    0 ≤ ltwDyadicInterpolationCost i := by
  dsimp only [ltwDyadicInterpolationCost]
  exact div_nonneg
    (mul_nonneg (by norm_num) (ltwFourthMomentBudget_nonneg _ _))
    (by positivity)

theorem eventually_measureReal_ltwInterpolationFailure_le_dyadicCost :
    ∀ᶠ i : ℕ in atTop,
      μ.real (ltwHypercontractiveInterpolationFailure i) ≤
        ltwDyadicInterpolationCost i := by
  have htest : Tendsto ltwRademacherTestPoint atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop
  filter_upwards [htest.eventually (eventually_ge_atTop 3),
      eventually_ltwInterpolationScale_testPoint_pos] with i hi hscale
  let a := ltwRademacherTestPoint i
  let b := ltwRademacherTestPoint (i + 1)
  let L := b - a
  let P := ltwDyadicLength L
  have hlarge : 3 ≤ a + P := by
    have ha : 3 ≤ a := by simpa only [a] using! hi
    omega
  simpa only [ltwHypercontractiveInterpolationFailure,
      ltwDyadicInterpolationCost, a, b, L, P] using!
    measureReal_fIntervalPrefixMax_gt_le_ltwDyadicBudget
      a L hlarge hscale

/-- Once the explicit dyadic cost is summable, Borel--Cantelli gives the
exact almost-sure LTW interpolation statement with constant `1`. -/
theorem LauTenenbaumWuRademacherInterpolation_of_dyadicCost
    (hcost : Summable ltwDyadicInterpolationCost) :
    LauTenenbaumWuRademacherInterpolation := by
  have hmeasure : Summable fun i =>
      μ.real (ltwHypercontractiveInterpolationFailure i) := by
    apply hcost.of_norm_bounded_eventually_nat
    filter_upwards [eventually_measureReal_ltwInterpolationFailure_le_dyadicCost]
      with i hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using! hi
  have hbc : ∀ᵐ omega ∂μ, ∀ᶠ i : ℕ in atTop,
      omega ∉ ltwHypercontractiveInterpolationFailure i := by
    apply ae_eventually_notMem
    have heq : (fun i => μ (ltwHypercontractiveInterpolationFailure i)) =
        fun i => ENNReal.ofReal
          (μ.real (ltwHypercontractiveInterpolationFailure i)) := by
      funext i
      exact (ofReal_measureReal
        (μ := μ) (s := ltwHypercontractiveInterpolationFailure i)).symm
    rw [heq]
    exact hmeasure.tsum_ofReal_ne_top
  filter_upwards [hbc] with omega homega
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [homega] with i hi
  intro N hiN hNi
  have hdiff : N - ltwRademacherTestPoint i ≤
      ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i :=
    Nat.sub_le_sub_right hNi _
  have hinc := abs_fIntervalSum_le_prefixMax omega
    (ltwRademacherTestPoint i) hdiff
  have hsum := partialSum_add_sub omega (ltwRademacherTestPoint i)
    (N - ltwRademacherTestPoint i)
  rw [Nat.add_sub_of_le hiN.le] at hsum
  rw [hsum]
  exact hinc.trans (by
    have hi' : ¬ltwInterpolationScale
        (ltwRademacherTestPoint (i + 1)) <
          fIntervalPrefixMax omega (ltwRademacherTestPoint i)
            (ltwRademacherTestPoint (i + 1) -
              ltwRademacherTestPoint i) := by
      simpa only [ltwHypercontractiveInterpolationFailure,
        Set.mem_setOf_eq] using! hi
    simpa using! not_lt.mp hi')

/-! ## Deterministic estimates for the root-exponential mesh -/

/-- Concavity of `t ↦ t^(1/350)` gives the sharp decay of one mesh step. -/
theorem ltw_rootExponent_step_le (i : ℕ) (hi : 1 ≤ i) :
    (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)) -
        (i : ℝ) ^ (1 / (350 : ℝ))) ≤
      (1 / (350 : ℝ)) *
        (i : ℝ) ^ ((1 / (350 : ℝ)) - 1) := by
  let p : ℝ := 1 / 350
  have hiR : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hone : 0 ≤ 1 + 1 / (i : ℝ) := by positivity
  have hfactor : (((i + 1 : ℕ) : ℝ)) =
      (i : ℝ) * (1 + 1 / (i : ℝ)) := by
    push_cast
    field_simp
  have hbern : (1 + 1 / (i : ℝ)) ^ p ≤
      1 + p * (1 / (i : ℝ)) := by
    exact rpow_one_add_le_one_add_mul_self
      ((show (-1 : ℝ) ≤ 0 by norm_num).trans (by positivity))
      (by positivity : 0 ≤ p) (by norm_num [p] : p ≤ 1)
  have hmul := mul_le_mul_of_nonneg_left hbern
    (Real.rpow_nonneg hiR.le p)
  change (((i + 1 : ℕ) : ℝ) ^ p - (i : ℝ) ^ p) ≤
    p * (i : ℝ) ^ (p - 1)
  rw [hfactor, Real.mul_rpow hiR.le hone]
  rw [Real.rpow_sub_one hiR.ne']
  calc
    (i : ℝ) ^ p * (1 + 1 / (i : ℝ)) ^ p - (i : ℝ) ^ p ≤
        (i : ℝ) ^ p * (1 + p * (1 / (i : ℝ))) -
          (i : ℝ) ^ p := sub_le_sub_right hmul _
    _ = p * ((i : ℝ) ^ p / (i : ℝ)) := by ring

/-- A slightly weakened exponent, chosen to leave room for all logarithmic
factors in the final p-series comparison. -/
theorem ltw_rootExponent_step_le_nine_tenths (i : ℕ) (hi : 1 ≤ i) :
    (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)) -
        (i : ℝ) ^ (1 / (350 : ℝ))) ≤
      (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hpow :
      (i : ℝ) ^ ((1 / (350 : ℝ)) - 1) ≤
        (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hiR (by norm_num)
  calc
    (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)) -
        (i : ℝ) ^ (1 / (350 : ℝ))) ≤
        (1 / (350 : ℝ)) *
          (i : ℝ) ^ ((1 / (350 : ℝ)) - 1) :=
      ltw_rootExponent_step_le i hi
    _ ≤ 1 * (i : ℝ) ^ ((1 / (350 : ℝ)) - 1) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ (i : ℝ) ^ (-(9 / 10 : ℝ)) := by simpa using! hpow

/-- The corresponding relative increment estimate before taking floors. -/
theorem ltw_rootExp_real_step_le (i : ℕ) (hi : 1 ≤ i) :
    Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) -
        Real.exp ((i : ℝ) ^ (1 / (350 : ℝ))) ≤
      Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) *
        (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
  let u : ℝ := (i : ℝ) ^ (1 / (350 : ℝ))
  let v : ℝ := ((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))
  have huv : u ≤ v := by
    dsimp [u, v]
    exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
  have hlinear : 1 - Real.exp (u - v) ≤ v - u := by
    linarith [Real.add_one_le_exp (u - v)]
  have hexpEq : Real.exp u = Real.exp v * Real.exp (u - v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp v - Real.exp u ≤
    Real.exp v * (i : ℝ) ^ (-(9 / 10 : ℝ))
  calc
    Real.exp v - Real.exp u =
        Real.exp v * (1 - Real.exp (u - v)) := by rw [hexpEq]; ring
    _ ≤ Real.exp v * (v - u) :=
      mul_le_mul_of_nonneg_left hlinear (Real.exp_pos _).le
    _ ≤ Real.exp v * (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
      gcongr
      simpa only [u, v] using! ltw_rootExponent_step_le_nine_tenths i hi

/-- Taking floors costs only one additional unit in the mesh gap. -/
theorem ltwRademacherTestPoint_gap_cast_le (i : ℕ) (hi : 1 ≤ i) :
    (ltwRademacherTestPoint (i + 1) -
        ltwRademacherTestPoint i : ℕ) ≤
      Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) *
          (i : ℝ) ^ (-(9 / 10 : ℝ)) + 1 := by
  let A : ℝ := Real.exp ((i : ℝ) ^ (1 / (350 : ℝ)))
  let B : ℝ :=
    Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)))
  have hAB : A ≤ B := by
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
  have hfloor : Nat.floor A ≤ Nat.floor B := Nat.floor_mono hAB
  have hcast : ((Nat.floor B - Nat.floor A : ℕ) : ℝ) =
      (Nat.floor B : ℝ) - (Nat.floor A : ℝ) := by
    rw [Nat.cast_sub hfloor]
  have hBfloor : (Nat.floor B : ℝ) ≤ B :=
    Nat.floor_le (Real.exp_pos _).le
  have hAfloor : A < (Nat.floor A : ℝ) + 1 := Nat.lt_floor_add_one A
  have hreal : B - A ≤ B * (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
    simpa only [A, B] using! ltw_rootExp_real_step_le i hi
  rw [ltwRademacherTestPoint_eq, ltwRademacherTestPoint_eq]
  change ((Nat.floor B - Nat.floor A : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp only [B]
  dsimp only [B] at hBfloor hreal
  dsimp only [A] at hAfloor hreal
  linarith

/-- The additive unit introduced by flooring is eventually absorbed by the
same relative power-law scale. -/
theorem eventually_ltw_rootExp_reciprocal_le_nine_tenths :
    ∀ᶠ i : ℕ in atTop,
      1 / Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) ≤
        (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
  have hp : (0 : ℝ) < 1 / (350 : ℝ) := by norm_num
  have hsmall := (isLittleO_log_rpow_atTop hp).eventuallyLE
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [hsmallNat, eventually_ge_atTop (1 : ℕ)] with i hiLog hi
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hiOne : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hlogNonneg : 0 ≤ Real.log (i : ℝ) := Real.log_nonneg hiOne
  have hpowNonneg : 0 ≤ (i : ℝ) ^ (1 / (350 : ℝ)) :=
    Real.rpow_nonneg hiR.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlogNonneg,
    Real.norm_eq_abs, abs_of_nonneg hpowNonneg] at hiLog
  have hexponent :
      (9 / 10 : ℝ) * Real.log (i : ℝ) ≤
        ((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)) := by
    have hrootMono : (i : ℝ) ^ (1 / (350 : ℝ)) ≤
        ((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    nlinarith
  have hpowExp : (i : ℝ) ^ (9 / 10 : ℝ) ≤
      Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) := by
    rw [Real.rpow_def_of_pos hiR]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using! hexponent)
  have hdenLeft : 0 < (i : ℝ) ^ (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hiR _
  have hdenRight : 0 <
      Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ))) :=
    Real.exp_pos _
  rw [Real.rpow_neg hiR.le]
  simpa only [one_div] using! one_div_le_one_div_of_le hdenLeft hpowExp

private theorem ltw_rootExpReal_le_two_testPoint (i : ℕ) :
    Real.exp ((i : ℝ) ^ (1 / (350 : ℝ))) ≤
      2 * (ltwRademacherTestPoint i : ℝ) := by
  let y : ℝ := Real.exp ((i : ℝ) ^ (1 / (350 : ℝ)))
  have hyOne : 1 ≤ Nat.floor y := by
    apply Nat.le_floor
    dsimp [y]
    simpa only [Nat.cast_one] using! Real.one_le_exp
      (Real.rpow_nonneg (show (0 : ℝ) ≤ i by positivity) _)
  have hylt : y < (Nat.floor y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hyOneR : (1 : ℝ) ≤ Nat.floor y := by exact_mod_cast hyOne
  rw [ltwRademacherTestPoint_eq]
  change y ≤ 2 * (Nat.floor y : ℝ)
  linarith

/-- Final usable mesh-gap estimate: the floored gap is at most a fixed
multiple of the right endpoint times `i^(-9/10)`. -/
theorem eventually_ltwRademacherTestPoint_gap_cast_le :
    ∀ᶠ i : ℕ in atTop,
      (ltwRademacherTestPoint (i + 1) -
          ltwRademacherTestPoint i : ℕ) ≤
        4 * (ltwRademacherTestPoint (i + 1) : ℝ) *
          (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
  filter_upwards [eventually_ltw_rootExp_reciprocal_le_nine_tenths,
      eventually_ge_atTop (1 : ℕ)] with i hrecip hi
  let B : ℝ :=
    Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)))
  let r : ℝ := (i : ℝ) ^ (-(9 / 10 : ℝ))
  have hB : 0 < B := Real.exp_pos _
  have hfloorAbsorb : 1 ≤ B * r := by
    have hrecip' : 1 / B ≤ r := by simpa only [B, r] using! hrecip
    have hmul : 1 ≤ r * B := (div_le_iff₀ hB).mp hrecip'
    nlinarith
  have hraw := ltwRademacherTestPoint_gap_cast_le i hi
  have hBtest : B ≤
      2 * (ltwRademacherTestPoint (i + 1) : ℝ) := by
    simpa only [B] using! ltw_rootExpReal_le_two_testPoint (i + 1)
  change (ltwRademacherTestPoint (i + 1) -
      ltwRademacherTestPoint i : ℕ) ≤
    4 * (ltwRademacherTestPoint (i + 1) : ℝ) * r
  change (ltwRademacherTestPoint (i + 1) -
      ltwRademacherTestPoint i : ℕ) ≤ B * r + 1 at hraw
  have hiR : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg hiR _
  have hBr : B * r ≤
      (2 * (ltwRademacherTestPoint (i + 1) : ℝ)) * r :=
    mul_le_mul_of_nonneg_right hBtest hr
  calc
    (ltwRademacherTestPoint (i + 1) -
        ltwRademacherTestPoint i : ℕ) ≤ B * r + 1 := hraw
    _ ≤ 2 * (B * r) := by linarith
    _ ≤ 2 * ((2 * (ltwRademacherTestPoint (i + 1) : ℝ)) * r) :=
      mul_le_mul_of_nonneg_left hBr (by norm_num)
    _ = 4 * (ltwRademacherTestPoint (i + 1) : ℝ) * r := by ring

/-- The least dyadic padding of the mesh gap obeys the same relative bound,
with a harmless doubled constant. -/
theorem eventually_ltwDyadicLength_gap_cast_le :
    ∀ᶠ i : ℕ in atTop,
      (ltwDyadicLength
          (ltwRademacherTestPoint (i + 1) -
            ltwRademacherTestPoint i) : ℝ) ≤
        8 * (ltwRademacherTestPoint (i + 1) : ℝ) *
          (i : ℝ) ^ (-(9 / 10 : ℝ)) := by
  filter_upwards [eventually_ltwRademacherTestPoint_gap_cast_le,
      eventually_ltw_rootExp_reciprocal_le_nine_tenths,
      eventually_ge_atTop (1 : ℕ)] with i hgap hrecip hi
  let a := ltwRademacherTestPoint i
  let b := ltwRademacherTestPoint (i + 1)
  let L := b - a
  let r : ℝ := (i : ℝ) ^ (-(9 / 10 : ℝ))
  let B : ℝ :=
    Real.exp (((i + 1 : ℕ) : ℝ) ^ (1 / (350 : ℝ)))
  have hB : 0 < B := Real.exp_pos _
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hfloorAbsorb : 1 ≤ B * r := by
    have hrecip' : 1 / B ≤ r := by simpa only [B, r] using! hrecip
    have hmul : 1 ≤ r * B := (div_le_iff₀ hB).mp hrecip'
    nlinarith
  have hBtest : B ≤ 2 * (b : ℝ) := by
    simpa only [B, b] using! ltw_rootExpReal_le_two_testPoint (i + 1)
  have hone : 1 ≤ 2 * (b : ℝ) * r := by
    have := mul_le_mul_of_nonneg_right hBtest hr
    nlinarith
  by_cases hL : L = 0
  · have hzero : ltwRademacherTestPoint (i + 1) -
        ltwRademacherTestPoint i = 0 := by simpa only [L, a, b] using! hL
    rw [hzero]
    simp only [ltwDyadicLength, ltwDyadicDepth, Nat.clog_zero_right,
      pow_zero, Nat.cast_one]
    change (1 : ℝ) ≤ 8 * (b : ℝ) * r
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ b) hr]
  · have hPnat : ltwDyadicLength L ≤ 2 * L :=
      ltwDyadicLength_le_two_mul (Nat.pos_of_ne_zero hL)
    have hPcast : (ltwDyadicLength L : ℝ) ≤ 2 * (L : ℝ) := by
      exact_mod_cast hPnat
    have hgap' : (L : ℝ) ≤ 4 * (b : ℝ) * r := by
      simpa only [L, a, b, r] using! hgap
    calc
      (ltwDyadicLength L : ℝ) ≤ 2 * (L : ℝ) := hPcast
      _ ≤ 2 * (4 * (b : ℝ) * r) :=
        mul_le_mul_of_nonneg_left hgap' (by norm_num)
      _ = 8 * (b : ℝ) * r := by ring

/-- Consequently, the padded ambient endpoint is at most nine times the
right endpoint of the original mesh interval. -/
theorem eventually_ltwPaddedEndpoint_le_nine_mul :
    ∀ᶠ i : ℕ in atTop,
      (ltwRademacherTestPoint i +
          ltwDyadicLength
            (ltwRademacherTestPoint (i + 1) -
              ltwRademacherTestPoint i) : ℝ) ≤
        9 * (ltwRademacherTestPoint (i + 1) : ℝ) := by
  filter_upwards [eventually_ltwDyadicLength_gap_cast_le,
      eventually_ge_atTop (1 : ℕ)] with i hP hi
  let a := ltwRademacherTestPoint i
  let b := ltwRademacherTestPoint (i + 1)
  let L := b - a
  let r : ℝ := (i : ℝ) ^ (-(9 / 10 : ℝ))
  have hab : a ≤ b := ltwRademacherTestPoint_mono (Nat.le_add_right i 1)
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hr : r ≤ 1 := by
    dsimp [r]
    simpa only [Real.rpow_zero] using!
      Real.rpow_le_rpow_of_exponent_le hiR (by norm_num : -(9 / 10 : ℝ) ≤ 0)
  have hbr : (b : ℝ) * r ≤ (b : ℝ) :=
    mul_le_of_le_one_right (by positivity) hr
  have hP' : (ltwDyadicLength L : ℝ) ≤ 8 * (b : ℝ) * r := by
    simpa only [L, a, b, r] using! hP
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  dsimp only [a, b, L] at habR hP' hbr ⊢
  nlinarith

end Problem520
end Erdos
