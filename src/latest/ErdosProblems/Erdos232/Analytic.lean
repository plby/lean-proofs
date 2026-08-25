/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import LeanCert.Core.IntervalRat.Basic

/-!
# Erdős Problem 232

For a Lebesgue measurable subset `A` of the Euclidean plane, its upper density is the
limsup, as the radius tends to infinity, of the proportion of a centred ball occupied by
`A`.  Erdős asked whether the supremum of the upper densities of sets avoiding distance
one is at most `1 / 4`.  Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki proved the
stronger bound `0.247`.

The definitions below are the literal measure-theoretic definitions in the problem.
The proof follows the autocorrelation, inclusion--exclusion, Fourier--Bessel, and exact
dual-certificate argument reconstructed in `tex/232.tex`.
-/

open Filter MeasureTheory Metric intervalIntegral
open scoped ENNReal Topology Interval

namespace Erdos232

/-- The Euclidean plane with its standard norm, metric, and Lebesgue measure. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A set containing no ordered pair of points at Euclidean distance one. -/
def UnitDistanceFree (A : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → dist x y ≠ 1

/-- The proportion of the radius-`R` ball occupied by `A`.

The values at nonpositive radii are immaterial to the `atTop` limsup.  `toReal` is
legitimate for positive radii because both measures are finite. -/
noncomputable def ballDensity (A : Set Plane) (R : ℝ) : ℝ :=
  (volume (A ∩ ball 0 R)).toReal / (volume (ball (0 : Plane) R)).toReal

/-- Upper asymptotic density with respect to balls centred at the origin. -/
noncomputable def upperDensity (A : Set Plane) : ℝ :=
  limsup (ballDensity A) atTop

/-- The set of upper densities occurring in Erdős Problem 232. -/
noncomputable def admissibleDensities : Set ℝ :=
  {d | ∃ A : Set Plane, MeasurableSet A ∧ UnitDistanceFree A ∧ upperDensity A = d}

/-- The extremal density `m₁` from Erdős Problem 232. -/
noncomputable def m1 : ℝ :=
  sSup admissibleDensities

@[simp] theorem unitDistanceFree_empty : UnitDistanceFree (∅ : Set Plane) := by
  simp [UnitDistanceFree]

@[simp] theorem ballDensity_empty (R : ℝ) : ballDensity (∅ : Set Plane) R = 0 := by
  simp [ballDensity]

theorem volume_ball_ne_top (R : ℝ) :
    volume (ball (0 : Plane) R) ≠ ∞ := by
  rw [EuclideanSpace.volume_ball_fin_two]
  finiteness

theorem volume_inter_ball_ne_top (A : Set Plane) (R : ℝ) :
    volume (A ∩ ball (0 : Plane) R) ≠ ∞ := by
  exact ne_of_lt <| (measure_mono Set.inter_subset_right).trans_lt
    (lt_top_iff_ne_top.mpr (volume_ball_ne_top R))

theorem ballDensity_nonneg (A : Set Plane) (R : ℝ) : 0 ≤ ballDensity A R := by
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem ballDensity_le_one (A : Set Plane) (R : ℝ) : ballDensity A R ≤ 1 := by
  by_cases hR : R ≤ 0
  · rw [ballDensity, ball_eq_empty.mpr hR]
    simp
  · have hden : 0 < (volume (ball (0 : Plane) R)).toReal := by
      apply ENNReal.toReal_pos
      · rw [EuclideanSpace.volume_ball_fin_two]
        exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt <| ENNReal.ofReal_pos.mpr <| not_le.mp hR))
          (ne_of_gt <| ENNReal.ofReal_pos.mpr Real.pi_pos)
      · exact volume_ball_ne_top R
    apply (div_le_one hden).mpr
    exact (ENNReal.toReal_le_toReal (volume_inter_ball_ne_top A R)
      (volume_ball_ne_top R)).mpr (measure_mono Set.inter_subset_right)

theorem upperDensity_le_one (A : Set Plane) : upperDensity A ≤ 1 := by
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (ballDensity_nonneg A)
  · exact Eventually.of_forall (ballDensity_le_one A)

@[simp] theorem upperDensity_empty : upperDensity (∅ : Set Plane) = 0 := by
  rw [upperDensity, show ballDensity (∅ : Set Plane) = fun _ ↦ 0 by funext R; simp]
  simp

theorem admissibleDensities_nonempty : admissibleDensities.Nonempty := by
  refine ⟨0, ∅, MeasurableSet.empty, unitDistanceFree_empty, ?_⟩
  exact upperDensity_empty

/-! ## The order-zero Bessel kernel

Mathlib v4.33.0 does not provide Bessel functions.  We therefore define the particular kernel
needed by the planar radial Fourier transform by its everywhere absolutely convergent power
series.  The normalization is `J₀(0) = 1`.
-/

/-- The `n`th term in the power series for the order-zero Bessel function. -/
noncomputable def besselJ0Term (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (x ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)

theorem summable_besselJ0Term (x : ℝ) : Summable (besselJ0Term x) := by
  apply Summable.of_norm
  refine (Real.summable_pow_div_factorial |x ^ 2 / 4|).of_nonneg_of_le
    (fun n ↦ by positivity) (fun n ↦ ?_)
  have hnfac : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  simp only [besselJ0Term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Real.norm_eq_abs, abs_of_nonneg hnfac]
  have hbase : |x ^ 2 / 4| = |x| ^ 2 / |(4 : ℝ)| := by rw [abs_div, abs_pow]
  rw [hbase]
  have hfac : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.factorial_pos n
  have hfacpos : (0 : ℝ) < n.factorial := lt_of_lt_of_le zero_lt_one hfac
  apply div_le_div_of_nonneg_left
    (pow_nonneg (div_nonneg (sq_nonneg |x|) (abs_nonneg 4)) n) hfacpos
  nlinarith [sq_nonneg ((n.factorial : ℝ) - 1)]

/-- The power-series presentation of the real Bessel function `J₀`. -/
noncomputable def besselJ0Series (x : ℝ) : ℝ :=
  ∑' n : ℕ, besselJ0Term x n

@[simp] theorem besselJ0Term_zero (n : ℕ) :
    besselJ0Term 0 n = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp [besselJ0Term]
  · simp [besselJ0Term]

@[simp] theorem besselJ0Series_zero : besselJ0Series 0 = 1 := by
  rw [besselJ0Series, tsum_eq_single 0]
  · simp [besselJ0Term]
  · intro n hn
    simp [besselJ0Term, hn]

@[simp] theorem besselJ0Series_neg (x : ℝ) : besselJ0Series (-x) = besselJ0Series x := by
  apply tsum_congr
  intro n
  simp [besselJ0Term]

/-- The `n`th derivative of the angular-integral presentation of `J₀`.

The phase shift by `nπ/2` packages all derivative signs into one formula. -/
noncomputable def besselDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
    Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n

/-- The order-zero Bessel kernel, normalized as an angular average. -/
noncomputable def besselJ0 (x : ℝ) : ℝ := besselDerivative 0 x

/-- Differentiating the angular presentation advances the derivative index. -/
theorem hasDerivAt_besselDerivative (n : ℕ) (x : ℝ) :
    HasDerivAt (besselDerivative n) (besselDerivative (n + 1) x) x := by
  unfold besselDerivative
  apply HasDerivAt.const_mul
  have h : IntervalIntegrable
        (fun θ : ℝ => -Real.sin (x * Real.cos θ + n * Real.pi / 2) *
          Real.cos θ * Real.cos θ ^ n) volume 0 (2 * Real.pi) ∧
      HasDerivAt
        (fun y => ∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.cos (y * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n)
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          -Real.sin (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ * Real.cos θ ^ n) x := by
    refine intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x θ : ℝ => Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n)
      (F' := fun y θ : ℝ => -Real.sin (y * Real.cos θ + n * Real.pi / 2) *
        Real.cos θ * Real.cos θ ^ n)
      (bound := fun _ : ℝ => 1)
      (s := Set.univ) (a := (0 : ℝ)) (b := 2 * Real.pi) (x₀ := x) (μ := volume)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [] with y
      exact (Real.continuous_cos.comp
        ((continuous_const.mul Real.continuous_cos).add continuous_const)).mul
          (Real.continuous_cos.pow n) |>.aestronglyMeasurable
    · exact ((Real.continuous_cos.comp
        ((continuous_const.mul Real.continuous_cos).add continuous_const)).mul
          (Real.continuous_cos.pow n)).intervalIntegrable _ _
    · exact (((Real.continuous_sin.comp
        ((continuous_const.mul Real.continuous_cos).add continuous_const)).neg.mul
          Real.continuous_cos).mul (Real.continuous_cos.pow n)).aestronglyMeasurable
    · filter_upwards [] with θ
      intro _ y _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_pow]
      exact mul_le_one₀
        (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
        (by positivity) (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
    · exact continuous_const.intervalIntegrable _ _
    · filter_upwards [] with θ
      intro _ y _
      simpa only [id_eq, one_mul] using (((((hasDerivAt_id y).mul_const
        (Real.cos θ)).add_const (n * Real.pi / 2)).cos).mul_const (Real.cos θ ^ n))
  have heq : (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos (x * Real.cos θ + (n + 1) * Real.pi / 2) * Real.cos θ ^ (n + 1)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        -Real.sin (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ * Real.cos θ ^ n := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [show (n : ℝ) + 1 = (n : ℝ) + 1 by rfl]
    rw [show ((n : ℝ) + 1) * Real.pi / 2 = n * Real.pi / 2 + Real.pi / 2 by ring]
    rw [show x * Real.cos θ + (n * Real.pi / 2 + Real.pi / 2) =
      (x * Real.cos θ + n * Real.pi / 2) + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two, pow_succ]
    ring
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  rw [heq]
  exact h.2

/-- Every derivative in the angular presentation is uniformly bounded by one. -/
theorem abs_besselDerivative_le_one (n : ℕ) (x : ℝ) : |besselDerivative n x| ≤ 1 := by
  unfold besselDerivative
  rw [abs_mul]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [abs_of_pos (inv_pos.mpr hp)]
  have hi : |∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n| ≤ 2 * Real.pi := by
    calc
      _ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi,
          |Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n| := by
        simpa [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm hp.le
            (μ := volume) (f := fun θ : ℝ =>
              Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n))
      _ ≤ ∫ _ in (0 : ℝ)..2 * Real.pi, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hp.le
          (((Real.continuous_cos.comp
            ((continuous_const.mul Real.continuous_cos).add continuous_const)).mul
              (Real.continuous_cos.pow n)).abs.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro θ _
        change |Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n| ≤ 1
        rw [abs_mul, abs_pow]
        exact mul_le_one₀ (Real.abs_cos_le_one _) (by positivity)
          (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
      _ = 2 * Real.pi := by simp
  calc
    (2 * Real.pi)⁻¹ * |∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos (x * Real.cos θ + n * Real.pi / 2) * Real.cos θ ^ n|
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem hasDerivAt_besselJ0 (x : ℝ) :
    HasDerivAt besselJ0 (besselDerivative 1 x) x := by
  change HasDerivAt (besselDerivative 0) (besselDerivative 1 x) x
  simpa using hasDerivAt_besselDerivative 0 x

theorem abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 := by
  exact abs_besselDerivative_le_one 0 x

@[simp] theorem besselJ0_zero : besselJ0 0 = 1 := by
  simp only [besselJ0, besselDerivative, Nat.cast_zero, zero_mul, zero_add, Real.cos_zero,
    zero_div, one_mul, pow_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- The angular Bessel kernel satisfies the order-zero Bessel differential equation.

This identity is proved directly by integrating the derivative of
`sin θ * sin (x * cos θ)` over a full period. -/
theorem besselDifferentialEquation (x : ℝ) :
    x * besselDerivative 2 x + besselDerivative 1 x + x * besselDerivative 0 x = 0 := by
  let g : ℝ → ℝ := fun θ => Real.sin θ * Real.sin (x * Real.cos θ)
  let gp : ℝ → ℝ := fun θ =>
    Real.cos θ * Real.sin (x * Real.cos θ) -
      x * Real.sin θ ^ 2 * Real.cos (x * Real.cos θ)
  have hgderiv (θ : ℝ) : HasDerivAt g (gp θ) θ := by
    change HasDerivAt (fun θ => Real.sin θ * Real.sin (x * Real.cos θ)) (gp θ) θ
    refine ((Real.hasDerivAt_sin θ).mul
      ((((hasDerivAt_const θ x).mul (Real.hasDerivAt_cos θ)).sin))).congr_deriv ?_
    dsimp [gp]
    ring
  have hgint : ∫ θ in (0 : ℝ)..2 * Real.pi, gp θ = 0 := by
    have hgpcont : Continuous gp := by
      dsimp [gp]
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hgderiv θ)
      (hgpcont.intervalIntegrable _ _)]
    simp [g, Real.sin_two_pi]
  unfold besselDerivative
  norm_num only [Nat.cast_ofNat, pow_zero, pow_one]
  rw [show (1 : ℝ) * Real.pi / 2 = Real.pi / 2 by ring,
    show (2 : ℝ) * Real.pi / 2 = Real.pi by ring]
  simp only [Real.cos_add_pi_div_two, Real.cos_add_pi, neg_mul]
  have hcombine :
      x * (∫ θ in (0 : ℝ)..2 * Real.pi,
          -(Real.cos (x * Real.cos θ)) * Real.cos θ ^ 2) +
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          -(Real.sin (x * Real.cos θ)) * Real.cos θ) +
        x * (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos (x * Real.cos θ)) =
      -(∫ θ in (0 : ℝ)..2 * Real.pi, gp θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    let f2 : ℝ → ℝ := fun θ => x * (-(Real.cos (x * Real.cos θ)) * Real.cos θ ^ 2)
    let f1 : ℝ → ℝ := fun θ => -(Real.sin (x * Real.cos θ)) * Real.cos θ
    let f0 : ℝ → ℝ := fun θ => x * Real.cos (x * Real.cos θ)
    change (∫ θ in (0 : ℝ)..2 * Real.pi, f2 θ) +
        (∫ θ in (0 : ℝ)..2 * Real.pi, f1 θ) +
        (∫ θ in (0 : ℝ)..2 * Real.pi, f0 θ) =
      -(∫ θ in (0 : ℝ)..2 * Real.pi, gp θ)
    have hf2 : IntervalIntegrable f2 volume 0 (2 * Real.pi) := by
      exact (by dsimp [f2]; fun_prop : Continuous f2).intervalIntegrable _ _
    have hf1 : IntervalIntegrable f1 volume 0 (2 * Real.pi) := by
      exact (by dsimp [f1]; fun_prop : Continuous f1).intervalIntegrable _ _
    have hf0 : IntervalIntegrable f0 volume 0 (2 * Real.pi) := by
      exact (by dsimp [f0]; fun_prop : Continuous f0).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hf2 hf1,
      ← intervalIntegral.integral_add (hf2.add hf1) hf0,
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [f2, f1, f0, gp]
    ring_nf
    rw [Real.sin_sq]
    ring
  simp only [zero_mul, zero_div, add_zero, one_mul] at ⊢
  have hc : x * (∫ θ in (0 : ℝ)..2 * Real.pi,
          -(Real.cos (x * Real.cos θ) * Real.cos θ ^ 2)) +
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          -(Real.sin (x * Real.cos θ) * Real.cos θ)) +
        x * (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos (x * Real.cos θ)) = 0 := by
    have hc' := hcombine
    rw [hgint, neg_zero] at hc'
    simpa only [neg_mul] using hc'
  have hscaled := congrArg (fun z : ℝ => (2 * Real.pi)⁻¹ * z) hc
  convert hscaled using 1 <;> ring

/-- The differentiated Bessel equation, in a form suitable for recursively computing every
higher derivative from the preceding two. -/
theorem besselDerivative_recurrence (n : ℕ) (x : ℝ) :
    x * besselDerivative (n + 2) x + (n + 1) * besselDerivative (n + 1) x +
      x * besselDerivative n x + n * besselDerivative (n - 1) x = 0 := by
  induction n generalizing x with
  | zero =>
      simpa using besselDifferentialEquation x
  | succ n ih =>
      let F : ℝ → ℝ := fun y =>
        y * besselDerivative (n + 2) y + (n + 1) * besselDerivative (n + 1) y +
          y * besselDerivative n y + n * besselDerivative (n - 1) y
      have hF : F = fun _ => 0 := by
        funext y
        exact ih y
      have hd : HasDerivAt F
          (x * besselDerivative (n + 3) x + (n + 2) * besselDerivative (n + 2) x +
            x * besselDerivative (n + 1) x + (n + 1) * besselDerivative n x) x := by
        change HasDerivAt (fun y =>
          y * besselDerivative (n + 2) y +
            (n + 1) * besselDerivative (n + 1) y + y * besselDerivative n y +
              n * besselDerivative (n - 1) y) _ x
        refine (((((hasDerivAt_id x).mul (hasDerivAt_besselDerivative (n + 2) x)).add
            ((hasDerivAt_const x (n + 1 : ℝ)).mul
              (hasDerivAt_besselDerivative (n + 1) x))).add
            ((hasDerivAt_id x).mul (hasDerivAt_besselDerivative n x))).add
            ((hasDerivAt_const x (n : ℝ)).mul
              (hasDerivAt_besselDerivative (n - 1) x))).congr_deriv ?_
        have hpred : (n : ℝ) * besselDerivative (n - 1 + 1) x =
            n * besselDerivative n x := by
          cases n <;> simp
        push_cast
        simp only [id_eq]
        rw [hpred]
        ring
      have hz : HasDerivAt F 0 x := by
        rw [hF]
        exact hasDerivAt_const x 0
      have hzero := hd.unique hz
      push_cast at hzero ⊢
      convert hzero using 1 <;> ring

theorem besselDerivative_differentiable (n : ℕ) :
    Differentiable ℝ (besselDerivative n) :=
  fun x => (hasDerivAt_besselDerivative n x).differentiableAt

theorem deriv_besselDerivative (n : ℕ) :
    deriv (besselDerivative n) = besselDerivative (n + 1) := by
  funext x
  exact (hasDerivAt_besselDerivative n x).deriv

/-- The angular Bessel kernel is smooth to every finite order. -/
theorem besselDerivative_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (besselDerivative n) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing n with
  | zero => exact contDiff_zero.mpr (besselDerivative_differentiable n).continuous
  | succ k ih =>
      rw [show (↑(k + 1) : WithTop ℕ∞) = (↑k : WithTop ℕ∞) + 1 by norm_num,
        contDiff_succ_iff_deriv]
      refine ⟨besselDerivative_differentiable n, ?_, ?_⟩
      · simp
      · rw [deriv_besselDerivative]
        exact ih (n + 1)

theorem iteratedDeriv_besselDerivative (r n : ℕ) :
    iteratedDeriv n (besselDerivative r) = besselDerivative (r + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih, deriv_besselDerivative]
      congr 1

/-- The Taylor polynomial of `besselDerivative r` through degree `n`. -/
noncomputable def besselTaylor (r n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    besselDerivative (r + k) x * (y - x) ^ k / k.factorial

private theorem taylorWithinEval_besselDerivative (r n : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    taylorWithinEval (besselDerivative r) n (Set.uIcc x y) x y =
      besselTaylor r n x y := by
  induction n with
  | zero => simp [besselTaylor]
  | succ n ih =>
      rw [taylorWithinEval_succ, ih]
      have hdegree : (↑(n + 1) : WithTop ℕ∞) ≤
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact WithTop.coe_le_coe.mpr le_top
      rw [iteratedDerivWithin_eq_iteratedDeriv (n := n + 1) (uniqueDiffOn_uIcc hxy)
        (((besselDerivative_contDiff r).of_le hdegree).contDiffAt) Set.left_mem_uIcc]
      rw [iteratedDeriv_besselDerivative]
      simp only [besselTaylor, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one,
        Nat.factorial_succ, smul_eq_mul]
      congr 1 <;> push_cast <;> ring

/-- Taylor's theorem with the uniform derivative bound specialized to the Bessel kernel. -/
theorem besselTaylor_bound (r n : ℕ) (x y : ℝ) :
    |besselDerivative r y - besselTaylor r n x y| ≤
      |y - x| ^ (n + 1) / (n + 1).factorial := by
  by_cases hxy : x = y
  · subst y
    rw [besselTaylor]
    simp only [sub_self]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hne
      simp [hne]
    · simp
  · have hdegree : (↑(n + 1) : WithTop ℕ∞) ≤
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.mpr le_top
    obtain ⟨z, _, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hxy
      (((besselDerivative_contDiff r).of_le hdegree).contDiffOn)
    rw [taylorWithinEval_besselDerivative r n hxy] at hrem
    rw [hrem, abs_div, abs_mul, abs_pow]
    have hderiv : |iteratedDeriv (n + 1) (besselDerivative r) z| ≤ 1 := by
      rw [iteratedDeriv_besselDerivative]
      exact abs_besselDerivative_le_one _ _
    have hfac : |((n + 1).factorial : ℝ)| = (n + 1).factorial :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hfac]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) hderiv) (Nat.cast_nonneg _)

/-- Exact rational values of the successive Bessel derivatives at zero. -/
def besselInitial : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | n + 2 => -(n + 1) * besselInitial n / (n + 2)

private theorem besselDerivative_one_zero : besselDerivative 1 0 = 0 := by
  simp [besselDerivative]

theorem besselDerivative_zero_eq_initial (n : ℕ) :
    besselDerivative n 0 = (besselInitial n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [besselInitial, besselDerivative]
      field_simp [Real.pi_ne_zero]
  | one => simp [besselInitial, besselDerivative_one_zero]
  | more n hn _ =>
      have hrec := besselDerivative_recurrence (n + 1) 0
      simp only [zero_mul, zero_add] at hrec
      simp only [Nat.add_sub_cancel] at hrec
      rw [hn] at hrec
      have hrec' : ((n : ℝ) + 2) * besselDerivative (n + 2) 0 +
          ((n : ℝ) + 1) * (besselInitial n : ℝ) = 0 := by
        convert hrec using 1 <;> push_cast <;> ring
      rw [besselInitial]
      push_cast
      have hnpos : (0 : ℝ) < n + 2 := by positivity
      apply (eq_div_iff hnpos.ne').2
      nlinarith [hrec']

/-! ## Exact rational interval evaluation of the Bessel kernel -/

open LeanCert.Core

/-- Three consecutive rational coefficient pairs in the differentiated Bessel equation. -/
@[ext] structure BesselCoefficientState where
  previous : ℚ × ℚ
  current : ℚ × ℚ
  next : ℚ × ℚ

/-- Linear-time recurrence producing three consecutive derivative coefficients. -/
def besselCoefficientState (x : ℚ) : ℕ → BesselCoefficientState
  | 0 => ⟨(1, 0), (0, 1), (-1, -1 / x)⟩
  | n + 1 =>
      let S := besselCoefficientState x n
      let k : ℚ := n + 1
      ⟨S.current, S.next,
        (-((k + 1) * S.next.1 + x * S.current.1 + k * S.previous.1) / x,
         -((k + 1) * S.next.2 + x * S.current.2 + k * S.previous.2) / x)⟩

/-- Rational coefficients expressing the `n`th derivative at a nonzero rational centre as a
linear combination of `J₀` and `J₀'` there.  The state-machine definition is deliberately
used so that exact certificate evaluation is quadratic, rather than exponential, in the Taylor
degree. -/
def besselCoefficients (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 => (besselCoefficientState x n).next

@[simp] theorem besselCoefficientState_next (x : ℚ) (n : ℕ) :
    (besselCoefficientState x n).next = besselCoefficients x (n + 2) := by
  rw [besselCoefficients]

@[simp] theorem besselCoefficientState_current (x : ℚ) (n : ℕ) :
    (besselCoefficientState x n).current = besselCoefficients x (n + 1) := by
  rcases n with _ | n
  · rfl
  · simp [besselCoefficientState]

@[simp] theorem besselCoefficientState_previous (x : ℚ) (n : ℕ) :
    (besselCoefficientState x n).previous = besselCoefficients x n := by
  rcases n with _ | n
  · rfl
  · simp [besselCoefficientState]

theorem besselCoefficientState_eq (x : ℚ) (n : ℕ) :
    besselCoefficientState x n =
      ⟨besselCoefficients x n, besselCoefficients x (n + 1),
        besselCoefficients x (n + 2)⟩ := by
  apply BesselCoefficientState.ext <;> simp

theorem besselCoefficients_add_two (x : ℚ) (hx : x ≠ 0) (n : ℕ) :
    besselCoefficients x (n + 2) =
      (-((n + 1) * (besselCoefficients x (n + 1)).1 +
          x * (besselCoefficients x n).1 + n * (besselCoefficients x (n - 1)).1) / x,
       -((n + 1) * (besselCoefficients x (n + 1)).2 +
          x * (besselCoefficients x n).2 + n * (besselCoefficients x (n - 1)).2) / x) := by
  rcases n with _ | n
  · simp [besselCoefficients, besselCoefficientState, hx]
  · rw [besselCoefficients, besselCoefficientState, besselCoefficientState_eq]
    simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]

theorem besselDerivative_eq_coefficients (q : ℚ) (hq : q ≠ 0) (n : ℕ) :
    besselDerivative n (q : ℝ) =
      (besselCoefficients q n).1 * besselDerivative 0 q +
        (besselCoefficients q n).2 * besselDerivative 1 q := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
      rcases k with (_ | _ | n)
      · simp [besselCoefficients]
      · simp [besselCoefficients]
      · have hn1 := ih (n + 1) (by omega)
        have hn := ih n (by omega)
        have hnm1 := ih (n - 1) (by omega)
        have hr := besselDerivative_recurrence n (q : ℝ)
        rw [hn1, hn, hnm1] at hr
        rw [besselCoefficients_add_two q hq]
        push_cast
        have hqr : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
        field_simp [hqr]
        nlinarith

/-- Rational Taylor-transition coefficients at centre `q`, offset `h`, through degree `n`. -/
def besselTransition (q h : ℚ) (r n : ℕ) : ℚ × ℚ :=
  (∑ k ∈ Finset.range (n + 1),
      (besselCoefficients q (r + k)).1 * h ^ k / k.factorial,
   ∑ k ∈ Finset.range (n + 1),
      (besselCoefficients q (r + k)).2 * h ^ k / k.factorial)

/-- One linear-time update of the three consecutive coefficient pairs. -/
def besselCoefficientStateStep (x : ℚ) (n : ℕ) (S : BesselCoefficientState) :
    BesselCoefficientState :=
  let k : ℚ := n + 1
  ⟨S.current, S.next,
    (-((k + 1) * S.next.1 + x * S.current.1 + k * S.previous.1) / x,
     -((k + 1) * S.next.2 + x * S.current.2 + k * S.previous.2) / x)⟩

@[simp] theorem besselCoefficientState_succ (x : ℚ) (n : ℕ) :
    besselCoefficientState x (n + 1) =
      besselCoefficientStateStep x n (besselCoefficientState x n) := by
  rfl

/-- Accumulator used by the executable, linear-time Taylor transition. -/
structure BesselTransitionState where
  coefficients : BesselCoefficientState
  power : ℚ
  factorial : ℚ
  zeroSum : ℚ × ℚ
  oneSum : ℚ × ℚ

/-- After `k` steps this contains the first `k` Taylor terms for both `J₀` and `J₀'`. -/
def besselTransitionLoop (q h : ℚ) : ℕ → BesselTransitionState
  | 0 => ⟨besselCoefficientState q 0, 1, 1, (0, 0), (0, 0)⟩
  | k + 1 =>
      let S := besselTransitionLoop q h k
      let z := S.power / S.factorial
      ⟨besselCoefficientStateStep q k S.coefficients,
       S.power * h, S.factorial * (k + 1),
       (S.zeroSum.1 + S.coefficients.previous.1 * z,
        S.zeroSum.2 + S.coefficients.previous.2 * z),
       (S.oneSum.1 + S.coefficients.current.1 * z,
        S.oneSum.2 + S.coefficients.current.2 * z)⟩

@[simp] theorem besselTransitionLoop_coefficients (q h : ℚ) (k : ℕ) :
    (besselTransitionLoop q h k).coefficients = besselCoefficientState q k := by
  induction k with
  | zero => simp [besselTransitionLoop]
  | succ k ih => simp [besselTransitionLoop, ih]

@[simp] theorem besselTransitionLoop_power (q h : ℚ) (k : ℕ) :
    (besselTransitionLoop q h k).power = h ^ k := by
  induction k with
  | zero => simp [besselTransitionLoop]
  | succ k ih => simp [besselTransitionLoop, ih, pow_succ]

@[simp] theorem besselTransitionLoop_factorial (q h : ℚ) (k : ℕ) :
    (besselTransitionLoop q h k).factorial = k.factorial := by
  induction k with
  | zero => simp [besselTransitionLoop]
  | succ k ih =>
      simp [besselTransitionLoop, ih, Nat.factorial_succ, mul_comm]

theorem besselTransitionLoop_zeroSum (q h : ℚ) (k : ℕ) :
    (besselTransitionLoop q h k).zeroSum =
      (∑ i ∈ Finset.range k, (besselCoefficients q i).1 * h ^ i / i.factorial,
       ∑ i ∈ Finset.range k, (besselCoefficients q i).2 * h ^ i / i.factorial) := by
  induction k with
  | zero => simp [besselTransitionLoop]
  | succ k ih =>
      rw [besselTransitionLoop]
      simp only [ih, besselTransitionLoop_power, besselTransitionLoop_factorial,
        besselTransitionLoop_coefficients, besselCoefficientState_previous]
      simp [Finset.sum_range_succ]
      constructor <;> ring

theorem besselTransitionLoop_oneSum (q h : ℚ) (k : ℕ) :
    (besselTransitionLoop q h k).oneSum =
      (∑ i ∈ Finset.range k, (besselCoefficients q (1 + i)).1 * h ^ i / i.factorial,
       ∑ i ∈ Finset.range k, (besselCoefficients q (1 + i)).2 * h ^ i / i.factorial) := by
  induction k with
  | zero => simp [besselTransitionLoop]
  | succ k ih =>
      rw [besselTransitionLoop]
      simp only [ih, besselTransitionLoop_power, besselTransitionLoop_factorial,
        besselTransitionLoop_coefficients, besselCoefficientState_current]
      simp [Finset.sum_range_succ, add_comm]
      constructor <;> ring

/-- Executable transition for precisely the two rows used in a Bessel state. -/
def besselTransitionFast (q h : ℚ) (n : ℕ) : (ℚ × ℚ) × (ℚ × ℚ) :=
  let S := besselTransitionLoop q h (n + 1)
  (S.zeroSum, S.oneSum)

theorem besselTransitionFast_zero (q h : ℚ) (n : ℕ) :
    (besselTransitionFast q h n).1 = besselTransition q h 0 n := by
  rw [besselTransitionFast, besselTransitionLoop_zeroSum, besselTransition]
  simp

theorem besselTransitionFast_one (q h : ℚ) (n : ℕ) :
    (besselTransitionFast q h n).2 = besselTransition q h 1 n := by
  rw [besselTransitionFast, besselTransitionLoop_oneSum, besselTransition]

theorem besselTaylor_eq_transition (q h : ℚ) (hq : q ≠ 0) (r n : ℕ) :
    besselTaylor r n q (q + h) =
      (besselTransition q h r n).1 * besselDerivative 0 q +
        (besselTransition q h r n).2 * besselDerivative 1 q := by
  rw [besselTaylor]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      besselDerivative (r + k) (q : ℝ) *
        ((q : ℝ) + (h : ℝ) - (q : ℝ)) ^ k / k.factorial) =
      ∑ k ∈ Finset.range (n + 1),
        (((besselCoefficients q (r + k)).1 * besselDerivative 0 q +
          (besselCoefficients q (r + k)).2 * besselDerivative 1 q) *
            ((q : ℝ) + (h : ℝ) - (q : ℝ)) ^ k / k.factorial) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [besselDerivative_eq_coefficients q hq]
  rw [hsum, besselTransition]
  push_cast
  simp only [add_sub_cancel_left, add_mul, add_div, Finset.sum_add_distrib]
  congr 1
  · calc
      (∑ k ∈ Finset.range (n + 1),
          (besselCoefficients q (r + k)).1 * besselDerivative 0 q * (h : ℝ) ^ k /
            k.factorial) =
          ∑ k ∈ Finset.range (n + 1),
            ((besselCoefficients q (r + k)).1 * (h : ℝ) ^ k / k.factorial) *
              besselDerivative 0 q := by
                apply Finset.sum_congr rfl
                intro k _
                ring
      _ = _ := (Finset.sum_mul (Finset.range (n + 1))
        (fun k => ((besselCoefficients q (r + k)).1 : ℝ) * (h : ℝ) ^ k / k.factorial)
        (besselDerivative 0 q)).symm
  · calc
      (∑ k ∈ Finset.range (n + 1),
          (besselCoefficients q (r + k)).2 * besselDerivative 1 q * (h : ℝ) ^ k /
            k.factorial) =
          ∑ k ∈ Finset.range (n + 1),
            ((besselCoefficients q (r + k)).2 * (h : ℝ) ^ k / k.factorial) *
              besselDerivative 1 q := by
                apply Finset.sum_congr rfl
                intro k _
                ring
      _ = _ := (Finset.sum_mul (Finset.range (n + 1))
        (fun k => ((besselCoefficients q (r + k)).2 : ℝ) * (h : ℝ) ^ k / k.factorial)
        (besselDerivative 1 q)).symm

/-- The Taylor transition at the origin, whose derivatives are exactly rational. -/
def besselZeroTransition (h : ℚ) (r n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), besselInitial (r + k) * h ^ k / k.factorial

theorem besselTaylor_zero_eq_transition (h : ℚ) (r n : ℕ) :
    besselTaylor r n 0 h = (besselZeroTransition h r n : ℝ) := by
  rw [besselTaylor]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      besselDerivative (r + k) 0 * (h - 0) ^ k / k.factorial) =
      ∑ k ∈ Finset.range (n + 1),
        (besselInitial (r + k) : ℝ) * (h - 0) ^ k / k.factorial := by
    apply Finset.sum_congr rfl
    intro k _
    rw [besselDerivative_zero_eq_initial]
  rw [hsum, besselZeroTransition]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- A symmetric rational error interval. -/
def rationalErrorInterval (e : ℚ) : IntervalRat where
  lo := -|e|
  hi := |e|
  le := neg_nonpos.mpr (abs_nonneg e) |>.trans (abs_nonneg e)

/-- Enlarge a rational interval by a symmetric rational error. -/
def widenInterval (e : ℚ) (I : IntervalRat) : IntervalRat :=
  IntervalRat.add I (rationalErrorInterval e)

theorem mem_rationalErrorInterval {x : ℝ} {e : ℚ} (hx : |x| ≤ |(e : ℝ)|) :
    x ∈ rationalErrorInterval e := by
  simp only [IntervalRat.mem_def, rationalErrorInterval, Rat.cast_neg, Rat.cast_abs]
  exact (abs_le.mp hx)

theorem mem_widenInterval {x y : ℝ} {e : ℚ} {I : IntervalRat}
    (hy : y ∈ I) (hxy : |x - y| ≤ |(e : ℝ)|) : x ∈ widenInterval e I := by
  have hd : x - y ∈ rationalErrorInterval e := mem_rationalErrorInterval hxy
  rw [show x = y + (x - y) by ring]
  exact IntervalRat.mem_add hy hd

/-- Interval evaluation of a rational linear form in the two Bessel state coordinates. -/
def linearInterval (a b : ℚ) (S : IntervalRat × IntervalRat) : IntervalRat :=
  IntervalRat.add (IntervalRat.scale a S.1) (IntervalRat.scale b S.2)

theorem mem_linearInterval {x y : ℝ} {a b : ℚ} {S : IntervalRat × IntervalRat}
    (hx : x ∈ S.1) (hy : y ∈ S.2) :
    (a : ℝ) * x + (b : ℝ) * y ∈ linearInterval a b S := by
  exact IntervalRat.mem_add (IntervalRat.mem_scale a hx) (IntervalRat.mem_scale b hy)

/-- A certified interval state for the pair `(J₀(x), J₀'(x))`. -/
def BesselStateValid (x : ℝ) (S : IntervalRat × IntervalRat) : Prop :=
  besselDerivative 0 x ∈ S.1 ∧ besselDerivative 1 x ∈ S.2

/-- The exact interval transition with a Taylor remainder of order `n+1`. -/
def besselIntervalStep (q h : ℚ) (n : ℕ) (S : IntervalRat × IntervalRat) :
    IntervalRat × IntervalRat :=
  let e : ℚ := |h| ^ (n + 1) / (n + 1).factorial
  let T := besselTransitionFast q h n
  (widenInterval e (linearInterval T.1.1 T.1.2 S),
   widenInterval e (linearInterval T.2.1 T.2.2 S))

theorem besselIntervalStep_valid (q h : ℚ) (hq : q ≠ 0) (n : ℕ)
    (S : IntervalRat × IntervalRat) (hS : BesselStateValid q S) :
    BesselStateValid (q + h : ℚ) (besselIntervalStep q h n S) := by
  constructor
  · apply mem_widenInterval
      (mem_linearInterval hS.1 hS.2)
    rw [besselTransitionFast_zero]
    rw [← besselTaylor_eq_transition q h hq 0 n]
    have he : (0 : ℚ) ≤ |h| ^ (n + 1) / (n + 1).factorial := by positivity
    have habs : |((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr he)
    rw [habs]
    have ht := besselTaylor_bound 0 n (q : ℝ) (q + h : ℚ)
    rw [show ((q + h : ℚ) : ℝ) - (q : ℝ) = (h : ℝ) by push_cast; ring] at ht
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast,
      Rat.cast_add, Rat.cast_sub] using ht
  · apply mem_widenInterval
      (mem_linearInterval hS.1 hS.2)
    rw [besselTransitionFast_one]
    rw [← besselTaylor_eq_transition q h hq 1 n]
    have he : (0 : ℚ) ≤ |h| ^ (n + 1) / (n + 1).factorial := by positivity
    have habs : |((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr he)
    rw [habs]
    have ht := besselTaylor_bound 1 n (q : ℝ) (q + h : ℚ)
    rw [show ((q + h : ℚ) : ℝ) - (q : ℝ) = (h : ℝ) by push_cast; ring] at ht
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast,
      Rat.cast_add, Rat.cast_sub] using ht

/-- The corresponding first interval step, based on exact derivatives at zero. -/
def besselIntervalStepZero (h : ℚ) (n : ℕ) : IntervalRat × IntervalRat :=
  let e : ℚ := |h| ^ (n + 1) / (n + 1).factorial
  (widenInterval e (IntervalRat.singleton (besselZeroTransition h 0 n)),
   widenInterval e (IntervalRat.singleton (besselZeroTransition h 1 n)))

theorem besselIntervalStepZero_valid (h : ℚ) (n : ℕ) :
    BesselStateValid (h : ℝ) (besselIntervalStepZero h n) := by
  constructor
  · apply mem_widenInterval (IntervalRat.mem_singleton _)
    rw [← besselTaylor_zero_eq_transition h 0 n]
    have he : (0 : ℚ) ≤ |h| ^ (n + 1) / (n + 1).factorial := by positivity
    have habs : |((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr he)
    rw [habs]
    have ht := besselTaylor_bound 0 n 0 (h : ℝ)
    rw [sub_zero] at ht
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast] using
      ht
  · apply mem_widenInterval (IntervalRat.mem_singleton _)
    rw [← besselTaylor_zero_eq_transition h 1 n]
    have he : (0 : ℚ) ≤ |h| ^ (n + 1) / (n + 1).factorial := by positivity
    have habs : |((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|h| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr he)
    rw [habs]
    have ht := besselTaylor_bound 1 n 0 (h : ℝ)
    rw [sub_zero] at ht
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast] using
      ht

/-- Decidable inclusion of rational intervals. -/
def rationalIntervalSubset (I J : IntervalRat) : Bool :=
  decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

/-- An interval constructor convenient for generated rational certificates. -/
def orderedInterval (a b : ℚ) : IntervalRat :=
  ⟨min a b, max a b, min_le_max⟩

theorem mem_of_rationalIntervalSubset {x : ℝ} {I J : IntervalRat}
    (hsub : rationalIntervalSubset I J = true) (hx : x ∈ I) : x ∈ J := by
  have h : J.lo ≤ I.lo ∧ I.hi ≤ J.hi := of_decide_eq_true hsub
  exact ⟨(Rat.cast_le.mpr h.1).trans hx.1, hx.2.trans (Rat.cast_le.mpr h.2)⟩

def besselStateSubset (S T : IntervalRat × IntervalRat) : Bool :=
  rationalIntervalSubset S.1 T.1 && rationalIntervalSubset S.2 T.2

theorem BesselStateValid.mono {x : ℝ} {S T : IntervalRat × IntervalRat}
    (hsub : besselStateSubset S T = true) (hS : BesselStateValid x S) :
    BesselStateValid x T := by
  simp only [besselStateSubset, Bool.and_eq_true] at hsub
  exact ⟨mem_of_rationalIntervalSubset hsub.1 hS.1,
    mem_of_rationalIntervalSubset hsub.2 hS.2⟩

end Erdos232
