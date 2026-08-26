import ErdosProblems.Erdos520.HarperPrimeBlockMeanAsymptotic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Stability of scheduled blocks away from the diagonal

The Harper application tilts at height `t` while evaluating a nearby mesh
height `u`.  This file records deterministic Lipschitz estimates which
transfer the diagonal variance and drift bounds to that off-diagonal pair.
-/

theorem abs_cos_sq_sub_cos_sq_le_two_mul_abs_sub (x z : ℝ) :
    |Real.cos x ^ 2 - Real.cos z ^ 2| ≤ 2 * |x - z| := by
  have hdiff := Real.abs_cos_sub_cos_le x z
  have hsum : |Real.cos x + Real.cos z| ≤ 2 := by
    calc
      |Real.cos x + Real.cos z| ≤
          |Real.cos x| + |Real.cos z| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one x)
        (Real.abs_cos_le_one z)
      _ = 2 := by norm_num
  rw [show Real.cos x ^ 2 - Real.cos z ^ 2 =
      (Real.cos x - Real.cos z) * (Real.cos x + Real.cos z) by ring,
    abs_mul]
  calc
    |Real.cos x - Real.cos z| * |Real.cos x + Real.cos z| ≤
        |x - z| * 2 :=
      mul_le_mul hdiff hsum (abs_nonneg _) (abs_nonneg _)
    _ = 2 * |x - z| := by ring

/-- One-prime off-diagonal variance stability. -/
theorem abs_harperLinearPrimeCenteredVariance_sub_diagonal_le
    {p : ℕ} (hp : 16 ≤ p) (t u : ℝ) :
    |harperLinearPrimeCenteredVariance p t u -
        harperLinearPrimeCenteredVariance p t t| ≤
      2 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  let q : ℝ := 1 - harperTiltBias p t ^ 2
  have hq0 : 0 ≤ q :=
    (three_fourths_le_one_sub_harperTiltBias_sq hp t).trans' (by norm_num)
  have hq1 : q ≤ 1 := one_sub_harperTiltBias_sq_le_one p t
  have harg :
      |u * Real.log (p : ℝ) - t * Real.log (p : ℝ)| =
        |u - t| * Real.log (p : ℝ) := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hlog]
  have hcos := abs_cos_sq_sub_cos_sq_le_two_mul_abs_sub
    (u * Real.log (p : ℝ)) (t * Real.log (p : ℝ))
  rw [harg] at hcos
  unfold harperLinearPrimeCenteredVariance
  rw [harperPrimeCoefficient_sq hp0, harperPrimeCoefficient_sq hp0,
    ← sub_mul, abs_mul, abs_of_nonneg hq0]
  have hcoeff :
      |Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) -
          Real.cos (t * Real.log (p : ℝ)) ^ 2 / (p : ℝ)| ≤
        (2 * |u - t| * Real.log (p : ℝ)) / (p : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hpR]
    exact div_le_div_of_nonneg_right (by
      simpa only [mul_assoc] using! hcos) hpR.le
  calc
    |Real.cos (u * Real.log (p : ℝ)) ^ 2 / (p : ℝ) -
          Real.cos (t * Real.log (p : ℝ)) ^ 2 / (p : ℝ)| * q ≤
        ((2 * |u - t| * Real.log (p : ℝ)) / (p : ℝ)) * 1 :=
      mul_le_mul hcoeff hq1 hq0
        (by positivity)
    _ = 2 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by ring

/-- Block variance stability before specializing the prime scale. -/
theorem abs_harperLinearBlockVariance_sub_diagonal_le_sum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h16 : ∀ p ∈ S, 16 ≤ p.1) (t u : ℝ) :
    |harperLinearBlockVariance y S t u -
        harperLinearBlockVariance y S t t| ≤
      ∑ p ∈ S, 2 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := by
  unfold harperLinearBlockVariance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperLinearPrimeCenteredVariance p.1 t u -
          harperLinearPrimeCenteredVariance p.1 t t)| ≤
        ∑ p ∈ S,
          |harperLinearPrimeCenteredVariance p.1 t u -
            harperLinearPrimeCenteredVariance p.1 t t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S,
        2 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := by
      exact Finset.sum_le_sum fun p hp ↦
        abs_harperLinearPrimeCenteredVariance_sub_diagonal_le
          (h16 p hp) t u

/-- Scheduled-block variance stability, with the scale-local displacement
factored from the reciprocal prime mass. -/
theorem abs_harperScheduledLinearBlockVariance_sub_diagonal_le
    (y j : ℕ) (t u : ℝ) :
    |harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t u -
        harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t| ≤
      (2 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
  have hraw := abs_harperLinearBlockVariance_sub_diagonal_le_sum y
    (harperScheduledPrimeBlock y j)
    (fun p hp ↦ sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp) t u
  calc
    |harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t u -
        harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t| ≤
      ∑ p ∈ harperScheduledPrimeBlock y j,
        2 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := hraw
    _ ≤ ∑ p ∈ harperScheduledPrimeBlock y j,
        (2 * |u - t| *
          Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
            (p.1 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 < p.1 := by
        have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega
      have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp0
      have hpB : p.1 ≤ harperBlockEndpoint (j + 1) :=
        (mem_harperScheduledPrimeBlock p).mp hp |>.2
      have hpBR : (p.1 : ℝ) ≤ harperBlockEndpoint (j + 1) := by
        exact_mod_cast hpB
      have hlog : Real.log (p.1 : ℝ) ≤
          Real.log (harperBlockEndpoint (j + 1) : ℝ) :=
        Real.log_le_log hpR hpBR
      have hmul : 2 * |u - t| * Real.log (p.1 : ℝ) ≤
          2 * |u - t| *
            Real.log (harperBlockEndpoint (j + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      calc
        2 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) ≤
            (2 * |u - t| *
              Real.log (harperBlockEndpoint (j + 1) : ℝ)) /
                (p.1 : ℝ) :=
          div_le_div_of_nonneg_right hmul hpR.le
        _ = (2 * |u - t| *
              Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
                (p.1 : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ = (2 * |u - t| *
          Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
      rw [Finset.mul_sum]

theorem abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
    (y j : ℕ) (t u δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hmass : (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) ≤
      (3 / 2 : ℝ))
    (hscale : |u - t| *
      Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ δ) :
    |harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t u -
        harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t| ≤
      3 * δ := by
  have hmass0 : 0 ≤
      ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
    Finset.sum_nonneg fun p _hp ↦ by positivity
  have hscale2 :
      2 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
        2 * δ := by nlinarith
  calc
    |harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t u -
        harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t| ≤
      (2 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      abs_harperScheduledLinearBlockVariance_sub_diagonal_le y j t u
    _ ≤ (2 * δ) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hscale2 hmass0
    _ ≤ (2 * δ) * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 3 * δ := by ring

/-- A scale-local mesh displacement preserves a uniformly nondegenerate
variance window. -/
theorem exists_eventually_harperScheduledOffDiagonalVariance_quarter_half
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            (1 / 4 : ℝ) <
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t u ∧
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t u < 1 / 2 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨max Jmass Jdiag, ?_⟩
  intro j hj y hy t htLower htUpper u hscale
  have hjmass : Jmass ≤ j := (le_max_left Jmass Jdiag).trans hj
  have hjdiag : Jdiag ≤ j := (le_max_right Jmass Jdiag).trans hj
  have hdiag := hJdiag j hjdiag y hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j hjmass y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-! ## Quadratic logarithmic drift -/

theorem abs_harperLinearPrimeMean_sub_diagonal_le
    {p : ℕ} (hp : 0 < p) (t u : ℝ) :
    |harperLinearPrimeMean p t u - harperLinearPrimeMean p t t| ≤
      2 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have harg :
      |u * Real.log (p : ℝ) - t * Real.log (p : ℝ)| =
        |u - t| * Real.log (p : ℝ) := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hlog]
  have hcos := Real.abs_cos_sub_cos_le
    (u * Real.log (p : ℝ)) (t * Real.log (p : ℝ))
  rw [harg] at hcos
  have hbias := abs_harperTiltBias_le hp t
  unfold harperLinearPrimeMean
  rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hsqrt]
  calc
    |harperTiltBias p t| *
        (|Real.cos (u * Real.log (p : ℝ)) -
            Real.cos (t * Real.log (p : ℝ))| /
          Real.sqrt (p : ℝ)) ≤
      (2 * (Real.sqrt (p : ℝ))⁻¹) *
        ((|u - t| * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ)) := by
      apply mul_le_mul hbias
      · exact div_le_div_of_nonneg_right hcos hsqrt.le
      · positivity
      · positivity
    _ = 2 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (2 * (Real.sqrt (p : ℝ))⁻¹) *
            (|u - t| * Real.log (p : ℝ) *
              (Real.sqrt (p : ℝ))⁻¹) =
          2 * |u - t| * Real.log (p : ℝ) *
            ((Real.sqrt (p : ℝ))⁻¹ ^ 2) := by ring
        _ = 2 * |u - t| * Real.log (p : ℝ) * (p : ℝ)⁻¹ := by
          rw [inv_pow, hsqrtSq]

theorem abs_harperPrimeSecondHarmonic_sub_diagonal_le
    {p : ℕ} (hp : 0 < p) (t u : ℝ) :
    |harperPrimeSecondHarmonic p u - harperPrimeSecondHarmonic p t| ≤
      |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have harg :
      |2 * (u * Real.log (p : ℝ)) -
          2 * (t * Real.log (p : ℝ))| =
        2 * (|u - t| * Real.log (p : ℝ)) := by
    rw [show 2 * (u * Real.log (p : ℝ)) -
        2 * (t * Real.log (p : ℝ)) =
      2 * ((u - t) * Real.log (p : ℝ)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_mul, abs_of_nonneg hlog]
  have hcos := Real.abs_cos_sub_cos_le
    (2 * (u * Real.log (p : ℝ)))
    (2 * (t * Real.log (p : ℝ)))
  rw [harg] at hcos
  unfold harperPrimeSecondHarmonic
  rw [← sub_div, abs_div, abs_of_pos (by positivity :
    (0 : ℝ) < 2 * (p : ℝ))]
  calc
    |Real.cos (2 * (u * Real.log (p : ℝ))) -
        Real.cos (2 * (t * Real.log (p : ℝ)))| /
          (2 * (p : ℝ)) ≤
      (2 * (|u - t| * Real.log (p : ℝ))) /
          (2 * (p : ℝ)) :=
      div_le_div_of_nonneg_right hcos (by positivity)
    _ = |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
      field_simp

theorem abs_harperPrimeMainMean_sub_diagonal_le
    {p : ℕ} (hp : 0 < p) (t u : ℝ) :
    |(harperLinearPrimeMean p t u - harperPrimeSecondHarmonic p u) -
        (harperLinearPrimeMean p t t - harperPrimeSecondHarmonic p t)| ≤
      3 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by
  have hlinear := abs_harperLinearPrimeMean_sub_diagonal_le hp t u
  have hsecond := abs_harperPrimeSecondHarmonic_sub_diagonal_le hp t u
  calc
    |(harperLinearPrimeMean p t u - harperPrimeSecondHarmonic p u) -
        (harperLinearPrimeMean p t t - harperPrimeSecondHarmonic p t)| =
      |(harperLinearPrimeMean p t u - harperLinearPrimeMean p t t) -
        (harperPrimeSecondHarmonic p u -
          harperPrimeSecondHarmonic p t)| := by
      congr 1
      ring
    _ ≤ |harperLinearPrimeMean p t u - harperLinearPrimeMean p t t| +
        |harperPrimeSecondHarmonic p u -
          harperPrimeSecondHarmonic p t| := abs_sub _ _
    _ ≤ (2 * |u - t| * Real.log (p : ℝ) / (p : ℝ)) +
        (|u - t| * Real.log (p : ℝ) / (p : ℝ)) :=
      add_le_add hlinear hsecond
    _ = 3 * |u - t| * Real.log (p : ℝ) / (p : ℝ) := by ring

theorem abs_harperLogMainBlockMean_sub_diagonal_le_sum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (hpos : ∀ p ∈ S, 0 < p.1) (t u : ℝ) :
    |harperLogMainBlockMean y S t u -
        harperLogMainBlockMean y S t t| ≤
      ∑ p ∈ S, 3 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := by
  unfold harperLogMainBlockMean
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        ((harperLinearPrimeMean p.1 t u - harperPrimeSecondHarmonic p.1 u) -
          (harperLinearPrimeMean p.1 t t -
            harperPrimeSecondHarmonic p.1 t))| ≤
      ∑ p ∈ S,
        |(harperLinearPrimeMean p.1 t u -
            harperPrimeSecondHarmonic p.1 u) -
          (harperLinearPrimeMean p.1 t t -
            harperPrimeSecondHarmonic p.1 t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S,
        3 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := by
      exact Finset.sum_le_sum fun p hp ↦
        abs_harperPrimeMainMean_sub_diagonal_le (hpos p hp) t u

theorem abs_harperScheduledLogMainBlockMean_sub_diagonal_le
    (y j : ℕ) (t u : ℝ) :
    |harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t u -
        harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t| ≤
      (3 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
  have hraw := abs_harperLogMainBlockMean_sub_diagonal_le_sum y
    (harperScheduledPrimeBlock y j)
    (fun p hp ↦ by
      have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
      omega) t u
  calc
    |harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t u -
        harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t| ≤
      ∑ p ∈ harperScheduledPrimeBlock y j,
        3 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) := hraw
    _ ≤ ∑ p ∈ harperScheduledPrimeBlock y j,
        (3 * |u - t| *
          Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
            (p.1 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 < p.1 := by
        have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega
      have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp0
      have hpB : p.1 ≤ harperBlockEndpoint (j + 1) :=
        (mem_harperScheduledPrimeBlock p).mp hp |>.2
      have hpBR : (p.1 : ℝ) ≤ harperBlockEndpoint (j + 1) := by
        exact_mod_cast hpB
      have hlog : Real.log (p.1 : ℝ) ≤
          Real.log (harperBlockEndpoint (j + 1) : ℝ) :=
        Real.log_le_log hpR hpBR
      have hmul : 3 * |u - t| * Real.log (p.1 : ℝ) ≤
          3 * |u - t| *
            Real.log (harperBlockEndpoint (j + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      calc
        3 * |u - t| * Real.log (p.1 : ℝ) / (p.1 : ℝ) ≤
            (3 * |u - t| *
              Real.log (harperBlockEndpoint (j + 1) : ℝ)) /
                (p.1 : ℝ) :=
          div_le_div_of_nonneg_right hmul hpR.le
        _ = (3 * |u - t| *
              Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
                (p.1 : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ = (3 * |u - t| *
          Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
      rw [Finset.mul_sum]

theorem abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
    (y j : ℕ) (t u δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hmass : (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) ≤
      (3 / 2 : ℝ))
    (hscale : |u - t| *
      Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ δ) :
    |harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t u -
        harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t| ≤
      (9 / 2 : ℝ) * δ := by
  have hmass0 : 0 ≤
      ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
    Finset.sum_nonneg fun p _hp ↦ by positivity
  have hscale3 :
      3 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
        3 * δ := by nlinarith
  calc
    |harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t u -
        harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t| ≤
      (3 * |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      abs_harperScheduledLogMainBlockMean_sub_diagonal_le y j t u
    _ ≤ (3 * δ) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hscale3 hmass0
    _ ≤ (3 * δ) * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (9 / 2 : ℝ) * δ := by ring

/-- The same local mesh condition preserves a positive, bounded
off-diagonal quadratic drift. -/
theorem exists_eventually_harperScheduledOffDiagonalMainMean_threeEighths_nineEighths
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            (3 / 8 : ℝ) <
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t u ∧
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t u < 9 / 8 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_eventually_harperScheduledDiagonalMainMean_half_one M
  refine ⟨max Jmass Jdiag, ?_⟩
  intro j hj y hy t htLower htUpper u hscale
  have hjmass : Jmass ≤ j := (le_max_left Jmass Jdiag).trans hj
  have hjdiag : Jdiag ≤ j := (le_max_right Jmass Jdiag).trans hj
  have hdiag := hJdiag j hjdiag y hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j hjmass y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-- Combined off-diagonal variance and drift window under one scale-local
closeness hypothesis. -/
theorem exists_eventually_harperScheduledOffDiagonalMoment_bounds
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            ((1 / 4 : ℝ) <
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t u ∧
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t u < 1 / 2) ∧
            ((3 / 8 : ℝ) <
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t u ∧
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t u < 9 / 8) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  obtain ⟨Jmean, hJmean⟩ :=
    exists_eventually_harperScheduledOffDiagonalMainMean_threeEighths_nineEighths M
  refine ⟨max Jvar Jmean, ?_⟩
  intro j hj y hy t htLower htUpper u hscale
  exact ⟨
    hJvar j ((le_max_left Jvar Jmean).trans hj) y hy t htLower htUpper u hscale,
    hJmean j ((le_max_right Jvar Jmean).trans hj) y hy t htLower htUpper u hscale⟩

end Problem520
end Erdos
