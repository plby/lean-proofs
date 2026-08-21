import Mathlib

/-!
# Oscillatory and telescoping estimates for Erdős Problem 228

This file supplies the calculus estimates used in Claims 1--3 of the
odd-sine kernel argument.  The first result is the smooth form of BBMST
Lemma 5.9.  It is stated with equality of the endpoint cosines; intervals
whose lengths are integer multiples of `π / n` satisfy precisely that
hypothesis.  The remaining results isolate the finite telescoping step, so
that the geometric part of the construction only has to establish ordering
and endpoint bounds for its interval family.
-/

namespace Erdos228.KernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

private lemma hasDerivAt_neg_cos_div (omega : ℝ) (homega : omega ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -Real.cos (omega * y) / omega)
      (Real.sin (omega * x)) x := by
  simpa [homega] using ((hasDerivAt_const_mul omega).cos.neg.div_const omega)

/-- Smooth monotone version of BBMST Lemma 5.9.  The endpoint-cosine
hypothesis follows whenever `b - a` is an integer multiple of `π / n`.

The differentiability assumptions are exactly what is needed for the three
kernel amplitudes (`1 / sin`, `1 / sin - 1 / id`, and `1 / id`) on each
component away from their poles. -/
theorem abs_integral_mul_sin_le_of_deriv_nonneg
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ h' x)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  let omega : ℝ := 2 * (n : ℝ)
  have homega : omega ≠ 0 := by
    dsimp [omega]
    positivity
  let v : ℝ → ℝ := fun x ↦ -Real.cos (omega * x) / omega
  have hvderiv : ∀ x ∈ Icc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    intro x hx
    exact hasDerivAt_neg_cos_div omega homega x
  have hh'int : IntervalIntegrable h' volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hv'int : IntervalIntegrable (fun x ↦ Real.sin (omega * x)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hderivU : ∀ x ∈ uIcc a b, HasDerivAt h (h' x) x := by
    simpa [uIcc_of_le hab] using hderiv
  have hvderivU : ∀ x ∈ uIcc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    simpa [uIcc_of_le hab] using hvderiv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) hderivU hvderivU hh'int hv'int
  have hhprime : (∫ x in a..b, h' x) = h b - h a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderivU hh'int
  have hdiff_nonneg : 0 ≤ h b - h a := by
    rw [← hhprime]
    exact intervalIntegral.integral_nonneg hab hnonneg
  have hv_bound (x : ℝ) : |v x| ≤ 1 / omega := by
    dsimp [v]
    rw [abs_div, abs_neg, abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have hj_bound : |∫ x in a..b, h' x * v x| ≤ (h b - h a) / omega := by
    calc
      |∫ x in a..b, h' x * v x| ≤ ∫ x in a..b, |h' x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, h' x * (1 / omega) := by
        refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
        · exact (hh'int.mul_continuousOn
            (show ContinuousOn v (uIcc a b) from by
              simpa [uIcc_of_le hab] using
                ((Real.continuous_cos.comp
                  (continuous_const.mul continuous_id)).neg.div_const _).continuousOn)).abs
        · exact hh'int.mul_const _
        · intro x hx
          rw [abs_mul, abs_of_nonneg (hnonneg x hx)]
          exact mul_le_mul_of_nonneg_left (hv_bound x) (hnonneg x hx)
      _ = (h b - h a) / omega := by
        rw [intervalIntegral.integral_mul_const, hhprime]
        ring
  have hboundary :
      h b * v b - h a * v a =
        (Real.cos (omega * a) * (h a - h b)) / omega := by
    dsimp [v, omega] at hcos ⊢
    rw [hcos]
    ring
  change |∫ x in a..b, h x * Real.sin (omega * x)| ≤ |h b - h a| / n
  rw [hparts, hboundary]
  have hboundary_abs :
      |Real.cos (omega * a) * (h a - h b) / omega| ≤
        (h b - h a) / omega := by
    rw [abs_div, abs_mul, abs_sub_comm, abs_of_nonneg hdiff_nonneg,
      abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left hdiff_nonneg (Real.abs_cos_le_one _)) (by positivity)
  calc
    |Real.cos (omega * a) * (h a - h b) / omega -
        ∫ x in a..b, h' x * v x| ≤
        |Real.cos (omega * a) * (h a - h b) / omega| +
          |∫ x in a..b, h' x * v x| := abs_sub _ _
    _ ≤ (h b - h a) / omega + (h b - h a) / omega :=
      add_le_add hboundary_abs hj_bound
    _ = |h b - h a| / n := by
      rw [abs_of_nonneg hdiff_nonneg]
      dsimp [omega]
      field_simp
      ring

/-- The decreasing version of the smooth oscillatory estimate. -/
theorem abs_integral_mul_sin_le_of_deriv_nonpos
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonpos : ∀ x ∈ Icc a b, h' x ≤ 0)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  have h := abs_integral_mul_sin_le_of_deriv_nonneg
    (h := fun x ↦ -h x) (h' := fun x ↦ -h' x) hn hab
    (fun x hx ↦ (hderiv x hx).neg) hcont.neg
    (fun x hx ↦ neg_nonneg.mpr (hnonpos x hx)) hcos
  simpa only [neg_mul, intervalIntegral.integral_neg, abs_neg, neg_sub_neg,
    abs_sub_comm] using h

/-- At a point of the `π / n` grid, the endpoint cosine in the oscillatory
estimate is one. -/
theorem cos_two_n_mul_gridPoint (n : ℕ) (hn : 0 < n) (k : ℤ) :
    Real.cos ((2 * (n : ℝ)) * ((k : ℝ) * Real.pi / n)) = 1 := by
  rw [show (2 * (n : ℝ)) * ((k : ℝ) * Real.pi / n) =
      (k : ℝ) * (2 * Real.pi) by
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]
    ]
  exact Real.cos_int_mul_two_pi k

/-- BBMST Lemma 5.9 on an interval whose endpoints lie in the `π / n`
grid, for an increasing smooth amplitude. -/
theorem abs_integral_mul_sin_grid_le_of_deriv_nonneg
    {h h' : ℝ → ℝ} {r s : ℤ} {n : ℕ}
    (hn : 0 < n)
    (hrs : (r : ℝ) ≤ s)
    (hderiv : ∀ x ∈ Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n),
      HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h'
      (Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n)))
    (hnonneg : ∀ x ∈ Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n),
      0 ≤ h' x) :
    |∫ x in ((r : ℝ) * Real.pi / n)..((s : ℝ) * Real.pi / n),
      h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
        |h ((s : ℝ) * Real.pi / n) - h ((r : ℝ) * Real.pi / n)| / n := by
  apply abs_integral_mul_sin_le_of_deriv_nonneg hn
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrs Real.pi_pos.le) (Nat.cast_nonneg n)
  · exact hderiv
  · exact hcont
  · exact hnonneg
  · rw [cos_two_n_mul_gridPoint n hn s, cos_two_n_mul_gridPoint n hn r]

/-- BBMST Lemma 5.9 on a grid interval, for a decreasing smooth amplitude. -/
theorem abs_integral_mul_sin_grid_le_of_deriv_nonpos
    {h h' : ℝ → ℝ} {r s : ℤ} {n : ℕ}
    (hn : 0 < n)
    (hrs : (r : ℝ) ≤ s)
    (hderiv : ∀ x ∈ Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n),
      HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h'
      (Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n)))
    (hnonpos : ∀ x ∈ Icc ((r : ℝ) * Real.pi / n) ((s : ℝ) * Real.pi / n),
      h' x ≤ 0) :
    |∫ x in ((r : ℝ) * Real.pi / n)..((s : ℝ) * Real.pi / n),
      h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
        |h ((s : ℝ) * Real.pi / n) - h ((r : ℝ) * Real.pi / n)| / n := by
  apply abs_integral_mul_sin_le_of_deriv_nonpos hn
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrs Real.pi_pos.le) (Nat.cast_nonneg n)
  · exact hderiv
  · exact hcont
  · exact hnonpos
  · rw [cos_two_n_mul_gridPoint n hn s, cos_two_n_mul_gridPoint n hn r]

/-! ## Finite telescoping bounds -/

/-- The sum of successive variations of an increasing sequence telescopes.
This is the algebraic core of Claims 1--3. -/
theorem sum_abs_succ_sub_of_monotone (f : ℕ → ℝ) (m : ℕ)
    (hf : ∀ k < m, f k ≤ f (k + 1)) :
    ∑ k ∈ Finset.range m, |f (k + 1) - f k| = f m - f 0 := by
  calc
    ∑ k ∈ Finset.range m, |f (k + 1) - f k| =
        ∑ k ∈ Finset.range m, (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_of_nonneg (sub_nonneg.mpr (hf k (Finset.mem_range.mp hk)))]
    _ = f m - f 0 := Finset.sum_range_sub f m

/-- Antitone analogue of `sum_abs_succ_sub_of_monotone`. -/
theorem sum_abs_succ_sub_of_antitone (f : ℕ → ℝ) (m : ℕ)
    (hf : ∀ k < m, f (k + 1) ≤ f k) :
    ∑ k ∈ Finset.range m, |f (k + 1) - f k| = f 0 - f m := by
  calc
    ∑ k ∈ Finset.range m, |f (k + 1) - f k| =
        ∑ k ∈ Finset.range m, (f k - f (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_of_nonpos (sub_nonpos.mpr (hf k (Finset.mem_range.mp hk)))]
      ring
    _ = f 0 - f m := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun k ↦ -f k) m

/-- Abstract form of the telescoping estimate used for a disjoint ordered
family of intervals on one increasing branch. -/
theorem sum_interval_error_le_of_monotone_endpoints
    {m : ℕ} {A B E : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ k < m, E k ≤ (B k - A k) / n)
    (hchain : ∀ k < m, B k ≤ A (k + 1)) :
    ∑ k ∈ Finset.range m, E k ≤ (A m - A 0) / n := by
  calc
    ∑ k ∈ Finset.range m, E k ≤
        ∑ k ∈ Finset.range m, (B k - A k) / n := by
      exact Finset.sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range m, (A (k + 1) - A k) / n := by
      refine Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right ?_ (by positivity)
      exact sub_le_sub_right (hchain k (Finset.mem_range.mp hk)) _
    _ = (A m - A 0) / n := by
      rw [← Finset.sum_div]
      congr 1
      simpa using Finset.sum_range_sub A m

/-- The corresponding telescope on a decreasing branch. -/
theorem sum_interval_error_le_of_antitone_endpoints
    {m : ℕ} {A B E : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ k < m, E k ≤ (A k - B k) / n)
    (hchain : ∀ k < m, A (k + 1) ≤ B k) :
    ∑ k ∈ Finset.range m, E k ≤ (A 0 - A m) / n := by
  calc
    ∑ k ∈ Finset.range m, E k ≤
        ∑ k ∈ Finset.range m, (A k - B k) / n := by
      exact Finset.sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range m, (A k - A (k + 1)) / n := by
      refine Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right ?_ (by positivity)
      exact sub_le_sub_left (hchain k (Finset.mem_range.mp hk)) _
    _ = (A 0 - A m) / n := by
      rw [← Finset.sum_div]
      congr 1
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun k ↦ -A k) m

/-- A two-branch telescope.  This is the common combinatorial conclusion of
Claims 1 and 3: after splitting at the single turning point or pole, each
side contributes only its endpoint variation. -/
theorem two_branch_error_le
    {left right leftVariation rightVariation : ℝ} {n : ℕ}
    (hleft : left ≤ leftVariation / n)
    (hright : right ≤ rightVariation / n) :
    left + right ≤ (leftVariation + rightVariation) / n := by
  calc
    left + right ≤ leftVariation / n + rightVariation / n := add_le_add hleft hright
    _ = (leftVariation + rightVariation) / n := by ring

/-- Explicit endpoint computation for Claim 2. -/
theorem claim2_endpoint_variation :
    (1 / Real.sin (Real.pi / 2) - 1 / (Real.pi / 2)) -
      (1 / Real.sin (-Real.pi / 2) - 1 / (-Real.pi / 2)) =
        2 - 4 / Real.pi := by
  rw [Real.sin_pi_div_two]
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.sin_neg,
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  ring

/-- Claim 2 after the monotone pieces have been telescoped. -/
theorem claim2_replacement_error_le {n : ℕ} {error : ℝ}
    (herror : error ≤
      (((1 / Real.sin (Real.pi / 2) - 1 / (Real.pi / 2)) -
        (1 / Real.sin (-Real.pi / 2) - 1 / (-Real.pi / 2))) / n)) :
    error ≤ (2 - 4 / Real.pi) / n := by
  rwa [claim2_endpoint_variation] at herror

/-- Claim 1 after the two monotone tails and the unique turning-point
interval have been estimated. -/
theorem claim1_reflected_error_le {n : ℕ} {eta left right crossing : ℝ}
    (hleft : left ≤ 1 / (n * Real.sin eta))
    (hright : right ≤ 1 / (n * Real.sin eta))
    (hcrossing : crossing ≤ 12 * Real.pi / n) :
    left + right + crossing ≤
      2 / (n * Real.sin eta) + 12 * Real.pi / n := by
  calc
    left + right + crossing ≤
        1 / (n * Real.sin eta) + 1 / (n * Real.sin eta) + 12 * Real.pi / n := by
      linarith
    _ = 2 / (n * Real.sin eta) + 12 * Real.pi / n := by ring

/-- Explicit reciprocal-distance bound in Claim 3: two branches, each at
distance at least `π / n`, contribute at most `1 / π`. -/
theorem claim3_two_sides_le_two_div_pi {n : ℕ} (hn : 0 < n)
    {left right : ℝ} (hleft : left ≤ (n / Real.pi) / n)
    (hright : right ≤ (n / Real.pi) / n) :
    left + right ≤ 2 / Real.pi := by
  calc
    left + right ≤ (n / Real.pi) / n + (n / Real.pi) / n := add_le_add hleft hright
    _ = 2 / Real.pi := by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [Real.pi_ne_zero, hn']
      ring

/-! ## Assembly of the three kernel claims -/

/-- Once Claims 1--3 bound the total kernel error by `2 / 3`, the self
interval contribution from BBMST Lemma 5.8 gives the normalized lower bound
`2 / 3` and the convenient global upper bound `5`.  This formulation keeps
the bookkeeping of the signed interval family separate from the analytic
estimates above. -/
theorem normalized_kernel_bounds {value main error : ℝ}
    (hvalue : value = main + error)
    (hmain_lower : 4 / 3 ≤ |main|)
    (hmain_upper : |main| ≤ 4)
    (herror : |error| ≤ 2 / 3) :
    2 / 3 ≤ |value| ∧ |value| ≤ 5 := by
  subst value
  constructor
  · have hreverse : |main| ≤ |main + error| + |error| := by
      calc
        |main| = |(main + error) - error| := by ring_nf
        _ ≤ |main + error| + |error| := abs_sub _ _
    linarith
  · have hforward : |main + error| ≤ |main| + |error| :=
      abs_add_le main error
    linarith

end Erdos228.KernelClaims
