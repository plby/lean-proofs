import ErdosProblems.Erdos543.PoissonAsymptotics

/-!
# Factorial tails at the growing Poisson cutoff

This file proves that the Taylor remainder used in the relative
Bonferroni estimate tends to zero.  The argument needs only the elementary
lower bound

`r! * (r + 1) ^ (r + 1) <= (2 * r + 1)!`.

The first factor of the resulting quotient is bounded by `exp lambda`; the
second is a geometric power because the collision parameter is little-oh of
the Poisson cutoff.
-/

open Filter
open scoped Topology

namespace Erdos543

noncomputable section

/-- Split a Taylor coefficient after its first `r` factors. -/
lemma pow_div_factorial_two_mul_add_one_le
    (lambda : ℝ) (r : ℕ) (hlambda : 0 ≤ lambda) :
    lambda ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) ≤
      Real.exp lambda * (lambda / (r + 1 : ℕ)) ^ (r + 1) := by
  have hfacNat :
      r.factorial * (r + 1) ^ (r + 1) ≤ (2 * r + 1).factorial := by
    simpa only [show r + (r + 1) = 2 * r + 1 by omega] using
      (Nat.factorial_mul_pow_le_factorial (m := r) (n := r + 1))
  have hfac :
      (r.factorial : ℝ) * ((r + 1 : ℕ) : ℝ) ^ (r + 1) ≤
        ((2 * r + 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hdenPos :
      0 < (r.factorial : ℝ) * ((r + 1 : ℕ) : ℝ) ^ (r + 1) := by
    positivity
  calc
    lambda ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) ≤
        lambda ^ (2 * r + 1) /
          ((r.factorial : ℝ) * ((r + 1 : ℕ) : ℝ) ^ (r + 1)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hlambda _)
        hdenPos hfac
    _ = (lambda ^ r / (r.factorial : ℝ)) *
        (lambda / (r + 1 : ℕ)) ^ (r + 1) := by
      rw [show 2 * r + 1 = r + (r + 1) by omega, pow_add, div_pow]
      field_simp
    _ ≤ Real.exp lambda * (lambda / (r + 1 : ℕ)) ^ (r + 1) := by
      exact mul_le_mul_of_nonneg_right
        (Real.pow_div_factorial_le_exp lambda hlambda r) (by positivity)

/-- A geometric majorant tends to zero whenever its nonnegative exponent is
eventually at most one eighth of the growing cutoff. -/
lemma tendsto_exp_two_mul_eighth_pow_poissonCutoff_zero_of_le
    (x : ℕ → ℝ) (hsmall : ∀ᶠ N : ℕ in atTop,
      x N ≤ (1 / 8 : ℝ) * (poissonCutoff N : ℝ)) :
    Tendsto (fun N : ℕ ↦
      Real.exp (2 * x N) *
        ((1 : ℝ) / 8) ^ (poissonCutoff N + 1))
      atTop (nhds 0) := by
  let q : ℝ := Real.exp ((1 : ℝ) / 4) / 8
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqLt : q < 1 := by
    dsimp [q]
    rw [div_lt_one (by norm_num : (0 : ℝ) < 8)]
    calc
      Real.exp ((1 : ℝ) / 4) < Real.exp 1 :=
        Real.exp_lt_exp.mpr (by norm_num)
      _ < 3 := Real.exp_one_lt_three
      _ < 8 := by norm_num
  have hqPow : Tendsto (fun N : ℕ ↦ q ^ poissonCutoff N)
      atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLt).comp
      tendsto_poissonCutoff_atTop
  have hmajor : ∀ᶠ N : ℕ in atTop,
      Real.exp (2 * x N) *
          ((1 : ℝ) / 8) ^ (poissonCutoff N + 1) ≤
        ((1 : ℝ) / 8) * q ^ poissonCutoff N := by
    filter_upwards [hsmall] with N hN
    have hexp :
        Real.exp (2 * x N) ≤
          Real.exp ((poissonCutoff N : ℝ) / 4) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      Real.exp (2 * x N) *
          ((1 : ℝ) / 8) ^ (poissonCutoff N + 1) ≤
        Real.exp ((poissonCutoff N : ℝ) / 4) *
          ((1 : ℝ) / 8) ^ (poissonCutoff N + 1) := by
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = ((1 : ℝ) / 8) * q ^ poissonCutoff N := by
        rw [pow_succ,
          show (poissonCutoff N : ℝ) / 4 =
            (poissonCutoff N : ℝ) * ((1 : ℝ) / 4) by ring,
        Real.exp_nat_mul]
        dsimp [q]
        rw [div_pow, div_pow]
        ring_nf
  apply squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) hmajor
  simpa using hqPow.const_mul ((1 : ℝ) / 8)

/-- The geometric majorant used for the relative Poisson tail tends to
zero along the selected cutoff. -/
lemma tendsto_exp_two_collision_mul_eighth_pow_poissonCutoff_zero
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦
      Real.exp (2 * collisionParameter g N) *
        ((1 : ℝ) / 8) ^ (poissonCutoff N + 1))
      atTop (nhds 0) := by
  apply tendsto_exp_two_mul_eighth_pow_poissonCutoff_zero_of_le
    (collisionParameter g)
  exact eventually_collisionParameter_le_mul_poissonCutoff hg
    (epsilon := (1 : ℝ) / 8) (by norm_num)

/-- Generic Taylor-tail convergence from an eventual one-eighth bound on
the nonnegative parameter. -/
lemma tendsto_taylor_relative_tail_zero_of_le
    (x : ℕ → ℝ) (hx : ∀ N, 0 ≤ x N)
    (hsmall : ∀ᶠ N : ℕ in atTop,
      x N ≤ (1 / 8 : ℝ) * (poissonCutoff N : ℝ)) :
    Tendsto (fun N : ℕ ↦
      Real.exp (x N) *
        (2 * x N ^ (2 * poissonCutoff N + 1) /
          ((2 * poissonCutoff N + 1).factorial : ℝ)))
      atTop (nhds 0) := by
  have hmajor : ∀ᶠ N : ℕ in atTop,
      Real.exp (x N) *
          (2 * x N ^ (2 * poissonCutoff N + 1) /
            ((2 * poissonCutoff N + 1).factorial : ℝ)) ≤
        2 * (Real.exp (2 * x N) *
          ((1 : ℝ) / 8) ^ (poissonCutoff N + 1)) := by
    filter_upwards [hsmall] with N hsmallN
    let lambda : ℝ := x N
    let r : ℕ := poissonCutoff N
    have hlambda : 0 ≤ lambda := hx N
    have hratio : lambda / (r + 1 : ℕ) ≤ (1 : ℝ) / 8 := by
      have hrpos : (0 : ℝ) < (r + 1 : ℕ) := by positivity
      rw [div_le_iff₀ hrpos]
      dsimp [lambda, r]
      norm_num at hsmallN ⊢
      nlinarith
    have hpow :
        (lambda / (r + 1 : ℕ)) ^ (r + 1) ≤
          ((1 : ℝ) / 8) ^ (r + 1) := by
      exact pow_le_pow_left₀ (div_nonneg hlambda (by positivity)) hratio _
    have hsplit := pow_div_factorial_two_mul_add_one_le lambda r hlambda
    dsimp [lambda, r] at hsplit ⊢
    calc
      Real.exp (x N) *
          (2 * x N ^ (2 * poissonCutoff N + 1) /
            ((2 * poissonCutoff N + 1).factorial : ℝ)) =
        2 * Real.exp (x N) *
          (x N ^ (2 * poissonCutoff N + 1) /
            ((2 * poissonCutoff N + 1).factorial : ℝ)) := by ring
      _ ≤ 2 * Real.exp (x N) *
          (Real.exp (x N) *
            (x N / (poissonCutoff N + 1 : ℕ)) ^
              (poissonCutoff N + 1)) := by
        exact mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ ≤ 2 * Real.exp (x N) *
          (Real.exp (x N) *
            ((1 : ℝ) / 8) ^ (poissonCutoff N + 1)) := by
        gcongr
      _ = 2 * (Real.exp (2 * x N) *
          ((1 : ℝ) / 8) ^ (poissonCutoff N + 1)) := by
        rw [show 2 * x N = x N + x N by ring, Real.exp_add]
        ring
  apply squeeze_zero' (Eventually.of_forall fun N ↦ by
    have hxN := hx N
    positivity) hmajor
  simpa using
    (tendsto_exp_two_mul_eighth_pow_poissonCutoff_zero_of_le x hsmall).const_mul 2

/-- The relative Taylor-tail term at the growing Bonferroni order vanishes. -/
theorem tendsto_poisson_taylor_relative_tail_zero
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦
      Real.exp (collisionParameter g N) *
        (2 * collisionParameter g N ^ (2 * poissonCutoff N + 1) /
          ((2 * poissonCutoff N + 1).factorial : ℝ)))
      atTop (nhds 0) := by
  apply tendsto_taylor_relative_tail_zero_of_le
    (collisionParameter g) (collisionParameter_nonneg g)
  exact eventually_collisionParameter_le_mul_poissonCutoff hg
    (epsilon := (1 : ℝ) / 8) (by norm_num)

/-- Fixed multiples of the collision parameter satisfy the same relative
Taylor-tail estimate.  The cases `m = 1` and `m = 2` are the one-target and
two-target estimates used in the final Poisson and second-moment arguments. -/
theorem tendsto_poisson_taylor_relative_tail_zero_nat_mul
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    (m : ℕ) :
    Tendsto (fun N : ℕ ↦
      Real.exp ((m : ℝ) * collisionParameter g N) *
        (2 * ((m : ℝ) * collisionParameter g N) ^
            (2 * poissonCutoff N + 1) /
          ((2 * poissonCutoff N + 1).factorial : ℝ)))
      atTop (nhds 0) := by
  let x : ℕ → ℝ := fun N ↦ (m : ℝ) * collisionParameter g N
  have hx : ∀ N, 0 ≤ x N := fun N ↦
    mul_nonneg (Nat.cast_nonneg m) (collisionParameter_nonneg g N)
  have hepsilon : 0 < (1 : ℝ) / (8 * ((m : ℝ) + 1)) := by positivity
  have hbase := eventually_collisionParameter_le_mul_poissonCutoff hg hepsilon
  have hsmall : ∀ᶠ N : ℕ in atTop,
      x N ≤ (1 / 8 : ℝ) * (poissonCutoff N : ℝ) := by
    filter_upwards [hbase] with N hN
    have hmnonneg : (0 : ℝ) ≤ m := by positivity
    have hmratio : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc
      x N ≤ (m : ℝ) *
          ((1 / (8 * ((m : ℝ) + 1))) * (poissonCutoff N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hN hmnonneg
      _ = ((1 : ℝ) / 8) * (poissonCutoff N : ℝ) *
          ((m : ℝ) / ((m : ℝ) + 1)) := by
        field_simp
      _ ≤ ((1 : ℝ) / 8) * (poissonCutoff N : ℝ) := by
        exact mul_le_of_le_one_right (by positivity) hmratio
  simpa [x] using tendsto_taylor_relative_tail_zero_of_le x hx hsmall

/-- Re-export of the characteristic-versus-factorial estimate in the
factorial-tail API used by the final assembly. -/
theorem eventually_factorial_momentRadius_lt_nat :
    ∀ᶠ N : ℕ in atTop, (momentRadius N).factorial < N :=
  eventually_momentRadius_factorial_lt_nat

end

end Erdos543
