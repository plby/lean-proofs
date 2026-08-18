import ErdosProblems.Erdos140.DensityIteration

/-!
# Reachability-restricted density iteration for Erdős Problem 140

The unrestricted `DensityIteration.OneStepHypothesis` is useful as a purely
logical bookkeeping interface, but its quantifier over every numerical state
is too strong for a concrete finite ambient problem: states with arbitrarily
large `card` need not arise from the initial Bohr set.

This file supplies the interface used by the analytic assembly.  Its
`Reachable` predicate is rooted at one specified initial state.  Every edge is
a controlled density increment and every reached cardinality is bounded by
the initial cardinality.  Consequently `OneStepHypothesis` asks for the
analytic count-or-increment alternative only at states that can actually be
produced by the iteration.  The finite recursion and its twelfth-power
specialization retain the exact same loss calculation.
-/

namespace Erdos140.ReachableIteration

noncomputable section

open Erdos140.DensityIteration

/-- A state obtained from `initial` by a finite chain of legitimate increment
moves, with every new ambient cardinality bounded by the initial one. -/
inductive Reachable (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (initial : State) : State → Prop
  | root : Reachable q rankCost sizeCost initial initial
  | step {s t : State} :
      Reachable q rankCost sizeCost initial s →
      IsIncrement q rankCost sizeCost s t →
      t.card ≤ initial.card →
      Reachable q rankCost sizeCost initial t

/-- Every reachable ambient set has cardinality at most the initial one. -/
theorem Reachable.card_le
    {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ} {initial s : State}
    (hs : Reachable q rankCost sizeCost initial s) :
    s.card ≤ initial.card := by
  cases hs with
  | root => exact le_rfl
  | step _ _ hcard => exact hcard

/-- The analytic input restricted to the cone reachable from `initial`.

In the increment alternative the returned cardinality bound makes the new
state reachable, so the same hypothesis is available at the following
recursive call. -/
def OneStepHypothesis (q : ℝ) (rankCost : ℕ)
    (sizeCost localCost count : ℝ) (initial : State) : Prop :=
  ∀ s : State, Reachable q rankCost sizeCost initial s →
    0 ≤ s.density → s.density ≤ 1 →
      HasCount localCost count s ∨
        ∃ t : State,
          IsIncrement q rankCost sizeCost s t ∧ t.card ≤ initial.card

private lemma square_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy),
    mul_nonneg hy (sub_nonneg.mpr hxy)]

/-- Finite count-or-increment recursion on the reachable cone.

The returned exponent includes two copies of every possible logarithmic size
loss, because the configuration count is quadratic in the ambient
cardinality. -/
theorem count_of_oneStep
    {q : ℝ} {rankCost fuel : ℕ} {sizeCost localCost count : ℝ}
    {initial : State}
    (hq : 0 ≤ q) (hsizeCost : 0 ≤ sizeCost) (_hlocalCost : 0 ≤ localCost)
    (hstep : OneStepHypothesis q rankCost sizeCost localCost count initial)
    (s : State) (hsReachable : Reachable q rankCost sizeCost initial s)
    (hs0 : 0 ≤ s.density) (hs1 : s.density ≤ 1)
    (hgrowth : 1 < q ^ fuel * s.density) :
    HasCount (localCost + 2 * (fuel : ℝ) * sizeCost) count s := by
  induction fuel generalizing s with
  | zero =>
      simp only [Nat.cast_zero, pow_zero, one_mul, mul_zero] at hgrowth ⊢
      exact (not_lt_of_ge hs1 hgrowth).elim
  | succ fuel ih =>
      rcases hstep s hsReachable hs0 hs1 with hcount | ⟨t, ht, htCard⟩
      · have hcost : localCost ≤
            localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost := by
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsizeCost)
        have hexp : Real.exp
              (-(localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost)) ≤
            Real.exp (-localCost) :=
          Real.exp_le_exp.mpr (neg_le_neg hcost)
        exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg (s.card : ℝ))).trans hcount
      · have htReachable : Reachable q rankCost sizeCost initial t :=
          Reachable.step hsReachable ht htCard
        have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq _
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left ht.2.1 hqpow
        have hrec := ih t htReachable ht.1 ht.2.2.1 hgrowth'
        have hscaled0 : 0 ≤ Real.exp (-sizeCost) * (s.card : ℝ) := by
          positivity
        have hsquare :
            (Real.exp (-sizeCost) * (s.card : ℝ)) ^ 2 ≤ (t.card : ℝ) ^ 2 :=
          square_mono hscaled0 ht.2.2.2.2
        have hfactor0 : 0 ≤
            Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) :=
          (Real.exp_pos _).le
        have hloss :
            Real.exp
                (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) *
                (s.card : ℝ) ^ 2 ≤
              Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                (t.card : ℝ) ^ 2 := by
          have hexp :
              Real.exp
                  (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) =
                Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                  Real.exp (-sizeCost) ^ 2 := by
            rw [pow_two, ← Real.exp_add, ← Real.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp]
          rw [mul_assoc, ← mul_pow]
          exact mul_le_mul_of_nonneg_left hsquare hfactor0
        exact hloss.trans hrec

private lemma dyadic_growth {L : ℕ} {density : ℝ}
    (hdensity : OnDyadicScale L density) :
    1 < (2 : ℝ) ^ (L + 1) * density := by
  have hfactor : 0 ≤ (2 : ℝ) ^ (L + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdensity hfactor
  have heq : (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) = 2 := by
    rw [pow_succ]
    field_simp
  calc
    1 < (2 : ℝ) := by norm_num
    _ = (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) := heq.symm
    _ ≤ (2 : ℝ) ^ (L + 1) * density := hmul

private lemma accumulatedCost_le_twelfthPowerCost {K : ℝ} {L : ℕ}
    (hK : 0 ≤ K) :
    K * ((L + 1 : ℕ) : ℝ) ^ 11 +
        2 * ((L + 1 : ℕ) : ℝ) * (K * ((L + 1 : ℕ) : ℝ) ^ 11) ≤
      twelfthPowerCost K L := by
  let x : ℝ := ((L + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le L))
  have ha : 0 ≤ K * x ^ 11 := mul_nonneg hK (pow_nonneg (by positivity) _)
  have hax : K * x ^ 11 ≤ x * (K * x ^ 11) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) ha]
  calc
    K * ((L + 1 : ℕ) : ℝ) ^ 11 +
          2 * ((L + 1 : ℕ) : ℝ) * (K * ((L + 1 : ℕ) : ℝ) ^ 11) =
        K * x ^ 11 + 2 * x * (K * x ^ 11) := by rfl
    _ ≤ 3 * x * (K * x ^ 11) := by linarith
    _ = twelfthPowerCost K L := by
      simp only [twelfthPowerCost, x]
      ring

/-- Reachability-restricted twelfth-power bookkeeping.

Only states in the increment cone rooted at `initial` are queried by `hstep`.
Thus the hypothesis is suitable for a concrete analytic one-step theorem on a
fixed finite ambient group, while the conclusion still has the standard
`exp (-O((L+1)^12))` form. -/
theorem count_lower_bound_twelfth
    {rankCost L : ℕ} {K count : ℝ} {initial : State}
    (hK : 0 ≤ K)
    (hstep : OneStepHypothesis 2 rankCost
      (K * ((L + 1 : ℕ) : ℝ) ^ 11)
      (K * ((L + 1 : ℕ) : ℝ) ^ 11) count initial)
    (hs0 : 0 ≤ initial.density) (hs1 : initial.density ≤ 1)
    (hscale : OnDyadicScale L initial.density) :
    HasCount (twelfthPowerCost K L) count initial := by
  let stepCost : ℝ := K * ((L + 1 : ℕ) : ℝ) ^ 11
  have hstepCost : 0 ≤ stepCost := by
    exact mul_nonneg hK (pow_nonneg (by positivity) _)
  have hiter :
      HasCount (stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost)
        count initial := by
    apply count_of_oneStep (q := 2) (rankCost := rankCost)
      (fuel := L + 1) (sizeCost := stepCost) (localCost := stepCost)
      (initial := initial) (by norm_num) hstepCost hstepCost
    · simpa [stepCost] using hstep
    · exact Reachable.root
    · exact hs0
    · exact hs1
    · exact dyadic_growth hscale
  have hcost : stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost ≤
      twelfthPowerCost K L := by
    simpa [stepCost] using accumulatedCost_le_twelfthPowerCost (L := L) hK
  have hexp : Real.exp (-(twelfthPowerCost K L)) ≤
      Real.exp (-(stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost)) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact (mul_le_mul_of_nonneg_right hexp
    (sq_nonneg (initial.card : ℝ))).trans hiter

end

end Erdos140.ReachableIteration
