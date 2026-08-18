import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quantitative density-iteration bookkeeping for Erdős Problem 140

This file isolates the finite recursion used after the analytic input in a
Bloom--Sisask/Kelley--Meka argument has supplied a count-or-increment lemma.
It deliberately does not assert that analytic input.  Instead,
`OneStepHypothesis` records it as a hypothesis and `count_of_oneStep` proves
that it can be iterated only finitely often.

The bookkeeping keeps the three quantities that change in an iteration:
the relative density, the rank of the ambient Bohr set, and its cardinality.
At an increment the density grows by a fixed factor, the rank grows by at most
`rankCost`, and the cardinality loses at most the factor `exp (-sizeCost)`.
The conclusion pays for every possible cardinality loss.  The final theorem
specializes to a dyadic density scale and turns an eleventh-power loss at each
of at most `L + 1` stages into the expected twelfth-power exponent.
-/

namespace Erdos140.DensityIteration

noncomputable section

/-- The numerical data retained at one stage of a density iteration.

`card` is the cardinality of the current finite ambient Bohr set.  We keep it
as a natural number, and cast it to `ℝ` only in analytic inequalities. -/
structure State where
  density : ℝ
  rank : ℕ
  card : ℕ

/-- A single legitimate density-increment move. -/
def IsIncrement (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (s t : State) : Prop :=
  0 ≤ t.density ∧
    q * s.density ≤ t.density ∧
    t.density ≤ 1 ∧
    t.rank ≤ s.rank + rankCost ∧
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- The local lower bound for the configuration count at a state. -/
def HasCount (cost count : ℝ) (s : State) : Prop :=
  Real.exp (-cost) * (s.card : ℝ) ^ 2 ≤ count

/-- The abstract analytic input to the density iteration.

Every state of density at most one either already has the desired local
configuration count, or admits a controlled density-increment move. -/
def OneStepHypothesis (q : ℝ) (rankCost : ℕ)
    (sizeCost localCost count : ℝ) : Prop :=
  ∀ s : State, 0 ≤ s.density → s.density ≤ 1 →
    HasCount localCost count s ∨
      ∃ t : State, IsIncrement q rankCost sizeCost s t

private lemma square_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy),
    mul_nonneg hy (sub_nonneg.mpr hxy)]

/-- **Finite count-or-increment recursion.**

If `q ^ fuel * density > 1`, `fuel` consecutive increment moves are
impossible because every admissible state has density at most one.  Thus a
count alternative occurs.  The exponent in the returned bound includes two
copies of every possible size loss, since the configuration count is
quadratic in the ambient cardinality. -/
theorem count_of_oneStep
    {q : ℝ} {rankCost fuel : ℕ} {sizeCost localCost count : ℝ}
    (hq : 0 ≤ q) (hsizeCost : 0 ≤ sizeCost) (_hlocalCost : 0 ≤ localCost)
    (hstep : OneStepHypothesis q rankCost sizeCost localCost count)
    (s : State) (hs0 : 0 ≤ s.density) (hs1 : s.density ≤ 1)
    (hgrowth : 1 < q ^ fuel * s.density) :
    HasCount (localCost + 2 * (fuel : ℝ) * sizeCost) count s := by
  induction fuel generalizing s with
  | zero =>
      simp only [Nat.cast_zero, pow_zero, one_mul, mul_zero] at hgrowth ⊢
      exact (not_lt_of_ge hs1 hgrowth).elim
  | succ fuel ih =>
      rcases hstep s hs0 hs1 with hcount | ⟨t, ht⟩
      · have hcost : localCost ≤
            localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost := by
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsizeCost)
        have hexp : Real.exp
              (-(localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost)) ≤
            Real.exp (-localCost) :=
          Real.exp_le_exp.mpr (neg_le_neg hcost)
        exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg (s.card : ℝ))).trans hcount
      · have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq _
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left ht.2.1 hqpow
        have hrec := ih t ht.1 ht.2.2.1 hgrowth'
        have hscaled0 : 0 ≤ Real.exp (-sizeCost) * (s.card : ℝ) := by positivity
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

/-- The dyadic logarithmic scale used for an initial density. -/
def OnDyadicScale (L : ℕ) (density : ℝ) : Prop :=
  1 / (2 : ℝ) ^ L ≤ density

/-- An explicit twelfth-power cost.  The harmless `L + 1` also covers the
top-density stopping step. -/
def twelfthPowerCost (K : ℝ) (L : ℕ) : ℝ :=
  3 * K * ((L + 1 : ℕ) : ℝ) ^ 12

private lemma dyadic_growth {L : ℕ} {density : ℝ}
    (hdensity : OnDyadicScale L density) :
    1 < (2 : ℝ) ^ (L + 1) * density := by
  have hp : 0 < (2 : ℝ) ^ L := pow_pos (by norm_num) _
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

/-- **Twelfth-power bookkeeping corollary.**

Suppose the analytic one-step lemma doubles density and, at each step, has
both local-count cost and logarithmic size cost at most
`K * (L + 1)^11`.  Starting from density at least `2^{-L}`, at most `L + 1`
increments are possible.  Consequently the global count is at least
`exp (-3 K (L + 1)^12)` times the square of the initial ambient cardinality.

The rank cost is retained explicitly in `hstep`; it is irrelevant to the
finite stopping calculation once the one-step lemma is uniformly available
at every resulting rank. -/
theorem count_lower_bound_twelfth
    {rankCost L : ℕ} {K count : ℝ}
    (hK : 0 ≤ K)
    (hstep : OneStepHypothesis 2 rankCost
      (K * ((L + 1 : ℕ) : ℝ) ^ 11)
      (K * ((L + 1 : ℕ) : ℝ) ^ 11) count)
    (s : State) (hs0 : 0 ≤ s.density) (hs1 : s.density ≤ 1)
    (hscale : OnDyadicScale L s.density) :
    HasCount (twelfthPowerCost K L) count s := by
  let stepCost : ℝ := K * ((L + 1 : ℕ) : ℝ) ^ 11
  have hstepCost : 0 ≤ stepCost := by
    exact mul_nonneg hK (pow_nonneg (by positivity) _)
  have hiter :
      HasCount (stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost) count s := by
    apply count_of_oneStep (q := 2) (rankCost := rankCost)
      (fuel := L + 1) (sizeCost := stepCost) (localCost := stepCost)
      (by norm_num) hstepCost hstepCost
    · simpa [stepCost] using hstep
    · exact hs0
    · exact hs1
    · exact dyadic_growth hscale
  have hcost : stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost ≤
      twelfthPowerCost K L := by
    simpa [stepCost] using accumulatedCost_le_twelfthPowerCost (L := L) hK
  have hexp : Real.exp (-(twelfthPowerCost K L)) ≤
      Real.exp (-(stepCost + 2 * (((L + 1 : ℕ) : ℝ)) * stepCost)) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg (s.card : ℝ))).trans hiter

end

end Erdos140.DensityIteration
