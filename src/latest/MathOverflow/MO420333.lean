/-

This is a Lean formalization of a solution to MathOverflow question
420333:

https://mathoverflow.net/questions/420333/sum-of-guesses-minimization-problem-also-does-this-problem-already-exist-in-the

The original question was asked by Vipul Naik.

The solution here is by ChatGPT-5.2 Pro (from OpenAI).


The proof was formalized by a combination of Aristotle (from Harmonic)
and ChatGPT.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.29.1
Mathlib version: v4.29.1

-/


/-
This module formalizes the "High-low guessing game" described in the user's LaTeX document.
It defines strategies, scores, and the value of the game in both bounded and unbounded settings.
It proves that the value of the unbounded game is 4.
It characterizes the value of the bounded game using "tight polynomials" and proves the exact value for specific ranges of B.
It also establishes the asymptotic behavior of the game value and the optimal strategy as B tends to infinity.
Key theorems include:
- `unbounded_value_eq_four`: The value of the unbounded game is 4.
- `boundedGameValue_eq_firstGuess`: The value of the bounded game is the first guess of the optimal strategy.
- `optimalStrategy_isOptimal`: The constructed strategy is optimal.
- `value_B_le_2`, `value_two_step`, `value_three_step`: Exact values for small B.
- `growthBase_limit`: The growth base tends to 2.
- `firstGuess_limit`: The first guess tends to 4.
-/

import Mathlib

namespace MO420333

set_option linter.style.setOption false
--
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.commandStart false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

open scoped Classical

/-
A Lean 4 formalization of the game:

* Unknown real `y ≥ 1`.
* A strategy is an increasing sequence of nonnegative reals with `x 0 ≥ 1`,
  and which eventually reaches any `y ≥ 1`.
* The game ends at the first index `n` with `y ≤ x n`.
* The score is `(∑ i ≤ n, x i) / y`.
* We minimize the worst-case score: `inf_x sup_{y≥1} score(x,y)`.

We put scores in `ENNReal` so that `iInf`/`iSup` are available.
-/

/-- A strategy is a nondecreasing sequence of nonnegative real guesses, starting at least `1`,
    which eventually reaches any target `y ≥ 1`. -/
structure Strategy where
  x       : ℕ → ℝ
  nonneg  : ∀ n, 0 ≤ x n
  one_le  : 1 ≤ x 0
  mono    : Monotone x
  hits    : ∀ {y : ℝ}, 1 ≤ y → ∃ n, y ≤ x n

/-- The first index at which the strategy reaches `y` (for `y ≥ 1`). -/
noncomputable def hitIndex (s : Strategy) (y : {y : ℝ // 1 ≤ y}) : ℕ :=
  Nat.find (s.hits y.property)

/-- Partial sum of guesses up to and including index `n`. -/
noncomputable def partialSum (s : Strategy) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), s.x i

/-- The score of strategy `s` against target `y ≥ 1`. -/
noncomputable def score (s : Strategy) (y : {y : ℝ // 1 ≤ y}) : ENNReal :=
  ENNReal.ofReal ((partialSum s (hitIndex s y)) / y.1)

/-- Worst-case score of a strategy: `sup_{y ≥ 1} score(s,y)`. -/
noncomputable def worstCaseScore (s : Strategy) : ENNReal :=
  ⨆ y : {y : ℝ // 1 ≤ y}, score s y

/-- The value of the game: `inf_s sup_{y ≥ 1} score(s,y)`. -/
noncomputable def gameValue : ENNReal :=
  ⨅ s : Strategy, worstCaseScore s

/-!
## Bounded variant: the adversary is restricted to `1 ≤ y ≤ B`.
-/

/-- Bounded score: same `score`, but only evaluated on `y` with `1 ≤ y ≤ B`. -/
noncomputable def boundedScore (s : Strategy) (B : ℝ) (y : {y : ℝ // 1 ≤ y ∧ y ≤ B}) : ENNReal :=
  score s ⟨y.1, y.2.1⟩

/-- Worst-case score when the target is restricted to `1 ≤ y ≤ B`. -/
noncomputable def boundedWorstCaseScore (s : Strategy) (B : ℝ) : ENNReal :=
  ⨆ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, boundedScore s B y

/-- The value of the bounded game: `inf_s sup_{1 ≤ y ≤ B} score(s,y)`. -/
noncomputable def boundedGameValue (B : ℝ) : ENNReal :=
  ⨅ s : Strategy, boundedWorstCaseScore s B

/-- A strategy is optimal for the bounded game if it attains the bounded game value. -/
def IsOptimalBounded (B : ℝ) (s : Strategy) : Prop :=
  boundedWorstCaseScore s B = boundedGameValue B

/-
A bounded-`B` variant and the general "n-step" picture:

* Breakpoints:      Bₙ = (2 cos(π/(n+3)))^(n+1)
* Tight polynomials p₀(R)=1, p₁(R)=R, pₙ₊₂(R)=R (pₙ₊₁(R) - pₙ(R))
* In the n-step regime (Bₙ₋₁ < B ≤ Bₙ), the optimal worst-case ratio R is characterized by
    pₙ(R) = B
  with R in the bracket [4 cos²(π/(n+2)), 4 cos²(π/(n+3))],
  and the optimal strategy starts with
    p₁(R), p₂(R), …, pₙ(R)=B.
-/

/-!
## Tight polynomials and breakpoints
-/

/-- The "tight polynomial" `pₙ(R)`:
`p₀(R)=1`, `p₁(R)=R`, `pₙ₊₂(R)=R*(pₙ₊₁(R) - pₙ(R))`. -/
noncomputable def tightPoly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, R => R
  | Nat.succ (Nat.succ n), R => R * (tightPoly (Nat.succ n) R - tightPoly n R)

/-- Map the 0-based strategy index `k` to the tight polynomial `p_{k+1}(R)`. -/
noncomputable def tightGuess (k : ℕ) (R : ℝ) : ℝ :=
  tightPoly (k + 1) R

/-- Breakpoint `Bₙ = (2 cos(π/(n+3)))^(n+1)`. -/
noncomputable def stepBreakpoint (n : ℕ) : ℝ :=
  (2 * Real.cos (Real.pi / ((n + 3 : ℕ) : ℝ))) ^ (n + 1)

/-- The "upper" ratio endpoint `Rₙ,upper = 4 cos²(π/(n+3))`. -/
noncomputable def ratioUpper (n : ℕ) : ℝ :=
  4 * (Real.cos (Real.pi / ((n + 3 : ℕ) : ℝ))) ^ (2 : ℕ)

/-- The "lower" ratio endpoint `Rₙ,lower = 4 cos²(π/(n+2))`. -/
noncomputable def ratioLower (n : ℕ) : ℝ :=
  4 * (Real.cos (Real.pi / ((n + 2 : ℕ) : ℝ))) ^ (2 : ℕ)

/-- The interval of `B` for which the optimal bounded solution uses exactly `n` active guesses. -/
def InStepRange (B : ℝ) (n : ℕ) : Prop :=
  stepBreakpoint (n - 1) < B ∧ B ≤ stepBreakpoint n

/-- A strategy `s` "starts with" the tight `n`-step pattern for ratio `R` and bound `B`. -/
def StartsWithTightNSteps (s : Strategy) (n : ℕ) (R B : ℝ) : Prop :=
  (∀ k, k < n - 1 → s.x k = tightGuess k R) ∧ s.x (n - 1) = B

/-!
## Step-count `n(B)` and first guess `x(B)` as functions of `B`
-/

-- These names are assumed to exist from the previous framework:
-- `stepBreakpoint`, `InStepRange`, `ratioLower`, `ratioUpper`, `tightPoly`,
-- `exists_stepCount_of_one_lt`, `existsUnique_ratio_of_inStepRange`.

theorem stepBreakpoint_zero : stepBreakpoint 0 = (1 : ℝ) := by
  -- By definition of `stepBreakpoint`, we have `stepBreakpoint 0 = (2 * Real.cos (Real.pi / 3)) ^ 1`.
  simp [stepBreakpoint]

/-- For any `B > 1`, there exists an `n ≥ 1` with `B` in the `n`-step breakpoint interval. -/
theorem exists_stepCount_of_one_lt
    {B : ℝ} (hB : 1 < B) :
    ∃ n : ℕ, 1 ≤ n ∧ InStepRange B n := by
  unfold InStepRange;
  -- To prove the existence of such an $n$, we use the fact that the sequence of breakpoints is strictly increasing and unbounded.
  have h_unbounded : ∀ M > 1, ∃ n : ℕ, stepBreakpoint n > M := by
    unfold stepBreakpoint;
    -- We'll use that $2 \cos(\pi / (n + 3))$ approaches $2$ as $n$ grows.
    have h_cos : Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 3))) Filter.atTop (nhds 2) := by
      exact le_trans ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| by norm_num;
    -- Since $2 \cos(\pi / (n + 3))$ approaches $2$ as $n$ grows, we can find an $N$ such that for all $n \geq N$, $2 \cos(\pi / (n + 3)) > 1.5$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, 2 * Real.cos (Real.pi / (n + 3)) > 1.5 := by
      simpa using h_cos.eventually ( lt_mem_nhds <| by norm_num );
    -- Since $2 \cos(\pi / (n + 3)) > 1.5$ for all $n \geq N$, we have $(2 \cos(\pi / (n + 3)))^{n + 1} > 1.5^{n + 1}$.
    have h_exp : ∀ n ≥ N, (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1) > 1.5 ^ (n + 1) := by
      exact fun n hn => pow_lt_pow_left₀ ( hN n hn ) ( by norm_num ) ( by linarith );
    -- Since $1.5^{n + 1}$ grows exponentially, we can find an $n$ such that $1.5^{n + 1} > M$.
    have h_exp_growth : Filter.Tendsto (fun n : ℕ => (1.5 : ℝ) ^ (n + 1)) Filter.atTop Filter.atTop := by
      exact tendsto_pow_atTop_atTop_of_one_lt ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1;
    exact fun M hM => by rcases Filter.eventually_atTop.mp ( h_exp_growth.eventually_gt_atTop M ) with ⟨ n, hn ⟩ ; exact ⟨ n + N, by have := hn ( n + N ) ( by linarith ) ; have := h_exp ( n + N ) ( by linarith ) ; norm_num at * ; linarith ⟩ ;
  contrapose! h_unbounded;
  field_simp;
  use B;
  refine ⟨ hB, fun x => ?_ ⟩;
  induction' x with n ih;
  · exact le_trans ( by norm_num [ stepBreakpoint_zero ] ) hB.le;
  · exact le_of_lt ( h_unbounded _ n.succ_pos ( Nat.recOn n ( by norm_num [ stepBreakpoint_zero ] ; linarith ) fun n ihn => by linarith! [ h_unbounded _ n.succ_pos ihn ] ) )

/-- `n(B)`: the (minimal) step-count in the breakpoint decomposition.
For `B ≤ 1` we set it to `1` by convention (irrelevant for `B → ∞`). -/
noncomputable def nSteps (B : ℝ) : ℕ :=
  if h : 1 < B then
    Nat.find (exists_stepCount_of_one_lt (B := B) h)
  else
    1

/-- Specification lemma for `nSteps` (in the nontrivial case `1 < B`). -/
theorem nSteps_spec {B : ℝ} (hB : 1 < B) :
    1 ≤ nSteps B ∧ InStepRange B (nSteps B) := by
  -- would follow from `Nat.find_spec` and the definition of `nSteps`
  unfold nSteps;
  grind

/-- Trigonometric closed form:
`pₙ(4 cos² θ) = (2 cos θ)^n * (sin((n+1)θ) / sin θ)`.

(We include `sin θ ≠ 0` to avoid division-by-zero side conditions in the statement.) -/
theorem tightPoly_eq_trig
    (n : ℕ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    tightPoly n (4 * (Real.cos θ) ^ (2 : ℕ)) =
      (2 * Real.cos θ) ^ n * (Real.sin (((n + 1 : ℕ) : ℝ) * θ) / Real.sin θ) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ', mul_assoc ];
  · rfl;
  · rw [ Real.sin_two_mul ] ; ring_nf at * ; aesop;
  · -- Apply the recurrence relation for tightPoly.
    have h_rec : tightPoly (n + 2) (4 * (Real.cos θ * Real.cos θ)) = 4 * (Real.cos θ * Real.cos θ) * (tightPoly (n + 1) (4 * (Real.cos θ * Real.cos θ)) - tightPoly n (4 * (Real.cos θ * Real.cos θ))) := by
      exact rfl;
    rw [ h_rec, ih (n + 1) (by omega), ih n (by omega) ] ; ring_nf;
    rw [ show θ * 3 = 3 * θ by ring ] ; norm_num [ Real.sin_add, Real.sin_three_mul, Real.cos_add, Real.cos_three_mul ] ; ring_nf;
    rw [ show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 by ring, Real.sin_sq ] ; norm_num [ Real.sin_add, Real.cos_add ] ; ring_nf;
    rw [ Real.sin_sq ] ; ring

/-
The value of the tight polynomial `p_n(R)` at the lower ratio bound `R_{n,lower}` is equal to the previous breakpoint `B_{n-1}`. This corresponds to the case where `θ = π / (n+2)`, making the sine ratio equal to 1.
-/
lemma tightPoly_lower_val {n : ℕ} (hn : 1 ≤ n) :
    tightPoly n (ratioLower n) = stepBreakpoint (n - 1) := by
      -- Apply the trigonometric closed form with θ = π / (n+2).
      have h_trig : tightPoly n (4 * (Real.cos (Real.pi / (n + 2))) ^ 2) = (2 * Real.cos (Real.pi / (n + 2))) ^ n * (Real.sin (((n + 1) : ℝ) * (Real.pi / (n + 2))) / Real.sin (Real.pi / (n + 2))) := by
        convert tightPoly_eq_trig n ( Real.pi / ( n + 2 ) ) _ using 1 ; norm_num;
        exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( div_lt_self Real.pi_pos ( by norm_cast; linarith ) ) );
      convert h_trig using 1;
      · unfold ratioLower; norm_num;
      · rw [ show ( ( n + 1 ) : ℝ ) * ( Real.pi / ( n + 2 ) ) = Real.pi - Real.pi / ( n + 2 ) by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n + 2 : ℝ ) ≠ 0 ) ], Real.sin_pi_sub ] ; ring_nf;
        rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, mul_inv_cancel₀ ( by positivity : ( 2 + n : ℝ ) ≠ 0 ) ] ) ) ) ] ; unfold stepBreakpoint ; ring_nf;
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        ring_nf

/-
The value of the tight polynomial `p_n(R)` at the upper ratio bound `R_{n,upper}` is equal to the current breakpoint `B_n`. This corresponds to the case where `θ = π / (n+3)`.
-/
lemma tightPoly_upper_val {n : ℕ} :
    tightPoly n (ratioUpper n) = stepBreakpoint n := by
      unfold ratioUpper stepBreakpoint;
      have := @tightPoly_eq_trig n ( Real.pi / ( n + 3 ) );
      norm_num +zetaDelta at *;
      rw [ this ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ) ) ) ];
      rw [ show ( n + 1 : ℝ ) * ( Real.pi / ( n + 3 ) ) = Real.pi - 2 * ( Real.pi / ( n + 3 ) ) by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ], Real.sin_pi_sub, Real.sin_two_mul ] ; ring_nf;
      norm_num [ ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, mul_inv_cancel₀ ( by positivity : ( 3 : ℝ ) + n ≠ 0 ) ] : Real.pi * ( 3 + n : ℝ ) ⁻¹ < Real.pi ) ) ]

/-
The tight polynomial `p_n(R)` is continuous with respect to `R` for any fixed `n`. This follows from the fact that it is a polynomial in `R`.
-/
lemma continuous_tightPoly (n : ℕ) : Continuous (tightPoly n) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n );
  · exact continuous_const;
  · exact continuous_id;
  · exact Continuous.mul ( continuous_id' ) ( Continuous.sub ( ih _ <| Nat.lt_succ_self _ ) ( ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ) )

set_option maxHeartbeats 0 in
/-
The trigonometric function `f(θ) = (2 cos θ)^n * sin((n+1)θ) / sin θ`
is strictly decreasing on `[π/(n+3), π/(n+2)]` for `n ≥ 1`.
-/
lemma tightPoly_trig_strictAntiOn {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ))
      (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
  let f : ℝ → ℝ := fun θ =>
    (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ)
  have h_deriv :
      ∀ θ ∈ Set.Ioo (Real.pi / (n + 3)) (Real.pi / (n + 2)),
        deriv f θ =
          (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ) *
            (-(n : ℝ) * Real.tan θ +
              (n + 1 : ℝ) * Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) -
                Real.cos θ / Real.sin θ) := by
    intro θ hθ
    have hsin : Real.sin θ ≠ 0 := by
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (lt_trans (by positivity) hθ.1)
        (hθ.2.trans_le (div_le_self Real.pi_pos.le (by linarith))))
    have hcos : Real.cos θ ≠ 0 := by
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
        linarith [Real.pi_pos, hθ.1, show 0 < Real.pi / (n + 3 : ℝ) by positivity]
      , by
        exact hθ.2.trans_le (by
          rw [div_le_iff₀] <;>
            nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast])⟩)
    have hsin2 : Real.sin ((n + 1) * θ) ≠ 0 := by
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos (by positivity) (lt_trans (by positivity) hθ.1))
        (by
          have hmul :
              ((n : ℝ) + 1) * θ <
                ((n : ℝ) + 1) * (Real.pi / (n + 2 : ℝ)) :=
            mul_lt_mul_of_pos_left hθ.2 (by positivity)
          have hbound : ((n : ℝ) + 1) * (Real.pi / (n + 2 : ℝ)) < Real.pi := by
            field_simp
            nlinarith [Real.pi_pos]
          exact hmul.trans hbound))
    dsimp [f]
    change deriv
        (fun x => ((2 * Real.cos x) ^ n) *
          (Real.sin ((n + 1) * x) / Real.sin x)) θ = _
    change deriv
        ((fun x => (2 * Real.cos x) ^ n) *
          (fun x => Real.sin ((n + 1) * x) / Real.sin x)) θ = _
    rw [deriv_mul]
    · rw [show deriv (fun x => (2 * Real.cos x) ^ n) θ =
          n * (2 * Real.cos θ) ^ (n - 1) * (2 * (-Real.sin θ)) by
        change deriv ((fun x => 2 * Real.cos x) ^ n) θ = _
        rw [deriv_pow]
        rw [show deriv (fun x => 2 * Real.cos x) θ = 2 * (-Real.sin θ) by
          rw [deriv_const_mul, deriv_cos] <;> simp]
        simp]
      rw [show deriv (fun x => Real.sin ((n + 1) * x) / Real.sin x) θ =
          (deriv (fun x => Real.sin ((n + 1) * x)) θ * Real.sin θ -
            Real.sin ((n + 1) * θ) * deriv (fun x => Real.sin x) θ) /
              Real.sin θ ^ 2 by
        change deriv ((fun x => Real.sin ((n + 1) * x)) / fun x => Real.sin x) θ = _
        rw [deriv_div (by fun_prop) (by fun_prop) hsin]]
      rw [show deriv (fun x => Real.sin ((n + 1) * x)) θ =
          Real.cos ((n + 1) * θ) * (n + 1) by
        rw [deriv_sin]
        · rw [show deriv (fun x : ℝ => (n + 1 : ℝ) * x) θ = (n + 1 : ℝ) by
            rw [deriv_const_mul_field]
            simp]
        · fun_prop]
      rw [show deriv (fun x => Real.sin x) θ = Real.cos θ by simp]
      simp [Real.tan_eq_sin_div_cos]
      field_simp [hsin, hcos, hsin2]
      rcases n with _ | n
      · norm_num at hn
      · simp [pow_succ, Nat.cast_add]
        ring_nf
    · fun_prop
    · exact DifferentiableAt.div (by fun_prop) (by fun_prop) hsin
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · dsimp [f]
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.pow (continuousOn_const.mul Real.continuousOn_cos) n
    · refine ContinuousOn.div ?_ Real.continuousOn_sin ?_
      · exact Continuous.continuousOn (Real.continuous_sin.comp (by continuity))
      · intro θ hθ
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (lt_of_lt_of_le (by positivity) hθ.1)
          (lt_of_le_of_lt hθ.2 (by
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [Real.pi_pos])))
  · intro θ hθ
    rw [interior_Icc] at hθ
    rw [h_deriv θ hθ]
    have h_tan_pos : 0 < Real.tan θ := by
      exact Real.tan_pos_of_pos_of_lt_pi_div_two (lt_trans (by positivity) hθ.1)
        (lt_of_lt_of_le hθ.2 (by
          rw [div_le_iff₀]
          · nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]
          · positivity))
    have h_cot_pos : 0 < Real.cos θ / Real.sin θ := by
      exact div_pos
        (Real.cos_pos_of_mem_Ioo ⟨by
          linarith [Real.pi_pos, hθ.1, show (Real.pi : ℝ) / (n + 3) > 0 by positivity]
        , by
          linarith [Real.pi_pos, hθ.2,
            show (Real.pi : ℝ) / (n + 2) < Real.pi / 2 by
              rw [div_lt_iff₀] <;>
                nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]]⟩)
        (Real.sin_pos_of_mem_Ioo ⟨by
          linarith [Real.pi_pos, hθ.1, show (Real.pi : ℝ) / (n + 3) > 0 by positivity]
        , by
          linarith [Real.pi_pos, hθ.2,
            show (Real.pi : ℝ) / (n + 2) < Real.pi by
              rw [div_lt_iff₀] <;>
                nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]]⟩)
    have h_cot_neg : Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) < 0 := by
      refine div_neg_of_neg_of_pos (Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_)
        (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
      · have hmul :
            ((n : ℝ) + 1) * (Real.pi / (n + 3 : ℝ)) <
              ((n : ℝ) + 1) * θ :=
          mul_lt_mul_of_pos_left hθ.1 (by positivity)
        have hbound : Real.pi / 2 ≤ ((n : ℝ) + 1) * (Real.pi / (n + 3 : ℝ)) := by
          field_simp
          nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]
        exact lt_of_le_of_lt hbound hmul
      · nlinarith [hθ.1, hθ.2, Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast,
          mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 3 ≠ 0),
          mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 2 ≠ 0)]
      · exact mul_pos (by positivity) (lt_trans (by positivity) hθ.1)
      · nlinarith [hθ.1, hθ.2, Real.pi_pos,
          mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 3 ≠ 0),
          mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 2 ≠ 0)]
    have h_term_neg :
        -(n : ℝ) * Real.tan θ +
            (n + 1 : ℝ) * Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) -
          Real.cos θ / Real.sin θ < 0 := by
      ring_nf at *
      nlinarith
    exact mul_neg_of_pos_of_neg
      (mul_pos
        (pow_pos (mul_pos zero_lt_two (Real.cos_pos_of_mem_Ioo ⟨by
          linarith [Real.pi_pos, hθ.1,
            div_nonneg Real.pi_pos.le (by positivity : 0 ≤ (n : ℝ) + 3)]
        , by
          exact hθ.2.trans_le (by
            rw [div_le_iff₀] <;>
              nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast])⟩)) n)
        (div_pos
          (Real.sin_pos_of_mem_Ioo ⟨by
            exact mul_pos (by positivity) (lt_trans (by positivity) hθ.1)
          , by
            nlinarith [hθ.1, hθ.2, Real.pi_pos,
              mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 3 ≠ 0),
              mul_div_cancel₀ Real.pi (by positivity : (n : ℝ) + 2 ≠ 0)]⟩)
          (Real.sin_pos_of_mem_Ioo ⟨by
            exact lt_trans (by positivity) hθ.1
          , by
            exact hθ.2.trans_le (div_le_self Real.pi_pos.le (by linarith))⟩)))
      h_term_neg

/-
The tight polynomial `p_n(R)` is strictly monotonic (increasing) on the interval `[R_{n,lower}, R_{n,upper}]`.
Proof:
Let `I_θ = [π/(n+3), π/(n+2)]`.
The map `g(θ) = 4 \cos^2 θ` is a strictly decreasing bijection from `I_θ` to `[R_{n,lower}, R_{n,upper}]`.
We have `tightPoly n (g(θ)) = f(θ)` where `f` is the trigonometric form.
We know `f` is strictly decreasing on `I_θ` (by `tightPoly_trig_strictAntiOn`).
Since `g` is strictly decreasing and `f` is strictly decreasing, the composition `tightPoly n = f \circ g^{-1}` is strictly increasing.
Specifically, for `y1 < y2` in the range, let `y1 = g(θ1)` and `y2 = g(θ2)`.
`g(θ1) < g(θ2) \implies θ1 > θ2` (since `g` is decreasing).
`θ1 > θ2 \implies f(θ1) < f(θ2)` (since `f` is decreasing).
Thus `tightPoly n y1 < tightPoly n y2`.
-/
lemma tightPoly_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (tightPoly n) (Set.Icc (ratioLower n) (ratioUpper n)) := by
      intro y1 hy1 y2 hy2 hlt;
      obtain ⟨θ1, hθ1⟩ : ∃ θ1 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), y1 = 4 * (Real.cos θ1) ^ 2 := by
        have h_cos_sq : ∃ θ1 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ1) ^ 2 = y1 := by
          apply_rules [ intermediate_value_Icc' ] <;> norm_num [ ratioLower, ratioUpper ] at *;
          · gcongr ; linarith;
          · exact Continuous.continuousOn ( by continuity );
          · tauto;
        aesop
      obtain ⟨θ2, hθ2⟩ : ∃ θ2 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), y2 = 4 * (Real.cos θ2) ^ 2 := by
        have hθ2_exists : ∃ θ2 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), Real.cos θ2 ^ 2 = y2 / 4 := by
          apply_rules [ intermediate_value_Icc' ];
          · grind;
          · exact Continuous.continuousOn ( Real.continuous_cos.pow 2 );
          · constructor <;> norm_num [ ratioLower, ratioUpper ] at * <;> linarith;
        exact ⟨ hθ2_exists.choose, hθ2_exists.choose_spec.1, by linarith [ hθ2_exists.choose_spec.2 ] ⟩
      have hθ1θ2 : θ1 > θ2 := by
        contrapose! hlt;
        exact hθ2.2.symm ▸ hθ1.2.symm ▸ mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.2 ] ⟩ ) ( Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ1.1.1 ] ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.2 ] ) hlt ) 2 ) zero_le_four;
      have hfθ1θ2 : (2 * Real.cos θ1) ^ n * (Real.sin ((n + 1) * θ1) / Real.sin θ1) < (2 * Real.cos θ2) ^ n * (Real.sin ((n + 1) * θ2) / Real.sin θ2) := by
        have := tightPoly_trig_strictAntiOn hn;
        exact this hθ2.1 hθ1.1 hθ1θ2;
      convert hfθ1θ2 using 1;
      · rw [ hθ1.2, tightPoly_eq_trig ]
        · aesop
        exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ1.1.1 ) ( lt_of_le_of_lt hθ1.1.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) );
      · rw [ hθ2.2, tightPoly_eq_trig ];
        · norm_cast;
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by exact lt_of_lt_of_le ( by positivity ) hθ2.1.1 ) ( by exact lt_of_le_of_lt hθ2.1.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) )

set_option maxHeartbeats 0 in
/-
The trigonometric function `f(θ) = (2 cos θ)^n * sin((n+1)θ) / sin θ` is strictly decreasing on the interval `[π/(n+3), π/(n+2)]` for `n ≥ 1`.
Proof idea:
1. Show `f` is continuous on the closed interval and differentiable on the open interval.
2. Compute the logarithmic derivative (or just the derivative factor):
   `f'(θ)/f(θ) = -n tan θ + (n+1) cot((n+1)θ) - cot θ`.
3. Show that for `θ` in the interval, `0 < θ < π/2` (so `tan θ > 0`, `cot θ > 0`) and `π/2 < (n+1)θ < π` (so `cot((n+1)θ) < 0`).
4. Conclude `f'(θ) < 0` on the open interval.
5. Use the mean value theorem or standard calculus lemmas to deduce strict monotonicity on the closed interval.
-/
lemma tightPoly_trig_strictAntiOn2 {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ))
      (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by
    exact le_trans (by positivity) hx.1
  have hy0 : 0 ≤ y := by
    exact le_trans (by positivity) hy.1
  have hy_pi : y ≤ Real.pi := by
    exact hy.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos])
  have hx_pi : x ≤ Real.pi := by
    exact hx.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos])
  have hx_pi_div_two : x ≤ Real.pi / 2 := by
    exact hx.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast])
  have hy_pi_div_two : y ≤ Real.pi / 2 := by
    exact hy.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast])
  have hcos_lt : Real.cos y < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hx0 hy_pi hxy
  have hcosx_nonneg : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx0], hx_pi_div_two⟩
  have hcosy_nonneg : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hy0], hy_pi_div_two⟩
  have hRyRx : 4 * Real.cos y ^ 2 < 4 * Real.cos x ^ 2 := by
    nlinarith [hcos_lt, hcosx_nonneg, hcosy_nonneg]
  have hR_mem : ∀ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)),
      4 * Real.cos θ ^ 2 ∈ Set.Icc (ratioLower n) (ratioUpper n) := by
    intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans (by positivity) hθ.1
    have hθ_pi : θ ≤ Real.pi :=
      hθ.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos])
    have hθ_pi_div_two : θ ≤ Real.pi / 2 := by
      exact hθ.2.trans (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast])
    have hcosθ_nonneg : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ0], hθ_pi_div_two⟩
    constructor
    · unfold ratioLower
      have hb0 : 0 ≤ Real.cos (Real.pi / (n + 2)) := by
        refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
        · linarith [Real.pi_pos, show 0 ≤ Real.pi / (n + 2 : ℝ) by positivity]
        · rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]
      have hle : Real.cos (Real.pi / (n + 2)) ≤ Real.cos θ :=
        Real.cos_le_cos_of_nonneg_of_le_pi hθ0
          (by rw [div_le_iff₀] <;> nlinarith [Real.pi_pos]) hθ.2
      have hsq : Real.cos (Real.pi / (n + 2)) ^ 2 ≤ Real.cos θ ^ 2 :=
        pow_le_pow_left₀ hb0 hle 2
      simpa [Nat.cast_add, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hsq zero_le_four
    · unfold ratioUpper
      have ha0 : 0 ≤ Real.cos (Real.pi / (n + 3)) := by
        refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
        · linarith [Real.pi_pos, show 0 ≤ Real.pi / (n + 3 : ℝ) by positivity]
        · rw [div_le_iff₀] <;> nlinarith [Real.pi_pos, show (n : ℝ) ≥ 1 by norm_cast]
      have hle : Real.cos θ ≤ Real.cos (Real.pi / (n + 3)) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθ_pi hθ.1
      have hsq : Real.cos θ ^ 2 ≤ Real.cos (Real.pi / (n + 3)) ^ 2 :=
        pow_le_pow_left₀ hcosθ_nonneg hle 2
      simpa [Nat.cast_add, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hsq zero_le_four
  have htp : tightPoly n (4 * Real.cos y ^ 2) < tightPoly n (4 * Real.cos x ^ 2) :=
    tightPoly_strictMonoOn hn (hR_mem y hy) (hR_mem x hx) hRyRx
  have hsinx : Real.sin x ≠ 0 := by
    have hx_lt_pi : x < Real.pi := by
      exact hx.2.trans_lt (by rw [div_lt_iff₀] <;> nlinarith [Real.pi_pos])
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le (by positivity) hx.1)
      hx_lt_pi)
  have hsiny : Real.sin y ≠ 0 := by
    have hy_lt_pi : y < Real.pi := by
      exact hy.2.trans_lt (by rw [div_lt_iff₀] <;> nlinarith [Real.pi_pos])
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le (by positivity) hy.1)
      hy_lt_pi)
  rw [tightPoly_eq_trig n y hsiny, tightPoly_eq_trig n x hsinx] at htp
  simpa using htp

/- In the `n`-step regime, there is a unique `R` in the bracket
`[ratioLower n, ratioUpper n]` such that `tightPoly n R = B`. -/
theorem existsUnique_ratio_of_inStepRange
    {B : ℝ} {n : ℕ} (hn : 1 ≤ n) (hBn : InStepRange B n) :
    ∃! R : ℝ, ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧ tightPoly n R = B := by
  obtain ⟨R, hR⟩ : ∃ R ∈ Set.Icc (ratioLower n) (ratioUpper n), tightPoly n R = B := by
    apply_rules [ intermediate_value_Icc ];
    · unfold ratioLower ratioUpper;
      gcongr <;> norm_num;
      · exact Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩;
      · exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ( by gcongr ; linarith );
    · exact continuous_tightPoly n |> Continuous.continuousOn;
    · exact ⟨ by rw [ tightPoly_lower_val hn ] ; exact hBn.1.le, by rw [ tightPoly_upper_val ] ; exact hBn.2 ⟩;
  exact ⟨ R, ⟨ hR.1.1, hR.1.2, hR.2 ⟩, fun x hx => StrictMonoOn.injOn ( tightPoly_strictMonoOn hn ) ⟨ hx.1, hx.2.1 ⟩ ⟨ hR.1.1, hR.1.2 ⟩ <| by aesop ⟩

/-- `x(B)`: the first guess of the canonical “tight” optimal strategy.
For `B ≤ 1` we set it to `1` by convention (irrelevant for `B → ∞`).

Definition: let `n := nSteps B`, and let `x(B)` be the unique `R` in the
bracket `[ratioLower n, ratioUpper n]` such that `tightPoly n R = B`.
-/
noncomputable def firstGuess (B : ℝ) : ℝ :=
by
  classical
  by_cases hB : 1 < B
  · let n : ℕ := nSteps B
    have hn : 1 ≤ n := (nSteps_spec (B := B) hB).1
    have hBn : InStepRange B n := (nSteps_spec (B := B) hB).2
    exact Classical.choose (existsUnique_ratio_of_inStepRange (B := B) (n := n) hn hBn)
  · exact 1

/-- The “growth base” associated to the optimal step count: `B^(1/n(B))`. -/
noncomputable def growthBase (B : ℝ) : ℝ :=
  Real.rpow B (1 / (nSteps B : ℝ))


/-
As B goes to infinity, the optimal number of steps n(B) also goes to infinity.
-/
open Filter Topology

theorem nSteps_tendsto_atTop : Tendsto nSteps atTop atTop := by
  -- For any fixed $n$, $B_n$ is a fixed number. Therefore, as $B \to \infty$, $B$ will eventually exceed $B_n$.
  have h_bounded : ∀ n : ℕ, ∃ B₀ : ℝ, ∀ B ≥ B₀, nSteps B > n := by
    -- For any $n$, let $B₀ = \max_{1 \leq k \leq n} B_k$. Then for any $B \geq B₀$, $n(B) > n$ because $B$ cannot be in the interval $[B_{k-1}, B_k]$ for any $k \leq n$.
    intros n
    obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ k ≤ n, stepBreakpoint k ≤ B₀ := by
      exact ⟨ ∑ k ∈ Finset.range ( n + 1 ), stepBreakpoint k, fun k hk => Finset.single_le_sum ( fun a _ => show 0 ≤ stepBreakpoint a from pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> norm_num <;> nlinarith [ Real.pi_pos, show ( a:ℝ ) + 3 ≥ 3 by linarith ], by rw [ div_le_iff₀ ] <;> norm_num <;> nlinarith [ Real.pi_pos ] ⟩ ) ) _ ) ( Finset.mem_range_succ_iff.mpr hk ) ⟩;
    use Max.max B₀ 2 + 1;
    intros B hB
    have h_not_in_interval : ∀ k ≤ n, ¬(stepBreakpoint (k - 1) < B ∧ B ≤ stepBreakpoint k) := by
      grind;
    contrapose! h_not_in_interval;
    have := nSteps_spec ( show 1 < B by linarith [ le_max_left B₀ 2, le_max_right B₀ 2 ] ) ; aesop;
  exact Filter.tendsto_atTop_atTop.mpr fun n => by obtain ⟨ B₀, hB₀ ⟩ := h_bounded n; exact ⟨ B₀, fun B hB => le_of_lt ( hB₀ B hB ) ⟩ ;

/-
The limit of B^(1/n(B)) as B goes to infinity is 2.
-/
theorem growthBase_tendsto_two : Tendsto growthBase atTop (𝓝 2) := by
  -- Using the bounds on $B$, we can show that $B^{1/n(B)}$ is squeezed between $2 \cos(\frac{\pi}{n+2})$ and $2 \cos(\frac{\pi}{n+3}) \cdot (2 \cos(\frac{\pi}{n+3}))^{\frac{1}{n}}$.
  have h_squeeze : ∀ B > 1, 2 * Real.cos (Real.pi / (nSteps B + 2)) ≤ growthBase B ∧ growthBase B ≤ 2 * Real.cos (Real.pi / (nSteps B + 3)) * (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ (1 / (nSteps B : ℝ)) := by
    intro B hB
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ InStepRange B n ∧ n = nSteps B := by
      exact ⟨ _, nSteps_spec hB |>.1, nSteps_spec hB |>.2, rfl ⟩;
    -- Using the bounds from Definition~\ref{def:breakpoints}, we have:
    have h_bounds : (2 * Real.cos (Real.pi / (n + 2))) ^ (n : ℝ) ≤ B ∧ B ≤ (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1 : ℝ) := by
      rcases n <;> norm_num [ stepBreakpoint ] at *;
      exact ⟨ mod_cast hn.1.1.le, mod_cast hn.1.2 ⟩;
    -- Taking the $n$-th root of the bounds, we get:
    have h_root_bounds : (2 * Real.cos (Real.pi / (n + 2))) ≤ B ^ (1 / (n : ℝ)) ∧ B ^ (1 / (n : ℝ)) ≤ (2 * Real.cos (Real.pi / (n + 3))) * (2 * Real.cos (Real.pi / (n + 3))) ^ (1 / (n : ℝ)) := by
      constructor;
      · exact le_trans ( by rw [ ← Real.rpow_mul ( by exact mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ⟩ ) ) ] ; norm_num [ show n ≠ 0 by linarith ] ) ( Real.rpow_le_rpow ( by exact Real.rpow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ⟩ ) ) _ ) h_bounds.1 <| by positivity );
      · convert Real.rpow_le_rpow ( by positivity ) h_bounds.2 _ using 1;
        · rw [ ← Real.rpow_mul ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ⟩ ) ), mul_comm ] ; ring_nf ; norm_num [ show n ≠ 0 by linarith ] ; ring_nf;
          rw [ Real.rpow_add ( mul_pos ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast; linarith, inv_mul_cancel₀ ( by linarith : ( 3 + n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast; linarith, inv_mul_cancel₀ ( by linarith : ( 3 + n : ℝ ) ≠ 0 ) ] ⟩ ) zero_lt_two ), Real.rpow_one ] ; ring;
        · positivity;
    unfold growthBase; aesop;
  -- As $B \to \infty$, $n(B) \to \infty$, so we can apply the squeeze theorem.
  have h_lim : Filter.Tendsto (fun B : ℝ => 2 * Real.cos (Real.pi / (nSteps B + 2))) atTop (nhds 2) ∧ Filter.Tendsto (fun B : ℝ => 2 * Real.cos (Real.pi / (nSteps B + 3)) * (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ (1 / (nSteps B : ℝ))) atTop (nhds 2) := by
    have h_cos_lim : Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 2))) Filter.atTop (nhds 2) ∧ Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 3)) * (2 * Real.cos (Real.pi / (n + 3))) ^ (1 / (n : ℝ))) Filter.atTop (nhds 2) := by
      constructor;
      · exact le_trans ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| by norm_num;
      · exact le_trans ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| Filter.Tendsto.rpow ( tendsto_const_nhds.mul <| Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ( tendsto_one_div_atTop_nhds_zero_nat ) <| by norm_num ) <| by norm_num;
    exact ⟨ h_cos_lim.1.comp <| nSteps_tendsto_atTop, h_cos_lim.2.comp <| nSteps_tendsto_atTop ⟩;
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim.1 h_lim.2 _ _;
  · filter_upwards [ Filter.eventually_gt_atTop 1 ] with B hB using h_squeeze B hB |>.1;
  · filter_upwards [ Filter.eventually_gt_atTop 1 ] with B hB using h_squeeze B hB |>.2

/-
The limit of the first guess x(B) as B goes to infinity is 4.
-/
theorem firstGuess_tendsto_four : Tendsto firstGuess atTop (𝓝 4) := by
  -- Let $B > 1$ and set $n = n(B)$.
  have h_bound : ∀ B > 1, ratioLower (nSteps B) ≤ firstGuess B ∧ firstGuess B ≤ ratioUpper (nSteps B) := by
    intro B hB;
    have := nSteps_spec hB;
    have := Classical.choose_spec ( existsUnique_ratio_of_inStepRange this.1 this.2 ) |>.1;
    unfold firstGuess; aesop;
  -- We will show that both `ratioLower` and `ratioUpper` tend to 4 as `n` tends to infinity.
  have h_ratio_lower : Filter.Tendsto ratioLower Filter.atTop (nhds 4) := by
    exact le_trans ( tendsto_const_nhds.mul ( Filter.Tendsto.pow ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun n => by norm_cast; linarith ) tendsto_natCast_atTop_atTop ) _ ) ) ( by norm_num )
  have h_ratio_upper : Filter.Tendsto ratioUpper Filter.atTop (nhds 4) := by
    exact le_trans ( tendsto_const_nhds.mul ( Filter.Tendsto.pow ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun _ => by norm_cast; linarith ) tendsto_natCast_atTop_atTop ) _ ) ) ( by norm_num );
  -- By the squeeze theorem, since `ratioLower` and `ratioUpper` tend to 4 and `firstGuess` is squeezed between them, `firstGuess` must also tend to 4.
  have h_squeeze : Filter.Tendsto (fun B => ratioLower (nSteps B)) Filter.atTop (nhds 4) ∧ Filter.Tendsto (fun B => ratioUpper (nSteps B)) Filter.atTop (nhds 4) := by
    exact ⟨ h_ratio_lower.comp <| nSteps_tendsto_atTop, h_ratio_upper.comp <| nSteps_tendsto_atTop ⟩;
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze.1 h_squeeze.2 ( Filter.eventually_atTop.2 ⟨ 2, fun B hB => h_bound B ( by linarith ) |>.1 ⟩ ) ( Filter.eventually_atTop.2 ⟨ 2, fun B hB => h_bound B ( by linarith ) |>.2 ⟩ )

/-
If y is in the interval (x_{k-1}, x_k], then the hit index is k.
-/
lemma hitIndex_eq_of_mem_Ioc {s : Strategy} {k : ℕ} {y : ℝ} (hy1 : 1 ≤ y)
    (h_lt : if k = 0 then 1 < y else s.x (k - 1) < y) (h_le : y ≤ s.x k) :
    hitIndex s ⟨y, hy1⟩ = k := by
      refine' le_antisymm _ _;
      · exact Nat.find_min' _ h_le;
      · refine' Nat.le_of_not_gt fun h => _;
        -- Since $k > hitIndex s ⟨y, hy1⟩$, we have $s.x (hitIndex s ⟨y, hy1⟩) \geq y$.
        have h_ge_y : s.x (hitIndex s ⟨y, hy1⟩) ≥ y := by
          exact Nat.find_spec ( s.hits hy1 );
        split_ifs at h_lt <;> linarith [ s.mono ( Nat.le_sub_one_of_lt h ) ]

/-
The hit index for y=1 is 0.
-/
lemma hitIndex_one (s : Strategy) : hitIndex s ⟨1, le_refl 1⟩ = 0 := by
  exact le_antisymm ( Nat.find_le <| by simpa using s.one_le ) ( Nat.zero_le _ )

/-
The union of the intervals (x_{k-1}, x_k] is the set of all real numbers greater than 1.
-/
lemma union_Ioc_eq_Ioi_one (s : Strategy) :
    (⋃ k, Set.Ioc (if k = 0 then 1 else s.x (k - 1)) (s.x k)) = Set.Ioi 1 := by
      ext x;
      simp +zetaDelta at *;
      constructor;
      · rintro ⟨ i, hi ⟩ ; split_ifs at hi <;> linarith [ s.nonneg 0, s.one_le, s.mono ( Nat.zero_le ( i - 1 ) ) ] ;
      · -- Since $x > 1$, there exists some $n$ such that $x \leq s.x n$.
        intro hx
        obtain ⟨n, hn⟩ : ∃ n, x ≤ s.x n := by
          exact s.hits hx.le;
        induction' n with n ih;
        · exact ⟨ 0, by aesop ⟩;
        · by_cases h : x ≤ s.x n <;> aesop

/-
The worst-case score is the supremum of the ratios S_{k+1}/x_k.
-/
lemma boundary_reduction (s : Strategy) :
    worstCaseScore s = ⨆ k : ℕ, ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1)) := by
      refine' le_antisymm _ _ <;> norm_num [ worstCaseScore, score ];
      · intro a ha;
        refine' le_trans _ ( le_iSup _ ( hitIndex s ⟨ a, ha ⟩ ) );
        rcases k : hitIndex s ⟨ a, ha ⟩ with ( _ | k ) <;> simp_all +decide [ div_eq_mul_inv ];
        · exact ENNReal.ofReal_le_ofReal ( mul_le_of_le_one_right ( Finset.sum_nonneg fun _ _ => s.nonneg _ ) ( inv_le_one_of_one_le₀ ha ) );
        · gcongr;
          · exact Finset.sum_nonneg fun _ _ => s.nonneg _;
          · exact lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) );
          · contrapose! k;
            exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.find_min' _ k.le ) );
      · intro k;
        by_cases hk : k = 0 <;> simp_all +decide [ partialSum ];
        · refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num ⟩ );
          · norm_num [ Finset.sum_range_succ, hitIndex_one ];
          · bound;
        · -- Consider $y = s.x (k - 1) + \epsilon$ for some small $\epsilon > 0$.
          have h_eps : ∀ ε > 0, ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), s.x i) / (s.x (k - 1) + ε)) ≤ ⨆ y : {y : ℝ // 1 ≤ y}, ENNReal.ofReal ((∑ i ∈ Finset.range (hitIndex s y + 1), s.x i) / y.1) := by
            intro ε hε_pos
            have h_eps_le : ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), s.x i) / (s.x (k - 1) + ε)) ≤ ENNReal.ofReal ((∑ i ∈ Finset.range (hitIndex s ⟨s.x (k - 1) + ε, by
              linarith [ s.nonneg ( k - 1 ), show 1 ≤ s.x ( k - 1 ) from Nat.recOn ( k - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ]⟩ + 1), s.x i) / (s.x (k - 1) + ε)) := by
              all_goals generalize_proofs at *;
              gcongr;
              · exact fun _ _ _ => s.nonneg _;
              · refine' Nat.le_of_not_lt fun h => _;
                have := Nat.find_spec ( s.hits ( show 1 ≤ s.x ( k - 1 ) + ε by linarith ) );
                exact this.not_gt <| lt_of_le_of_lt ( s.mono <| Nat.le_sub_one_of_lt h ) <| lt_add_of_pos_right _ hε_pos
            generalize_proofs at *;
            exact le_trans h_eps_le ( le_iSup_of_le ⟨ s.x ( k - 1 ) + ε, by assumption ⟩ ( by aesop ) );
          -- Taking the limit as $\epsilon \to 0$, we get the desired inequality.
          have h_lim : Filter.Tendsto (fun ε => ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), s.x i) / (s.x (k - 1) + ε))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), s.x i) / s.x (k - 1)))) := by
            refine' ENNReal.tendsto_ofReal _;
            exact tendsto_const_nhds.div ( tendsto_nhdsWithin_of_tendsto_nhds ( by norm_num [ Filter.Tendsto ] ) ) ( by linarith [ show 0 < s.x ( k - 1 ) from lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) ] );
          exact le_of_tendsto h_lim ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_eps ε hε )

/-
Define the doubling strategy x_n = 2^n.
-/
def doublingStrategy : Strategy :=
  { x := fun n => 2 ^ n
    nonneg := fun n => by
      positivity
    one_le := by
      norm_num
    mono := fun i j hij => by
      exact pow_le_pow_right₀ ( by norm_num ) hij
    hits := fun {y} hy => by
      exact pow_unbounded_of_one_lt y one_lt_two |> fun ⟨ n, hn ⟩ => ⟨ n, hn.le ⟩ }

/-
The worst-case score of the doubling strategy is 4.
-/
theorem doublingStrategy_worstCaseScore_eq_four : worstCaseScore doublingStrategy = 4 := by
  -- Using boundary_reduction, we need to compute the sup of (S_k / x_{k-1}).
  have h_boundary : worstCaseScore doublingStrategy = ⨆ k : ℕ, ENNReal.ofReal (partialSum doublingStrategy k / if k = 0 then 1 else doublingStrategy.x (k - 1)) := by
    exact boundary_reduction doublingStrategy;
  -- Let's simplify the expression for the supremum.
  have h_simplify : ∀ k : ℕ, k ≠ 0 → ENNReal.ofReal (partialSum doublingStrategy k / if k = 0 then 1 else doublingStrategy.x (k - 1)) = ENNReal.ofReal (4 - 1 / 2 ^ (k - 1)) := by
    intro k hk; rcases k with ( _ | k ) <;> norm_num [ partialSum, Finset.sum_range_succ, doublingStrategy ] at *;
    norm_num [ pow_succ, geom_sum_eq ] ; ring_nf;
    norm_num [ ← mul_pow ] ; ring_nf;
  -- Taking the limit as $k$ approaches infinity, we get $\lim_{k \to \infty} (4 - 1 / 2^{k-1}) = 4$.
  have h_limit : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (4 - 1 / 2 ^ (k - 1))) Filter.atTop (nhds (ENNReal.ofReal 4)) := by
    exact le_trans ( ENNReal.tendsto_ofReal ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat _ ) ) ) ) ( by norm_num );
  -- Since the supremum of a set of numbers that approach 4 is 4, we can conclude that the worst-case score is 4.
  have h_sup : ⨆ k : ℕ, ENNReal.ofReal (partialSum doublingStrategy k / if k = 0 then 1 else doublingStrategy.x (k - 1)) = ENNReal.ofReal 4 := by
    refine' le_antisymm _ _;
    · refine' iSup_le _;
      intro k; by_cases hk : k = 0 <;> simp_all +decide;
      unfold partialSum; norm_num [ doublingStrategy ];
    · exact le_of_tendsto h_limit ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => by rw [ ← h_simplify k ( by linarith ) ] ; exact le_iSup_of_le k le_rfl ⟩ );
  aesop

/-
The sequence a_k satisfies a recurrence relation derived from the worst-case score bound.
-/
noncomputable def a_seq (s : Strategy) (k : ℕ) : ℝ :=
  partialSum s k / s.x k

lemma a_seq_recurrence {s : Strategy} {R : ℝ} (h_score : worstCaseScore s ≤ ENNReal.ofReal R) (k : ℕ) :
    a_seq s k ≤ R - 1 ∧ a_seq s (k + 1) ≥ R / (R - a_seq s k) := by
      -- By definition of $a_seq$, we know that $S_{k+1} / x_k \leq R$.
      have h_ak_le_R : ∀ k, partialSum s (k + 1) / s.x k ≤ R := by
        rw [ boundary_reduction ] at h_score;
        intro k; contrapose! h_score;
        refine' lt_of_lt_of_le _ ( le_iSup _ ( k + 1 ) );
        rw [ ENNReal.ofReal_lt_ofReal_iff ];
        · exact h_score;
        · refine' div_pos _ _ <;> norm_num [ partialSum ];
          · exact lt_of_lt_of_le ( by linarith [ s.one_le ] ) ( Finset.single_le_sum ( fun i _ => s.nonneg i ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) );
          · exact lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) );
      -- By definition of $a_seq$, we know that $a_{k+1} = 1 + a_k / t_{k+1}$ where $t_{k+1} = x_{k+1} / x_k$.
      have h_ak1 : a_seq s (k + 1) = 1 + a_seq s k / (s.x (k + 1) / s.x k) := by
        unfold a_seq partialSum;
        rw [ Finset.sum_range_succ, add_div' ] <;> ring_nf <;> norm_num [ ne_of_gt ( show 0 < s.x k from lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) ) ];
        exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) );
      -- Since $t_{k+1} \leq R - a_k$, we have $a_{k+1} \geq 1 + a_k / (R - a_k)$.
      have h_ak1_ge : a_seq s (k + 1) ≥ 1 + a_seq s k / (R - a_seq s k) := by
        rw [h_ak1];
        gcongr;
        · exact div_nonneg ( Finset.sum_nonneg fun _ _ => s.nonneg _ ) ( s.nonneg _ );
        · exact div_pos ( lt_of_lt_of_le ( show 0 < s.x 0 from by linarith [ s.one_le ] ) ( s.mono ( Nat.zero_le _ ) ) ) ( lt_of_lt_of_le ( show 0 < s.x 0 from by linarith [ s.one_le ] ) ( s.mono ( Nat.zero_le _ ) ) );
        · have := h_ak_le_R k;
          unfold partialSum a_seq at *;
          unfold partialSum; norm_num [ Finset.sum_range_succ ] at *; ring_nf at *; linarith;
      have h_ak_le_R_minus_1 : a_seq s k ≤ R - 1 := by
        have := h_ak_le_R k;
        rw [ div_le_iff₀ ] at this;
        · rw [ show partialSum s ( k + 1 ) = partialSum s k + s.x ( k + 1 ) by exact Finset.sum_range_succ _ _ ] at this;
          rw [ le_sub_iff_add_le ];
          rw [ show a_seq s k = partialSum s k / s.x k from rfl, div_add_one, div_le_iff₀ ] <;> nlinarith [ show 0 < s.x k from lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ), show s.x ( k + 1 ) ≥ s.x k from s.mono ( Nat.le_succ _ ) ];
        · exact lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) );
      grind

/-
Define the function g and the sequence b_n.
-/
noncomputable def g (R a : ℝ) : ℝ := R / (R - a)

noncomputable def b_seq (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => g R (b_seq R n)

/-
If 1 < R < 4 and a < R, then g(R, a) > a.
-/
lemma g_gt_self_of_lt_R {R a : ℝ} (hR : 1 < R) (hR4 : R < 4) (ha : a < R) : g R a > a := by
  unfold g;
  rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ sq_nonneg ( a - R / 2 ) ]

/-
The function g(R, a) is monotone increasing in a for a < R.
-/
lemma g_monotone {R a b : ℝ} (hR : 0 < R) (ha : a < R) (hb : b < R) (hab : a ≤ b) : g R a ≤ g R b := by
  exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( by linarith ) ( by linarith ) ) hR.le

/-
The sequence b_k is a lower bound for a_k.
-/
lemma b_seq_le_a_seq {s : Strategy} {R : ℝ} (h_score : worstCaseScore s ≤ ENNReal.ofReal R)
    (hR : 1 < R) (k : ℕ) : b_seq R k ≤ a_seq s k := by
      induction' k with k ih;
      · unfold a_seq b_seq;
        unfold partialSum;
        rw [ Finset.sum_range_one, le_div_iff₀ ] <;> linarith [ s.nonneg 0, s.one_le ];
      · -- By definition of $b_seq$, we have $b_seq R (k + 1) = g R (b_seq R k)$.
        have h_b_succ : b_seq R (k + 1) = g R (b_seq R k) := by
          rfl;
        refine' h_b_succ ▸ le_trans ( g_monotone _ _ _ ih ) _;
        · linarith;
        · have := a_seq_recurrence h_score k;
          linarith;
        · exact lt_of_le_of_lt ( a_seq_recurrence h_score k |>.1 ) ( by linarith );
        · exact a_seq_recurrence h_score k |>.2

/-
If 0 < R < 4, then g(R, x) is never equal to x.
-/
lemma no_fixed_point_of_lt_four {R x : ℝ} (hR1 : 0 < R) (hR4 : R < 4) : g R x ≠ x := by
  by_contra h_contra;
  unfold g at h_contra;
  rw [ div_eq_iff ] at h_contra;
  · nlinarith [ sq_nonneg ( x - R / 2 ) ];
  · aesop

/-
If the sequence b_n is bounded by R-1, we reach a contradiction (for 1 < R < 4).
-/
lemma b_seq_unbounded_aux {R : ℝ} (hR1 : 1 < R) (hR4 : R < 4) (h_bound : ∀ n, b_seq R n ≤ R - 1) : False := by
  -- Since $b_n$ is strictly increasing and bounded above by $R-1$, it converges to some limit $L \le R-1$.
  obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto (fun n => b_seq R n) Filter.atTop (nhds L) := by
    have h_monotone : Monotone (fun n => b_seq R n) := by
      refine' monotone_nat_of_le_succ _;
      intro n;
      exact le_of_lt ( g_gt_self_of_lt_R hR1 hR4 ( by linarith [ h_bound n ] ) );
    exact ⟨ _, tendsto_atTop_isLUB h_monotone ( isLUB_ciSup ⟨ R - 1, Set.forall_mem_range.mpr h_bound ⟩ ) ⟩;
  -- Since $g$ is continuous on $(-\infty, R)$, and $b_n \to L < R$, $g(b_n) \to g(L)$.
  have h_cont : Filter.Tendsto (fun n => g R (b_seq R n)) Filter.atTop (nhds (g R L)) := by
    exact Filter.Tendsto.div tendsto_const_nhds ( tendsto_const_nhds.sub hL ) ( by linarith [ show L < R from lt_of_le_of_lt ( le_of_tendsto_of_tendsto' hL tendsto_const_nhds fun n => h_bound n ) ( by linarith ) ] );
  -- But $g(b_n) = b_{n+1} \to L$.
  have h_eq : Filter.Tendsto (fun n => b_seq R (n + 1)) Filter.atTop (nhds L) := by
    exact hL.comp ( Filter.tendsto_add_atTop_nat 1 );
  exact absurd ( tendsto_nhds_unique h_cont ( by simpa using h_eq ) ) ( by exact no_fixed_point_of_lt_four ( by linarith ) hR4 )

/-
The value of the unbounded game is 4.
-/
theorem unbounded_value_eq_four : gameValue = 4 := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, Set.forall_mem_range.2 fun s => zero_le _ ⟩;
    · exact ⟨ doublingStrategy, doublingStrategy_worstCaseScore_eq_four ⟩;
  · -- By definition of $V_\infty$, if $V_\infty < 4$, then there exists a strategy $s$ with $W = \text{worstCaseScore}(s) < 4$.
    by_contra h_contra
    obtain ⟨s, hs⟩ : ∃ s : Strategy, worstCaseScore s < 4 := by
      simp_all +decide [ gameValue ];
    -- Let $r = \text{ENNReal.toReal}(W)$. Since $W < 4$, $r < 4$.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, worstCaseScore s = ENNReal.ofReal r ∧ r < 4 := by
      have h_real : ∃ r : ℝ, worstCaseScore s = ENNReal.ofReal r := by
        refine' ⟨ _, Eq.symm <| ENNReal.ofReal_toReal _ ⟩;
        aesop;
      aesop;
    -- Let $R = \max(r, 2)$. Then $1 < R < 4$ and $W \le R$.
    set R : ℝ := max r 2
    have hR1 : 1 < R := by
      exact lt_max_of_lt_right ( by norm_num )
    have hR4 : R < 4 := by
      grind
    have hW_le_R : worstCaseScore s ≤ ENNReal.ofReal R := by
      exact hr.1.symm ▸ ENNReal.ofReal_le_ofReal ( le_max_left _ _ );
    exact b_seq_unbounded_aux hR1 hR4 fun n => by linarith [ b_seq_le_a_seq hW_le_R hR1 n, a_seq_recurrence hW_le_R n |>.1 ] ;

/-
For the tight strategy defined by tight polynomials, the partial sum of the first k+1 terms equals R times the k-th term.
-/
theorem tight_strategies_sum (n : ℕ) (R : ℝ) :
    ∀ k, k < n → ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R = R * tightPoly k R := by
      intro k hk;
      induction k <;> simp_all +decide [ Finset.sum_range_succ ];
      · -- By definition of tightPoly, we have tightPoly 0 R = 1.
        have h_tightPoly0 : tightPoly 0 R = 1 := by
          rfl;
        aesop;
      · rename_i k ih; rw [ ih ( Nat.lt_of_succ_lt hk ) ] ; rw [ show tightPoly ( k + 2 ) R = R * ( tightPoly ( k + 1 ) R - tightPoly k R ) from rfl ] ; ring;

/-
The union of the intervals (x_{k-1}, x_k] for k from 0 to n is the interval (1, B].
-/
lemma union_Ioc_eq_Ioc_one_B {s : Strategy} {B : ℝ} {n : ℕ} (h_n : s.x n = B) :
    (⋃ k ∈ Finset.range (n + 1), Set.Ioc (if k = 0 then 1 else s.x (k - 1)) (s.x k)) = Set.Ioc 1 B := by
      ext y;
      norm_num +zetaDelta at *;
      constructor;
      · rintro ⟨ i, hi₁, hi₂, hi₃ ⟩ ; exact ⟨ by split_ifs at hi₁ <;> linarith [ show 1 ≤ s.x 0 from s.one_le, show s.x ( i - 1 ) ≥ 1 from Nat.recOn ( i - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ], by linarith [ show s.x i ≤ s.x n from s.mono hi₂ ] ⟩ ;
      · intro hy;
        -- By the properties of the range, there exists some $k$ such that $s.x (k - 1) < y$ and $y \leq s.x k$.
        obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range (n + 1), y ≤ s.x k ∧ ∀ j ∈ Finset.range k, s.x j < y := by
          have h_exists_k : ∃ k ∈ Finset.range (n + 1), y ≤ s.x k := by
            exact ⟨ n, Finset.mem_range.mpr ( Nat.lt_succ_self _ ), by linarith ⟩;
          exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => lt_of_not_ge fun h => Nat.find_min h_exists_k ( Finset.mem_range.mp hj ) ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp ( Nat.find_spec h_exists_k |>.1 ), Finset.mem_range.mp hj ] ), h ⟩ ⟩;
        rcases k <;> aesop

/-
If y is in the interval (x_{k-1}, x_k], then the score is S_k/y.
-/
lemma score_eq_of_mem_Ioc {s : Strategy} {k : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioc (if k = 0 then 1 else s.x (k - 1)) (s.x k)) (hy1 : 1 ≤ y) :
    score s ⟨y, hy1⟩ = ENNReal.ofReal (partialSum s k / y) := by
      unfold score;
      rw [ hitIndex_eq_of_mem_Ioc hy1 ];
      · aesop;
      · exact hy.2

/-
The bounded worst-case score is at most the maximum of the ratios S_{k+1}/x_k.
-/
lemma bounded_boundary_reduction_le {s : Strategy} {B : ℝ} {n : ℕ}
    (h_n : s.x n = B) (h_prev : n = 0 ∨ s.x (n - 1) < B) :
    boundedWorstCaseScore s B ≤ ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1)) := by
      -- Let $y \in [1, B]$. We want to show $\text{score}(y) \le \text{RHS}$.
      have h_score_le : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, score s ⟨y.1, y.2.1⟩ ≤ ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (partialSum s k / (if k = 0 then 1 else s.x (k - 1))) := by
        -- If $y > 1$, then $y \in (1, B]$. By `union_Ioc_eq_Ioc_one_B`, there exists $k \in \{0, \dots, n\}$ such that $y \in (x_{k-1}, x_k]$ (with $x_{-1}=1$).
        intros y
        by_cases hy1 : y.val = 1;
        · simp +zetaDelta at *;
          refine' le_trans _ ( le_iSup₂_of_le 0 ( Nat.zero_le n ) _ ) <;> norm_num [ hy1 ];
          convert le_rfl;
          unfold score partialSum;
          rw [ hitIndex_one ] ; norm_num;
        · -- If $y > 1$, then $y \in (1, B]$. By `union_Ioc_eq_Ioc_one_B`, there exists $k \in \{0, \dots, n\}$ such that $y \in (x_{k-1}, x_k]$.
          obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range (n + 1), y.val ∈ Set.Ioc (if k = 0 then 1 else s.x (k - 1)) (s.x k) := by
            have := union_Ioc_eq_Ioc_one_B ( s := s ) ( n := n ) ( h_n := h_n ) |> fun h => h.symm.subset ( show ( y : ℝ ) ∈ Set.Ioc 1 B from ⟨ lt_of_le_of_ne y.2.1 ( Ne.symm hy1 ), y.2.2 ⟩ ) ; aesop;
          -- By `score_eq_of_mem_Ioc`, $\text{score}(y) = S_{k+1}/y$.
          have h_score_eq : score s ⟨y.val, by
            exact y.2.1⟩ = ENNReal.ofReal (partialSum s k / y.val) := by
            convert score_eq_of_mem_Ioc hk.2 _ using 1
          generalize_proofs at *;
          refine' le_trans _ ( le_iSup₂_of_le k hk.1 _ );
          exact h_score_eq.le;
          gcongr;
          · exact Finset.sum_nonneg fun _ _ => s.nonneg _;
          · field_simp;
            split_ifs <;> linarith [ s.nonneg ( k - 1 ), s.one_le, show ( 1 : ℝ ) ≤ s.x ( k - 1 ) from Nat.recOn ( k - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ];
          · exact hk.2.1.le;
      exact iSup_le fun y => h_score_le y

/-
The bounded worst-case score is at least the maximum of the ratios S_{k+1}/x_k.
-/
lemma bounded_boundary_reduction_ge {s : Strategy} {B : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x n = B) :
    boundedWorstCaseScore s B ≥ ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1)) := by
      refine' iSup₂_le _;
      intro i hi;
      by_cases hi0 : i = 0 <;> simp_all
      · refine' le_trans _ ( le_ciSup _ ⟨ 1, _ ⟩ ) <;> norm_num [ partialSum ];
        all_goals norm_num [ boundedScore, score ];
        · exact ENNReal.ofReal_le_ofReal ( by exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun a _ => s.nonneg a ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ) );
        linarith [ s.one_le, h_strict.monotone ( Nat.zero_le n ) ];
      · -- Consider the sequence $y_m \downarrow x_{i-1}$ with $y_m \in (x_{i-1}, x_i]$.
        obtain ⟨y_m, hy_m⟩ : ∃ y_m : ℕ → ℝ, (∀ m, y_m m ∈ Set.Ioc (s.x (i - 1)) (s.x i)) ∧ Filter.Tendsto y_m Filter.atTop (nhds (s.x (i - 1))) := by
          use fun m => s.x (i - 1) + (s.x i - s.x (i - 1)) / (m + 2);
          exact ⟨ fun m => ⟨ lt_add_of_pos_right _ <| div_pos ( sub_pos.mpr <| h_strict <| Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ) <| by positivity, by rw [ add_div', div_le_iff₀ ] <;> nlinarith [ h_strict <| Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ] ⟩, by
            have h_inv : Filter.Tendsto (fun m : ℕ => (((m + 2 : ℕ) : ℝ))⁻¹)
                Filter.atTop (nhds 0) := by
              have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
                (Filter.tendsto_add_atTop_nat 1))
              change Filter.Tendsto (fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) + 1))
                Filter.atTop (nhds 0) at h
              convert h using 1
              · ext m
                norm_num [Nat.cast_add, one_div]
                ring
            have h_const : Filter.Tendsto (fun _ : ℕ => (s.x i - s.x (i - 1) : ℝ))
                Filter.atTop (nhds (s.x i - s.x (i - 1))) := tendsto_const_nhds
            have h_prod : Filter.Tendsto
                (fun m : ℕ => (s.x i - s.x (i - 1)) * (((m + 2 : ℕ) : ℝ))⁻¹)
                Filter.atTop (nhds 0) := by
              simpa [zero_mul] using h_const.mul h_inv
            simpa [div_eq_mul_inv, zero_mul, add_zero] using
              tendsto_const_nhds.add h_prod ⟩;
        -- Since $\text{score}(y_m) = S_{i+1}/y_m \to S_{i+1}/x_{i-1}$, and $\text{score}(y_m) \le \text{boundedWorstCaseScore}$, the limit is also $\le$.
        have h_lim : Filter.Tendsto (fun m => score s ⟨y_m m, by
          exact le_trans ( s.one_le.trans ( h_strict.monotone ( Nat.zero_le _ ) ) ) ( hy_m.1 m |>.1.le )⟩) Filter.atTop (nhds (ENNReal.ofReal (partialSum s i / s.x (i - 1)))) := by
          all_goals generalize_proofs at *;
          have h_lim : Filter.Tendsto (fun m => ENNReal.ofReal (partialSum s i / y_m m)) Filter.atTop (nhds (ENNReal.ofReal (partialSum s i / s.x (i - 1)))) := by
            exact ENNReal.tendsto_ofReal ( tendsto_const_nhds.div hy_m.2 <| ne_of_gt <| lt_of_lt_of_le ( show 0 < s.x ( i - 1 ) from lt_of_lt_of_le ( show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one <| s.one_le ) <| s.mono <| Nat.zero_le _ ) <| le_rfl )
          generalize_proofs at *;
          convert h_lim using 2;
          rw [ score_eq_of_mem_Ioc ] ; aesop
        generalize_proofs at *;
        refine' le_of_tendsto h_lim _;
        refine' Filter.Eventually.of_forall fun m => _;
        refine' le_iSup_of_le ⟨ y_m m, by
          (expose_names; exact pf m), _ ⟩ le_rfl
        generalize_proofs at *;
        exact le_trans ( hy_m.1 m |>.2 ) ( h_n ▸ h_strict.monotone hi )

/-
If x_{k-1} = x_k, then the k-th term is less than or equal to the (k+1)-th term.
-/
noncomputable def term (s : Strategy) (k : ℕ) : ENNReal :=
  ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1))

lemma term_mono_of_eq {s : Strategy} {k : ℕ} (h_eq : s.x (k - 1) = s.x k) (hk : k > 0) :
    term s k ≤ term s (k + 1) := by
      unfold term;
      unfold partialSum;
      rw [ ENNReal.ofReal_le_ofReal_iff ] <;> norm_num [ Finset.sum_range_succ, h_eq ];
      · rw [ if_neg hk.ne' ];
        gcongr
        · linarith [ s.nonneg k, s.nonneg ( k + 1 ) ];
        · exact le_add_of_nonneg_right ( s.nonneg _ );
        · exact s.mono ( Nat.le_succ _ );
      · exact div_nonneg ( add_nonneg ( add_nonneg ( Finset.sum_nonneg fun _ _ => s.nonneg _ ) ( s.nonneg _ ) ) ( s.nonneg _ ) ) ( s.nonneg _ )

/-
If x_{k-1} = x_k, then the k-th score term is less than or equal to the (k+1)-th score term.
-/
noncomputable def scoreTerm (s : Strategy) (k : ℕ) : ENNReal :=
  ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1))

lemma scoreTerm_mono_of_eq {s : Strategy} {k : ℕ} (h_eq : s.x (k - 1) = s.x k) (hk : k > 0) :
    scoreTerm s k ≤ scoreTerm s (k + 1) := by
      apply term_mono_of_eq h_eq hk

/-
The bounded worst-case score is the maximum of the ratios S_{k+1}/x_k (assuming strict strategy).
-/
lemma bounded_boundary_reduction {s : Strategy} {B : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x n = B) (h_prev : n = 0 ∨ s.x (n - 1) < B) :
    boundedWorstCaseScore s B = ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1)) := by
      exact le_antisymm ( bounded_boundary_reduction_le h_n h_prev ) ( bounded_boundary_reduction_ge h_strict h_n )

/-
Each score term is bounded by the bounded worst-case score.
-/
lemma scoreTerm_le_boundedWorstCaseScore {s : Strategy} {B : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x) (h_n : s.x n = B) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    scoreTerm s k ≤ boundedWorstCaseScore s B := by
      have h_term_le : ∀ k ∈ Finset.range (n + 1), scoreTerm s k ≤ ⨆ k ∈ Finset.range (n + 1), scoreTerm s k := by
        exact fun k hk => le_iSup₂_of_le k hk le_rfl;
      norm_num +zetaDelta at *;
      convert h_term_le k hk using 1;
      convert bounded_boundary_reduction h_strict h_n _ using 1;
      · simp +decide [ Finset.mem_range, scoreTerm ];
      · rcases n <;> aesop

/-
There exists a later index m with a strict increase (or m=0) that dominates the k-th score term.
-/
lemma exists_strict_ge {s : Strategy} {n k : ℕ} (hk : k < n) (h_n : s.x (n - 1) = B)
    (h_prev : n = 1 ∨ s.x (n - 2) < B) :
    ∃ m, k ≤ m ∧ m < n ∧ (m = 0 ∨ s.x (m - 1) < s.x m) ∧ scoreTerm s k ≤ scoreTerm s m := by
      -- We proceed by induction on $n - k$.
      induction' hnk : n - k with m ih generalizing k;
      · omega;
      · by_cases h_eq : s.x (k - 1) = s.x k ∧ k > 0;
        · -- Since $s.x (k - 1) = s.x k$, we have $scoreTerm s k ≤ scoreTerm s (k + 1)$.
          have h_score_term_le : scoreTerm s k ≤ scoreTerm s (k + 1) := by
            apply scoreTerm_mono_of_eq; exact h_eq.left; exact h_eq.right;
          obtain ⟨ m, hm₁, hm₂, hm₃, hm₄ ⟩ := ih ( show k + 1 < n from lt_of_le_of_ne hk ( by aesop_cat ) ) ( by omega ) ; exact ⟨ m, by linarith, by linarith, hm₃, h_score_term_le.trans hm₄ ⟩;
        · by_cases hk0 : k = 0
          · subst k
            exact ⟨ 0, le_rfl, hk, Or.inl rfl, le_rfl ⟩;
          · exact ⟨ k, le_rfl, hk, by
              right
              by_contra hle
              have hmono : s.x (k - 1) ≤ s.x k := s.mono (Nat.sub_le k 1)
              have heq : s.x (k - 1) = s.x k := le_antisymm hmono (by linarith)
              exact h_eq ⟨heq, Nat.pos_of_ne_zero hk0⟩, le_rfl ⟩

/-
The first guess $x_0$ is bounded by $R$.
-/
lemma recurrence_start {s : Strategy} {B R : ℝ}
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hB : 1 ≤ B) (h_x0 : s.x 0 ≤ B) : s.x 0 ≤ R := by
      -- By considering the score when $y = 1$, we have $\text{score}(s, 1) = s.x 0$.
      have h_score_one : score s ⟨1, by linarith⟩ = ENNReal.ofReal (s.x 0) := by
        unfold score;
        unfold partialSum; norm_num [ hitIndex_one ] ;
      have h_le_R : ENNReal.ofReal (s.x 0) ≤ ENNReal.ofReal R := by
        refine' le_trans _ h_score;
        exact h_score_one ▸ le_iSup_of_le ⟨ 1, by norm_num, hB ⟩ ( le_rfl );
      rw [ ENNReal.ofReal_le_ofReal_iff ] at h_le_R <;> try linarith [ s.nonneg 0 ];
      contrapose! h_le_R;
      rw [ ENNReal.ofReal_eq_zero.mpr h_le_R.le ] ; exact ENNReal.ofReal_pos.mpr ( by linarith [ s.one_le ] )

/-
For a strictly increasing strategy, the guesses satisfy the recurrence $x_k \le R x_{k-1} - S_{k-1}$.
-/
lemma recurrence_strict {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    s.x 0 ≤ R ∧ ∀ k, 1 ≤ k → k < n → s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
      have := bounded_boundary_reduction_ge h_strict h_n;
      refine' ⟨ _, _ ⟩;
      · convert recurrence_start h_score _ _;
        · exact h_n ▸ s.one_le.trans ( h_strict.monotone ( Nat.zero_le _ ) );
        · exact h_n ▸ h_strict.monotone ( Nat.zero_le _ );
      · intro k hk₁ hk₂
        have h_partialSum : partialSum s k ≤ R * s.x (k - 1) := by
          have h_partialSum : ENNReal.ofReal (partialSum s k / s.x (k - 1)) ≤ ENNReal.ofReal R := by
            refine' le_trans _ h_score;
            refine' le_trans _ this;
            refine' le_trans _ ( le_iSup₂_of_le k ( Finset.mem_range.mpr ( by omega ) ) le_rfl ) ; aesop;
          rw [ ENNReal.ofReal_le_ofReal_iff ] at h_partialSum;
          · rwa [ div_le_iff₀ ( show 0 < s.x ( k - 1 ) from lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) ) ] at h_partialSum;
          · contrapose! h_partialSum;
            simp [ENNReal.ofReal];
            exact ⟨ lt_of_lt_of_le h_partialSum <| div_nonneg ( Finset.sum_nonneg fun _ _ => s.nonneg _ ) <| s.nonneg _, div_pos ( Finset.sum_pos ( fun _ _ => lt_of_lt_of_le zero_lt_one <| s.one_le.trans <| s.mono <| Nat.zero_le _ ) <| by norm_num ) <| lt_of_lt_of_le zero_lt_one <| s.one_le.trans <| s.mono <| Nat.zero_le _ ⟩;
        rcases k <;> simp_all +decide [ Finset.sum_range_succ, partialSum ];
        linarith

/-
If $B > 2$, then the worst-case score is at least 2.
-/
lemma boundedWorstCaseScore_ge_two {s : Strategy} {B : ℝ} (hB : 2 < B) :
    2 ≤ boundedWorstCaseScore s B := by
      -- Consider two cases: when $x_0 < 2$ and when $x_0 \ge 2$.
      by_cases hx0 : s.x 0 < 2;
      · -- Since $x_0 < 2$, we have $x_0 < B$. Consider $y$ slightly larger than $x_0$.
        -- The hit index is at least 1.
        -- The score is $S_k/y \ge S_1/y = (x_0 + x_1)/y$.
        -- As $y \downarrow x_0$, this approaches $(x_0 + x_1)/x_0$.
        -- Since $x_1 \ge x_0$, this is $\ge 2x_0/x_0 = 2$.
        have h_score_ge_two : ∀ ε > 0, ε < B - s.x 0 → ENNReal.ofReal ((partialSum s 1) / (s.x 0 + ε)) ≤ boundedWorstCaseScore s B := by
          intros ε hε_pos hε_lt;
          refine' le_trans _ ( le_ciSup _ ⟨ s.x 0 + ε, _, _ ⟩ ) <;> norm_num [ *, partialSum ];
          all_goals try linarith [ s.one_le ];
          refine' ENNReal.ofReal_le_ofReal _;
          gcongr;
          · linarith [ s.nonneg 0 ];
          · refine' Finset.sum_le_sum_of_subset_of_nonneg _ _ <;> norm_num [ Finset.sum_range_succ ];
            · unfold hitIndex; aesop;
            · exact fun _ _ _ => s.nonneg _;
        -- Taking the limit as $\epsilon \to 0$, we get $(partialSum s 1) / s.x 0 \le boundedWorstCaseScore s B$.
        have h_limit : ENNReal.ofReal ((partialSum s 1) / s.x 0) ≤ boundedWorstCaseScore s B := by
          have h_limit : Filter.Tendsto (fun ε => ENNReal.ofReal ((partialSum s 1) / (s.x 0 + ε))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal ((partialSum s 1) / s.x 0))) := by
            refine' ENNReal.tendsto_ofReal _;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using tendsto_const_nhds.div ( Continuous.tendsto ( show Continuous fun ε : ℝ => s.x 0 + ε from continuous_const.add continuous_id' ) 0 ) ( show ( s.x 0 + 0 ) ≠ 0 from by linarith [ s.nonneg 0, s.one_le ] ) );
          exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT <| show 0 < B - s.x 0 from sub_pos.mpr <| by linarith [ s.one_le ] ) fun ε hε => h_score_ge_two ε hε.1 hε.2 );
        simp_all +decide [ partialSum ];
        refine le_trans ?_ h_limit ; norm_num [ Finset.sum_range_succ ];
        rw [ le_div_iff₀ ] <;> linarith [ s.nonneg 0, s.nonneg 1, s.one_le, s.mono zero_le_one ];
      · refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num, by linarith ⟩ );
        · refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right ( Finset.single_le_sum ( fun a _ => s.nonneg a ) ( Finset.mem_range.mpr <| Nat.succ_pos _ ) ) <| by positivity ) ; norm_num;
          linarith;
        · exact OrderTop.bddAbove (Set.range fun y ↦ boundedScore s B y)

/-
If the strategy is strictly increasing and has at least 2 steps, then $R \ge 2$.
-/
lemma R_ge_two_strict {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (hn : 2 ≤ n) (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) : 2 ≤ R := by
      -- Since $n \ge 2$, the range $0 \dots n-1$ contains $k=1$. By `bounded_boundary_reduction_ge` (applied to $n-1$), $W_B \ge S_2/x_0$.
      have h_worst_case_ge_two : boundedWorstCaseScore s B ≥ ENNReal.ofReal ((partialSum s 1) / (s.x 0)) := by
        refine' le_trans _ ( bounded_boundary_reduction_ge h_strict h_n );
        refine' le_trans _ ( le_iSup₂ 1 _ ) <;> norm_num;
        linarith;
      have h_worst_case_ge_two : ENNReal.ofReal ((partialSum s 1) / (s.x 0)) > ENNReal.ofReal 2 := by
        norm_num [ partialSum ];
        rw [ lt_div_iff₀ ] <;> norm_num [ Finset.sum_range_succ ] <;> linarith [ s.nonneg 0, s.nonneg 1, s.one_le, h_strict ( show 0 < 1 from by norm_num ) ];
      contrapose! h_worst_case_ge_two;
      exact le_trans ‹_› ( h_score.trans ( ENNReal.ofReal_le_ofReal h_worst_case_ge_two.le ) )

/-
The partial sums of the difference sequence satisfy $\Delta_k \ge R \Delta_{k-1} - R \Delta_{k-2}$.
-/
noncomputable def diff_sum (s : Strategy) (R : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (tightPoly (i + 1) R - s.x i)

lemma diff_sum_recurrence {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    diff_sum s R 0 = R - s.x 0 ∧
    (1 < n → diff_sum s R 1 ≥ R * diff_sum s R 0) ∧
    ∀ k, 2 ≤ k → k < n → diff_sum s R k ≥ R * diff_sum s R (k - 1) - R * diff_sum s R (k - 2) := by
      refine' ⟨ _, _, _ ⟩;
      · unfold diff_sum; aesop;
      · intro hn;
        have := recurrence_strict h_strict h_n h_score;
        unfold diff_sum;
        norm_num [ Finset.sum_range_succ, tightPoly ];
        have := this.2 1 ( by norm_num ) ( by linarith ) ; norm_num [ partialSum ] at this ; nlinarith [ h_strict <| show 0 < 1 from by norm_num ] ;
      · -- For $k \ge 2$, we use the recurrence relation $x_k \le R x_{k-1} - S_{k-1}$.
        have h_recurrence : ∀ k, 2 ≤ k → k < n → s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
          exact fun k hk₁ hk₂ => recurrence_strict h_strict h_n h_score |>.2 k ( by linarith ) ( by linarith );
        intro k hk hk'; have := h_recurrence k hk hk'; rcases k with ( _ | _ | k ) <;> norm_num [ diff_sum, partialSum ] at *;
        have h_diff_sum : ∑ x ∈ Finset.range (k + 3), tightPoly (x + 1) R = R * tightPoly (k + 2) R := by
          convert tight_strategies_sum ( k + 3 ) R ( k + 2 ) ( by linarith ) using 1;
        norm_num [ Finset.sum_range_succ ] at *;
        nlinarith!

/-
Definition of `diff_seq`.
-/
noncomputable def diff_seq (s : Strategy) (R : ℝ) (k : ℕ) : ℝ := tightPoly (k + 1) R - s.x k

/-
The difference sequence satisfies $\delta_k \ge R \delta_{k-1} - S_{k-1}^\delta$.
-/
lemma diff_seq_recurrence_sum {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    diff_seq s R 0 = R - s.x 0 ∧
    ∀ k, 1 ≤ k → k < n → diff_seq s R k ≥ R * diff_seq s R (k - 1) - diff_sum s R (k - 1) := by
      unfold diff_seq diff_sum;
      refine' ⟨ _, fun k hk₁ hk₂ => _ ⟩;
      · rfl;
      · rcases k with ( _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
        -- Apply the recurrence relation for the tight polynomial.
        have h_tight_poly : tightPoly (k + 2) R = R * (tightPoly (k + 1) R - tightPoly k R) := by
          exact rfl;
        -- Apply the recurrence relation for the strategy.
        have h_strategy : s.x (k + 1) ≤ R * s.x k - ∑ i ∈ Finset.range (k + 1), s.x i := by
          apply (recurrence_strict h_strict h_n h_score).right (k + 1) (by linarith) (by linarith);
        have h_tight_poly_sum : ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R = R * tightPoly k R := by
          apply tight_strategies_sum;
          exact Nat.lt_of_succ_lt hk₂;
        norm_num [ Finset.sum_range_succ ] at * ; nlinarith

/-
The difference sequence $\delta_k = p_{k+1} - x_k$ satisfies $\delta_k \ge R \delta_{k-1} - \sum_{j < k} \delta_j$.
-/
lemma diff_seq_recurrence_explicit {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    (tightPoly 1 R - s.x 0 = R - s.x 0) ∧
    ∀ k, 1 ≤ k → k < n →
      (tightPoly (k + 1) R - s.x k) ≥ R * (tightPoly k R - s.x (k - 1)) - ∑ i ∈ Finset.range k, (tightPoly (i + 1) R - s.x i) := by
        have := @diff_seq_recurrence_sum s B R n h_strict h_n h_score;
        unfold diff_seq diff_sum at this; aesop;

/-
The tight polynomials satisfy the linear recurrence $p_{k+2} = R p_{k+1} - R p_k$.
-/
lemma tightPoly_recurrence_values (R : ℝ) (k : ℕ) :
    tightPoly (k + 2) R = R * tightPoly (k + 1) R - R * tightPoly k R := by
      -- By definition of tightPoly, we have:
      have h_def : tightPoly (k + 2) R = R * (tightPoly (k + 1) R - tightPoly k R) := by
        exact rfl;
      rw [ h_def, mul_sub ]

/-
The strategy guesses satisfy the recurrence $x_k \le (R-1)x_{k-1} - S_{k-2}$.
-/
lemma strategy_recurrence_correct {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    (s.x 0 ≤ R) ∧
    (1 < n → s.x 1 ≤ (R - 1) * s.x 0) ∧
    (∀ k, 2 ≤ k → k < n → s.x k ≤ (R - 1) * s.x (k - 1) - partialSum s (k - 2)) := by
      refine' ⟨ _, _, _ ⟩;
      · apply recurrence_start h_score;
        · exact h_n ▸ s.one_le.trans ( h_strict.monotone ( Nat.zero_le _ ) );
        · exact h_n ▸ h_strict.monotone ( Nat.zero_le _ );
      · intro hn;
        have := recurrence_strict h_strict h_n h_score;
        have := this.2 1 ( by norm_num ) ( by linarith ) ; norm_num [ partialSum ] at * ; linarith;
      · intro k hk₁ hk₂
        have h_recurrence : s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
          have := recurrence_strict h_strict h_n h_score;
          exact this.2 k ( by linarith ) ( by linarith );
        rcases k with ( _ | _ | k ) <;> simp_all
        unfold partialSum at *; norm_num [ Finset.sum_range_succ ] at *; linarith;

/-
For each $k < n$, the partial sum $S_k$ is bounded by $R$ times the previous guess.
-/
lemma partial_sum_le {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    ∀ k, k < n → partialSum s k ≤ R * (if k = 0 then 1 else s.x (k - 1)) := by
      by_contra h_contra;
      have h_partialSum_bound : ∀ k, k < n → ENNReal.ofReal (partialSum s k / if k = 0 then 1 else s.x (k - 1)) ≤ ENNReal.ofReal R := by
        intro k hk_lt_n
        have h_term_le : scoreTerm s k ≤ boundedWorstCaseScore s B := by
          have h_term_le : k ∈ Finset.range (n + 1) := by
            exact Finset.mem_range.mpr ( Nat.lt_succ_of_lt hk_lt_n );
          apply_rules [ scoreTerm_le_boundedWorstCaseScore ];
          exact Finset.mem_range.mpr ( by omega );
        exact le_trans h_term_le h_score;
      apply h_contra;
      intro k hk; specialize h_partialSum_bound k hk; rw [ ENNReal.ofReal_le_ofReal_iff ] at h_partialSum_bound;
      · rwa [ div_le_iff₀ ] at h_partialSum_bound;
        split_ifs <;> norm_num ; linarith [ s.nonneg ( k - 1 ), s.one_le, h_strict.monotone ( Nat.zero_le ( k - 1 ) ) ];
      · contrapose! h_partialSum_bound;
        rw [ ENNReal.ofReal_eq_zero.mpr h_partialSum_bound.le ] ; exact ENNReal.ofReal_pos.mpr ( div_pos ( Finset.sum_pos ( fun _ _ => s.nonneg _ |> lt_of_le_of_ne <| Ne.symm <| by linarith [ s.one_le, show 0 < s.x ‹_› from lt_of_lt_of_le ( by linarith [ s.one_le ] ) ( s.mono <| Nat.zero_le _ ) ] ) <| by norm_num ) <| by split_ifs <;> linarith [ s.one_le, show 0 < s.x ( k - 1 ) from lt_of_lt_of_le ( by linarith [ s.one_le ] ) ( s.mono <| Nat.zero_le _ ) ] )

/-
The tight polynomials satisfy the identity $p_{k+1} = (R-1)p_k - R p_{k-2}$ for $k \ge 2$.
-/
lemma tightPoly_algebraic_identity {R : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    tightPoly (k + 1) R = (R - 1) * tightPoly k R - R * tightPoly (k - 2) R := by
      rcases k with ( _ | _ | k ) <;> norm_num [ tightPoly ] at *;
      ring!

/-
Lemma 3: Trigonometric form of the tight polynomials.
If R = 4 cos^2(theta), then p_k(R) = (2 cos theta)^k * sin((k+1)theta) / sin theta.
-/
theorem tightPoly_trig_form (θ : ℝ) (hθ : Real.sin θ ≠ 0) (k : ℕ) :
    let R := 4 * (Real.cos θ) ^ 2
    tightPoly k R = (2 * Real.cos θ) ^ k * Real.sin ((k + 1) * θ) / Real.sin θ := by
      induction' k using Nat.strong_induction_on with n ih;
      rcases n with ( _ | _ | n ) <;> norm_num [ Nat.succ_eq_add_one, ih ];
      · aesop;
      · rw [ Real.sin_two_mul ] ; ring_nf;
        aesop;
      · -- Applying the recurrence relation for tightPoly, we have:
        have h_rec : tightPoly (n + 2) (4 * Real.cos θ ^ 2) = 4 * Real.cos θ ^ 2 * (tightPoly (n + 1) (4 * Real.cos θ ^ 2) - tightPoly n (4 * Real.cos θ ^ 2)) := by
          exact rfl;
        rw [ h_rec, ih _ <| Nat.lt_succ_self _, ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ];
        norm_num [ add_mul, Real.sin_add, Real.cos_add, pow_succ' ] ; ring_nf;
        rw [ show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 by ring, Real.sin_sq ] ; ring

/-
Lemma 4 (Part 1): Difference formula for tight polynomials.
If R = 4 cos^2(theta) with theta in (0, pi), then p_{k+1}(R) - p_k(R) = (2 cos theta)^k * sin((k+3)theta) / sin theta.
-/
theorem tightPoly_diff_sign (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi) (k : ℕ) :
    let R := 4 * (Real.cos θ) ^ 2
    tightPoly (k + 1) R - tightPoly k R = (2 * Real.cos θ) ^ k * Real.sin ((k + 3) * θ) / Real.sin θ := by
      have h_diff : tightPoly (k + 1) (4 * (Real.cos θ) ^ 2) - tightPoly k (4 * (Real.cos θ) ^ 2) =
          (2 * Real.cos θ) ^ k * (2 * Real.cos θ * Real.sin ((k + 2) * θ) - Real.sin ((k + 1) * θ)) / Real.sin θ := by
            have h_diff : ∀ k, tightPoly k (4 * (Real.cos θ) ^ 2) = (2 * Real.cos θ) ^ k * Real.sin ((k + 1) * θ) / Real.sin θ := by
              intro k;
              convert tightPoly_trig_form θ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt ) ) k using 1;
            grind;
      convert h_diff using 2 ; rw [ show ( k + 3 : ℝ ) * θ = ( k + 2 ) * θ + θ by ring, show ( k + 1 : ℝ ) * θ = ( k + 2 ) * θ - θ by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;

/-
Lemma 4 (Part 2): Monotonicity of tight polynomials for small angles.
If 0 < theta <= pi/(m+3), then p_0(R) <= p_1(R) <= ... <= p_m(R).
-/
theorem tightPoly_monotone_of_small_angle (m : ℕ) (θ : ℝ)
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / (m + 3)) (k : ℕ) (hk : k < m) :
    let R := 4 * (Real.cos θ) ^ 2
    tightPoly k R ≤ tightPoly (k + 1) R := by
      have h_diff_pos : 0 < (2 * Real.cos θ) ^ k * Real.sin ((k + 3) * θ) / Real.sin θ := by
        refine' div_pos ( mul_pos ( pow_pos ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ _, _ ⟩ ) ) _ ) ( Real.sin_pos_of_mem_Ioo ⟨ _, _ ⟩ ) ) ( Real.sin_pos_of_mem_Ioo ⟨ hθ_pos, _ ⟩ );
        · linarith [ Real.pi_pos ];
        · rw [ le_div_iff₀ ] at hθ_le <;> nlinarith [ Real.pi_pos ];
        · positivity;
        · rw [ le_div_iff₀ ] at hθ_le <;> nlinarith [ Real.pi_pos, show ( k : ℝ ) + 1 ≤ m by norm_cast ];
        · rw [ le_div_iff₀ ] at hθ_le <;> nlinarith [ Real.pi_pos ];
      have h_diff_pos : tightPoly (k + 1) (4 * (Real.cos θ) ^ 2) - tightPoly k (4 * (Real.cos θ) ^ 2) = (2 * Real.cos θ) ^ k * Real.sin ((k + 3) * θ) / Real.sin θ := by
        convert tightPoly_diff_sign θ hθ_pos ( by linarith [ Real.pi_pos, show θ < Real.pi from hθ_le.trans_lt <| by rw [ div_lt_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ] ) k using 1;
      linarith

/-
Lemma 5: Endpoint values.
p_n(rho_{n-1}) = B_{n-1} and p_n(rho_n) = B_n.
-/
theorem tightPoly_endpoints (n : ℕ) (hn : 1 ≤ n) :
    tightPoly n (ratioLower n) = stepBreakpoint (n - 1) ∧
    tightPoly n (ratioUpper n) = stepBreakpoint n := by
      unfold ratioLower ratioUpper stepBreakpoint;
      constructor;
      · rw [ Nat.sub_add_cancel hn, tightPoly_trig_form ];
        · rw [ div_eq_iff ];
          · rw [ ← Real.sin_pi_sub ] ; ring_nf;
            rcases n with ( _ | _ | n ) <;> norm_num at *;
            · norm_num [ Real.sin_add, Real.sin_sub, mul_div ];
              ring;
            · field_simp;
              ring_nf;
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; norm_num; nlinarith [ Real.pi_pos ] ) );
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; norm_num; nlinarith [ Real.pi_pos ] ) );
      · convert tightPoly_trig_form ( Real.pi / ( n + 3 ) ) _ n using 1 <;> norm_num;
        · rw [ eq_div_iff ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ) ) ) ] ; rw [ show ( n + 1 : ℝ ) * ( Real.pi / ( n + 3 ) ) = Real.pi - 2 * ( Real.pi / ( n + 3 ) ) by linarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ] ] ; rw [ Real.sin_pi_sub, Real.sin_two_mul ] ; ring;
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ) )

set_option maxHeartbeats 0 in
/-
Lemma 6: Strict monotonicity of p_n on the bracket [rho_{n-1}, rho_n].
-/
theorem tightPoly_strictMono_on_bracket (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (tightPoly n) (Set.Icc (ratioLower n) (ratioUpper n)) := by
      -- By definition of $R$, we know that $p_n(R) = (2 \cos \theta)^n \frac{\sin((n+1)\theta)}{\sin \theta}$ where $\theta = \arccos(\sqrt{R}/2)$.
      have h_trig_form : ∀ R ∈ Set.Icc (ratioLower n) (ratioUpper n), tightPoly n R = (2 * Real.cos (Real.arccos (Real.sqrt R / 2))) ^ n * Real.sin ((n + 1) * Real.arccos (Real.sqrt R / 2)) / Real.sin (Real.arccos (Real.sqrt R / 2)) := by
        intro R hR
        have h_cos : Real.cos (Real.arccos (Real.sqrt R / 2)) = Real.sqrt R / 2 := by
          rw [ Real.cos_arccos ];
          · linarith [ Real.sqrt_nonneg R ];
          · rw [ div_le_iff₀, Real.sqrt_le_left ] <;> norm_num;
            exact hR.2.trans ( by exact mul_le_of_le_one_right ( by norm_num ) ( Real.cos_sq_le_one _ ) |> le_trans <| by norm_num )
        have h_sin : Real.sin (Real.arccos (Real.sqrt R / 2)) ≠ 0 := by
          norm_num [ Real.sin_arccos ];
          field_simp;
          rw [ Real.sqrt_eq_zero' ] ; norm_num;
          rw [ Real.sq_sqrt ] <;> norm_num [ ratioLower, ratioUpper ] at *;
          · exact hR.2.trans_lt ( by nlinarith only [ Real.cos_sq' ( Real.pi / ( n + 3 ) ), Real.sin_pos_of_pos_of_lt_pi ( show 0 < Real.pi / ( n + 3 ) from by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] );
          · nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 2 ) ) ];
        convert tightPoly_trig_form ( Real.arccos ( Real.sqrt R / 2 ) ) h_sin n using 1;
        rw [ h_cos ] ; ring_nf;
        rw [ Real.sq_sqrt ( show 0 ≤ R by exact le_trans ( by exact mul_nonneg zero_le_four ( sq_nonneg _ ) ) hR.1 ) ];
      -- Since $\theta$ is strictly decreasing in $R$, we need to show that $p_n(R)$ is strictly decreasing in $\theta$.
      have h_trig_decreasing : StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n * Real.sin ((n + 1) * θ) / Real.sin θ) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
        -- The factors $(2 \cos \theta)^n$, $\sin((n+1)\theta)$, and $1/\sin \theta$ are all strictly decreasing in $\theta$ on $[\pi/(n+3), \pi/(n+2)]$.
        have h_factors_decreasing : StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) ∧ StrictAntiOn (fun θ => Real.sin ((n + 1) * θ)) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) ∧ StrictAntiOn (fun θ => 1 / Real.sin θ) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
          refine' ⟨ _, _, _ ⟩;
          · -- Since $\cos$ is strictly decreasing on $[0, \pi]$, multiplying by $2$ (which is positive) preserves the strict decrease.
            have h_cos_decreasing : StrictAntiOn Real.cos (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
              exact Real.strictAntiOn_cos.mono ( Set.Icc_subset_Icc ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) );
            exact fun x hx y hy hxy => pow_lt_pow_left₀ ( mul_lt_mul_of_pos_left ( h_cos_decreasing hx hy hxy ) zero_lt_two ) ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, hx.1, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ], by nlinarith [ Real.pi_pos, hy.2, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ) ) ( by positivity );
          · -- The sine function is strictly decreasing on the interval $[\frac{\pi}{2}, \pi]$.
            have h_sin_decreasing : StrictAntiOn Real.sin (Set.Icc (Real.pi / 2) Real.pi) := by
              exact fun x hx y hy hxy => by rw [ ← Real.cos_sub_pi_div_two, ← Real.cos_sub_pi_div_two ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith [ Set.mem_Icc.mp hx, Set.mem_Icc.mp hy ] ) ( by linarith [ Set.mem_Icc.mp hx, Set.mem_Icc.mp hy ] ) ( by linarith [ Set.mem_Icc.mp hx, Set.mem_Icc.mp hy ] ) ;
            intro θ hθ θ' hθ' hθθ';
            refine' h_sin_decreasing ⟨ _, _ ⟩ ⟨ _, _ ⟩ _;
            · rw [ Set.mem_Icc ] at hθ ; rw [ div_le_iff₀ ] at * <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ];
            · nlinarith [ hθ.1, hθ.2, hθ'.1, hθ'.2, Real.pi_pos, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
            · rw [ Set.mem_Icc ] at *;
              rw [ div_le_iff₀ ] at * <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ];
            · nlinarith [ hθ'.1, hθ'.2, Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ];
            · exact mul_lt_mul_of_pos_left hθθ' <| by positivity;
          · refine' fun x hx y hy hxy => one_div_lt_one_div_of_lt _ _;
            · exact Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hx.1 ) ( lt_of_le_of_lt hx.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) );
            · rw [ ← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub ] ; refine' Real.cos_lt_cos_of_nonneg_of_le_pi _ _ _ <;> nlinarith [ Real.pi_pos, hx.1, hx.2, hy.1, hy.2, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
        have h_prod_decreasing : StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n * Real.sin ((n + 1) * θ)) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) ∧ StrictAntiOn (fun θ => 1 / Real.sin θ) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
          simp_all +decide [ StrictAntiOn ];
          intro a ha₁ ha₂ b hb₁ hb₂ hab; have := h_factors_decreasing.1 ha₁ ha₂ hb₁ hb₂ hab; have := h_factors_decreasing.2.1 ha₁ ha₂ hb₁ hb₂ hab; gcongr;
          · exact pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show ( Real.pi : ℝ ) / ( n + 3 ) ≥ 0 by positivity ], by linarith [ Real.pi_pos, show ( Real.pi : ℝ ) / ( n + 2 ) ≤ Real.pi / 2 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ] ⟩ ) ) _;
          · exact Real.sin_nonneg_of_nonneg_of_le_pi ( by exact mul_nonneg ( by positivity ) ( by exact le_trans ( by positivity ) hb₁ ) ) ( by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] );
        simp_all +decide [ StrictAntiOn ];
        field_simp;
        intro a ha₁ ha₂ b hb₁ hb₂ hab; have := h_prod_decreasing ( show Real.pi / ( n + 3 ) ≤ a by rw [ div_le_iff₀ <| by positivity ] ; linarith ) ( show a ≤ Real.pi / ( n + 2 ) by rw [ le_div_iff₀ <| by positivity ] ; linarith ) ( show Real.pi / ( n + 3 ) ≤ b by rw [ div_le_iff₀ <| by positivity ] ; linarith ) ( show b ≤ Real.pi / ( n + 2 ) by rw [ le_div_iff₀ <| by positivity ] ; linarith ) hab; simp_all +decide [ mul_comm ] ;
        gcongr;
        · exact mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) _ ) ( Real.sin_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ );
        · exact Real.sin_pos_of_pos_of_lt_pi ( by nlinarith [ Real.pi_pos ] ) ( by nlinarith [ Real.pi_pos ] );
        · rw [ ← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] );
      -- Since $\theta$ is strictly decreasing in $R$, we need to show that $p_n(R)$ is strictly increasing in $R$.
      intros R1 hR1 R2 hR2 hR_lt
      have hθ_lt : Real.arccos (Real.sqrt R1 / 2) > Real.arccos (Real.sqrt R2 / 2) := by
        gcongr;
        · linarith [ Real.sqrt_nonneg R1 ];
        · unfold ratioUpper at *;
          exact div_le_one_of_le₀ ( Real.sqrt_le_iff.mpr ⟨ by norm_num, by norm_num at *; nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 3 ) ) ] ⟩ ) ( by norm_num );
        · exact le_trans ( by exact mul_nonneg zero_le_four ( sq_nonneg _ ) ) hR1.1;
      have hθ_bounds : Real.pi / (n + 3) ≤ Real.arccos (Real.sqrt R1 / 2) ∧ Real.arccos (Real.sqrt R1 / 2) ≤ Real.pi / (n + 2) ∧ Real.pi / (n + 3) ≤ Real.arccos (Real.sqrt R2 / 2) ∧ Real.arccos (Real.sqrt R2 / 2) ≤ Real.pi / (n + 2) := by
        have hθ_bounds : ∀ R ∈ Set.Icc (ratioLower n) (ratioUpper n), Real.pi / (n + 3) ≤ Real.arccos (Real.sqrt R / 2) ∧ Real.arccos (Real.sqrt R / 2) ≤ Real.pi / (n + 2) := by
          intros R hR
          have hθ_bounds : Real.cos (Real.pi / (n + 2)) ≤ Real.sqrt R / 2 ∧ Real.sqrt R / 2 ≤ Real.cos (Real.pi / (n + 3)) := by
            constructor;
            · have h_cos_lower : Real.cos (Real.pi / (n + 2)) ≤ Real.sqrt (ratioLower n) / 2 := by
                unfold ratioLower; norm_num;
                rw [ Real.sqrt_sq ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ];
              exact le_trans h_cos_lower ( by gcongr ; linarith [ hR.1 ] );
            · have h_sqrt_R_le : R ≤ (2 * Real.cos (Real.pi / (n + 3))) ^ 2 := by
                exact hR.2.trans ( by unfold ratioUpper; ring_nf; norm_num );
              rw [ div_le_iff₀, Real.sqrt_le_left ] <;> nlinarith [ show 0 ≤ Real.cos ( Real.pi / ( n + 3 ) ) from Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ];
          rw [ Real.arccos_eq_arcsin ];
          · rw [ Real.le_arcsin_iff_sin_le', Real.arcsin_le_iff_le_sin ];
            · constructor;
              · rw [ Real.sin_eq_sqrt_one_sub_cos_sq ] <;> try linarith [ Real.pi_pos, div_pos Real.pi_pos ( by positivity : 0 < ( n : ℝ ) + 3 ) ];
                · exact Real.sqrt_le_sqrt <| sub_le_sub_left ( pow_le_pow_left₀ ( by positivity ) hθ_bounds.2 2 ) _;
                · exact div_le_self Real.pi_pos.le ( by linarith );
              · rw [ Real.sin_eq_sqrt_one_sub_cos_sq ] <;> try linarith [ Real.pi_pos, div_le_self Real.pi_pos.le ( by linarith : ( n : ℝ ) + 2 ≥ 1 ) ];
                · exact Real.sqrt_le_sqrt <| sub_le_sub_left ( pow_le_pow_left₀ ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) hθ_bounds.1 2 ) _;
                · positivity;
            · exact ⟨ by linarith [ Real.sqrt_nonneg ( 1 - ( Real.sqrt R / 2 ) ^ 2 ) ], Real.sqrt_le_iff.mpr ⟨ by norm_num, by nlinarith [ Real.sqrt_nonneg R ] ⟩ ⟩;
            · exact ⟨ by rw [ le_div_iff₀ ] <;> nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ ] <;> nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩;
            · exact ⟨ by rw [ lt_div_iff₀ ] <;> nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ ] <;> nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩;
          · positivity;
        exact ⟨ hθ_bounds R1 hR1 |>.1, hθ_bounds R1 hR1 |>.2, hθ_bounds R2 hR2 |>.1, hθ_bounds R2 hR2 |>.2 ⟩;
      aesop

/-
Lemma 7: Step limit property.
If R is in [rho_{n-1}, rho_n], then p_{n+1}(R) <= p_n(R) and p_{n+2}(R) <= 0.
-/
theorem tightPoly_step_limit (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    tightPoly (n + 1) R ≤ tightPoly n R ∧ tightPoly (n + 2) R ≤ 0 := by
      -- Since R is in the interval [ρ_{n-1}, ρ_n], we can find θ such that R = 4 cos^2 θ and θ is in [π/(n+3), π/(n+2)].
      obtain ⟨θ, hθ⟩ : ∃ θ, R = 4 * (Real.cos θ) ^ 2 ∧ Real.pi / (n + 3) ≤ θ ∧ θ ≤ Real.pi / (n + 2) := by
        obtain ⟨θ, hθ_range, hθ_R⟩ : ∃ θ, Real.pi / (n + 3) ≤ θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ) ^ 2 := by
          have hθ_exists : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ) ^ 2 = R := by
            apply_rules [ intermediate_value_Icc' ];
            · bound;
            · exact Continuous.continuousOn ( by continuity );
            · unfold ratioLower ratioUpper at hR; aesop
          aesop;
        grind;
      have h_sin_le_zero : Real.sin ((n + 3) * θ) ≤ 0 := by
        rw [ ← Real.cos_sub_pi_div_two ];
        refine' Real.cos_nonpos_of_pi_div_two_le_of_le _ _;
        · rw [ div_le_iff₀ ] at hθ <;> nlinarith [ Real.pi_pos ];
        · rw [ le_div_iff₀ ] at hθ <;> nlinarith [ Real.pi_pos ];
      have h_pn1_le_pn : tightPoly (n + 1) R - tightPoly n R ≤ 0 := by
        have h_diff : tightPoly (n + 1) R - tightPoly n R = (2 * Real.cos θ) ^ n * Real.sin ((n + 3) * θ) / Real.sin θ := by
          have := tightPoly_diff_sign θ ( show 0 < θ from lt_of_lt_of_le ( by positivity ) hθ.2.1 ) ( show θ < Real.pi from lt_of_le_of_lt hθ.2.2 ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ) n; aesop;
        exact h_diff.symm ▸ div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ by exact le_trans ( by positivity ) hθ.2.1 ], by rw [ le_div_iff₀ ] at * <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) _ ) h_sin_le_zero ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ by exact le_trans ( by positivity ) hθ.2.1 ], by rw [ le_div_iff₀ ] at * <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ )
      have h_pn2_le_zero : tightPoly (n + 2) R ≤ 0 := by
        have h_pn2_le_zero : tightPoly (n + 2) R = (2 * Real.cos θ) ^ (n + 2) * Real.sin ((n + 3) * θ) / Real.sin θ := by
          convert tightPoly_trig_form θ _ ( n + 2 ) using 1 ; aesop;
          · norm_cast;
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by exact lt_of_lt_of_le ( by positivity ) hθ.2.1 ) ( by exact lt_of_le_of_lt hθ.2.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) );
        exact h_pn2_le_zero ▸ div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ by exact le_trans ( by positivity ) hθ.2.1 ], by linarith [ Real.pi_pos, show θ ≤ Real.pi / 2 by exact hθ.2.2.trans ( by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ ) ) _ ) h_sin_le_zero ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ by exact le_trans ( by positivity ) hθ.2.1 ], by linarith [ Real.pi_pos, show θ ≤ Real.pi / 2 by exact hθ.2.2.trans ( by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ )
      exact ⟨by linarith, h_pn2_le_zero⟩

/-
Definition of the sequence of guesses for the optimal strategy.
-/
noncomputable def optimalStrategy_x (n : ℕ) (R B : ℝ) (k : ℕ) : ℝ :=
  if k < n then tightPoly (k + 1) R else B + (k - (n - 1))

/-
Lemma: ratioLower n >= 1 for n >= 1.
-/
theorem ratioLower_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ ratioLower n := by
  unfold ratioLower;
  have h_cos : Real.cos (Real.pi / (n + 2)) ≥ 1 / 2 := by
    exact Real.cos_pi_div_three ▸ Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] );
  norm_num; nlinarith

/-
Lemma: tightPoly k R is positive for k <= n and R in the n-step range.
-/
theorem tightPoly_pos (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) (k : ℕ) (hk : k ≤ n) :
    0 < tightPoly k R := by
      -- Let θ be such that R = 4 cos^2 θ.
      obtain ⟨θ, hθ⟩ : ∃ θ, 0 < θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ) ^ 2 := by
        -- By definition of ratioLower and ratioUpper, we know that R is in the interval [4 * cos²(π/(n+2)), 4 * cos²(π/(n+3))].
        obtain ⟨θ, hθ⟩ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), R = 4 * (Real.cos θ) ^ 2 := by
          -- Since $R \in [\rho_{n-1}, \rho_n]$, we can use the fact that $4 \cos^2 \theta$ is continuous and strictly decreasing on $[0, \frac{\pi}{2}]$.
          have h_cont : ContinuousOn (fun θ => 4 * (Real.cos θ) ^ 2) (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
            exact Continuous.continuousOn ( by continuity );
          have h_ivt : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ) ^ 2 = R := by
            apply_rules [ intermediate_value_Icc' ];
            · bound;
            · unfold ratioLower ratioUpper at hR; aesop;
          aesop;
        exact ⟨ θ, lt_of_lt_of_le ( by positivity ) hθ.1.1, hθ.1.2, hθ.2 ⟩;
      -- For k ≤ n, (k+1)θ ≤ (n+1)θ ≤ (n+1)π/(n+2) = π - π/(n+2) < π.
      have h_angle_bound : (k + 1) * θ < Real.pi := by
        nlinarith [ Real.pi_pos, show ( k : ℝ ) ≤ n by norm_cast, mul_div_cancel₀ Real.pi ( by linarith : ( n : ℝ ) + 2 ≠ 0 ) ];
      -- Since $(k+1)\theta < \pi$ and $\theta > 0$, we have $\sin((k+1)\theta) > 0$.
      have h_sin_pos : Real.sin ((k + 1) * θ) > 0 := by
        exact Real.sin_pos_of_pos_of_lt_pi ( by nlinarith ) h_angle_bound;
      -- Since $(k+1)\theta < \pi$ and $\theta > 0$, we have $(2 \cos \theta)^k > 0$.
      have h_cos_pos : 0 < (2 * Real.cos θ) ^ k := by
        exact pow_pos ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ) ) _;
      have h_tightPoly_pos : tightPoly k R = (2 * Real.cos θ) ^ k * Real.sin ((k + 1) * θ) / Real.sin θ := by
        convert tightPoly_trig_form θ ( ne_of_gt <| Real.sin_pos_of_pos_of_lt_pi hθ.left <| by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) k using 1 ; aesop;
      exact h_tightPoly_pos.symm ▸ div_pos ( mul_pos h_cos_pos h_sin_pos ) ( Real.sin_pos_of_pos_of_lt_pi hθ.1 ( by linarith [ Real.pi_pos, show θ ≤ Real.pi / 3 by exact le_trans hθ.2.1 ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ) )

/-
Specification of the first guess R: it lies in the correct interval and satisfies p_n(R) = B.
-/
theorem firstGuess_spec {B : ℝ} (hB : 1 < B) :
    let n := nSteps B
    let R := firstGuess B
    ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧ tightPoly n R = B := by
      unfold firstGuess;
      field_simp;
      split_ifs;
      · have := Classical.choose_spec ( existsUnique_ratio_of_inStepRange ( B := B ) ( n := nSteps B ) ( nSteps_spec hB |>.1 ) ( nSteps_spec hB |>.2 ) );
        tauto;
      · contradiction

/-
Lemma: optimalStrategy_x is non-negative.
-/
theorem optimalStrategy_x_nonneg (n : ℕ) (R B : ℝ)
    (hn : 1 ≤ n) (hB : 1 < B)
    (hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (h_tight : tightPoly n R = B) (k : ℕ) :
    0 ≤ optimalStrategy_x n R B k := by
      unfold optimalStrategy_x;
      split_ifs <;> try linarith [ tightPoly_pos n hn R hR_range ( k + 1 ) ( by linarith ) ];
      linarith [ show ( k : ℝ ) ≥ n by norm_cast; linarith ]

/-
Lemma: The first guess of the optimal strategy is at least 1.
-/
theorem optimalStrategy_x_one_le (n : ℕ) (R B : ℝ)
    (hn : 1 ≤ n) (hB : 1 < B)
    (hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (h_tight : tightPoly n R = B) :
    1 ≤ optimalStrategy_x n R B 0 := by
      -- By definition of `optimalStrategy_x`, we have `optimalStrategy_x n R B 0 = tightPoly 1 R`.
      have h_def : optimalStrategy_x n R B 0 = tightPoly 1 R := by
        unfold optimalStrategy_x; aesop;
      norm_num [ h_def ];
      exact le_trans ( ratioLower_ge_one n hn ) hR_range.1

/-
Lemma: The optimal strategy sequence is monotonic.
-/
theorem optimalStrategy_x_mono (n : ℕ) (R B : ℝ)
    (hn : 1 ≤ n) (hB : 1 < B)
    (hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (h_tight : tightPoly n R = B) :
    Monotone (optimalStrategy_x n R B) := by
      refine' monotone_nat_of_le_succ fun k => _;
      by_cases hk : k < n <;> simp_all +decide [ optimalStrategy_x ];
      · -- Since $R \in [\rho_{n-1}, \rho_n]$, we have $R = 4 \cos^2(\theta)$ for some $\theta \in [\frac{\pi}{n+2}, \frac{\pi}{n+3}]$.
        obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ) ^ 2 := by
          unfold ratioLower ratioUpper at hR_range;
          -- Since $R$ is between $4 \cos^2(\pi/(n+2))$ and $4 \cos^2(\pi/(n+3))$, we can find $\theta$ such that $\cos(\theta) = \sqrt{R/4}$.
          obtain ⟨θ, hθ⟩ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), Real.cos θ ^ 2 = R / 4 := by
            apply_rules [ intermediate_value_Icc' ] <;> norm_num;
            · gcongr ; linarith;
            · exact Continuous.continuousOn ( Real.continuous_cos.pow 2 );
            · constructor <;> push_cast at * <;> linarith;
          exact ⟨ θ, lt_of_lt_of_le ( by positivity ) hθ.1.1, hθ.1.2, by linarith ⟩;
        split_ifs <;> simp_all
        · have h_sin_nonneg : Real.sin ((k + 4) * θ) ≥ 0 := by
            exact Real.sin_nonneg_of_nonneg_of_le_pi ( by nlinarith ) ( by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith [ Real.pi_pos, show ( k : ℝ ) + 1 + 1 ≤ n by norm_cast ] );
          have h_sin_nonneg : tightPoly (k + 2) (4 * Real.cos θ ^ 2) - tightPoly (k + 1) (4 * Real.cos θ ^ 2) = (2 * Real.cos θ) ^ (k + 1) * Real.sin ((k + 4) * θ) / Real.sin θ := by
            convert tightPoly_diff_sign θ hθ.1 ( show θ < Real.pi from by rw [ le_div_iff₀ ( by positivity ) ] at hθ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ( k + 1 ) using 1 ; norm_num [ mul_assoc, pow_succ' ] ; ring_nf;
          exact le_of_sub_nonneg ( h_sin_nonneg.symm ▸ div_nonneg ( mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos, show θ ≤ Real.pi / 2 by exact hθ.2.1.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ ) ) _ ) ‹_› ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos, show θ ≤ Real.pi / 2 by exact hθ.2.1.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ ) );
        · cases eq_or_lt_of_le ‹_› <;> first | linarith | aesop;
      · split_ifs <;> linarith [ ( by norm_cast : ( n : ℝ ) ≤ k ) ]

/-
Definition of the optimal strategy as a Strategy structure.
-/
noncomputable def optimalStrategy (B : ℝ) : Strategy :=
  if hB : 1 < B then
    let n := nSteps B
    let R := firstGuess B
    have hn : 1 ≤ n := (nSteps_spec hB).1
    have h_spec := firstGuess_spec hB
    have hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n) := ⟨h_spec.1, h_spec.2.1⟩
    have h_tight : tightPoly n R = B := h_spec.2.2
    { x := optimalStrategy_x n R B
      nonneg := optimalStrategy_x_nonneg n R B hn hB hR_range h_tight
      one_le := optimalStrategy_x_one_le n R B hn hB hR_range h_tight
      mono := optimalStrategy_x_mono n R B hn hB hR_range h_tight
      hits := fun {y} hy => by
        -- Since $y \geq 1$, we can choose $n$ large enough such that $B + (n - (n - 1)) \geq y$.
        use Nat.ceil (y - B) + n;
        unfold optimalStrategy_x;
        split_ifs <;> norm_num at * ; linarith [ Nat.le_ceil ( y - B ) ] }
  else
    doublingStrategy

/-
Lemma: If B > 1, then the first guess R is strictly greater than the lower bound of the interval.
-/
theorem firstGuess_gt_ratioLower {B : ℝ} (hB : 1 < B) :
    ratioLower (nSteps B) < firstGuess B := by
      have := firstGuess_spec hB
      obtain ⟨hR_range, h_tight⟩ := this;
      refine' hR_range.lt_of_ne' _;
      have := tightPoly_endpoints ( nSteps B ) ( by linarith [ nSteps_spec hB ] );
      have := nSteps_spec hB;
      unfold InStepRange at this; aesop;

/-
Lemma: For the optimal strategy, the ratio of the partial sum to the previous guess is equal to the first guess R, for all steps k < n.
-/
theorem optimalStrategy_ratio_eq_firstGuess (B : ℝ) (hB : 1 < B) (k : ℕ) (hk : k < nSteps B) :
    partialSum (optimalStrategy B) k / (if k = 0 then 1 else (optimalStrategy B).x (k - 1)) = firstGuess B := by
      -- Let's use the fact that `optimalStrategy_x` is equal to `tightGuess k R` for `k < n` and `B + (k - (n - 1))` for `k ≥ n`.
      have h_optimal_x : ∀ k < (if 1 < B then nSteps B else 0), (optimalStrategy B).x k = tightGuess k (firstGuess B) := by
        unfold optimalStrategy;
        unfold optimalStrategy_x; aesop;
      rcases k <;> simp_all +decide [ partialSum ];
      · exact rfl;
      · rw [ Finset.sum_congr rfl fun i hi => h_optimal_x i ( by linarith [ Finset.mem_range.mp hi ] ) ];
        -- By definition of `tightGuess`, we know that `∑ i ∈ Finset.range (n + 2), tightGuess i R = R * tightGuess n R`.
        have h_sum : ∑ i ∈ Finset.range (Nat.succ ‹_› + 1), tightGuess i (firstGuess B) = firstGuess B * tightGuess ‹_› (firstGuess B) := by
          apply tight_strategies_sum;
          exact hk;
        rw [ h_sum, h_optimal_x _ ( by linarith ), mul_div_cancel_right₀ _ ( ne_of_gt <| by exact ( show 0 < tightGuess _ _ from by exact ( show 0 < tightPoly ( Nat.succ _ ) _ from by exact ( show 0 < tightPoly ( Nat.succ _ ) _ from by exact ( tightPoly_pos _ ( by linarith ) _ ⟨ ( firstGuess_spec hB ) |>.1, ( firstGuess_spec hB ) |>.2.1 ⟩ _ ( by linarith ) ) ) ) ) ) ]

/-
Lemma: tightPoly is strictly increasing in k for k < n, given R > ratioLower n.
-/
theorem tightPoly_strictMono_in_k (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (hR_gt : ratioLower n < R) (j : ℕ) (hj : j < n) :
    tightPoly j R < tightPoly (j + 1) R := by
      -- Let θ be such that R = 4 cos^2 θ.
      obtain ⟨θ, hθ⟩ : ∃ θ ∈ Set.Ioo 0 (Real.pi / (n + 2)), R = 4 * (Real.cos θ) ^ 2 := by
        have hθ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), R = 4 * (Real.cos θ) ^ 2 := by
          unfold ratioLower ratioUpper at *;
          have hθ_exists : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ) ^ 2 = R := by
            apply_rules [ intermediate_value_Icc' ] <;> norm_num;
            · gcongr ; norm_num;
            · exact Continuous.continuousOn ( by continuity );
            · aesop;
          aesop;
        obtain ⟨ θ, hθ₁, hθ₂ ⟩ := hθ;
        by_cases hθ_eq : θ = Real.pi / (n + 2);
        · simp_all +decide [ ratioLower ];
        · exact ⟨ θ, ⟨ lt_of_lt_of_le ( by positivity ) hθ₁.1, lt_of_le_of_ne hθ₁.2 hθ_eq ⟩, hθ₂ ⟩;
      have h_pos : 0 < (2 * Real.cos θ) ^ j * Real.sin ((j + 3) * θ) / Real.sin θ := by
        refine' div_pos ( mul_pos ( pow_pos ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ _, _ ⟩ ) ) _ ) ( Real.sin_pos_of_mem_Ioo ⟨ _, _ ⟩ ) ) ( Real.sin_pos_of_mem_Ioo ⟨ _, _ ⟩ );
        all_goals nlinarith [ hθ.1.1, hθ.1.2, Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), show ( j : ℝ ) + 3 ≤ n + 2 by norm_cast; linarith ];
      have h_diff : tightPoly (j + 1) R - tightPoly j R = (2 * Real.cos θ) ^ j * Real.sin ((j + 3) * θ) / Real.sin θ := by
        have := tightPoly_diff_sign θ hθ.1.1 ( by linarith [ hθ.1.2, Real.pi_pos, div_le_self Real.pi_pos.le ( by linarith : ( n : ℝ ) + 2 ≥ 1 ) ] ) j; aesop;
      linarith

/-
Lemma: optimalStrategy_x is strictly monotonic.
-/
theorem optimalStrategy_x_strictMono (n : ℕ) (R B : ℝ)
    (hn : 1 ≤ n) (hB : 1 < B)
    (hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (hR_gt : ratioLower n < R)
    (h_tight : tightPoly n R = B) :
    StrictMono (optimalStrategy_x n R B) := by
      refine' strictMono_nat_of_lt_succ fun k => _;
      by_cases hk : k < n <;> by_cases hk' : k + 1 < n <;> simp +decide [ *, optimalStrategy_x ];
      · convert tightPoly_strictMono_in_k n hn R hR_range hR_gt ( k + 1 ) hk' using 1;
      · cases eq_or_lt_of_le ( Nat.succ_le_of_lt hk ) <;> aesop;
      · linarith

/-
Lemma: The optimal strategy is strictly increasing.
-/
theorem optimalStrategy_strictMono (B : ℝ) (hB : 1 < B) :
    StrictMono (optimalStrategy B).x := by
      unfold optimalStrategy;
      split_ifs;
      apply_rules [ optimalStrategy_x_strictMono ];
      · exact ( nSteps_spec hB ).1;
      · exact ⟨ firstGuess_spec hB |>.1, firstGuess_spec hB |>.2.1 ⟩;
      · exact firstGuess_gt_ratioLower hB;
      · exact firstGuess_spec hB |>.2.2

/-
Lemma: The (n-1)-th guess of the optimal strategy is B.
-/
theorem optimalStrategy_x_at_n_minus_one (n : ℕ) (R B : ℝ)
    (hn : 1 ≤ n) (h_tight : tightPoly n R = B) :
    optimalStrategy_x n R B (n - 1) = B := by
      unfold optimalStrategy_x; aesop;

/-
Theorem: The bounded worst-case score of the optimal strategy is exactly the first guess R.
-/
theorem optimalStrategy_boundedScore (B : ℝ) (hB : 1 < B) :
    boundedWorstCaseScore (optimalStrategy B) B = ENNReal.ofReal (firstGuess B) := by
      let n := nSteps B
      let R := firstGuess B
      have hR_range : R ∈ Set.Icc (ratioLower n) (ratioUpper n) ∧ tightPoly n R = B := by
        exact ⟨ ⟨ firstGuess_spec hB |>.1, firstGuess_spec hB |>.2.1 ⟩, firstGuess_spec hB |>.2.2 ⟩
      have h_strict : StrictMono (optimalStrategy B).x := by
        exact optimalStrategy_strictMono B hB
      have h_xn_minus_one : (optimalStrategy B).x (n - 1) = B := by
        convert optimalStrategy_x_at_n_minus_one n R B _ _;
        · unfold optimalStrategy; aesop;
        · exact nSteps_spec hB |>.1;
        · exact hR_range.2;
      -- We apply bounded_boundary_reduction with index m.
      have h_bounded : ⨆ k ∈ Finset.range n, ENNReal.ofReal (partialSum (optimalStrategy B) k / if k = 0 then 1 else (optimalStrategy B).x (k - 1)) = ENNReal.ofReal (firstGuess B) := by
        have h_bounded : ∀ k ∈ Finset.range n, ENNReal.ofReal (partialSum (optimalStrategy B) k / if k = 0 then 1 else (optimalStrategy B).x (k - 1)) = ENNReal.ofReal R := by
          intro k hk; rw [ optimalStrategy_ratio_eq_firstGuess B hB k ( Finset.mem_range.mp hk ) ] ;
        rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · intro i; rw [ ciSup_eq_ite ] ; aesop;
        · intro w hw;
          use 0;
          rcases n with ( _ | _ | n ) <;> norm_num at *;
          · exact absurd hR_range.2 ( by erw [ show tightPoly 0 R = 1 by rfl ] ; linarith );
          · aesop;
          · specialize h_bounded 0 ; aesop;
      rw [ ← h_bounded, bounded_boundary_reduction ];
      any_goals exact n - 1;
      · rw [ Nat.sub_add_cancel ( show 1 ≤ n from ( nSteps_spec hB ).1 ) ];
      · assumption;
      · exact h_xn_minus_one;
      · rcases n with ( _ | _ | n ) <;> simp_all
        linarith [ h_strict ( Nat.lt_succ_self n ) ]

/-
Lemma: The supremum of the ratios for the optimal strategy is equal to the first guess R.
-/
lemma optimalStrategy_sup_ratio (B : ℝ) (hB : 1 < B) :
    (⨆ k ∈ Finset.range (nSteps B), ENNReal.ofReal (partialSum (optimalStrategy B) k / if k = 0 then 1 else (optimalStrategy B).x (k - 1))) = ENNReal.ofReal (firstGuess B) := by
      refine' le_antisymm _ _;
      · refine' iSup_le fun k => iSup_le fun hk => _;
        rw [ optimalStrategy_ratio_eq_firstGuess B hB k ( Finset.mem_range.mp hk ) ];
      · field_simp;
        refine' le_trans _ ( le_iSup₂_of_le ( nSteps B - 1 ) ( Finset.mem_range.mpr ( Nat.sub_lt ( by linarith [ show 1 ≤ nSteps B from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by { intro h; have := nSteps_spec hB; aesop } ) ) ] ) zero_lt_one ) ) le_rfl );
        rw [ optimalStrategy_ratio_eq_firstGuess ];
        · linarith;
        · exact Nat.pred_lt ( ne_bot_of_gt ( nSteps_spec hB |>.1 ) )

/-
Lemma: The optimal strategy is strictly increasing (renamed to avoid conflict).
-/
theorem optimalStrategy_strictMono_proof (B : ℝ) (hB : 1 < B) :
    StrictMono (optimalStrategy B).x := by
      exact optimalStrategy_strictMono B hB

/-
Lemma: If the strategy guesses are bounded by the tight polynomials, then the partial sum is bounded by R times the k-th tight polynomial.
-/
theorem dominance_le_tightPoly_sum {s : Strategy} {R : ℝ} {n k : ℕ}
    (hk : k < n)
    (h : ∀ j, j ≤ k → s.x j ≤ tightPoly (j + 1) R) :
    partialSum s k ≤ R * tightPoly k R := by
      have h_partialSum : ∑ i ∈ Finset.range (k + 1), s.x i ≤ ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R := by
        exact Finset.sum_le_sum fun i hi => h i <| Finset.mem_range_succ_iff.mp hi;
      exact h_partialSum.trans ( by rw [ tight_strategies_sum n R k hk ] )

/-
The value of the 1st breakpoint B_1 is 2.
-/
lemma stepBreakpoint_one : stepBreakpoint 1 = 2 := by
  unfold stepBreakpoint; norm_num [ Real.cos_pi_div_four ] ;
  ring_nf; norm_num;

/-
The value of the 2nd breakpoint B_2 is 2 + sqrt(5).
-/
lemma stepBreakpoint_two : stepBreakpoint 2 = 2 + Real.sqrt 5 := by
  norm_num [ stepBreakpoint ];
  grind

/-
The value of the 3rd breakpoint B_3 is 9.
-/
lemma stepBreakpoint_three : stepBreakpoint 3 = 9 := by
  -- By definition of stepBreakpoint, we have stepBreakpoint 3 = (2 * cos(π/6))^4.
  simp [stepBreakpoint];
  grind

/-
The 0-th term of the difference sum sequence is non-negative.
-/
lemma diff_sum_nonneg_zero {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R) :
    0 ≤ diff_sum s R 0 := by
      unfold diff_sum;
      have := recurrence_start h_score ( show 1 ≤ B by linarith [ s.one_le, h_strict.monotone ( show 0 ≤ n - 1 from Nat.zero_le _ ) ] ) ( show s.x 0 ≤ B by linarith [ s.one_le, h_strict.monotone ( show 0 ≤ n - 1 from Nat.zero_le _ ) ] ) ; aesop;

/-
Define the slack variable $\epsilon_k = R x_{k-1} - S_k$ (with $x_{-1}=1$).
-/
noncomputable def slack (s : Strategy) (R : ℝ) (k : ℕ) : ℝ :=
  R * (if k = 0 then 1 else s.x (k - 1)) - partialSum s k

/-
The slack variables are non-negative.
-/
lemma slack_nonneg {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (k : ℕ) (hk : k < n) :
    0 ≤ slack s R k := by
      -- By the partial_sum_le lemma, we have partialSum s k ≤ R * (if k = 0 then 1 else s.x (k - 1)).
      have h_partial_sum_le : partialSum s k ≤ R * (if k = 0 then 1 else s.x (k - 1)) := by
        exact partial_sum_le h_strict h_n h_score k hk;
      exact sub_nonneg_of_le h_partial_sum_le

/-
$p_{m+1}(R)/R = p_m(R) - p_{m-1}(R)$.
-/
lemma tightPoly_div_R_eq_diff {R : ℝ} {m : ℕ} (hm : 1 ≤ m) (hR : R ≠ 0) :
    tightPoly (m + 1) R / R = tightPoly m R - tightPoly (m - 1) R := by
      field_simp;
      rcases m with ( _ | _ | m ) <;> aesop

/-
Define the explicit formula for $x_k$ in terms of tight polynomials and slack variables.
-/
noncomputable def formula_x (s : Strategy) (R : ℝ) (k : ℕ) : ℝ :=
  tightPoly (k + 1) R - ∑ j ∈ Finset.range (k + 1), (tightPoly (k - j + 1) R / R) * slack s R j

/-
`formula_x` satisfies the recurrence $x_k = R x_{k-1} - R x_{k-2} + \epsilon_{k-1} - \epsilon_k$.
-/
lemma formula_x_recurrence {s : Strategy} {R : ℝ} (hR : R ≠ 0) (k : ℕ) (hk : 2 ≤ k) :
    formula_x s R k = R * formula_x s R (k - 1) - R * formula_x s R (k - 2) + slack s R (k - 1) - slack s R k := by
      unfold formula_x;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
      have h_recurrence : ∀ k, tightPoly (k + 2) R = R * (tightPoly (k + 1) R - tightPoly k R) := by
        exact fun k ↦ rfl;
      simp_all [ sub_eq_iff_eq_add ];
      rw [ show tightPoly ( k + 1 + 1 - k + 1 ) R = tightPoly 3 R by rw [ show k + 1 + 1 - k = 2 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ] ; rw [ show tightPoly 3 R = R * ( tightPoly 2 R - tightPoly 1 R ) by exact h_recurrence 1 ] ; rw [ show tightPoly 2 R = R * ( tightPoly 1 R - tightPoly 0 R ) by exact h_recurrence 0 ] ; norm_num [ Finset.sum_range_succ', hR ] ; ring_nf;
      rw [ show tightPoly 1 R = R by rfl, show tightPoly 0 R = 1 by rfl ] ; norm_num [ hR, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
      rw [ show ( Finset.range k ).sum ( fun x => slack s R x * tightPoly ( 1 + ( 1 + k - x ) ) R ) = ( Finset.range k ).sum ( fun x => R * R⁻¹ * slack s R x * tightPoly ( 1 + ( k - x ) ) R ) + ( Finset.range k ).sum ( fun x => R⁻¹ * slack s R x * tightPoly ( 1 + ( 2 + k - x ) ) R ) from ?_ ]
      have hRRinv : R * R⁻¹ = 1 := by
        field_simp [hR]
      · simp [hRRinv]
        ring
      rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ show 1 + ( 1 + k - x ) = 1 + ( k - x ) + 1 by linarith [ Nat.sub_add_cancel ( show x ≤ k from Finset.mem_range_le hx ), Nat.sub_add_cancel ( show x ≤ 1 + k from by linarith [ Finset.mem_range_le hx ] ) ] ] ; rw [ show 1 + ( 2 + k - x ) = 1 + ( k - x ) + 2 by linarith [ Nat.sub_add_cancel ( show x ≤ k from Finset.mem_range_le hx ), Nat.sub_add_cancel ( show x ≤ 2 + k from by linarith [ Finset.mem_range_le hx ] ) ] ] ; ring_nf;
      rw [ show 3 + ( k - x ) = 2 + ( k - x ) + 1 by ring, show 2 + ( k - x ) = 1 + ( k - x ) + 1 by ring ]
      rw [ h_recurrence ]
      field_simp [hR]
      ring

/-
$x_k$ satisfies the recurrence $x_k = R x_{k-1} - R x_{k-2} + \epsilon_{k-1} - \epsilon_k$.
-/
lemma strategy_recurrence_slack {s : Strategy} {R : ℝ} (k : ℕ) (hk : 2 ≤ k) :
    s.x k = R * s.x (k - 1) - R * s.x (k - 2) + slack s R (k - 1) - slack s R k := by
      rcases k with ( _ | _ | k ) <;> norm_num [ slack ] at *;
      unfold partialSum; norm_num [ Finset.sum_range_succ ] ; ring!;

/-
$x_k$ equals `formula_x` for all $k < n$.
-/
lemma strategy_eq_formula_x {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : R ≠ 0)
    (k : ℕ) (hk : k < n) :
    s.x k = formula_x s R k := by
      -- We proceed by induction on $k$.
      induction' k using Nat.strong_induction_on with k ih;
      by_cases hk0 : k = 0 ∨ k = 1;
      · rcases hk0 with ( rfl | rfl ) <;> norm_num [ formula_x ];
        · field_simp;
          unfold slack; unfold partialSum; norm_num [ Finset.sum_range_succ ] ; ring_nf;
          exact rfl;
        · unfold slack; norm_num [ Finset.sum_range_succ, tightPoly ] ; ring_nf;
          field_simp;
          unfold partialSum; norm_num [ Finset.sum_range_succ ] ; ring;
      · have h_recurrence : s.x k = R * s.x (k - 1) - R * s.x (k - 2) + slack s R (k - 1) - slack s R k ∧ formula_x s R k = R * formula_x s R (k - 1) - R * formula_x s R (k - 2) + slack s R (k - 1) - slack s R k := by
          exact ⟨ strategy_recurrence_slack k ( by omega ), formula_x_recurrence hR k ( by omega ) ⟩;
        grind

/-
If $R \ge 4$, then $p_k(R) \ge 1$ for all $k$.
-/
lemma tightPoly_ge_one_of_ge_four {R : ℝ} (hR : 4 ≤ R) (k : ℕ) :
    1 ≤ tightPoly k R := by
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_two : 2 ≤ R := by linarith
  have hmain : ∀ k : ℕ, 1 ≤ tightPoly k R ∧ 2 * tightPoly k R ≤ tightPoly (k + 1) R := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp [tightPoly]
        · simp [tightPoly]
          linarith
    | succ k ih =>
        rcases ih with ⟨h_one, h_double⟩
        constructor
        · nlinarith
        · have hdiff : tightPoly (k + 1) R - tightPoly k R ≥ tightPoly (k + 1) R / 2 := by
            nlinarith
          have hnext_nonneg : 0 ≤ tightPoly (k + 1) R := by nlinarith
          have hnonneg : 0 ≤ tightPoly (k + 1) R / 2 := by nlinarith
          have hmul : R * (tightPoly (k + 1) R - tightPoly k R) ≥
              2 * tightPoly (k + 1) R := by
            nlinarith [mul_le_mul hR_two hdiff hnonneg hR_nonneg]
          simpa [tightPoly, Nat.add_assoc, Nat.succ_eq_add_one] using hmul
  exact (hmain k).1

/-
The lemma `tightPoly_pos_of_le_tightPoly` is false.
-/
lemma tightPoly_pos_counterexample :
    ∃ n R, 1 ≤ R ∧ 1 ≤ tightPoly n R ∧ ∃ k ≤ n, tightPoly k R < 0 := by
      use 10;
      use 2.25;
      norm_num +zetaDelta at *;
      refine' ⟨ _, 6, _, _ ⟩ <;> norm_num [ tightPoly ]

/-
The first guess is at most R.
-/
lemma strategy_recurrence_base {s : Strategy} {B R : ℝ}
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hB : 1 ≤ B) :
    s.x 0 ≤ R := by
      -- Since $y = 1$ is in the interval $(1, x_0]$, the score for $y = 1$ is $s.x 0 / 1 = s.x 0$.
      have h_score_one : score s ⟨1, by norm_num⟩ ≤ ENNReal.ofReal R := by
        refine' le_trans _ h_score;
        refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num, by linarith ⟩ );
        · exact
          Std.IsPreorder.le_refl
            (score s
              ⟨1,
                Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl true)⟩);
        · simp +zetaDelta at *;
      unfold score at h_score_one;
      rw [ ENNReal.ofReal_le_ofReal_iff ] at h_score_one <;> norm_num at *;
      · rw [ hitIndex_one ] at h_score_one;
        exact le_trans ( by unfold partialSum; norm_num ) h_score_one;
      · contrapose! h_score_one;
        rw [ ENNReal.ofReal_eq_zero.mpr h_score_one.le ] ; exact ENNReal.ofReal_pos.mpr ( show 0 < partialSum s ( hitIndex s ⟨ 1, by norm_num ⟩ ) from Finset.sum_pos ( fun i hi => by exact lt_of_lt_of_le zero_lt_one ( by exact Nat.recOn i ( s.one_le ) fun n ihn => by exact le_trans ihn ( s.mono ( Nat.le_succ _ ) ) ) ) ( by norm_num ) )

/-
The k-th guess satisfies the recurrence relation.
-/
lemma strategy_recurrence_simple {s : Strategy} {B R : ℝ} {k : ℕ}
    (h_strict : StrictMono s.x)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hk : k > 0)
    (h_bound : s.x (k - 1) < B) :
    s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
      -- Using the definition of partialSum, we can rewrite the inequality.
      have h_partialSum : partialSum s k = partialSum s (k - 1) + s.x k := by
        cases k <;> simp_all +decide [ Finset.sum_range_succ, partialSum ];
      have h_partialSum_le : partialSum s k ≤ R * s.x (k - 1) := by
        have h_partialSum_le : ∀ y ∈ Set.Ioc (s.x (k - 1)) B, (partialSum s k / y) ≤ R := by
          intros y hy
          have h_score_y : score s ⟨y, by
            exact le_trans ( s.one_le ) ( h_strict.monotone ( Nat.zero_le _ ) ) |> le_trans <| hy.1.le⟩ ≤ ENNReal.ofReal R := by
            all_goals generalize_proofs at *;
            refine' le_trans _ h_score;
            exact le_iSup_of_le ⟨ y, by linarith [ hy.1, hy.2 ], by linarith [ hy.1, hy.2 ] ⟩ le_rfl
          generalize_proofs at *;
          rw [ score ] at h_score_y;
          rw [ ENNReal.ofReal_le_ofReal_iff ] at h_score_y;
          · refine' le_trans _ h_score_y;
            gcongr;
            refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
            · refine' Finset.range_mono ( Nat.succ_le_succ _ );
              contrapose! hy;
              exact fun h => h.1.not_ge <| by linarith [ h_strict.monotone <| show hitIndex s ⟨ y, by linarith ⟩ ≤ k - 1 from Nat.le_pred_of_lt hy, show s.x ( hitIndex s ⟨ y, by linarith ⟩ ) ≥ y from Nat.find_spec ( s.hits <| by linarith ) |> le_trans ( by aesop ) ] ;
            · exact fun _ _ _ => s.nonneg _;
          · contrapose! h_score_y;
            rw [ ENNReal.ofReal_eq_zero.mpr h_score_y.le ] ; norm_num;
            refine' div_pos _ ( by linarith );
            exact Finset.sum_pos ( fun i hi => by linarith [ s.nonneg i, h_strict.monotone ( show i ≥ 0 from Nat.zero_le i ), show s.x i > 0 from lt_of_lt_of_le ( by linarith ) ( s.one_le.trans ( h_strict.monotone ( show i ≥ 0 from Nat.zero_le i ) ) ) ] ) ( by norm_num );
        -- Taking the limit as $y$ approaches $s.x (k - 1)$ from the right, we get $\partialSum s k / s.x (k - 1) \le R$.
        have h_limit : Filter.Tendsto (fun y => partialSum s k / y) (nhdsWithin (s.x (k - 1)) (Set.Ioi (s.x (k - 1)))) (nhds (partialSum s k / s.x (k - 1))) := by
          exact tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( ne_of_gt <| by linarith [ h_strict.monotone <| show 0 ≤ k - 1 from Nat.zero_le _, show 1 ≤ s.x 0 from s.one_le ] );
        have h_limit_le : partialSum s k / s.x (k - 1) ≤ R := by
          exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by linarith, h_bound ⟩ ) fun y hy => h_partialSum_le y ⟨ hy.1, hy.2.le ⟩ );
        rwa [ div_le_iff₀ ( show 0 < s.x ( k - 1 ) from lt_of_lt_of_le zero_lt_one ( by exact Nat.recOn ( k - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ h_strict n.lt_succ_self ] ) ) ] at h_limit_le;
      linarith

/-
The tight polynomials satisfy the recurrence relation $p_{k+1} = R p_k - R p_{k-1}$ for $k \ge 2$.
-/
lemma tightPoly_recurrence_k_ge_2 {R : ℝ} {k : ℕ} (hk : k ≥ 2) :
    tightPoly (k + 1) R = R * tightPoly k R - R * tightPoly (k - 1) R := by
      rcases k with ( _ | _ | k ) <;> norm_num [ Nat.succ_eq_add_one ] at *;
      exact tightPoly_recurrence_values R (k + 1)

/-
The sum of the first k+1 tight polynomials is equal to R times the k-th tight polynomial.
-/
lemma tightPoly_sum_identity (R : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R = R * tightPoly k R := by
      induction k <;> simp_all +decide [ Finset.sum_range_succ ];
      · exact show R = R * 1 by ring;
      · rw [ show tightPoly ( _ + 1 + 1 ) R = R * ( tightPoly ( _ + 1 ) R - tightPoly _ R ) by exact
        rfl ] ; ring

/-
The difference sequence satisfies a sum recurrence.
-/
noncomputable def diffSeq (s : Strategy) (R : ℝ) (k : ℕ) : ℝ := tightPoly (k + 1) R - s.x k

lemma diffSeq_recurrence_sum {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (k : ℕ) (hk : 1 ≤ k) (hk_lt : k < n) :
    diffSeq s R k ≥ R * diffSeq s R (k - 1) - ∑ j ∈ Finset.range k, diffSeq s R j := by
      -- By definition of $diffSeq$, we know that $s.x k \le R * s.x (k - 1) - partialSum s (k - 1)$.
      have h_x_k : s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
        -- Apply the lemma strategy_recurrence_simple with the given conditions.
        apply strategy_recurrence_simple h_strict h_score hk (by
        exact h_n ▸ h_strict ( by omega ));
      -- By definition of $diffSeq$, we know that $p_{k+1}(R) = R p_k(R) - S_{k-1}^{tight}$.
      have h_p_k1 : tightPoly (k + 1) R = R * tightPoly k R - ∑ i ∈ Finset.range k, tightPoly (i + 1) R := by
        have h_p_k1 : ∀ k, tightPoly (k + 1) R = R * tightPoly k R - ∑ i ∈ Finset.range k, tightPoly (i + 1) R := by
          intro k;
          induction' k with k ih;
          · exact show R = R * 1 - 0 by ring;
          · rw [ Finset.sum_range_succ, tightPoly_recurrence_values ] ; linarith;
        exact h_p_k1 k;
      unfold diffSeq;
      cases k <;> norm_num [ Finset.sum_range_succ, partialSum ] at * ; linarith!

/-
The upper bound sequence satisfies the recurrence relation.
-/
noncomputable def upperBoundSeq (R x0 : ℝ) (k : ℕ) : ℝ := (tightPoly (k + 1) R / R) * x0

lemma upperBoundSeq_recurrence {R x0 : ℝ} {k : ℕ} (hk : k ≥ 2) (hR : R ≠ 0) :
    upperBoundSeq R x0 k = (R - 1) * upperBoundSeq R x0 (k - 1) - ∑ j ∈ Finset.range (k - 1), upperBoundSeq R x0 j := by
      -- For the inductive step, assume the theorem holds for all $j < k$. We need to show it holds for $k$.
      induction' k with k ih;
      · contradiction;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ upperBoundSeq ];
        · rw [ show tightPoly 3 R = R * ( tightPoly 2 R - tightPoly 1 R ) by rfl, show tightPoly 2 R = R * ( tightPoly 1 R - tightPoly 0 R ) by rfl, show tightPoly 1 R = R by rfl, show tightPoly 0 R = 1 by rfl ] ; ring;
        · simp_all +decide [ Finset.sum_range_succ, tightPoly_recurrence_values ];
          grind

/-
The sequence C_k satisfies the recurrence relation.
-/
noncomputable def C_seq (R : ℝ) (k : ℕ) : ℝ := tightPoly (k + 1) R / R

lemma C_seq_recurrence {R : ℝ} (hR : R ≠ 0) (k : ℕ) (hk : k ≥ 2) :
    C_seq R k = R * C_seq R (k - 1) - R * C_seq R (k - 2) := by
      -- By definition of $C_seq$, we know that $C_seq R k = tightPoly (k + 1) R / R$.
      have h_def : ∀ k, C_seq R k = tightPoly (k + 1) R / R := by
        exact fun k ↦ rfl;
      rcases k with ( _ | _ | k ) <;> simp_all
      field_simp;
      exact rfl

/-
Define the impulse sequence and its recurrence.
-/
noncomputable def impulseSeq (R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 1 else R * impulseSeq R (k - 1) - R * impulseSeq R (k - 2)

lemma impulseSeq_recurrence {R : ℝ} (k : ℕ) (hk : k ≥ 2) :
    impulseSeq R k = R * impulseSeq R (k - 1) - R * impulseSeq R (k - 2) := by
      -- We'll use induction to prove that the impulse sequence satisfies the given recurrence relation.
      induction' k with k ih;
      · contradiction;
      · rcases k with ( _ | _ | k ) <;> simp_all
        · -- By definition of impulseSeq, we have:
          simp [impulseSeq];
        · rw [ ← ih, impulseSeq ];
          grind

/-
The partial sums of the difference sequence satisfy a recurrence.
-/
noncomputable def diffSum (s : Strategy) (R : ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), diffSeq s R j

lemma diffSum_recurrence {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (k : ℕ) (hk : 2 ≤ k) (hk_lt : k < n) :
    diffSum s R k ≥ R * diffSum s R (k - 1) - R * diffSum s R (k - 2) := by
      have := diffSeq_recurrence_sum h_strict h_n h_score k ( by linarith ) hk_lt;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
      unfold diffSum diffSeq at *; norm_num [ Finset.sum_range_succ ] at *; linarith;

/-
Algebraic identity for tight polynomials used in the dominance proof.
-/
lemma tightPoly_dominance_identity {R : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    (R - 1) * tightPoly (k + 1) R - R * tightPoly (k - 1) R = tightPoly (k + 2) R := by
      -- By definition of `tightPoly`, we know that `tightPoly (k + 2) R = R * tightPoly (k + 1) R - R * tightPoly k R`.
      have h_rec : tightPoly (k + 2) R = R * tightPoly (k + 1) R - R * tightPoly k R := by
        exact tightPoly_recurrence_values R k;
      rcases k with ( _ | _ | k ) <;> simp_all
      · rw [ show tightPoly 2 R = R * ( tightPoly 1 R - tightPoly 0 R ) by rfl, show tightPoly 1 R = R by rfl, show tightPoly 0 R = 1 by rfl ] ; ring;
      · rw [ show tightPoly ( k + 2 + 1 ) R = R * tightPoly ( k + 2 ) R - R * tightPoly ( k + 1 ) R from ?_ ]
        · ring;
        exact tightPoly_recurrence_values R (k + 1)

/-
Lemma: $p_{k+1}(R) = R p_k(R) - \sum_{j=0}^{k-1} p_{j+1}(R)$.
-/
lemma tightPoly_recurrence_sum {R : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    tightPoly (k + 1) R = R * tightPoly k R - ∑ j ∈ Finset.range k, tightPoly (j + 1) R := by
      -- We proceed by induction on $k$.
      induction' k with k ih;
      · contradiction;
      · induction' k with k ih <;> simp_all +decide [ Finset.sum_range_succ ];
        · exact show R * ( R - 1 ) = R * R - R by ring;
        · rw [ ← ih ];
          exact tightPoly_recurrence_values R (k + 1)

/-
Lemma: The supremum of S/y on (a, b] is S/a.
-/
lemma sup_score_segment {S a b : ℝ} (hS : 0 ≤ S) (ha : 0 < a) (hab : a < b) :
    (⨆ y ∈ Set.Ioc a b, ENNReal.ofReal (S / y)) = ENNReal.ofReal (S / a) := by
      -- We need to show that the supremum of the set is $S / a$.
      have h_sup : ∀ y ∈ Set.Ioc a b, ENNReal.ofReal (S / y) ≤ ENNReal.ofReal (S / a) := by
        intro y hy; gcongr ; linarith [ hy.1, hy.2 ] ;
      -- To show that the supremum is exactly $S / a$, we need to find a sequence $\{y_n\}$ in $(a, b]$ such that $S / y_n$ converges to $S / a$.
      have h_seq : ∃ (y_n : ℕ → ℝ), (∀ n, a < y_n n ∧ y_n n ≤ b) ∧ Filter.Tendsto (fun n => S / y_n n) Filter.atTop (nhds (S / a)) := by
        use fun n => a + (b - a) / (n + 1);
        exact ⟨ fun n => ⟨ by norm_num; nlinarith [ div_mul_cancel₀ ( b - a ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ div_mul_cancel₀ ( b - a ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩, le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) <| by linarith ) <| by norm_num ⟩;
      -- By the definition of supremum, if there exists a sequence {y_n} in (a, b] such that S/y_n converges to S/a, then the supremum is at least S/a.
      obtain ⟨y_n, hy_n_bounds, hy_n_limit⟩ := h_seq;
      have h_sup_ge : ENNReal.ofReal (S / a) ≤ ⨆ y ∈ Set.Ioc a b, ENNReal.ofReal (S / y) := by
        have h_sup_ge : Filter.Tendsto (fun n => ENNReal.ofReal (S / y_n n)) Filter.atTop (nhds (ENNReal.ofReal (S / a))) := by
          exact ENNReal.tendsto_ofReal hy_n_limit;
        exact le_of_tendsto h_sup_ge ( Filter.eventually_atTop.mpr ⟨ 0, fun n hn => le_iSup_of_le ( y_n n ) ( by aesop ) ⟩ );
      exact le_antisymm ( iSup_le fun y => iSup_le fun hy => h_sup y hy ) h_sup_ge

/-
Lemma: The partial sums are bounded by R times the previous guess.
-/
lemma partial_sum_le_of_score_le {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (k : ℕ) (hk : k < n) :
    partialSum s k ≤ R * (if k = 0 then 1 else s.x (k - 1)) := by
      -- Apply the hypothesis `h` with the given `k` and `hk`.
      apply partial_sum_le;
      all_goals tauto

/-
The sum of the first k+1 tight polynomials (shifted by 1) is equal to R times the k-th tight polynomial.
-/
lemma tightPoly_sum_eq_R_mul_prev (R : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R = R * tightPoly k R := by
      exact tightPoly_sum_identity R k

/-
The k-th guess satisfies the recurrence inequality x_k <= R * x_{k-1} - S_{k-1}.
-/
lemma strategy_recurrence_simple_proof {s : Strategy} {B R : ℝ} {k : ℕ}
    (h_strict : StrictMono s.x)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hk : k > 0)
    (h_bound : s.x (k - 1) < B) :
    s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
      have := @strategy_recurrence_simple s B R k h_strict h_score hk h_bound; aesop;

/-
The impulse response sequence satisfies the recurrence G_k = R G_{k-1} - sum_{j < k} G_j.
-/
noncomputable def impulseResponse (R : ℝ) (k : ℕ) : ℝ := tightPoly (k + 1) R / R

lemma impulseResponse_recurrence {R : ℝ} (hR : R ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    impulseResponse R k = R * impulseResponse R (k - 1) - ∑ j ∈ Finset.range k, impulseResponse R j := by
      have h_identity : ∑ i ∈ Finset.range k, impulseResponse R i = tightPoly (k - 1) R := by
        unfold impulseResponse;
        have := tightPoly_sum_eq_R_mul_prev R ( k - 1 ) ; cases k <;> simp_all +decide [ Finset.sum_range_succ ] ;
        rw [ ← Finset.sum_div, ← add_div, this, mul_div_cancel_left₀ _ hR ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ, impulseResponse ];
      · rw [ show tightPoly 2 R = R * ( tightPoly 1 R - tightPoly 0 R ) by rfl, show tightPoly 1 R = R by rfl, show tightPoly 0 R = 1 by rfl ] ; ring_nf;
        norm_num [ sq, hR ];
      · field_simp;
        exact rfl

/-
The convolution of the impulse response and a sequence e satisfies the recurrence relation.
-/
lemma convolution_recurrence_identity {R : ℝ} {e : ℕ → ℝ} (hR : R ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    let d := fun n => ∑ j ∈ Finset.range (n + 1), impulseResponse R (n - j) * e j
    d k = R * d (k - 1) - (∑ j ∈ Finset.range k, d j) + e k := by
      have h_impulse : ∀ k, 1 ≤ k → impulseResponse R k = R * impulseResponse R (k - 1) - ∑ j ∈ Finset.range k, impulseResponse R j := by
        exact fun k a ↦ impulseResponse_recurrence hR k a;
      have h_convolution : ∀ k, 1 ≤ k → ∑ j ∈ Finset.range (k + 1), impulseResponse R (k - j) * e j = R * ∑ j ∈ Finset.range k, impulseResponse R (k - 1 - j) * e j - ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (j + 1), impulseResponse R (j - i) * e i + e k := by
        intros k hk
        have h_split : ∑ j ∈ Finset.range (k + 1), impulseResponse R (k - j) * e j = e k + ∑ j ∈ Finset.range k, impulseResponse R (k - j) * e j := by
          simp +decide [ Finset.sum_range_succ ];
          unfold impulseResponse; norm_num; ring_nf;
          rw [ show tightPoly 1 R = R by rfl ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, hR ];
        have h_swap : ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (j + 1), impulseResponse R (j - i) * e i = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k, impulseResponse R (j - i) * e i := by
          rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
        have h_swap : ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k, impulseResponse R (j - i) * e i = ∑ i ∈ Finset.range k, e i * ∑ j ∈ Finset.range (k - i), impulseResponse R j := by
          simp +decide [ Finset.mul_sum _ _ _, mul_comm, Finset.sum_Ico_eq_sum_range ];
        have h_swap : ∑ j ∈ Finset.range k, impulseResponse R (k - j) * e j = ∑ j ∈ Finset.range k, e j * (R * impulseResponse R (k - j - 1) - ∑ i ∈ Finset.range (k - j), impulseResponse R i) := by
          exact Finset.sum_congr rfl fun x hx => by rw [ ← h_impulse _ ( Nat.sub_pos_of_lt ( Finset.mem_range.mp hx ) ) ] ; ring;
        simp_all +decide [ mul_sub,mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        simp +decide only [tsub_right_comm, add_comm];
      cases k <;> aesop

/-
The slack sequence is defined as the difference between the actual value and the value predicted by the recurrence.
-/
noncomputable def slackSeq (d : ℕ → ℝ) (R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then d 0 else d k - (R * d (k - 1) - ∑ j ∈ Finset.range k, d j)

/-
The sequence d k can be expressed as the convolution of the impulse response and the slack sequence.
-/
lemma diffSeq_eq_convolution {d : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : R ≠ 0)
    (h_rec : ∀ k, 1 ≤ k → k < n → d k ≥ R * d (k - 1) - ∑ j ∈ Finset.range k, d j) :
    ∀ k, k < n → d k = ∑ j ∈ Finset.range (k + 1), impulseResponse R (k - j) * slackSeq d R j := by
      -- By definition of `impulseResponse` and `slackSeq`, we can expand the right-hand side of the equation.
      have h_expand : ∀ k < n, ∑ j ∈ Finset.range (k + 1), (tightPoly (k - j + 1) R / R) * (slackSeq d R j) = d k := by
        intro k hk_lt_n
        induction' k using Nat.case_strong_induction_on with k ih;
        · field_simp;
          unfold slackSeq; norm_num;
          rw [ show tightPoly 1 R = R by rfl, mul_div_cancel_left₀ _ hR ];
        · -- Apply the convolution recurrence identity with `e_j = slackSeq d R j`.
          have h_convolution : ∑ j ∈ Finset.range (k + 2), tightPoly (k + 1 - j + 1) R / R * slackSeq d R j = R * ∑ j ∈ Finset.range (k + 1), tightPoly (k - j + 1) R / R * slackSeq d R j - ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), tightPoly (j - i + 1) R / R * slackSeq d R i + slackSeq d R (k + 1) := by
            convert convolution_recurrence_identity hR ( k + 1 ) ( by linarith ) using 1;
          -- Substitute the induction hypothesis into the convolution recurrence identity.
          have h_substitute : ∑ j ∈ Finset.range (k + 2), tightPoly (k + 1 - j + 1) R / R * slackSeq d R j = R * d k - ∑ j ∈ Finset.range (k + 1), d j + slackSeq d R (k + 1) := by
            rw [ h_convolution, ih k le_rfl ( by linarith ), Finset.sum_congr rfl fun j hj => ih j ( by linarith [ Finset.mem_range.mp hj ] ) ( by linarith [ Finset.mem_range.mp hj ] ) ];
          unfold slackSeq at * ; aesop;
      exact fun k hk => Eq.symm ( h_expand k hk )

/-
If a sequence satisfies the difference recurrence with R > 0 and tight polynomials are non-negative, then the sequence is non-negative.
-/
lemma nonneg_of_diffSeq_recurrence_bounded {d : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : 0 < R)
    (h0 : 0 ≤ d 0)
    (h_rec : ∀ k, 1 ≤ k → k < n → d k ≥ R * d (k - 1) - ∑ j ∈ Finset.range k, d j)
    (h_tight_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R) :
    ∀ k, k < n → 0 ≤ d k := by
      intros k hk;
      -- By Lemma `diffSeq_eq_convolution`, we can express $d k$ as the convolution of the impulse response and the slack sequence.
      have h_conv : d k = ∑ j ∈ Finset.range (k + 1), (tightPoly (k - j + 1) R / R) * slackSeq d R j := by
        convert diffSeq_eq_convolution hR.ne' h_rec k hk using 1;
      -- Since $R > 0$, each term in the sum is non-negative.
      have h_term_nonneg : ∀ j ≤ k, 0 ≤ (tightPoly (k - j + 1) R / R) * slackSeq d R j := by
        intros j hj;
        by_cases hj0 : j = 0 <;> simp_all +decide [ slackSeq ];
        · exact mul_nonneg ( div_nonneg ( h_tight_nonneg _ ( by linarith ) ) hR.le ) h0;
        · exact mul_nonneg ( div_nonneg ( h_tight_nonneg _ ( by omega ) ) hR.le ) ( by linarith [ h_rec j ( Nat.pos_of_ne_zero hj0 ) ( by omega ) ] );
      exact h_conv.symm ▸ Finset.sum_nonneg fun j hj => h_term_nonneg j ( Finset.mem_range_succ_iff.mp hj )

/-
If the worst-case score is at most R and tight polynomials are non-negative, then the strategy guesses are bounded by the tight polynomials.
-/
lemma dominance_property_proof {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R)
    (h_tight_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R) :
    ∀ k, k < n → s.x k ≤ tightPoly (k + 1) R := by
      -- Apply the nonneg_of_diffSeq_recurrence_bounded lemma to the sequence d k = diffSeq s R k.
      have h_diffSeq_nonneg : ∀ k < n, 0 ≤ diffSeq s R k := by
        intros k hk_lt_n
        apply nonneg_of_diffSeq_recurrence_bounded;
        exact zero_lt_one.trans_le hR;
        all_goals norm_cast;
        · -- By definition of `diffSeq`, we have `diffSeq s R 0 = tightPoly 1 R - s.x 0`.
          simp [diffSeq];
          convert recurrence_start h_score ( show 1 ≤ B from _ ) _ using 1;
          · linarith [ s.one_le, h_strict.monotone ( Nat.zero_le ( n - 1 ) ) ];
          · exact h_n ▸ h_strict.monotone ( Nat.zero_le _ );
        · exact fun k a a_1 ↦ diffSeq_recurrence_sum h_strict h_n h_score k a a_1;
      exact fun k hk => le_of_sub_nonneg <| h_diffSeq_nonneg k hk

/-
If R is in the n-th bracket, then the first n tight polynomials are non-negative.
-/
lemma tightPoly_nonneg_of_mem_bracket {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    ∀ k, k ≤ n → 0 ≤ tightPoly k R := by
      have := tightPoly_pos n hn R hR;
      exact fun k hk => le_of_lt ( this k hk )

/-
If R is in the n-th bracket, then the n-th tight polynomial is the maximum among the first n+1 polynomials.
-/
lemma tightPoly_le_max_upto_n_plus_one {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    ∀ k, k ≤ n + 1 → tightPoly k R ≤ tightPoly n R := by
      -- For $k < n$, we use `tightPoly_monotone_of_small_angle`.
      have h_monotone : ∀ k < n, tightPoly k R ≤ tightPoly (k + 1) R := by
        -- By Lemma 4, $p_n(rho_n) = B_n$. Since $R \ge \rho_n$, we have $R \ge 4 \cos^2(\frac{\pi}{n+2})$. Let $\theta = \frac{\pi}{n+2}$.
        obtain ⟨θ, hθ_pos, hθ_le⟩ : ∃ θ, 0 < θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ) ^ 2 := by
          unfold ratioLower ratioUpper at hR;
          have hθ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ) ^ 2 = R := by
            apply_rules [ intermediate_value_Icc' ] <;> norm_num;
            · gcongr ; norm_num;
            · exact Continuous.continuousOn ( by continuity );
            · grind;
          exact ⟨ hθ.choose, lt_of_lt_of_le ( by positivity ) hθ.choose_spec.1.1, hθ.choose_spec.1.2, hθ.choose_spec.2.symm ⟩;
        -- Since $\theta \leq \frac{\pi}{n+2}$, we have $(k+3)\theta \leq \pi$ for all $k < n$.
        have h_sin_nonneg : ∀ k < n, 0 ≤ Real.sin ((k + 3) * θ) := by
          exact fun k hk => Real.sin_nonneg_of_nonneg_of_le_pi ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] at hθ_le; nlinarith [ Real.pi_pos, show ( k : ℝ ) + 1 ≤ n by norm_cast ] );
        -- Using the trigonometric form of the tight polynomials, we have $p_{k+1}(R) - p_k(R) = (2 \cos \theta)^k \frac{\sin((k+3)\theta)}{\sin \theta}$.
        have h_diff_trig : ∀ k < n, tightPoly (k + 1) R - tightPoly k R = (2 * Real.cos θ) ^ k * Real.sin ((k + 3) * θ) / Real.sin θ := by
          intros k hk_lt_n
          rw [hθ_le.right]
          apply tightPoly_diff_sign θ hθ_pos (by
          exact hθ_le.1.trans_lt ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] )) k;
        exact fun k hk => by have := h_diff_trig k hk; exact le_of_sub_nonneg ( this.symm ▸ div_nonneg ( mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) _ ) ( h_sin_nonneg k hk ) ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) ;
      -- For $k \leq n$, we use `tightPoly_monotone_of_small_angle`.
      intros k hk
      by_cases hkn : k ≤ n;
      · -- By induction on $i$, we can show that $tightPoly k R \leq tightPoly (k + i) R$ for any $i \geq 0$.
        have h_ind : ∀ i, k + i ≤ n → tightPoly k R ≤ tightPoly (k + i) R := by
          intro i hi; induction' i with i ih <;> simp_all +decide [ ← add_assoc ] ;
          exact le_trans ( ih ( by linarith ) ) ( h_monotone _ ( by linarith ) );
        simpa only [ add_tsub_cancel_of_le hkn ] using h_ind ( n - k ) ( by rw [ add_tsub_cancel_of_le hkn ] );
      · norm_num [ show k = n + 1 by linarith ];
        have := tightPoly_step_limit n hn R hR; aesop;

/-
Definition of the sequence x_n for the tight unbounded strategy.
x_n = (n+2) * 2^(n-1) (0-based indexing).
-/
noncomputable def tightUnboundedStrategyX (n : ℕ) : ℝ :=
  (n + 2 : ℝ) * (2 : ℝ) ^ ((n : ℤ) - 1)

/-
Definition of the tight unbounded strategy structure.
-/
noncomputable def tightUnboundedStrategy : Strategy :=
  { x := tightUnboundedStrategyX
    nonneg := by
      exact fun n => by unfold tightUnboundedStrategyX; positivity;
    one_le := by
      -- By definition of `tightUnboundedStrategyX`, we have `tightUnboundedStrategyX 0 = (0 + 2) * 2 ^ ((0 : ℤ) - 1)`.
      simp [tightUnboundedStrategyX]
    mono := by
      refine' monotone_nat_of_le_succ fun n => _;
      unfold tightUnboundedStrategyX; ring_nf; norm_num;
      norm_num [ zpow_add₀, zpow_one ] ; ring_nf ; norm_num;
      nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ]
    hits := by
      intro y hy
      use Nat.ceil (y / 2) + 1;
      unfold tightUnboundedStrategyX; norm_num [ Nat.ceil_le ];
      nlinarith [ Nat.le_ceil ( y / 2 ), show ( 2 : ℝ ) ^ ⌈y / 2⌉₊ ≥ ⌈y / 2⌉₊ + 1 by exact mod_cast Nat.recOn ⌈y / 2⌉₊ ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ Nat.le_ceil ( y / 2 ) ] ] }

/-
For the tight unbounded strategy, the partial sum $S_{n+1}$ equals $4x_n$.
In 0-based indexing: $\sum_{i=0}^n x_i = 4 x_{n-1}$ for $n \ge 1$.
-/
theorem tightUnboundedStrategy_sum (n : ℕ) (hn : 1 ≤ n) :
    partialSum tightUnboundedStrategy n = 4 * tightUnboundedStrategy.x (n - 1) := by
      unfold partialSum;
      induction hn <;> norm_num [ Finset.sum_range_succ, tightUnboundedStrategy ] at *;
      · unfold tightUnboundedStrategyX; norm_num;
      · rename_i k hk ih; rcases k with ( _ | _ | k ) <;> norm_num [ Finset.sum_range_succ, tightUnboundedStrategyX ] at *;
        norm_num [ zpow_add₀, zpow_sub₀ ] at * ; ring_nf at * ; linarith

/-
The worst-case score of the tight unbounded strategy is 4.
-/
theorem tightUnboundedStrategy_worstCaseScore :
    worstCaseScore tightUnboundedStrategy = 4 := by
      have h_worst_case_score : ∀ k, partialSum tightUnboundedStrategy k / (if k = 0 then 1 else tightUnboundedStrategy.x (k - 1)) = if k = 0 then 1 else 4 := by
        intro k; split_ifs <;> simp_all +decide [ partialSum ] ;
        · unfold tightUnboundedStrategy; norm_num;
          unfold tightUnboundedStrategyX; norm_num;
        · rw [ div_eq_iff ];
          · convert tightUnboundedStrategy_sum k ( Nat.pos_of_ne_zero ‹_› ) using 1;
          · exact ne_of_gt ( by exact mul_pos ( by positivity ) ( by positivity ) );
      rw [ boundary_reduction ];
      -- The supremum of a set containing only 1 and 4 is 4.
      have h_sup : ⨆ k : ℕ, ENNReal.ofReal (if k = 0 then 1 else 4) = 4 := by
        rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num;
        · exact fun i => by split_ifs <;> norm_num;
        · exact fun w hw => ⟨ 1, hw.trans_le <| by norm_num ⟩;
      aesop

/-
The bounded worst-case score is at least 1.
-/
lemma boundedWorstCaseScore_ge_one {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    1 ≤ boundedWorstCaseScore s B := by
      refine' le_trans _ ( le_ciSup _ ⟨ 1, _ ⟩ );
      all_goals norm_num [ hB ];
      unfold boundedScore;
      unfold score;
      rw [ show hitIndex s ⟨ 1, by norm_num ⟩ = 0 from ?_ ];
      · norm_num [ partialSum ];
        exact s.one_le;
      · exact hitIndex_one s

/-
For a strictly increasing strategy, the partial sum $S_k$ is bounded by $R$ times the previous guess (or 1 if k=0).
-/
lemma partialSum_le_of_score_le_strict {s : Strategy} {B R : ℝ} {n k : ℕ}
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (hk : k < n) :
    partialSum s k ≤ R * (if k = 0 then 1 else s.x (k - 1)) := by
      exact partial_sum_le_of_score_le h_strict h_n h_score k hk

/-
If a strategy strictly increases at step k, then $S_k \le R x_{k-1}$.
-/
lemma partialSum_le_of_strict_step {s : Strategy} {B R : ℝ} {k : ℕ}
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hk : k > 0)
    (h_step : s.x (k - 1) < s.x k)
    (h_bound : s.x k ≤ B) :
    partialSum s k ≤ R * s.x (k - 1) := by
      have h_score_interval : ∀ y ∈ Set.Ioc (s.x (k - 1)) (s.x k), ENNReal.ofReal (partialSum s k / y) ≤ ENNReal.ofReal R := by
        refine' fun y hy => le_trans _ h_score;
        refine' le_trans _ ( le_ciSup _ ⟨ y, _ ⟩ );
        all_goals norm_num [ boundedScore ];
        rw [ score_eq_of_mem_Ioc ];
        · aesop;
        · exact ⟨ by linarith [ hy.1, show 1 ≤ s.x ( k - 1 ) from Nat.recOn ( k - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ], by linarith [ hy.2 ] ⟩;
      -- Taking the limit as $y$ approaches $x_{k-1}$ from the right, we get $S_k / x_{k-1} \le R$.
      have h_limit : Filter.Tendsto (fun y => ENNReal.ofReal (partialSum s k / y)) (nhdsWithin (s.x (k - 1)) (Set.Ioi (s.x (k - 1)))) (nhds (ENNReal.ofReal (partialSum s k / s.x (k - 1)))) := by
        exact ENNReal.tendsto_ofReal ( tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( ne_of_gt ( show 0 < s.x ( k - 1 ) from Nat.recOn ( k - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono ( Nat.le_succ n ) ] ) ) );
      have h_limit_le : ENNReal.ofReal (partialSum s k / s.x (k - 1)) ≤ ENNReal.ofReal R := by
        exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, h_step ⟩ ) fun y hy => h_score_interval y ⟨ hy.1, hy.2.le ⟩ );
      rw [ ENNReal.ofReal_le_ofReal_iff ] at h_limit_le;
      · rwa [ div_le_iff₀ ( show 0 < s.x ( k - 1 ) from lt_of_lt_of_le ( by linarith [ s.one_le ] ) ( s.mono ( Nat.zero_le _ ) ) ) ] at h_limit_le;
      · contrapose! h_limit_le;
        rw [ ENNReal.ofReal_eq_zero.mpr h_limit_le.le ] ; exact ENNReal.ofReal_pos.mpr ( div_pos ( show 0 < partialSum s k from Finset.sum_pos ( fun _ _ => show 0 < s.x _ from s.nonneg _ |> lt_of_le_of_ne <| Ne.symm <| by linarith [ s.one_le, s.mono <| Nat.zero_le ‹_› ] ) <| by aesop ) <| show 0 < s.x ( k - 1 ) from s.nonneg _ |> lt_of_le_of_ne <| Ne.symm <| by linarith [ s.one_le, s.mono <| Nat.zero_le ( k - 1 ) ] )

/-
If a strategy strictly increases at step k, then $x_k \le (R-1)x_{k-1} - S_{k-2}$.
-/
lemma strategy_recurrence_bound_strict {s : Strategy} {B R : ℝ} {k : ℕ}
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hk : 2 ≤ k)
    (h_step : s.x (k - 1) < s.x k)
    (h_bound : s.x k ≤ B) :
    s.x k ≤ (R - 1) * s.x (k - 1) - partialSum s (k - 2) := by
      have := partialSum_le_of_strict_step h_score ( by linarith ) h_step h_bound;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ partialSum ];
      norm_num [ Finset.sum_range_succ ] at * ; linarith

/-
Identity for tight polynomials: $p_{k+1} = (R-1)p_k - \sum_{j=0}^{k-2} p_{j+1}$.
-/
lemma tightPoly_recurrence_sum_identity {R : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    tightPoly (k + 1) R = (R - 1) * tightPoly k R - ∑ i ∈ Finset.range (k - 1), tightPoly (i + 1) R := by
      rcases k with ( _ | _ | k ) <;> norm_num [ Finset.sum_range_succ' ] at *;
      induction' k with k ih <;> norm_num [ Finset.sum_range_succ, tightPoly ] at *;
      · ring;
      · linarith

/-
If R is in the n-th bracket, then tight polynomials are non-decreasing up to index n.
-/
lemma tightPoly_monotone_of_mem_bracket {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    ∀ k, k < n → tightPoly k R ≤ tightPoly (k + 1) R := by
      -- Let $\theta \in [\pi/(n+3), \pi/(n+2)]$ such that $R = 4 \cos^2 \theta$.
      obtain ⟨θ, hθ_pos, hθ_lt, hθ_eq⟩ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), R = 4 * (Real.cos θ) ^ 2 := by
        -- By definition of $ratioLower$ and $ratioUpper$, we know that $R$ lies in the range of $4 \cos^2 \theta$ for $\theta \in [\pi/(n+3), \pi/(n+2)]$.
        have h_cos_range : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), Real.cos θ ^ 2 = R / 4 := by
          apply_rules [ intermediate_value_Icc' ] <;> norm_num;
          · bound;
          · exact Continuous.continuousOn ( Real.continuous_cos.pow 2 );
          · unfold ratioLower ratioUpper at hR;
            constructor <;> push_cast at * <;> linarith [ hR.1, hR.2 ];
        exact ⟨ h_cos_range.choose, h_cos_range.choose_spec.1, by linarith [ h_cos_range.choose_spec.2 ] ⟩;
      have h_sin_nonneg : ∀ k < n, 0 ≤ (2 * Real.cos θ) ^ k * Real.sin ((k + 3) * θ) / Real.sin θ := by
        intros k hk
        have h_sin_range : 0 < θ ∧ θ ≤ Real.pi / 2 := by
          exact ⟨ lt_of_lt_of_le ( by positivity ) hθ_pos.1, hθ_pos.2.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ⟩;
        exact div_nonneg ( mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith, by linarith ⟩ ) ) _ ) ( Real.sin_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( k : ℝ ) + 3 ≤ n + 2 by norm_cast; linarith ], by nlinarith [ Real.pi_pos, show ( k : ℝ ) + 3 ≤ n + 2 by norm_cast; linarith, hθ_pos.2, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ) ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith, by linarith ⟩ );
      intro k hk; specialize h_sin_nonneg k hk; rw [ ← tightPoly_diff_sign θ ( show 0 < θ by exact lt_of_lt_of_le ( by positivity ) hθ_pos.1 ) ( show θ < Real.pi by exact lt_of_le_of_lt hθ_pos.2 ( by rw [ div_lt_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ) ] at *; linarith;

/-
Identity relating b_seq to tight polynomials.
-/
lemma b_seq_eq_tightPoly_ratio {R : ℝ} {k : ℕ}
    (h_pos : ∀ j ≤ k + 1, 0 < tightPoly j R) :
    b_seq R k = R * tightPoly k R / tightPoly (k + 1) R := by
      induction' k with k ih;
      · -- By definition of $b_seq$, we have $b_seq R 0 = 1$.
        simp [b_seq];
        rw [ eq_div_iff ] <;> have := h_pos 0 <;> have := h_pos 1 <;> norm_num [ tightPoly ] at * ; linarith;
      · rw [ show b_seq R ( k + 1 ) = R / ( R - b_seq R k ) from rfl ];
        rw [ ih fun j hj => h_pos j ( by linarith ), sub_div' ];
        · rw [ div_div_eq_mul_div, tightPoly_recurrence_values ];
        · linarith [ h_pos ( k + 1 ) ( by linarith ) ]

/-
Auxiliary sequence definition and recurrence.
-/
noncomputable def dominance_aux_seq (delta1 R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else delta1 * tightPoly (k - 1) R

lemma dominance_aux_seq_recurrence {delta1 R : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    dominance_aux_seq delta1 R k = R * (dominance_aux_seq delta1 R (k - 1) - dominance_aux_seq delta1 R (k - 2)) := by
      rcases k with ( _ | _ | k ) <;> norm_num [ Nat.succ_eq_add_one, dominance_aux_seq ] at * ; ring_nf;
      rcases k with ( _ | k ) <;> simp +decide [ Nat.add_comm 2, Nat.add_comm 1, tightPoly ] ; ring

/-
Reconstruction of a sequence from its recurrence errors using convolution with tight polynomials.
-/
noncomputable def recurrence_error (u : ℕ → ℝ) (R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then u 0
  else if k = 1 then u 1 - R * u 0
  else u k - R * (u (k - 1) - u (k - 2))

lemma recurrence_reconstruction {u : ℕ → ℝ} {R : ℝ} (k : ℕ) :
    u k = ∑ j ∈ Finset.range (k + 1), tightPoly (k - j) R * recurrence_error u R j := by
  induction' k using Nat.strong_induction_on with k ih
  by_cases hk : k < 2
  · interval_cases k <;> norm_num [Finset.sum_range_succ]
    · unfold recurrence_error
      norm_num [tightPoly]
    · unfold recurrence_error
      ring_nf!
      norm_num [tightPoly]
  · have h_rec : u k = R * u (k - 1) - R * u (k - 2) + recurrence_error u R k := by
      unfold recurrence_error
      rcases k with (_ | _ | k) <;> norm_num at *
      ring!
    have h_subst :
        u k =
          R * (∑ j ∈ Finset.range k, tightPoly (k - 1 - j) R * recurrence_error u R j) -
            R * (∑ j ∈ Finset.range (k - 1), tightPoly (k - 2 - j) R * recurrence_error u R j) +
              recurrence_error u R k := by
      rcases k with (_ | _ | k) <;> simp_all +decide [Finset.sum_range_succ]
    rcases k with (_ | _ | k) <;> simp_all +decide [Finset.sum_range_succ]
    norm_num [add_assoc, add_tsub_assoc_of_le, Finset.sum_add_distrib, mul_add, mul_sub,
      sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul,
      tightPoly]
    rw [show
      ∑ i ∈ Finset.range k, R * (recurrence_error u R i * tightPoly (k + 1 - i) R) =
        ∑ i ∈ Finset.range k, recurrence_error u R i * tightPoly (k + 2 - i) R +
          ∑ i ∈ Finset.range k, R * (recurrence_error u R i * tightPoly (k - i) R) from ?_]
    · ring
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [show k + 2 - i = k + 1 - i + 1 from by
      rw [tsub_add_eq_add_tsub (by linarith [Finset.mem_range.mp hi])]]
    rw [show k + 1 - i = k - i + 1 from by
      rw [tsub_add_eq_add_tsub (by linarith [Finset.mem_range.mp hi])]]
    norm_num [tightPoly]
    ring

/-
The value of the bounded game is at most the first guess of the optimal strategy.
-/
theorem boundedGameValue_le_firstGuess {B : ℝ} (hB : 1 < B) :
    boundedGameValue B ≤ ENNReal.ofReal (firstGuess B) := by
      have := optimalStrategy_boundedScore B hB;
      exact this ▸ iInf_le _ _

/-
If R is in the n-th bracket, then the tight polynomials are non-decreasing up to index n.
-/
lemma tightPoly_monotone_upto_n {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    ∀ k, k < n → tightPoly k R ≤ tightPoly (k + 1) R := by
      exact fun k a ↦ tightPoly_monotone_of_mem_bracket hn hR k a

/-
If W is between 1 and rho_n, it lies in some bracket [rho_{j-1}, rho_j] for 1 <= j <= n.
-/
lemma exists_bracket_of_le_rho {n : ℕ} {W : ℝ} (hn : 1 ≤ n) (hW1 : 1 ≤ W) (hW_le : W ≤ ratioUpper n) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ W ∈ Set.Icc (ratioLower j) (ratioUpper j) := by
      norm_num [ ratioLower, ratioUpper ] at *;
      -- Let's choose the smallest $j$ such that $4 \cos^2(\pi / (j + 3)) \geq W$.
      obtain ⟨j, hj⟩ : ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ 4 * Real.cos (Real.pi / (j + 3)) ^ 2 ≥ W ∧ ∀ i : ℕ, 1 ≤ i → i < j → 4 * Real.cos (Real.pi / (i + 3)) ^ 2 < W := by
        have h_exists_j : ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ 4 * Real.cos (Real.pi / (j + 3)) ^ 2 ≥ W := by
          exact ⟨ n, hn, le_rfl, hW_le ⟩;
        exact ⟨ Nat.find h_exists_j, Nat.find_spec h_exists_j |>.1, Nat.find_spec h_exists_j |>.2.1, Nat.find_spec h_exists_j |>.2.2, fun i hi₁ hi₂ => not_le.1 fun hi₃ => Nat.find_min h_exists_j hi₂ ⟨ hi₁, by linarith [ Nat.find_spec h_exists_j |>.2.1 ], hi₃ ⟩ ⟩;
      refine' ⟨ j, hj.1, hj.2.1, _, hj.2.2.1 ⟩;
      rcases j with ( _ | _ | j ) <;> norm_num at *;
      · linarith;
      · have := hj.2.2 ( j + 1 ) ( by linarith ) ( by linarith ) ; norm_num [ add_assoc ] at * ; linarith

/-
If the current guess is less than B, there is a future step where the guess strictly increases.
-/
lemma exists_strict_step_ge {s : Strategy} {B : ℝ} {n k : ℕ}
    (h_n : s.x (n - 1) = B)
    (hk : k < n)
    (hk_val : if k = 0 then 1 < B else s.x (k - 1) < B) :
    ∃ m, k ≤ m ∧ m < n ∧ (if m = 0 then 1 < s.x 0 else s.x (m - 1) < s.x m) := by
      by_cases h_empty : ∀ m, k ≤ m ∧ m < n → s.x (m - 1) = s.x m;
      · have h_eq : ∀ m, k ≤ m ∧ m < n → s.x (k - 1) = s.x m := by
          intro m hm
          induction' m with m ih;
          · grind;
          · grind;
        specialize h_eq ( n - 1 ) ⟨ Nat.le_sub_one_of_lt hk, Nat.pred_lt ( ne_bot_of_gt hk ) ⟩ ; aesop;
      · obtain ⟨m, hm⟩ : ∃ m, k ≤ m ∧ m < n ∧ s.x (m - 1) ≠ s.x m := by
          aesop;
        -- Since s.x is monotone, if m is not zero, then s.x (m-1) < s.x m.
        have h_monotone : s.x (m - 1) ≤ s.x m := by
          exact s.mono ( Nat.pred_le _ );
        cases lt_or_eq_of_le h_monotone <;> aesop

/-
If R is in the n-th bracket, then the (n+1)-th tight polynomial is non-negative.
-/
theorem tightPoly_n_plus_one_nonneg {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n)) :
    0 ≤ tightPoly (n + 1) R := by
      -- By Lemma~\ref{lem:def:tightPoly_trig_form}, we know that $p_{n+1}(R) = (2 \cos \theta)^{n+1} \sin((n+2)\theta) / \sin \theta$.
      obtain ⟨θ, hθ_pos, hθ_pi, hR_eq⟩ : ∃ θ, 0 < θ ∧ θ < Real.pi ∧ R = 4 * Real.cos θ ^ 2 ∧ Real.pi / (n + 3) ≤ θ ∧ θ ≤ Real.pi / (n + 2) := by
        -- By Lemma~\ref{lem:def:tightPoly_trig_form}, we know that $R = 4 \cos^2 \theta$ for some $\theta$ in $[\pi/(n+3), \pi/(n+2)]$.
        obtain ⟨θ, hθ_range⟩ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), R = 4 * Real.cos θ ^ 2 := by
          have h_trig : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ) ^ 2 = R := by
            apply_rules [ intermediate_value_Icc' ];
            · bound;
            · exact Continuous.continuousOn ( by continuity );
            · unfold ratioLower ratioUpper at hR; aesop;
          grind;
        exact ⟨ θ, lt_of_lt_of_le ( by positivity ) hθ_range.1.1, lt_of_le_of_lt hθ_range.1.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ), hθ_range.2, hθ_range.1.1, hθ_range.1.2 ⟩;
      -- Since $\theta \in [\pi/(n+3), \pi/(n+2)]$, we have $(n+2)\theta \in [(n+2)\pi/(n+3), \pi]$.
      have h_sin_range : 0 ≤ Real.sin ((n + 2) * θ) := by
        exact Real.sin_nonneg_of_nonneg_of_le_pi ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith );
      have h_tightPoly_pos : tightPoly (n + 1) R = (2 * Real.cos θ) ^ (n + 1) * Real.sin ((n + 2) * θ) / Real.sin θ := by
        convert tightPoly_trig_form θ _ _ using 1 <;> norm_num [ hR_eq ];
        exacts [ rfl, by norm_cast, ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_pi ) ];
      exact h_tightPoly_pos.symm ▸ div_nonneg ( mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith, by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ) ) _ ) h_sin_range ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith, by linarith ⟩ )

/-
The number of steps n(B) tends to infinity as B tends to infinity.
-/
theorem nSteps_tendsto_atTop_proof : Tendsto nSteps atTop atTop := by
  exact nSteps_tendsto_atTop

/-
The growth base B^(1/n(B)) tends to 2 as B tends to infinity.
-/
theorem growthBase_tendsto_two_proof : Tendsto growthBase atTop (𝓝 2) := by
  exact growthBase_tendsto_two

/-
The first guess x(B) tends to 4 as B tends to infinity.
-/
theorem firstGuess_tendsto_four_proof : Tendsto firstGuess atTop (𝓝 4) := by
  exact firstGuess_tendsto_four

/-
If 1 < B <= 2, then nSteps B = 1.
-/
lemma nSteps_eq_one {B : ℝ} (hB1 : 1 < B) (hB2 : B ≤ 2) : nSteps B = 1 := by
  unfold nSteps;
  norm_num [ hB1, hB2 ];
  norm_num [ Nat.find_eq_iff ];
  exact ⟨ by norm_num [ stepBreakpoint_zero ] ; linarith, by norm_num [ stepBreakpoint_one ] ; linarith ⟩

/-
If 2 < B <= 2 + sqrt(5), then nSteps B = 2.
-/
lemma nSteps_eq_two {B : ℝ} (hB1 : 2 < B) (hB2 : B ≤ 2 + Real.sqrt 5) : nSteps B = 2 := by
  unfold nSteps;
  split_ifs <;> norm_num [ Nat.find_eq_iff ] at *;
  · unfold InStepRange;
    norm_num [ stepBreakpoint ] at *;
    exact ⟨ ⟨ by ring_nf; norm_num; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ], by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩, fun n hn hn' hn'' => by interval_cases n ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩;
  · linarith

/-
If 2 + sqrt(5) < B <= 9, then nSteps B = 3.
-/
lemma nSteps_eq_three {B : ℝ} (hB1 : 2 + Real.sqrt 5 < B) (hB2 : B ≤ 9) : nSteps B = 3 := by
  apply le_antisymm;
  · unfold nSteps;
    split_ifs <;> norm_num [ Nat.find_eq_iff ];
    use 3; norm_num [ InStepRange ];
    exact ⟨ by rw [ stepBreakpoint_two ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ], by rw [ stepBreakpoint_three ] ; linarith ⟩;
  · unfold nSteps;
    split_ifs <;> norm_num;
    · intro m hm₁ hm₂; interval_cases m <;> norm_num [ InStepRange ] at *;
      · exact fun _ => by rw [ stepBreakpoint_one ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;
      · unfold stepBreakpoint; norm_num; intros; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;
    · linarith [ Real.sqrt_nonneg 5 ]

/-
If nSteps B = 1, then firstGuess B = B.
-/
lemma firstGuess_eq_B_of_n_eq_one {B : ℝ} (hB : 1 < B) (hn : nSteps B = 1) : firstGuess B = B := by
  have := firstGuess_spec hB;
  unfold ratioLower ratioUpper at this; aesop;

/-
If nSteps B = 2, then firstGuess B is the positive root of R^2 - R - B = 0.
-/
lemma firstGuess_eq_root_of_n_eq_two {B : ℝ} (hB : 1 < B) (hn : nSteps B = 2) :
    firstGuess B = (1 + Real.sqrt (1 + 4 * B)) / 2 := by
      -- Since $n=2$, `firstGuess B` satisfies $p_2(R) = B$.
      have h_poly : tightPoly 2 (firstGuess B) = B := by
        have := firstGuess_spec hB; aesop;
      -- By definition of `tightPoly`, we know that `tightPoly 2 R = R * (R - 1)`.
      have h_poly_def : tightPoly 2 (firstGuess B) = firstGuess B * (firstGuess B - 1) := by
        bound;
      have h_quad : firstGuess B = (1 + Real.sqrt (1 + 4 * B)) / 2 ∨ firstGuess B = (1 - Real.sqrt (1 + 4 * B)) / 2 := by
        exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;
      have h_pos : 1 ≤ firstGuess B := by
        have := firstGuess_spec hB;
        exact this.1.trans' ( ratioLower_ge_one _ <| by linarith );
      exact h_quad.resolve_right ( by nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.sq_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] )

/-
If nSteps B = 3, then firstGuess B satisfies R^2(R-2) = B.
-/
lemma firstGuess_eq_root_of_n_eq_three {B : ℝ} (hB : 1 < B) (hn : nSteps B = 3) :
    (firstGuess B) ^ 2 * (firstGuess B - 2) = B := by
      have := @firstGuess_spec B hB;
      norm_num [ hn, tightPoly ] at this ⊢ ; linarith!

/-
The lower ratio endpoint for n steps is equal to the upper ratio endpoint for n-1 steps.
-/
lemma ratioLower_eq_ratioUpper_prev (n : ℕ) (hn : 1 ≤ n) :
    ratioLower n = ratioUpper (n - 1) := by
      cases n <;> aesop

/-
The sequence of breakpoints B_n is strictly increasing.
-/
lemma stepBreakpoint_strictMono : StrictMono stepBreakpoint := by
  refine' strictMono_nat_of_lt_succ _;
  -- The base function $2 \cos(\pi/(n+3))$ is strictly increasing for $n \geq 0$, and the exponent $n+1$ is strictly increasing.
  intros n
  have h_base : 2 * Real.cos (Real.pi / (n + 3)) < 2 * Real.cos (Real.pi / (n + 4)) := by
    exact mul_lt_mul_of_pos_left ( Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ( by gcongr ; linarith ) ) zero_lt_two
  have h_exp : (n + 1 : ℕ) < (n + 2 : ℕ) := by
    linarith;
  have h_base : 1 ≤ 2 * Real.cos (Real.pi / (n + 3)) := by
    exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( Real.cos_pi_div_three.symm.le.trans ( Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ] ) ) ) zero_le_two );
  have h_exp : (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1) < (2 * Real.cos (Real.pi / (n + 4))) ^ (n + 2) := by
    exact lt_of_lt_of_le ( pow_lt_pow_left₀ ‹_› ( by linarith ) ( by linarith ) ) ( pow_le_pow_right₀ ( by linarith ) ( by linarith ) );
  exact_mod_cast h_exp

/-
If R is in the n-th bracket and all tight polynomials up to k are non-negative, then p_k(R) is at most p_n(R).
-/
lemma tightPoly_max_first_lobe {n : ℕ} {R : ℝ} (hn : 1 ≤ n)
    (hR : R ∈ Set.Icc (ratioLower n) (ratioUpper n))
    (k : ℕ) (h_pos : ∀ i ≤ k, 0 ≤ tightPoly i R) :
    tightPoly k R ≤ tightPoly n R := by
      by_cases hk : k ≤ n + 2;
      · by_cases hk_le_n_plus_1 : k ≤ n + 1
        · exact tightPoly_le_max_upto_n_plus_one hn hR k (by linarith)
        · norm_num [ show k = n + 2 by linarith ] at *;
          exact le_trans ( tightPoly_step_limit n hn R hR |>.2 ) ( by linarith [ h_pos n ( by linarith ) ] );
      · -- If $k \ge n+3$, then $p_{n+3}(R) \ge 0 \implies p_{n+3}=0 \implies p_{n+1}=0$.
        have h_p_n_plus_3_zero : tightPoly (n + 3) R = 0 := by
          have h_p_n_plus_3_nonpos : tightPoly (n + 3) R ≤ 0 := by
            have h_tightPoly_n_plus_3_nonpos : tightPoly (n + 2) R ≤ 0 := by
              exact tightPoly_step_limit n hn R hR |>.2;
            exact mul_nonpos_of_nonneg_of_nonpos ( by linarith [ Set.mem_Icc.mp hR, show 0 ≤ R from le_trans ( by exact le_trans ( by norm_num ) ( ratioLower_ge_one n hn ) ) hR.1 ] ) ( sub_nonpos_of_le <| by linarith [ Set.mem_Icc.mp hR, show 0 ≤ R from le_trans ( by exact le_trans ( by norm_num ) ( ratioLower_ge_one n hn ) ) hR.1, h_pos ( n + 1 ) <| by linarith, h_pos ( n + 2 ) <| by linarith ] );
          exact le_antisymm h_p_n_plus_3_nonpos ( h_pos _ ( by linarith ) );
        -- If $p_{n+3}(R) = 0$, then $p_{n+1}(R) = 0$.
        have h_p_n_plus_1_zero : tightPoly (n + 1) R = 0 := by
          -- If $p_{n+3}(R) = 0$, then $p_{n+2}(R) = 0$.
          have h_p_n_plus_2_zero : tightPoly (n + 2) R = 0 := by
            have := tightPoly_step_limit n hn R hR;
            grind;
          have h_p_n_plus_1_zero : tightPoly (n + 3) R = R * (tightPoly (n + 2) R - tightPoly (n + 1) R) := by
            exact rfl;
          nlinarith [ hR.1, show 0 < R from lt_of_lt_of_le ( by exact lt_of_lt_of_le ( by positivity ) ( ratioLower_ge_one n hn ) ) hR.1 ];
        -- If $p_{n+1}(R) = 0$, then $p_n(R) = 0$.
        have h_p_n_zero : tightPoly n R = 0 := by
          have h_p_n_zero : tightPoly (n + 2) R = R * (tightPoly (n + 1) R - tightPoly n R) := by
            exact rfl;
          nlinarith [ h_pos n ( by linarith ), h_pos ( n + 1 ) ( by linarith ), h_pos ( n + 2 ) ( by linarith ), hR.1, hR.2, show 0 < R from lt_of_lt_of_le ( by exact lt_of_lt_of_le ( by norm_num ) ( ratioLower_ge_one n hn ) ) hR.1 ];
        have := tightPoly_pos n hn R hR n le_rfl; aesop;

/-
If W is less than the first guess x(B) and tight polynomials are non-negative up to m, then p_m(W) < B.
-/
lemma tightPoly_lt_B_of_lt_firstGuess_valid {B : ℝ} {W : ℝ} (hB : 1 < B) (hW1 : 1 ≤ W) (hW_lt : W < firstGuess B) :
    ∀ m, (∀ i ≤ m, 0 ≤ tightPoly i W) → tightPoly m W < B := by
      -- Let `n = nSteps B` and `R = firstGuess B`.
      set n := nSteps B
      set R := firstGuess B
      generalize_proofs at *; (
      -- By `exists_bracket_of_le_rho`, `W` is in some bracket `j` with `1 \le j \le n`.
      obtain ⟨j, hj1, hj2, hj3⟩ : ∃ j, 1 ≤ j ∧ j ≤ n ∧ W ∈ Set.Icc (ratioLower j) (ratioUpper j) := by
        apply exists_bracket_of_le_rho;
        · exact nSteps_spec hB |>.1;
        · linarith;
        · exact le_trans hW_lt.le ( firstGuess_spec hB |>.2.1 );
      -- By `tightPoly_max_first_lobe` (applied to `j` and `W`), `tightPoly m W \le tightPoly j W`.
      intros m hm_nonneg
      have hm_le_j : tightPoly m W ≤ tightPoly j W := by
        apply tightPoly_max_first_lobe hj1 hj3 m hm_nonneg;
      -- Case 1: `j < n`.
      by_cases hj_lt_n : j < n;
      · -- `tightPoly j W \le tightPoly j (ratioUpper j)` (by monotonicity on bracket).
        have hj_le_ratioUpper : tightPoly j W ≤ tightPoly j (ratioUpper j) := by
          have := tightPoly_strictMono_on_bracket j hj1;
          exact this.le_iff_le hj3 ( Set.right_mem_Icc.mpr <| by linarith [ hj3.1, hj3.2 ] ) |>.2 hj3.2;
        -- `tightPoly j (ratioUpper j) = stepBreakpoint j`.
        have hj_eq_stepBreakpoint : tightPoly j (ratioUpper j) = stepBreakpoint j := by
          exact tightPoly_endpoints j hj1 |>.2;
        have := nSteps_spec hB;
        exact hm_le_j.trans_lt ( lt_of_le_of_lt hj_le_ratioUpper ( by linarith [ this.2.1, this.2.2, stepBreakpoint_strictMono.monotone ( Nat.le_sub_one_of_lt hj_lt_n ) ] ) );
      · -- Since $j = n$, we have $tightPoly j W = tightPoly n W$.
        have hj_eq_n : j = n := by
          grind
        rw [hj_eq_n] at hj3 hm_le_j
        generalize_proofs at *; (
        -- Since $W < R$, we have $tightPoly n W < tightPoly n R$.
        have h_tightPoly_n_lt_R : tightPoly n W < tightPoly n R := by
          have h_tightPoly_n_lt_R : StrictMonoOn (tightPoly n) (Set.Icc (ratioLower n) (ratioUpper n)) := by
            exact tightPoly_strictMono_on_bracket n ( by linarith [ nSteps_spec hB ] )
          generalize_proofs at *; (
          exact h_tightPoly_n_lt_R hj3 ( firstGuess_spec hB |>.1 |> fun x => ⟨ x, firstGuess_spec hB |>.2.1 ⟩ ) hW_lt);
        linarith [ firstGuess_spec hB |>.2.2 ]))

/-
If a sequence u satisfies the recurrence u_k >= R*u_{k-1} - sum(u_j) and starts non-negative, and tight polynomials are non-negative, then u_k is non-negative.
-/
lemma recurrence_positivity {u : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : 1 ≤ R)
    (h_u0 : 0 ≤ u 0)
    (h_rec : ∀ k, 1 ≤ k → k < n → u k ≥ R * u (k - 1) - ∑ j ∈ Finset.range k, u j)
    (h_tight_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R) :
    ∀ k, k < n → 0 ≤ u k := by
      revert u R n hR h_u0 h_rec h_tight_nonneg; (
      intros u R n hR h_u0 h_rec h_tight_nonneg k hk_lt; exact (by
      -- Apply the lemma `dominance_property` to conclude that $u_k \leq \text{tightPoly}(k + 1, R)$.
      have h_dominate : ∀ m, m ≤ n → 0 ≤ tightPoly m R := by
        assumption;
      apply_rules [ nonneg_of_diffSeq_recurrence_bounded ];
      linarith))

/-
If u satisfies the difference recurrence, then its partial sums S satisfy the linear recurrence S_k >= R*S_{k-1} - R*S_{k-2}.
-/
lemma partial_sum_recurrence_of_diff_recurrence {u : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (h_rec : ∀ k, 1 ≤ k → k < n → u k ≥ R * u (k - 1) - ∑ j ∈ Finset.range k, u j) :
    let S := fun k => ∑ j ∈ Finset.range (k + 1), u j
    ∀ k, 2 ≤ k → k < n → S k ≥ R * S (k - 1) - R * S (k - 2) := by
      intro S k hk hk'; have := h_rec k ( by linarith ) hk'; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ] ;
      simp +zetaDelta at *;
      have := h_rec ( k + 1 ) ( by linarith ) ( by linarith ) ; have := h_rec ( k + 2 ) ( by linarith ) ( by linarith ) ; norm_num [ Finset.sum_range_succ ] at * ; nlinarith;

/-
If u satisfies the recurrence and tight polynomials are increasing, then u is non-negative.
-/
lemma recurrence_positivity_v2 {u : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : 1 ≤ R)
    (h_u0 : 0 ≤ u 0)
    (h_rec : ∀ k, 1 ≤ k → k < n → u k ≥ R * u (k - 1) - ∑ j ∈ Finset.range k, u j)
    (h_tight_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R)
    (h_mono : ∀ k, k < n → tightPoly k R ≤ tightPoly (k + 1) R) :
    ∀ k, k < n → 0 ≤ u k := by
      -- Apply the recurrence_positivity lemma with the given hypotheses.
      apply recurrence_positivity hR h_u0 h_rec h_tight_nonneg

/-
For a strictly increasing strategy with bounded score, the k-th guess is bounded by R times the previous guess minus the previous partial sum.
-/
lemma strategy_recurrence_sum_form {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (k : ℕ) (hk : 1 ≤ k) (hk_lt : k < n) :
    s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
      have := partial_sum_le_of_score_le h_strict h_n h_score k hk_lt;
      unfold partialSum at *;
      cases k <;> norm_num [ Finset.sum_range_succ ] at * ; nlinarith

/-
The difference sequence u_k = p_{k+1} - x_k satisfies the recurrence u_k >= R*u_{k-1} - sum(u_j), assuming the strategy is strictly increasing.
-/
lemma diffSeq_satisfies_recurrence {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R) :
    let u := fun k => tightPoly (k + 1) R - s.x k
    ∀ k, 1 ≤ k → k < n → u k ≥ R * u (k - 1) - ∑ j ∈ Finset.range k, u j := by
      simp +zetaDelta at *;
      -- Substitute the recurrence relation for tightPoly into the inequality.
      intro k hk hk_lt
      have h_tightPoly_rec : tightPoly (k + 1) R = R * tightPoly k R - ∑ j ∈ Finset.range k, tightPoly (j + 1) R := by
        exact tightPoly_recurrence_sum hk;
      have h_subst : s.x k ≤ R * s.x (k - 1) - partialSum s (k - 1) := by
        apply strategy_recurrence_sum_form h_strict h_n h_score k hk hk_lt;
      unfold partialSum at h_subst; rcases k with ( _ | k ) <;> norm_num at * ; linarith!;

/-
If a strictly increasing strategy has bounded score, its guesses are bounded by the tight polynomials.
-/
lemma dominance_property_strict {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R)
    (h_tight_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R)
    (h_mono : ∀ k, k < n → tightPoly k R ≤ tightPoly (k + 1) R) :
    ∀ k, k < n → s.x k ≤ tightPoly (k + 1) R := by
      exact fun k a ↦ dominance_property_proof h_strict h_n h_score hR h_tight_nonneg k a

/-
If S satisfies the linear recurrence inequalities, then its recurrence error terms are non-negative.
-/
lemma recurrence_error_nonneg {S : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (h_S0 : 0 ≤ S 0)
    (h_S1 : R * S 0 ≤ S 1)
    (h_rec : ∀ k, 2 ≤ k → k < n → S k ≥ R * S (k - 1) - R * S (k - 2)) :
    ∀ k, k < n → 0 ≤ recurrence_error S R k := by
      intro k hk
      by_cases hk0 : k = 0;
      · unfold recurrence_error; aesop;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ recurrence_error ];
        grind

/-
If tight polynomials are non-negative and monotone up to step j, then the strategy guesses are bounded by tight polynomials up to step j.
-/
lemma dominance_monotone_part {s : Strategy} {B R : ℝ} {n j : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R)
    (hj_le : j ≤ n)
    (h_tight_nonneg : ∀ k, k ≤ j → 0 ≤ tightPoly k R)
    (h_mono : ∀ k, k < j → tightPoly k R ≤ tightPoly (k + 1) R) :
    ∀ k, k < j → s.x k ≤ tightPoly (k + 1) R := by
      -- Fix an arbitrary `j`. Consider the strategy truncated at step `j`:
      -- `s_trunc` is defined only for `0 ≤ k ≤ j`. The properties of `s` (strict monotonicity, hitting, score) should be inherited by `s_trunc`, except that it doesn't necessarily hit `B`.
      let s_trunc : Strategy := ⟨fun k => s.x k, by
        exact s.nonneg, by
        exact s.one_le, by
        exact h_strict.monotone, by
        exact s.hits⟩
      generalize_proofs at *;
      -- By Lemma~\ref{lem:dominance_property_strict}, the hypotheses guarantee `x_trunc k ≤ p_{k+1} R` for `k ≤ j`.
      have h_truncated : ∀ k < j, s_trunc.x k ≤ tightPoly (k + 1) R := by
        have h_score_trunc : boundedWorstCaseScore s_trunc (s_trunc.x (j - 1)) ≤ ENNReal.ofReal R := by
          refine' le_trans _ h_score;
          refine' iSup_mono' _;
          simp +zetaDelta at *;
          exact fun a ha hb => ⟨ a, ⟨ ha, hb.trans <| h_n ▸ h_strict.monotone ( Nat.sub_le_sub_right hj_le 1 ) ⟩, le_rfl ⟩
        have h_mono_trunc : ∀ k < j, tightPoly k R ≤ tightPoly (k + 1) R := by
          assumption
        have h_tight_nonneg_trunc : ∀ k ≤ j, 0 ≤ tightPoly k R := by
          assumption
        apply_rules [ dominance_property_strict ]
      generalize_proofs at *;
      exact h_truncated

/-
If a strictly increasing strategy has bounded score, its guesses are bounded by the tight polynomials up to any step k where the tight polynomials are non-negative and monotone.
-/
lemma dominance_property_upto {s : Strategy} {B R : ℝ} {m : ℕ}
    (h_strict : StrictMono s.x)
    (h_m : s.x (m - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R)
    (k : ℕ) (hk : k < m)
    (h_tight_nonneg : ∀ j, j ≤ k → 0 ≤ tightPoly j R)
    (h_mono : ∀ j, j < k → tightPoly j R ≤ tightPoly (j + 1) R) :
    s.x k ≤ tightPoly (k + 1) R := by
      by_contra h_contra;
      exact h_contra <| strategy_eq_formula_x h_strict h_m h_score ( show R ≠ 0 by linarith ) k hk ▸ by
                                                                      unfold formula_x;
                                                                      norm_num [ Finset.sum_range_succ' ];
                                                                      refine' add_nonneg _ _;
                                                                      · refine' Finset.sum_nonneg fun i hi => mul_nonneg _ _;
                                                                        · exact div_nonneg ( h_tight_nonneg _ ( by norm_num at *; omega ) ) ( by positivity );
                                                                        · apply slack_nonneg h_strict h_m h_score (i + 1) (by linarith [Finset.mem_range.mp hi]);
                                                                      · refine' mul_nonneg ( div_nonneg ( _ ) ( by positivity ) ) ( _ );
                                                                        · induction' k with k ih;
                                                                          · exact le_of_lt ( by erw [ show tightPoly 1 R = R from rfl ] ; linarith );
                                                                          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( h_mono _ ( Nat.lt_succ_self _ ) ) );
                                                                        · apply_rules [ slack_nonneg ];
                                                                          linarith;



/-
If a strictly increasing strategy has worst-case score at most R, then the tight polynomials p_k(R) are non-negative for all k up to the length of the strategy.
-/
lemma tightPoly_nonneg_of_strict_strategy {s : Strategy} {B R : ℝ} {n : ℕ}
    (h_strict : StrictMono s.x)
    (h_n : s.x (n - 1) = B)
    (h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal R)
    (hR : 1 ≤ R) :
    ∀ k, k ≤ n → 0 ≤ tightPoly k R := by
      -- We prove this by induction on $k$.
      intro k hk_le_n
      induction' k using Nat.strong_induction_on with k ih;
      rcases k with ( _ | _ | k ) <;> norm_num [ tightPoly ] at *;
      · linarith;
      · -- By Lemma~\ref{lem:dominance_eq_formula_x}, $x_k = p_{k+1}(R) - \sum_{j=0}^k \frac{p_{k-j+1}(R)}{R} \epsilon_j$
        have h_x_eq : ∀ k < n, s.x k = tightPoly (k + 1) R - ∑ j ∈ Finset.range (k + 1), (tightPoly (k - j + 1) R / R) * slack s R j := by
          intros k hk_lt_n
          apply strategy_eq_formula_x h_strict h_n h_score (by linarith) k hk_lt_n;
        -- Split the sum into $j=0$ and $j > 0$.
        have h_split_sum : s.x (k + 1) = tightPoly (k + 2) R * (s.x 0 / R) - ∑ j ∈ Finset.range (k + 1), (tightPoly (k + 1 - j) R / R) * slack s R (j + 1) := by
          have h_x_eq_split : s.x (k + 1) = tightPoly (k + 2) R - (tightPoly (k + 2) R / R) * slack s R 0 - ∑ j ∈ Finset.range (k + 1), (tightPoly (k + 1 - j) R / R) * slack s R (j + 1) := by
            rw [ h_x_eq _ ( by linarith ), Finset.sum_range_succ' ] ; norm_num ; ring_nf;
            simp +decide [ add_tsub_add_eq_tsub_left, mul_comm, mul_left_comm ];
            exact Finset.sum_congr rfl fun x hx => by rw [ Nat.add_sub_assoc ( by linarith [ Finset.mem_range.mp hx ] ) ] ;
          convert h_x_eq_split using 1 ; unfold slack ; norm_num ; ring_nf;
          unfold partialSum; norm_num; ring_nf;
          norm_num [ show R ≠ 0 by linarith ];
        have h_tightPoly_nonneg : 0 ≤ tightPoly (k + 2) R * (s.x 0 / R) := by
          have h_nonneg : 0 ≤ s.x (k + 1) + ∑ j ∈ Finset.range (k + 1), (tightPoly (k + 1 - j) R / R) * slack s R (j + 1) := by
            refine' add_nonneg _ _;
            · exact s.nonneg _;
            · refine' Finset.sum_nonneg fun j hj => mul_nonneg _ _;
              · exact div_nonneg ( ih _ ( by omega ) ( by omega ) ) ( by positivity );
              · apply slack_nonneg h_strict h_n h_score (j + 1) (by linarith [Finset.mem_range.mp hj]);
          linarith;
        exact le_of_not_gt fun h => h_tightPoly_nonneg.not_gt <| mul_neg_of_neg_of_pos h <| div_pos ( by linarith [ s.nonneg 0, s.one_le ] ) <| by linarith;

/-
For a strictly increasing strategy ending at B, the worst-case score is at least the first guess x(B).
-/
theorem boundedWorstCaseScore_ge_firstGuess_strict {s : Strategy} {B : ℝ} (hB : 1 < B)
    (h_strict : StrictMono s.x) (n : ℕ) (hn : 1 ≤ n) (h_n : s.x (n - 1) = B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (firstGuess B) := by
      by_contra h_contra;
      -- Assume for contradiction that $W_B < \text{firstGuess}(B)$.
      obtain ⟨R, hR_ge_1, hR_lt⟩ : ∃ R, 1 ≤ R ∧ boundedWorstCaseScore s B ≤ ENNReal.ofReal R ∧ R < firstGuess B := by
        have hR_ge_one : 1 ≤ ENNReal.toReal (boundedWorstCaseScore s B) := by
          convert boundedWorstCaseScore_ge_one hB.le;
          rw [ ← ENNReal.ofReal_one, ENNReal.ofReal_le_iff_le_toReal ];
          aesop;
        refine' ⟨ ENNReal.toReal ( boundedWorstCaseScore s B ), hR_ge_one, _, _ ⟩;
        · rw [ ENNReal.ofReal_toReal ];
          aesop;
        · rw [ not_le, ENNReal.lt_ofReal_iff_toReal_lt ] at h_contra <;> aesop;
      -- By `tightPoly_nonneg_of_strict_strategy`, $p_k(R) \ge 0$ for all $k \le n$.
      have h_tightPoly_nonneg : ∀ k, k ≤ n → 0 ≤ tightPoly k R := by
        apply tightPoly_nonneg_of_strict_strategy;
        exacts [ h_strict, h_n, hR_lt.1, hR_ge_1 ];
      -- By `dominance_property_proof`, $s.x (n-1) \le p_n(R)$.
      have h_dom : B ≤ tightPoly n R := by
        have := dominance_property_proof h_strict h_n hR_lt.1 hR_ge_1 h_tightPoly_nonneg;
        rcases n <;> aesop;
      -- By `tightPoly_lt_B_of_lt_firstGuess_valid`, $p_n(R) < B$.
      have h_lt : tightPoly n R < B := by
        apply_rules [ tightPoly_lt_B_of_lt_firstGuess_valid ];
        linarith;
      linarith

/-
Truncate a strategy at B, replacing guesses >= B with B and then increasing linearly.
-/
noncomputable def truncateStrategy (s : Strategy) (B : ℝ) (hB : 1 ≤ B) : Strategy :=
  let N := Nat.find (s.hits hB)
  { x := fun k => if k < N then s.x k else B + (k - N)
    nonneg := fun k => by
      -- If $k < N$, then $s.x k$ is non-negative by the strategy's definition.
      by_cases hk : k < N;
      · -- Since $k < N$, we can use the hypothesis $h_unboundedNonneg$ to conclude that $0 \leq s.x k$.
        simp [hk, s.nonneg];
      · rw [ if_neg hk ] ; linarith [ show ( k : ℝ ) ≥ N by exact_mod_cast le_of_not_gt hk ]
    one_le := by
      -- If $N = 0$, then $s.x 0 > B$, and since $B \geq 1$, we have $s.x 0 > 1$.
      by_cases hN_zero : N = 0;
      · norm_num [ hN_zero, hB ];
      · rw [ if_pos ( Nat.pos_of_ne_zero hN_zero ) ];
        exact s.one_le
    mono := by
      refine' monotone_nat_of_le_succ _;
      intro n; split_ifs <;> norm_num at *;
      · exact s.mono ( Nat.le_succ _ );
      · -- Since $N \leq n + 1$, we have $B + (n + 1 - N) \geq B$.
        have h_ge_B : B + (n + 1 - N) ≥ B := by
          linarith [ show ( N : ℝ ) ≤ n + 1 by norm_cast ];
        refine' le_trans _ h_ge_B;
        exact le_of_not_gt fun h => by linarith [ Nat.find_min ( show ∃ N, s.x N ≥ B from ⟨ _, h.le ⟩ ) ( by linarith : n < N ) ] ;
      · linarith
    hits := fun {y} hy => by
      exact ⟨ N + ⌈y⌉₊, by rw [ if_neg ] <;> push_cast <;> linarith [ Nat.le_ceil y ] ⟩ }

/-
Truncate a strategy at B, replacing guesses >= B with B and then increasing linearly.
-/
noncomputable def truncateStrategyAux (s : Strategy) (B : ℝ) (hB : 1 ≤ B) : Strategy :=
  let N := Nat.find (s.hits hB)
  { x := fun k => if k < N then s.x k else B + (k - N)
    nonneg := fun k => by
      split_ifs <;> norm_num [ s.nonneg ];
      linarith [ show ( k : ℝ ) ≥ N by norm_cast; linarith ]
    one_le := by
      split_ifs <;> norm_num;
      · -- By definition of `Strategy`, we know that `s.x 0 ≥ 1`.
        apply s.one_le;
      · linarith [ show ( N : ℝ ) = 0 by norm_cast; linarith ]
    mono := by
      refine' monotone_nat_of_le_succ _;
      intro n; split_ifs <;> norm_num;
      · exact s.mono ( Nat.le_succ _ );
      · -- Since $s.x$ is strictly monotone, we have $s.x n < B$.
        have h_lt_B : s.x n < B := by
          aesop;
        linarith [ show ( n : ℝ ) + 1 ≥ N by norm_cast; linarith ];
      · linarith
    hits := fun {y} hy => by
      exact ⟨ N + Nat.ceil y, by push_cast; split_ifs <;> linarith [ Nat.le_ceil y ] ⟩ }

/-
The index at which the strategy first hits B.
-/
noncomputable def truncateIndex (s : Strategy) (B : ℝ) (hB : 1 ≤ B) : ℕ :=
  Nat.find (s.hits hB)

/-
The truncated strategy agrees with the original strategy before the truncation index.
-/
lemma truncateStrategyAux_x_eq_s {s : Strategy} {B : ℝ} {hB : 1 ≤ B} {k : ℕ}
    (hk : k < truncateIndex s B hB) :
    (truncateStrategyAux s B hB).x k = s.x k := by
      exact if_pos hk

/-
The truncated strategy hits any target y <= B at the same index as the original strategy.
-/
lemma hitIndex_truncateStrategyAux_eq {s : Strategy} {B : ℝ} {hB : 1 ≤ B} {y : {y : ℝ // 1 ≤ y ∧ y ≤ B}} :
    hitIndex (truncateStrategyAux s B hB) ⟨y.1, y.2.1⟩ = hitIndex s ⟨y.1, y.2.1⟩ := by
      generalize_proofs at *;
      refine' le_antisymm _ _;
      · -- By definition of `truncateStrategyAux`, we know that for any `k`, if `k < truncateIndex s B hB`, then `(truncateStrategyAux s B hB).x k = s.x k`. Therefore, if `s.x k ≥ y`, then `(truncateStrategyAux s B hB).x k ≥ y` as well.
        have h_truncate_x_ge_s_x : ∀ k, (s.x k ≥ y.val) → ((truncateStrategyAux s B hB).x k ≥ y.val) := by
          intro k hk_ge_y
          by_cases hk_lt_truncateIndex : k < truncateIndex s B hB;
          · exact hk_ge_y.trans ( by rw [ show ( truncateStrategyAux s B hB ).x k = s.x k from if_pos hk_lt_truncateIndex ] );
          · -- Since $k \geq \text{truncateIndex}$, we have $\text{truncateStrategyAux s B hB}.x k = B + (k - \text{truncateIndex})$.
            have h_truncate_x_ge_B : (truncateStrategyAux s B hB).x k = B + (k - truncateIndex s B hB) := by
              exact if_neg hk_lt_truncateIndex;
            linarith [ y.2.2, show ( k : ℝ ) ≥ truncateIndex s B hB by exact_mod_cast le_of_not_gt hk_lt_truncateIndex ];
        exact Nat.find_min' _ ( h_truncate_x_ge_s_x _ ( Nat.find_spec ( s.hits ‹_› ) ) );
      · unfold hitIndex;
        norm_num +zetaDelta at *;
        unfold truncateStrategyAux;
        grind

/-
The strategy's value at the truncation index is at least B.
-/
lemma s_x_ge_B_at_truncateIndex {s : Strategy} {B : ℝ} {hB : 1 ≤ B} :
    s.x (truncateIndex s B hB) ≥ B := by
      exact Nat.find_spec ( s.hits hB )

/-
The hit index for a target y <= B is at most the truncation index (hit index for B).
-/
lemma hitIndex_le_truncateIndex {s : Strategy} {B : ℝ} {hB : 1 ≤ B} {y : {y : ℝ // 1 ≤ y ∧ y ≤ B}} :
    hitIndex s ⟨y.1, y.2.1⟩ ≤ truncateIndex s B hB := by
      apply Nat.find_min';
      exact le_trans y.2.2 ( s_x_ge_B_at_truncateIndex )

/-
The partial sums of the truncated strategy are equal to the original strategy's partial sums before the truncation index.
-/
lemma partialSum_truncateStrategyAux_eq {s : Strategy} {B : ℝ} {hB : 1 ≤ B} {k : ℕ}
    (hk : k < truncateIndex s B hB) :
    partialSum (truncateStrategyAux s B hB) k = partialSum s k := by
      refine' Finset.sum_congr rfl fun i hi => _;
      -- Since $i \leq k < \text{truncateIndex}$, we have $i < \text{truncateIndex}$.
      have h_lt : i < truncateIndex s B hB := by
        linarith [ Finset.mem_range.mp hi ];
      exact if_pos h_lt

/-
The partial sums of the truncated strategy are less than or equal to the original strategy's partial sums up to the truncation index.
-/
lemma partialSum_truncateStrategyAux_le {s : Strategy} {B : ℝ} {hB : 1 ≤ B} {k : ℕ}
    (hk : k ≤ truncateIndex s B hB) :
    partialSum (truncateStrategyAux s B hB) k ≤ partialSum s k := by
      cases hk.eq_or_lt <;> simp_all +decide [ partialSum ];
      · rw [ Finset.sum_range_succ, Finset.sum_range_succ ];
        gcongr;
        · rw [ truncateStrategyAux_x_eq_s ] ; aesop;
        · -- By definition of `truncateStrategyAux`, we have `x (truncateIndex s B hB) = B`.
          simp [truncateStrategyAux];
          split_ifs <;> norm_num;
          rw [ show Nat.find ( s.hits hB ) = truncateIndex s B hB from _ ];
          · exact Nat.find_spec ( s.hits hB ) |> fun h => by aesop;
          · exact rfl;
      · -- Since the truncated strategy's guesses are equal to the original strategy's guesses up to k, their partial sums are equal.
        have h_partial_sum_eq : ∀ i ∈ Finset.range (k + 1), (truncateStrategyAux s B hB).x i = s.x i := by
          exact fun i hi => truncateStrategyAux_x_eq_s ( by linarith [ Finset.mem_range.mp hi ] );
        rw [ Finset.sum_congr rfl h_partial_sum_eq ]

/-
The truncated strategy has a worst-case score no worse than the original strategy.
-/
lemma truncateStrategyAux_score_le {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    boundedWorstCaseScore (truncateStrategyAux s B hB) B ≤ boundedWorstCaseScore s B := by
      refine' iSup_le _;
      intro y;
      refine' le_trans _ ( le_iSup _ y );
      unfold boundedScore;
      unfold score;
      gcongr;
      · exact le_trans zero_le_one y.2.1;
      · have h_partial_sum_le : ∀ k ≤ truncateIndex s B hB, partialSum (truncateStrategyAux s B hB) k ≤ partialSum s k := by
          exact fun k a ↦ partialSum_truncateStrategyAux_le a;
        rw [ hitIndex_truncateStrategyAux_eq ];
        exact h_partial_sum_le _ ( hitIndex_le_truncateIndex )

/-
Define a strategy that removes duplicates from the first N+1 guesses of an existing strategy and extends linearly.
-/
noncomputable def strictifyStrategy (s : Strategy) (N : ℕ) : Strategy :=
  let L := (List.range (N + 1)).map s.x
  let L_unique := L.dedup
  let M := L_unique.length
  have hL : L ≠ [] := by
    aesop
  have hL_unique : L_unique ≠ [] := by
    aesop
  have hM : 0 < M := by
    exact List.length_pos_iff.mpr hL_unique
  { x := fun k => if h : k < M then L_unique.get ⟨k, h⟩ else L_unique.getLast hL_unique + (k - (M - 1))
    nonneg := by
      -- Since $s$ is a strategy, all its guesses are non-negative. Therefore, each element in $L_unique$ is also non-negative.
      have hL_unique_nonneg : ∀ x ∈ L_unique, 0 ≤ x := by
        simp +zetaDelta at *;
        exact fun a ha => s.nonneg a;
      intro n; split_ifs <;> norm_num;
      · bound;
      · exact add_nonneg ( hL_unique_nonneg _ ( List.getLast_mem hL_unique ) ) ( by linarith [ show ( n : ℝ ) ≥ M by norm_cast; linarith ] )
    one_le := by
      -- Since $s$ is a strategy, $s.x 0 \geq 1$.
      have h_x0_ge_1 : 1 ≤ s.x 0 := by
        exact s.one_le;
      -- Since $L_unique$ is a deduplicated list of the first $N+1$ elements of $s$, and $s.x 0 \geq 1$, the first element of $L_unique$ is also at least $1$.
      have hL_unique_first_ge_1 : ∀ {l : List ℝ}, (∀ x ∈ l, 1 ≤ x) → ∀ {x : ℝ}, x ∈ l → 1 ≤ x := by
        exact fun {l} a {x} a_1 ↦ a x a_1;
      have hL_unique_first_ge_1 : ∀ x ∈ L_unique, 1 ≤ x := by
        intros x hx; exact hL_unique_first_ge_1 ( fun x hx => by
          have hL_unique_first_ge_1 : ∀ x ∈ L, 1 ≤ x := by
            intro x hx; rw [ List.mem_map ] at hx; obtain ⟨ k, hk, rfl ⟩ := hx; exact Nat.recOn k h_x0_ge_1 fun n ihn => by simpa using le_trans ihn ( s.mono n.le_succ ) ;
          exact hL_unique_first_ge_1 x ( List.mem_dedup.mp hx ) ) hx;
      grind
    mono := by
      refine' monotone_nat_of_le_succ fun n => _;
      split_ifs <;> norm_num at *;
      · have h_sorted : List.Sorted (· ≤ ·) L := by
          have h_sorted : Monotone s.x := by
            exact monotone_nat_of_le_succ fun n => s.mono n.le_succ;
          rw [ List.Sorted ];
          rw [ List.pairwise_map ];
          rw [ List.pairwise_iff_get ];
          exact fun i j hij => h_sorted <| by simpa using hij.le;
        have h_sorted_dedup : List.Sorted (· ≤ ·) (L.dedup) := by
          exact h_sorted.sublist ( List.dedup_sublist _ );
        have := List.pairwise_iff_get.mp h_sorted_dedup;
        exact this ⟨ n, by linarith ⟩ ⟨ n + 1, by linarith ⟩ ( Nat.lt_succ_self _ );
      · -- Since $M \leq n + 1$, we have $L_unique[n] = L_unique.getLast hL_unique$.
        have h_eq : L_unique[n] = L_unique.getLast hL_unique := by
          grind +ring;
        linarith [ show ( M : ℝ ) ≤ n + 1 by norm_cast ];
      · linarith
    hits := by
      intro y hy
      use Nat.ceil (y - L_unique.getLast hL_unique) + M;
      simp
      linarith [ Nat.le_ceil ( y - L_unique.getLast hL_unique ) ] }

/-
The strictified strategy is strictly increasing.
-/
lemma strictifyStrategy_strictMono {s : Strategy} {N : ℕ} :
    StrictMono (strictifyStrategy s N).x := by
  unfold strictifyStrategy
  simp +zetaDelta
  refine strictMono_nat_of_lt_succ ?_
  intro n
  split_ifs
  · have h_sorted : List.Sorted (· ≤ ·) ((List.range (N + 1)).map s.x) := by
      have h_sorted : Monotone s.x := by
        exact monotone_nat_of_le_succ fun n => s.mono n.le_succ
      rw [List.Sorted]
      rw [List.pairwise_map]
      rw [List.pairwise_iff_get]
      exact fun i j hij => h_sorted <| by simpa using hij.le
    have h_sorted_dedup : List.Sorted (· ≤ ·) (((List.range (N + 1)).map s.x).dedup) := by
      exact h_sorted.sublist (List.dedup_sublist _)
    have hle := List.pairwise_iff_get.mp h_sorted_dedup
        ⟨n, by assumption⟩ ⟨n + 1, by assumption⟩ (Nat.lt_succ_self _)
    have hne :
        (((List.range (N + 1)).map s.x).dedup).get ⟨n, by assumption⟩ ≠
          (((List.range (N + 1)).map s.x).dedup).get ⟨n + 1, by assumption⟩ := by
      intro heq
      have hfin :
          (⟨n, by assumption⟩ :
              Fin (((List.range (N + 1)).map s.x).dedup.length)) =
            ⟨n + 1, by assumption⟩ := by
        exact (List.Nodup.get_inj_iff (List.nodup_dedup _)).mp heq
      exact Nat.succ_ne_self n (by simpa using congrArg Fin.val hfin)
    exact lt_of_le_of_ne hle hne
  · have h_eq :
        ((List.map s.x (List.range (N + 1))).dedup)[n] =
          ((List.map s.x (List.range (N + 1))).dedup).getLast (by aesop) := by
      grind +ring
    rw [h_eq]
    norm_num
    have hlen : ((List.map s.x (List.range (N + 1))).dedup.length : ℝ) = n + 1 := by
      norm_cast
      omega
    linarith
  · omega
  · ring_nf
    norm_num at *
    linarith

/-
For a sorted non-empty list, deduplication preserves the last element.
-/
lemma List_dedup_getLast_eq_getLast_of_sorted {α : Type*} [LinearOrder α] {L : List α}
    (h_sorted : List.Sorted (· ≤ ·) L) (h_ne_nil : L ≠ []) :
    L.dedup.getLast (by simpa using h_ne_nil) = L.getLast h_ne_nil := by
      induction' L with x xs ih
      · contradiction
      · cases' xs with y ys
        · simp
        · have h_tail : List.Sorted (· ≤ ·) (y :: ys) := List.Sorted.tail h_sorted
          by_cases hx : x ∈ y :: ys
          · simpa [List.dedup_cons_of_mem hx, List.getLast_cons] using ih h_tail (by simp)
          · simpa [List.dedup_cons_of_notMem hx, List.getLast_cons] using ih h_tail (by simp)

/-
The strictified truncated strategy ends at B.
-/
lemma strictifyStrategy_ends_at_B {s : Strategy} {B : ℝ} {hB : 1 ≤ B} :
    let N := truncateIndex s B hB
    let s_trunc := truncateStrategyAux s B hB
    let s_strict := strictifyStrategy s_trunc N
    ∃ n, 1 ≤ n ∧ s_strict.x (n - 1) = B := by
      have h_last : B ∈ (List.range (truncateIndex s B hB + 1)).map (fun k => (truncateStrategyAux s B hB).x k) := by
        have h_last : (truncateStrategyAux s B hB).x (truncateIndex s B hB) = B := by
          unfold truncateStrategyAux truncateIndex; aesop;
        exact List.mem_map.mpr ⟨ _, List.mem_range.mpr ( Nat.lt_succ_self _ ), h_last ⟩;
      have h_last : B ∈ (List.map (fun k => (truncateStrategyAux s B hB).x k) (List.range (truncateIndex s B hB + 1))).dedup := by
        rw [ List.mem_dedup ] ; aesop;
      obtain ⟨ n, hn ⟩ := List.mem_iff_get.1 h_last;
      use n.val + 1;
      unfold strictifyStrategy; aesop;

/-
The strict strategy is obtained by truncating at B and removing duplicates.
-/
noncomputable def strictStrategy (s : Strategy) (B : ℝ) (hB : 1 ≤ B) : Strategy :=
  strictifyStrategy (truncateStrategyAux s B hB) (truncateIndex s B hB)

/-
The strict strategy is strictly increasing.
-/
theorem strictStrategy_strictMono {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    StrictMono (strictStrategy s B hB).x := by
      exact strictifyStrategy_strictMono

/-
The strict strategy ends at B.
-/
theorem strictStrategy_ends_at_B_valid {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    ∃ n, 1 ≤ n ∧ (strictStrategy s B hB).x (n - 1) = B := by
      -- Apply the lemma that states the strictified truncated strategy ends at B.
      apply strictifyStrategy_ends_at_B

/-
The values of the strictified strategy are present in the original strategy's values (up to N).
-/
lemma strictifyStrategy_mem_values {s : Strategy} {N : ℕ} {k : ℕ}
    (hk : k < ((List.range (N + 1)).map s.x).dedup.length) :
    (strictifyStrategy s N).x k ∈ (List.range (N + 1)).map s.x := by
      have h_exists : ∀ s : Strategy, ∀ N, ∀ k < (List.map s.x (List.range (N + 1))).dedup.length, (strictifyStrategy s N).x k ∈ (List.map s.x (List.range (N + 1))).dedup := by
        unfold strictifyStrategy; aesop;
      exact List.mem_dedup.mp ( h_exists s N k hk )

/-
The sum of a deduplicated list of non-negative numbers is less than or equal to the sum of the original list.
-/
lemma List_dedup_sum_le_sum {L : List ℝ} (h_nonneg : ∀ x ∈ L, 0 ≤ x) :
    L.dedup.sum ≤ L.sum := by
      induction' L with a L ih <;> simp_all
      by_cases ha : a ∈ L <;> simp_all +decide [ List.dedup_cons_of_mem ];
      linarith

/-
The value of the strategy at the hit index is the smallest value in the strategy's range that is at least y.
-/
lemma value_at_hitIndex_eq_min {s : Strategy} {y : ℝ} (hy : 1 ≤ y) :
    IsLeast { v | v ∈ Set.range s.x ∧ y ≤ v } (s.x (hitIndex s ⟨y, hy⟩)) := by
      constructor;
      · exact ⟨ Set.mem_range_self _, by exact Nat.find_spec ( s.hits hy ) ⟩;
      · rintro _ ⟨ ⟨ k, rfl ⟩, hk ⟩ ; exact s.mono ( Nat.le_of_not_lt fun h => by linarith [ Nat.find_min ( show ∃ n, s.x n ≥ y from ⟨ k, hk ⟩ ) h ] ) ;

/-
The set of values of the strictified strategy (up to its length) is exactly the set of values of the original strategy (up to N).
-/
lemma mem_strictifyStrategy_range {s : Strategy} {N : ℕ} (v : ℝ) :
    (∃ k, k ≤ N ∧ s.x k = v) ↔
    (∃ k, k < ((List.range (N + 1)).map s.x).dedup.length ∧ (strictifyStrategy s N).x k = v) := by
      constructor
      · rintro ⟨k, hkN, rfl⟩
        have h_mem : s.x k ∈ ((List.range (N + 1)).map s.x).dedup := by
          rw [List.mem_dedup]
          exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_mem
        refine' ⟨i, i.2, _⟩
        unfold strictifyStrategy
        simpa [hi]
      · rintro ⟨k, hk, hk_eq⟩
        have h_mem_dedup :
            v ∈ ((List.range (N + 1)).map s.x).dedup := by
          rw [← hk_eq]
          unfold strictifyStrategy
          simp [hk]
        have h_mem : v ∈ (List.range (N + 1)).map s.x := List.mem_dedup.mp h_mem_dedup
        obtain ⟨j, hj, hjv⟩ := List.mem_map.mp h_mem
        exact ⟨j, Nat.le_of_lt_succ (List.mem_range.mp hj), hjv⟩

/-
The sum of a filtered deduplicated list is less than or equal to the sum of the filtered original list, assuming non-negative elements.
-/
lemma List_dedup_filter_sum_le {L : List ℝ} (p : ℝ → Bool) (h_nonneg : ∀ x ∈ L, 0 ≤ x) :
    (L.dedup.filter p).sum ≤ (L.filter p).sum := by
      by_contra h_contra;
      induction' L with x L ih generalizing p;
      · norm_num at h_contra;
      · by_cases hx : x ∈ L <;> simp_all +decide [ List.filter_cons ];
        · grind;
        · split_ifs at h_contra <;> simp_all +decide [ List.sum_cons ];
          · linarith [ ih p ];
          · linarith [ ih p ]

/-
The truncated strategy takes the value B at the truncation index.
-/
lemma truncateStrategyAux_at_N_eq_B {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    (truncateStrategyAux s B hB).x (truncateIndex s B hB) = B := by
      unfold truncateStrategyAux;
      unfold truncateIndex; aesop

/-
The set of values of the strictified strategy that are at most the last value of the original segment is exactly the set of values in the original segment.
-/
lemma strictifyStrategy_range_le_last {s : Strategy} {N : ℕ} :
    let B' := s.x N
    { v ∈ Set.range (strictifyStrategy s N).x | v ≤ B' } = { v | v ∈ (List.range (N + 1)).map s.x } := by
      ext v
      constructor
      · rintro ⟨⟨k, hk_eq⟩, hv_le⟩
        by_cases hk : k < ((List.range (N + 1)).map s.x).dedup.length
        · have h_mem_dedup :
              v ∈ ((List.range (N + 1)).map s.x).dedup := by
            rw [← hk_eq]
            unfold strictifyStrategy
            simp [hk]
          exact List.mem_dedup.mp h_mem_dedup
        · have h_sorted : List.Sorted (· ≤ ·) ((List.range (N + 1)).map s.x) := by
            rw [List.Sorted, List.pairwise_map, List.pairwise_iff_get]
            exact fun i j hij =>
              (monotone_nat_of_le_succ fun n => s.mono n.le_succ) (by simpa using hij.le)
          have h_last :
              ((List.range (N + 1)).map s.x).dedup.getLast (by aesop) = s.x N := by
            have h_getLast :
                ((List.range (N + 1)).map s.x).getLast (by aesop) = s.x N := by
              simp [List.range_succ]
            exact (List_dedup_getLast_eq_getLast_of_sorted h_sorted (by aesop)).trans h_getLast
          have hv_eq :
              v =
                ((List.range (N + 1)).map s.x).dedup.getLast (by aesop) +
                  (k - (((List.range (N + 1)).map s.x).dedup.length - 1)) := by
            unfold strictifyStrategy at hk_eq
            simpa [hk] using hk_eq.symm
          have hv_eq_last : v = s.x N := by
            have hv_eq' :
                v =
                  s.x N +
                    (k - (((List.range (N + 1)).map s.x).dedup.length - 1)) := by
              simpa [h_last] using hv_eq
            have hnonneg :
                0 ≤
                  ((k - (((List.range (N + 1)).map s.x).dedup.length - 1) : ℕ) : ℝ) := by
              positivity
            have hk_ge_nat :
                (List.map s.x (List.range (N + 1))).dedup.length ≤ k := by
              exact not_lt.mp hk
            have hk_ge_real :
                ((List.map s.x (List.range (N + 1))).dedup.length : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast hk_ge_nat
            have htail_nonneg :
                0 ≤
                  ((k : ℝ) -
                    (((List.map s.x (List.range (N + 1))).dedup.length : ℝ) - 1)) := by
              linarith
            linarith [hv_eq', hv_le, htail_nonneg]
          rw [hv_eq_last]
          exact List.mem_map.mpr ⟨N, List.mem_range.mpr (Nat.lt_succ_self N), rfl⟩
      · intro hv
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
        have hkN : k ≤ N := Nat.le_of_lt_succ (List.mem_range.mp hk)
        obtain ⟨j, hj, hj_eq⟩ :=
          (mem_strictifyStrategy_range (s := s) (N := N) (s.x k)).1 ⟨k, hkN, rfl⟩
        exact ⟨⟨j, hj_eq⟩, (monotone_nat_of_le_succ fun n => s.mono n.le_succ) hkN⟩

/-
If two sets have the same intersection with $(-\infty, B]$, and both contain an element $\le B$ which is $\ge y$, then their least elements $\ge y$ are the same.
-/
lemma IsLeast_ge_eq_of_inter_le_eq {S1 S2 : Set ℝ} {y B : ℝ}
    (h_inter : {v ∈ S1 | v ≤ B} = {v ∈ S2 | v ≤ B})
    (h_yB : y ≤ B)
    (m1 m2 : ℝ)
    (h_m1 : IsLeast {v ∈ S1 | y ≤ v} m1)
    (h_m2 : IsLeast {v ∈ S2 | y ≤ v} m2)
    (h_B1 : B ∈ S1) :
    m1 = m2 := by
      apply le_antisymm;
      · -- Since $m2$ is the least element of $\{v \in S2 \mid y \le v\}$, we have $m2 \le B$.
        have h_m2_le_B : m2 ≤ B := by
          exact h_m2.2 ⟨ h_inter.subset ⟨ h_B1, le_rfl ⟩ |>.1, h_yB ⟩;
        exact h_m1.2 ⟨ h_inter.symm.subset ⟨ h_m2.1.1, h_m2_le_B ⟩ |>.1, h_m2.1.2 ⟩;
      · refine' h_m2.2 ⟨ _, _ ⟩;
        · -- Since $m1 \leq B$ and $m1 \in S1$, by $h_inter$, we have $m1 \in S2$.
          have h_m1_in_S2 : m1 ∈ S2 := by
            have h_m1_le_B : m1 ≤ B := by
              exact h_m1.2 ⟨ h_B1, h_yB ⟩
            exact h_inter.subset ⟨ h_m1.1.1, h_m1_le_B ⟩ |>.1;
          exact h_m1_in_S2;
        · exact h_m1.1.2

/-
The value hit by the strict strategy is the same as the value hit by the truncated strategy for any target y <= B.
-/
lemma strictifyStrategy_hit_value_eq {s : Strategy} {B : ℝ} (hB : 1 ≤ B) {y : {y : ℝ // 1 ≤ y ∧ y ≤ B}} :
    (strictStrategy s B hB).x (hitIndex (strictStrategy s B hB) ⟨y.1, y.2.1⟩) =
    (truncateStrategyAux s B hB).x (hitIndex (truncateStrategyAux s B hB) ⟨y.1, y.2.1⟩) := by
      all_goals generalize_proofs at *;
      have h_eq : IsLeast { v ∈ Set.range (strictStrategy s B hB).x | y.val ≤ v } ( (strictStrategy s B hB).x (hitIndex (strictStrategy s B hB) ⟨y.val, by linarith⟩) ) ∧ IsLeast { v ∈ Set.range (truncateStrategyAux s B hB).x | y.val ≤ v } ( (truncateStrategyAux s B hB).x (hitIndex (truncateStrategyAux s B hB) ⟨y.val, by linarith⟩) ) := by
        exact ⟨ value_at_hitIndex_eq_min <| by linarith, value_at_hitIndex_eq_min <| by linarith ⟩;
      have h_eq : { v ∈ Set.range (strictStrategy s B hB).x | v ≤ B } = { v ∈ Set.range (truncateStrategyAux s B hB).x | v ≤ B } := by
        have h_eq : { v ∈ Set.range (strictStrategy s B hB).x | v ≤ B } = { v | v ∈ (List.range (truncateIndex s B hB + 1)).map (truncateStrategyAux s B hB).x } := by
          convert strictifyStrategy_range_le_last using 1;
          congr! 2;
          rw [ truncateStrategyAux_at_N_eq_B ] ; aesop;
        ext v;
        simp_all +decide [ Set.ext_iff ];
        constructor <;> intro h;
        · grind;
        · rcases h with ⟨ ⟨ y, rfl ⟩, hy ⟩;
          refine' ⟨ y, _, rfl ⟩;
          contrapose! hy;
          rw [ truncateStrategyAux ];
          field_simp;
          rw [ if_neg ] <;> norm_num;
          · exact ⟨ truncateIndex s B hB, by linarith, s_x_ge_B_at_truncateIndex ⟩;
          · exact ⟨ truncateIndex s B hB, by linarith, Nat.find_spec ( s.hits hB ) ⟩;
      apply IsLeast_ge_eq_of_inter_le_eq;
      · exact h_eq;
      · exact y.2.2;
      · tauto;
      · tauto;
      · obtain ⟨ n, hn ⟩ := strictStrategy_ends_at_B_valid hB;
        exact ⟨ _, hn.2 ⟩

/-
For a sorted strategy, the partial sum at the hit index equals the sum of guesses strictly less than y plus the hit value.
-/
lemma partialSum_eq_filter_sum_add {s : Strategy} {y : ℝ} (hy : 1 ≤ y) {N : ℕ}
    (h_sorted : Monotone s.x)
    (h_hit : hitIndex s ⟨y, hy⟩ < N) :
    partialSum s (hitIndex s ⟨y, hy⟩) =
    (((List.range N).map s.x).filter (fun x => x < y)).sum + s.x (hitIndex s ⟨y, hy⟩) := by
      -- The filtered list contains exactly the elements of the original list up to the hit index.
      have h_filter : List.filter (fun x => x < y) (List.map s.x (List.range N)) = List.map s.x (List.range (hitIndex s ⟨y, hy⟩)) := by
        have h_filter : List.filter (fun x => x < y) (List.map s.x (List.range N)) = List.map s.x (List.filter (fun i => s.x i < y) (List.range N)) := by
          rw [ List.filter_map ];
          rfl;
        have h_filter_eq : List.filter (fun i => s.x i < y) (List.range N) = List.range (hitIndex s ⟨y, hy⟩) := by
          have h_filter_eq : ∀ i < N, s.x i < y ↔ i < hitIndex s ⟨y, hy⟩ := by
            intro i hi
            constructor;
            · exact fun h => lt_of_not_ge fun h' => h.not_ge <| h_sorted h' |> le_trans ( Nat.find_spec ( s.hits hy ) );
            · exact fun h => lt_of_not_ge fun h' => h.not_ge <| Nat.le_of_not_lt fun h'' => by have := Nat.find_min ( show ∃ k, s.x k ≥ y from ⟨ _, h' ⟩ ) h''; aesop;
          have h_filter_eq : List.filter (fun i => s.x i < y) (List.range N) = List.filter (fun i => i < hitIndex s ⟨y, hy⟩) (List.range N) := by
            exact List.filter_congr fun i hi => by aesop;
          rw [ h_filter_eq ];
          have h_filter_eq : ∀ {n m : ℕ}, n ≤ m → List.filter (fun i => decide (i < n)) (List.range m) = List.range n := by
            intros n m hnm; induction' hnm with m hnm ih <;> simp_all +decide [ List.range_succ ] ;
          exact h_filter_eq h_hit.le;
        rw [h_filter, h_filter_eq];
      simp +decide [ h_filter, partialSum ];
      rw [ Finset.sum_range_succ, List.sum_eq_foldr ] ; aesop

/-
For a sorted list, filtering then deduplicating is the same as deduplicating then filtering.
-/
lemma Sorted_dedup_filter_eq_filter_dedup {L : List ℝ} (h : List.Sorted (· ≤ ·) L) (y : ℝ) :
    (L.dedup.filter (· < y)) = (L.filter (· < y)).dedup := by
      have h_sorted_dedup : List.Sorted (· ≤ ·) (List.dedup L) := by
        exact h.sublist ( List.dedup_sublist _ );
      have h_sorted_filter_dedup : List.Sorted (· ≤ ·) (List.dedup (List.filter (fun x => x < y) L)) := by
        have h_sorted_filter_dedup : List.Sorted (· ≤ ·) (List.filter (fun x => x < y) L) := by
          exact h.filter _;
        exact h_sorted_filter_dedup.sublist ( List.dedup_sublist _ );
      have h_eq_elements : List.Perm (List.filter (fun x => x < y) (List.dedup L)) (List.dedup (List.filter (fun x => x < y) L)) := by
        rw [ List.perm_iff_count ];
        intro x; by_cases hx : x < y <;> simp_all +decide [ List.count_dedup ] ;
        rw [ List.count_eq_zero_of_not_mem ] <;> aesop;
      exact List.eq_of_perm_of_sorted
        (fun a b _ _ hab hba => le_antisymm hab hba)
        ( List.Sorted.filter ( fun x => decide ( x < y ) ) h_sorted_dedup )
        h_sorted_filter_dedup h_eq_elements

/-
For a sorted list, if the prefix elements are less than y and the suffix elements are at least y, then filtering for elements less than y yields the prefix.
-/
lemma List_filter_lt_eq_take_of_sorted {L : List ℝ} (h_sorted : List.Sorted (· ≤ ·) L) (y : ℝ) (k : ℕ)
    (h_take : ∀ x ∈ L.take k, x < y)
    (h_drop : ∀ x ∈ L.drop k, y ≤ x) :
    L.filter (· < y) = L.take k := by
      induction' L with a L ih generalizing k
      · simp
      · cases' k with k
        · have h_not : ∀ x ∈ a :: L, ¬x < y := by
            intro x hx
            exact not_lt.mpr (h_drop x hx)
          have h_filter_nil : (a :: L).filter (fun x => decide (x < y)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro x hx hdec
            exact h_not x hx (of_decide_eq_true hdec)
          simpa using h_filter_nil
        · have ha : a < y := h_take a (by simp)
          have h_take_tail : ∀ x ∈ L.take k, x < y := by
            intro x hx
            exact h_take x (by simp [hx])
          have h_drop_tail : ∀ x ∈ L.drop k, y ≤ x := by
            intro x hx
            exact h_drop x (by simpa using hx)
          simp [ha, ih (List.Sorted.tail h_sorted) k h_take_tail h_drop_tail]

/-
For a sorted list, taking the prefix before the first element >= y is equivalent to filtering for elements < y.
-/
lemma List_take_eq_filter_lt_of_sorted {L : List ℝ} (h_sorted : List.Sorted (· ≤ ·) L) (y : ℝ) (k : ℕ)
    (hk_lt : k < L.length)
    (h_k : L.get ⟨k, hk_lt⟩ ≥ y)
    (h_prev : ∀ j, (hj : j < k) → L.get ⟨j, by linarith⟩ < y) :
    L.take k = L.filter (· < y) := by
      have h_take_eq_filter : ∀ {L : List ℝ} {k : ℕ} (_ : k ≤ L.length), (List.Sorted (· ≤ ·) L) → (∀ j, j < k → L[j]! < y) → (∀ j, k ≤ j → j < L.length → y ≤ L[j]!) → List.take k L = List.filter (fun x => x < y) L := by
        intros L k hk_le_L h_sorted h_k_lt h_k_ge;
        have h_take_eq_filter : ∀ {L : List ℝ} {k : ℕ} (_ : k ≤ L.length), (List.Sorted (· ≤ ·) L) → (∀ j, j < k → L[j]! < y) → (∀ j, k ≤ j → j < L.length → y ≤ L[j]!) → ∀ {i : ℕ}, i ≤ k → List.take i L = List.filter (fun x => x < y) (List.take i L) := by
          intros L k hk_le_L h_sorted h_k_lt h_k_ge i hi_le_k;
          induction' i with i ih;
          · norm_num;
          · rw [ List.take_succ ];
            rw [ List.filter_append, ih ( Nat.le_of_succ_le hi_le_k ) ];
            by_cases hi : i < L.length <;> simp_all
            grind;
        specialize @h_take_eq_filter L k hk_le_L h_sorted h_k_lt h_k_ge k le_rfl;
        rw [ h_take_eq_filter, ← List.take_append_drop k L, List.filter_append ];
        simp
        intro a ha; rw [ List.mem_iff_get ] at ha; obtain ⟨ j, hj ⟩ := ha; aesop;
      specialize @h_take_eq_filter L k ( Nat.le_of_lt hk_lt ) h_sorted;
      simp_all only [List.get_eq_getElem, ge_iff_le, List.getElem!_eq_getElem?_getD, getElem!_pos]
      exact h_take_eq_filter
        ( fun j hj => by simpa [hj.trans_le (Nat.le_of_lt hk_lt)] using h_prev j hj )
        ( fun j hj₁ hj₂ => by simpa [ List.getElem!_eq_getElem?_getD, hj₂ ] using by exact le_trans h_k ( by exact monotone_iff_forall_lt.mpr ( fun i j hij => by exact List.pairwise_iff_get.mp h_sorted i j hij ) hj₁ ) )

/-
The list of values of the strictified strategy strictly less than y is equal to the deduplicated list of original values strictly less than y.
-/
lemma strictifyStrategy_values_lt_eq_dedup_filter {s : Strategy} {N : ℕ} {y : ℝ}
    (h_sorted : Monotone s.x)
    (h_y : y ≤ s.x N)
    (hy1 : 1 ≤ y) :
    let s' := strictifyStrategy s N
    let L := (List.range (N + 1)).map s.x
    let k := hitIndex s' ⟨y, hy1⟩
    (List.range k).map s'.x = L.dedup.filter (fun x => x < y) := by
      have h_m_ge_y' : (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩) < ((List.range (N + 1)).map s.x).dedup.length := by
        have h_m_ge_y' : (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩) ≤ (List.map s.x (List.range (N + 1))).dedup.length - 1 := by
          have h_m_ge_y' : ∃ n, n < ((List.map s.x (List.range (N + 1))).dedup.length) ∧ (strictifyStrategy s N).x n ≥ y := by
            have h_m_ge_y' : ∃ n, n < ((List.map s.x (List.range (N + 1))).dedup.length) ∧ ((List.map s.x (List.range (N + 1))).dedup)[n]! ≥ y := by
              have h_m_ge_y' : s.x N ∈ (List.map s.x (List.range (N + 1))).dedup := by
                simp +decide [ List.range_succ ];
              obtain ⟨ n, hn ⟩ := List.mem_iff_get.mp h_m_ge_y';
              use n.val;
              aesop;
            unfold strictifyStrategy; aesop;
          exact Nat.le_sub_one_of_lt ( h_m_ge_y'.choose_spec.1.trans_le' ( Nat.find_min' _ h_m_ge_y'.choose_spec.2 ) );
        exact lt_of_le_of_lt h_m_ge_y' ( Nat.pred_lt ( by aesop ) );
      have h_take_filter : (List.take (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩) ((List.range (N + 1)).map s.x).dedup) = (List.filter (fun x => x < y) ((List.range (N + 1)).map s.x).dedup) := by
        apply_rules [ List_take_eq_filter_lt_of_sorted ];
        · have h_sorted : List.Sorted (· ≤ ·) (List.map s.x (List.range (N + 1))) := by
            have h_sorted : List.Pairwise (· ≤ ·) (List.map s.x (List.range (N + 1))) := by
              have h_sorted : ∀ i j : ℕ, i < j → s.x i ≤ s.x j := by
                exact fun i j hij => h_sorted hij.le
              rw [ List.pairwise_iff_get ];
              aesop;
            exact h_sorted;
          exact h_sorted.sublist ( List.dedup_sublist _ );
        · have h_take_filter : (List.map (strictifyStrategy s N).x (List.range (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩ + 1))).getLast (by
          aesop) ≥ y := by
            all_goals generalize_proofs at *;
            have h_take_filter : (List.map (strictifyStrategy s N).x (List.range (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩ + 1))).getLast ‹_› = (strictifyStrategy s N).x (hitIndex (strictifyStrategy s N) ⟨y, hy1⟩) := by
              simp +decide [ List.range_succ ];
            exact h_take_filter.symm ▸ Nat.find_spec ( _ : ∃ n, y ≤ ( strictifyStrategy s N ).x n )
          generalize_proofs at *;
          have h_take_filter : ∀ k < ((List.range (N + 1)).map s.x).dedup.length, (((List.range (N + 1)).map s.x).dedup)[k]! = (strictifyStrategy s N).x k := by
            unfold strictifyStrategy; aesop;
          aesop;
        · intro j hj
          have h_lt_y : (strictifyStrategy s N).x j < y := by
            exact lt_of_not_ge fun h => hj.not_ge <| Nat.le_of_not_lt fun h' => by have := Nat.find_min ( show ∃ n, y ≤ ( strictifyStrategy s N ).x n from ⟨ _, h ⟩ ) h'; linarith;
          convert h_lt_y using 1
          generalize_proofs at *;
          unfold strictifyStrategy; aesop;
      convert h_take_filter using 1;
      have h_take_filter_eq : ∀ k < ((List.range (N + 1)).map s.x).dedup.length, (List.map (strictifyStrategy s N).x (List.range k)) = (List.take k ((List.range (N + 1)).map s.x).dedup) := by
        intro k hk; induction' k with k ih <;> simp_all +decide [ List.range_succ ] ;
        rw [ ih ( Nat.lt_of_succ_lt hk ), List.take_succ ];
        -- Since the strictifyStrategy's x function is defined as the deduplicated list's elements, the (k+1)-th element of the strictifyStrategy's x function is the same as the (k+1)-th element of the deduplicated list.
        have h_eq : ∀ k < ((List.range (N + 1)).map s.x).dedup.length, (strictifyStrategy s N).x k = (((List.range (N + 1)).map s.x).dedup)[k]! := by
          unfold strictifyStrategy; aesop;
        simp_all +decide [ List.range_succ ];
        rw [ h_eq k ( Nat.lt_of_succ_lt hk ), List.getElem?_eq_getElem ] ; aesop;
      exact h_take_filter_eq _ h_m_ge_y'

/-
The first k values of the strictified strategy are exactly the first k values of the deduplicated list of the original strategy's values.
-/
lemma strictifyStrategy_eq_dedup_take {s : Strategy} {N : ℕ} {k : ℕ}
    (hk : k ≤ ((List.range (N + 1)).map s.x).dedup.length) :
    (List.range k).map (strictifyStrategy s N).x = ((List.range (N + 1)).map s.x).dedup.take k := by
      have h_perm : List.Perm (List.map (strictifyStrategy s N).x (List.range ((List.map s.x (List.range (N + 1))).dedup.length))) (List.map s.x (List.range (N + 1)) |>.dedup) := by
        have h_perm : List.Perm (List.map (fun i => (strictifyStrategy s N).x i) (List.range ((List.map s.x (List.range (N + 1))).dedup.length))) (List.map (fun i => (List.map s.x (List.range (N + 1))).dedup[i]!) (List.range ((List.map s.x (List.range (N + 1))).dedup.length))) := by
          rw [ List.map_congr_left ];
          unfold strictifyStrategy; aesop;
        convert h_perm using 1;
        refine' List.ext_get _ _ <;> aesop;
      have h_perm_sorted : List.Sorted (· ≤ ·) (List.map (strictifyStrategy s N).x (List.range ((List.map s.x (List.range (N + 1))).dedup.length))) := by
        have h_perm_sorted : StrictMono (strictifyStrategy s N).x := by
          exact strictifyStrategy_strictMono;
        rw [ List.Sorted ];
        rw [ List.pairwise_map ];
        rw [ List.pairwise_iff_get ];
        exact fun i j hij => h_perm_sorted.monotone <| by simpa using hij.le;
      have h_perm_sorted : List.Sorted (· ≤ ·) (List.map s.x (List.range (N + 1)) |>.dedup) := by
        have h_perm_sorted : List.Sorted (· ≤ ·) (List.map s.x (List.range (N + 1))) := by
          have h_perm_sorted : Monotone (fun n => s.x n) := by
            exact monotone_nat_of_le_succ fun n => s.mono n.le_succ;
          rw [ List.Sorted ];
          rw [ List.pairwise_map ];
          rw [ List.pairwise_iff_get ];
          exact fun i j hij => h_perm_sorted <| by simpa using hij.le;
        exact h_perm_sorted.sublist ( List.dedup_sublist _ );
      have h_perm_sorted : List.map (strictifyStrategy s N).x (List.range ((List.map s.x (List.range (N + 1))).dedup.length)) = List.dedup (List.map s.x (List.range (N + 1))) := by
        exact List.eq_of_perm_of_sorted
          (fun a b _ _ hab hba => le_antisymm hab hba) ‹_› ‹_› h_perm;
      rw [ ← h_perm_sorted, ← List.take_append_drop k ( List.range ( List.map s.x ( List.range ( N + 1 ) ) |> List.dedup |> List.length ) ), List.map_append ] ; aesop;

/-
The list of values of a sorted strategy strictly less than y (up to N) is equal to the filtered list of values up to N.
-/
lemma truncateStrategy_values_lt_eq_filter {s : Strategy} {N : ℕ} {y : ℝ}
    (h_sorted : Monotone s.x)
    (hy : 1 ≤ y)
    (h_hit : hitIndex s ⟨y, hy⟩ ≤ N) :
    let L := (List.range (N + 1)).map s.x
    let k := hitIndex s ⟨y, hy⟩
    (List.range k).map s.x = L.filter (· < y) := by
      have h_take_eq_filter : List.take (hitIndex s ⟨y, hy⟩) ((List.range (N + 1)).map s.x) = ((List.range (N + 1)).map s.x).filter (· < y) := by
        apply List_take_eq_filter_lt_of_sorted;
        all_goals norm_num;
        · exact List.pairwise_iff_get.mpr ( by simpa using fun i j hij => h_sorted hij.le );
        · exact Nat.find_spec ( s.hits hy );
        · exact fun j hj => lt_of_not_ge fun h => hj.not_ge ( Nat.le_of_not_lt fun h' => by have := Nat.find_min ( s.hits hy ) h'; aesop );
        · linarith;
      convert h_take_eq_filter using 1;
      rw [ ← List.map_take ];
      grind

/-
The hit index of the strict strategy for a target y <= B is strictly less than the length of the deduplicated list.
-/
lemma strictifyStrategy_hitIndex_lt_length {s : Strategy} {B : ℝ} (hB : 1 ≤ B) {y : {y : ℝ // 1 ≤ y ∧ y ≤ B}} :
    hitIndex (strictStrategy s B hB) ⟨y.1, y.2.1⟩ < ((List.range (truncateIndex s B hB + 1)).map (truncateStrategyAux s B hB).x).dedup.length := by
      have h_hit_lt_dedup_length : (strictStrategy s B hB).x (hitIndex (strictStrategy s B hB) ⟨y.1, y.2.1⟩) ≤ (truncateStrategyAux s B hB).x (truncateIndex s B hB) := by
        rw [ strictifyStrategy_hit_value_eq ];
        refine' ( truncateStrategyAux s B hB ).mono _;
        have h_hit_le_truncateIndex : hitIndex (truncateStrategyAux s B hB) ⟨y, y.2.1⟩ ≤ hitIndex s ⟨y, y.2.1⟩ := by
          rw [ hitIndex_truncateStrategyAux_eq ];
        exact le_trans h_hit_le_truncateIndex ( hitIndex_le_truncateIndex )
      generalize_proofs at *; (
      have h_hit_lt_dedup_length : ∀ k, k ≥ (List.map (truncateStrategyAux s B hB).x (List.range (truncateIndex s B hB + 1))).dedup.length → (strictStrategy s B hB).x k > (truncateStrategyAux s B hB).x (truncateIndex s B hB) := by
        -- By definition of strictStrategy, if k is greater than or equal to the length of the deduplicated list, then strictStrategy s B hB).x k is defined as the last element of the deduplicated list plus (k - (length - 1)).
        intros k hk
        have h_def : (strictStrategy s B hB).x k = (List.map (truncateStrategyAux s B hB).x (List.range (truncateIndex s B hB + 1))).dedup.getLast (by
        aesop) + (k - ((List.map (truncateStrategyAux s B hB).x (List.range (truncateIndex s B hB + 1))).dedup.length - 1)) := by
          unfold strictStrategy
          generalize_proofs at *; (
          unfold strictifyStrategy; aesop;)
        generalize_proofs at *; (
        have h_last_eq : (List.map (truncateStrategyAux s B hB).x (List.range (truncateIndex s B hB + 1))).dedup.getLast ‹_› = (truncateStrategyAux s B hB).x (truncateIndex s B hB) := by
          convert List_dedup_getLast_eq_getLast_of_sorted _ _ using 1
          generalize_proofs at *; (
          simp +decide [ List.range_succ ]);
          · have h_sorted : Monotone (truncateStrategyAux s B hB).x := by
              exact monotone_nat_of_le_succ fun n => by simpa using ( truncateStrategyAux s B hB ).mono n.le_succ;
            generalize_proofs at *; (
            exact List.pairwise_iff_get.mpr ( by intros i j hij; simpa using h_sorted hij.le ));
          · aesop
        generalize_proofs at *; (
        linarith [ show ( k : ℝ ) ≥ ( List.map ( truncateStrategyAux s B hB ).x ( List.range ( truncateIndex s B hB + 1 ) ) ).dedup.length by exact_mod_cast hk, show ( List.map ( truncateStrategyAux s B hB ).x ( List.range ( truncateIndex s B hB + 1 ) ) ).dedup.length ≥ 1 by exact List.length_pos_iff.mpr ‹_› ]))
      generalize_proofs at *; (
      exact lt_of_not_ge fun h => not_le_of_gt ( h_hit_lt_dedup_length _ h ) ‹_›))

/-
The sum of the values of the strict strategy strictly less than y is less than or equal to the sum of the values of the truncated strategy strictly less than y.
-/
lemma strictStrategy_sum_lt_le_sum_trunc_lt {s : Strategy} {B : ℝ} (hB : 1 ≤ B) {y : {y : ℝ // 1 ≤ y ∧ y ≤ B}} :
    ((List.range (hitIndex (strictStrategy s B hB) ⟨y.1, y.2.1⟩)).map (strictStrategy s B hB).x).sum ≤
    ((List.range (hitIndex (truncateStrategyAux s B hB) ⟨y.1, y.2.1⟩)).map (truncateStrategyAux s B hB).x).sum := by
      have h_filter_eq : let L := (List.range (truncateIndex s B hB + 1)).map (truncateStrategyAux s B hB).x; let k := hitIndex (strictStrategy s B hB) ⟨y.1, y.2.1⟩; (List.range k).map (strictStrategy s B hB).x = L.dedup.filter (fun x => x < y.1) := by
        apply strictifyStrategy_values_lt_eq_dedup_filter;
        · exact (truncateStrategyAux s B hB).mono;
        · exact y.2.2.trans ( by rw [ truncateStrategyAux_at_N_eq_B hB ] );
      have h_filter_eq_trunc : let L := (List.range (truncateIndex s B hB + 1)).map (truncateStrategyAux s B hB).x; let k := hitIndex (truncateStrategyAux s B hB) ⟨y.1, y.2.1⟩; (List.range k).map (truncateStrategyAux s B hB).x = L.filter (fun x => x < y.1) := by
        apply truncateStrategy_values_lt_eq_filter;
        · exact (truncateStrategyAux s B hB).mono;
        · refine' Nat.find_min' _ _;
          exact le_trans y.2.2 ( truncateStrategyAux_at_N_eq_B hB |> fun h => h.symm ▸ le_rfl );
      simp_all
      apply List_dedup_filter_sum_le;
      intro x hx; rw [ List.mem_map ] at hx; obtain ⟨ k, _, rfl ⟩ := hx; exact ( truncateStrategyAux s B hB ).nonneg k;

/-
The strict strategy derived from s has a worst-case score no larger than s.
-/
theorem strictStrategy_score_le {s : Strategy} {B : ℝ} (hB : 1 ≤ B) :
    boundedWorstCaseScore (strictStrategy s B hB) B ≤ boundedWorstCaseScore s B := by
      -- The worst-case score of the strict strategy is bounded by the worst-case score of the truncated strategy.
      have h_strict_le_trunc : boundedWorstCaseScore (strictStrategy s B hB) B ≤ boundedWorstCaseScore (truncateStrategyAux s B hB) B := by
        rw [ boundedWorstCaseScore, boundedWorstCaseScore ];
        apply iSup_le;
        -- For any target y in [1, B], the score of the strict strategy against y is less than or equal to the score of the truncated strategy against y.
        have h_score_le : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, boundedScore (strictStrategy s B hB) B y ≤ boundedScore (truncateStrategyAux s B hB) B y := by
          -- By definition of boundedScore, we know that the score of the strict strategy is less than or equal to the score of the truncated strategy.
          intros y
          simp [boundedScore];
          unfold score;
          unfold partialSum;
          gcongr;
          · exact le_trans zero_le_one y.2.1;
          · rw [ Finset.sum_range_succ, Finset.sum_range_succ ];
            refine' add_le_add _ _;
            · convert strictStrategy_sum_lt_le_sum_trunc_lt hB using 1;
            · rw [ strictifyStrategy_hit_value_eq ];
        exact fun y => le_iSup_of_le y ( h_score_le y );
      exact h_strict_le_trunc.trans ( truncateStrategyAux_score_le hB )

/-
The value of the bounded game is exactly the first guess of the optimal strategy.
-/
theorem boundedGameValue_eq_firstGuess {B : ℝ} (hB : 1 < B) :
    boundedGameValue B = ENNReal.ofReal (firstGuess B) := by
      -- By definition of `boundedGameValue`, we know that it is the infimum of the scores of all strategies.
      have h_inf : ∀ s : Strategy, boundedWorstCaseScore s B ≥ ENNReal.ofReal (firstGuess B) := by
        intro s
        set s' := strictStrategy s B hB.le;
        refine' le_trans _ ( strictStrategy_score_le _ );
        apply_rules [ boundedWorstCaseScore_ge_firstGuess_strict ];
        refine strictStrategy_strictMono ?_;
        rotate_left;
        exact Exists.choose_spec ( strictStrategy_ends_at_B_valid hB.le ) |>.2;
        exact Exists.choose_spec ( strictStrategy_ends_at_B_valid hB.le ) |>.1;
      refine' le_antisymm _ _;
      · exact boundedGameValue_le_firstGuess hB;
      · exact le_csInf ⟨ _, ⟨ optimalStrategy B, rfl ⟩ ⟩ fun x hx => hx.choose_spec ▸ h_inf _

/-
The optimal strategy is indeed optimal.
-/
theorem optimalStrategy_isOptimal (B : ℝ) (hB : 1 < B) :
    IsOptimalBounded B (optimalStrategy B) := by
      -- We've proved that the worst-case score of the optimal strategy is exactly the first guess.
      have h_optimal_score : boundedWorstCaseScore (optimalStrategy B) B = ENNReal.ofReal (firstGuess B) := by
        exact optimalStrategy_boundedScore B hB;
      exact h_optimal_score.trans ( boundedGameValue_eq_firstGuess hB ▸ rfl )

/-
If 1 <= B <= 2, then V(B) = B.
-/
theorem value_B_le_2 {B : ℝ} (hB1 : 1 ≤ B) (hB2 : B ≤ 2) :
    boundedGameValue B = ENNReal.ofReal B := by
      by_cases hB3 : B = 1 <;> simp_all +decide [ boundedGameValue ];
      · refine' le_antisymm _ _ <;> norm_num [ boundedWorstCaseScore ];
        · refine' le_trans ( ciInf_le _ ( optimalStrategy 1 ) ) _ <;> norm_num [ optimalStrategy ];
          intro a ha₁ ha₂; rw [ boundedScore ] ; norm_num [ ha₁, ha₂ ] ;
          rw [ score ] ; norm_num [ ha₁, ha₂ ];
          rw [ show hitIndex doublingStrategy ⟨ a, by linarith ⟩ = 0 from _ ];
          · norm_num [ partialSum ];
            norm_num [ show a = 1 by linarith, doublingStrategy ];
          · unfold hitIndex; aesop;
        · intro s
          refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num ⟩ )
          · norm_num [boundedScore]
            · simp [score]
              exact le_trans s.one_le
                (Finset.single_le_sum (fun a _ => s.nonneg a)
                  (Finset.mem_range.mpr (Nat.succ_pos _)))
          · bound
      · have h_eq : boundedGameValue B = ENNReal.ofReal (firstGuess B) := by
          exact boundedGameValue_eq_firstGuess ( lt_of_le_of_ne hB1 ( Ne.symm hB3 ) );
        -- Since $nSteps B = 1$ for $1 < B \leq 2$, we can apply the lemma firstGuess_eq_B_of_n_eq_one.
        have h_n_eq_one : nSteps B = 1 := by
          exact nSteps_eq_one ( lt_of_le_of_ne hB1 ( Ne.symm hB3 ) ) hB2;
        exact h_eq.trans ( by rw [ firstGuess_eq_B_of_n_eq_one ( by linarith [ show B > 1 from lt_of_le_of_ne hB1 ( Ne.symm hB3 ) ] ) h_n_eq_one ] )

/-
If 2 < B <= 2+sqrt(5), then V(B) = (1+sqrt(1+4B))/2.
-/
theorem value_two_step {B : ℝ} (hB1 : 2 < B) (hB2 : B ≤ 2 + Real.sqrt 5) :
    boundedGameValue B = ENNReal.ofReal ((1 + Real.sqrt (1 + 4 * B)) / 2) := by
      rw [ boundedGameValue_eq_firstGuess ];
      · rw [ firstGuess_eq_root_of_n_eq_two ] <;> try linarith;
        exact nSteps_eq_two hB1 hB2;
      · linarith

/-
If 2+sqrt(5) < B <= 9, then V(B) satisfies R^2(R-2)=B with R in ((3+sqrt 5)/2, 3].
-/
theorem value_three_step {B : ℝ} (hB1 : 2 + Real.sqrt 5 < B) (hB2 : B ≤ 9) :
    ∃ R, boundedGameValue B = ENNReal.ofReal R ∧
    R ^ 2 * (R - 2) = B ∧
    (3 + Real.sqrt 5) / 2 < R ∧ R ≤ 3 := by
      obtain ⟨R, hR⟩ : ∃ R, boundedGameValue B = ENNReal.ofReal R ∧ R^2*(R - 2) = B := by
        have h_R : boundedGameValue B = ENNReal.ofReal (firstGuess B) := by
          exact boundedGameValue_eq_firstGuess ( by linarith [ Real.sqrt_nonneg 5 ] );
        use firstGuess B;
        exact ⟨ h_R, firstGuess_eq_root_of_n_eq_three ( by linarith [ Real.sqrt_nonneg 5 ] ) ( nSteps_eq_three ( by linarith [ Real.sqrt_nonneg 5 ] ) hB2 ) ⟩;
      refine' ⟨ R, hR.1, hR.2, _, _ ⟩;
      · -- Since $B > 2 + \sqrt{5}$, we have $f((3 + \sqrt{5})/2) = 2 + \sqrt{5} < B$.
        have h_f_lt_B : ((3 + Real.sqrt 5) / 2) ^ 2 * (((3 + Real.sqrt 5) / 2) - 2) < B := by
          nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        contrapose! h_f_lt_B;
        exact hR.2 ▸ mul_le_mul ( pow_le_pow_left₀ ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) h_f_lt_B 2 ) ( sub_le_sub_right h_f_lt_B _ ) ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by positivity );
      · nlinarith [ sq_nonneg ( R - 3 ) ]

/-
The sequence of breakpoints B_n tends to infinity.
-/
theorem stepBreakpoint_tendsto_atTop : Tendsto stepBreakpoint atTop atTop := by
  -- We'll use the fact that $2 \cos(\pi/(n+3)) \geq \sqrt{3}$ for $n \geq 3$.
  have h_cos_bound : ∀ n ≥ 3, 2 * Real.cos (Real.pi / (n + 3)) ≥ Real.sqrt 3 := by
    intro n hn; nlinarith [ show Real.cos ( Real.pi / ( n + 3 ) ) ≥ Real.sqrt 3 / 2 by rw [ ← Real.cos_pi_div_six ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n + 3 ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n + 3 ) ≠ 0 ) ] ), Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;
  -- Since $\sqrt{3} > 1$, we have $(\sqrt{3})^{n+1} \to \infty$ as $n \to \infty$.
  have h_sqrt3_pow_inf : Filter.Tendsto (fun n : ℕ => (Real.sqrt 3) ^ (n + 1)) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1;
  refine' Filter.tendsto_atTop_mono' _ _ h_sqrt3_pow_inf;
  filter_upwards [ Filter.eventually_ge_atTop 3 ] with n hn using pow_le_pow_left₀ ( by positivity ) ( h_cos_bound n ( mod_cast hn ) ) _ |> le_trans <| by norm_cast;

/-
The number of steps n(B) tends to infinity as B tends to infinity.
-/
theorem nSteps_limit : Tendsto nSteps atTop atTop := by
  exact nSteps_tendsto_atTop

/-
The growth base B^(1/n(B)) tends to 2.
-/
theorem growthBase_limit : Tendsto growthBase atTop (𝓝 2) := by
  exact growthBase_tendsto_two_proof

/-
The first guess x(B) tends to 4.
-/
theorem firstGuess_limit : Tendsto firstGuess atTop (𝓝 4) := by
  -- Apply the fact that the firstGuess function tends to 4 as B approaches infinity.
  have h_tendsto : Filter.Tendsto (fun B : ℝ => firstGuess B) Filter.atTop (nhds 4) := by
    have := firstGuess_tendsto_four_proof
    exact this;
  exact h_tendsto

end MO420333
