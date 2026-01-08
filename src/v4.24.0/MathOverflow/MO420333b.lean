import Mathlib

set_option linter.style.longLine false

set_option maxHeartbeats 0

open Classical
open scoped BigOperators

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
    rw [ h_rec, ih _ <| Nat.lt_succ_self _, ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ] ; ring_nf;
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
lemma tightPoly_trig_strictAntiOn {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (fun θ => (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ))
      (Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2))) := by
        have h_deriv_neg : ∀ θ ∈ Set.Ioo (Real.pi / (n + 3)) (Real.pi / (n + 2)), deriv (fun θ => (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ)) θ < 0 := by
          have h_deriv_neg : ∀ θ ∈ Set.Ioo (Real.pi / (n + 3)) (Real.pi / (n + 2)), deriv (fun θ => (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ)) θ = (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ) * (-n * Real.tan θ + (n + 1) * Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) - Real.cos θ / Real.sin θ) := by
            intro θ hθ;
            norm_num [ Real.tan_eq_sin_div_cos, mul_comm, Real.differentiableAt_sin, Real.differentiableAt_cos, ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( show 0 < θ by exact lt_trans ( by positivity ) hθ.1 ) ( by exact hθ.2.trans_le ( div_le_self Real.pi_pos.le ( by linarith ) ) ) ) ] ; ring_nf;
            by_cases hsin : Real.sin θ = 0 <;> by_cases hcos : Real.cos θ = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
            · exact absurd hcos ( ne_of_gt ( Real.cos_pos_of_mem_Ioo ⟨ by rw [ div_lt_iff₀ ( by positivity ) ] at hθ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ lt_div_iff₀ ( by positivity ) ] at hθ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) );
            · rcases n <;> simp_all +decide [ pow_succ', mul_assoc ] ; ring_nf;
              by_cases hsin' : Real.sin ( ( ↑‹ℕ› : ℝ ) * θ + θ * 2 ) = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
              · rw [ Real.sin_eq_zero_iff ] at hsin';
                obtain ⟨ k, hk ⟩ := hsin'; rw [ div_lt_iff₀ ( by positivity ), lt_div_iff₀ ( by positivity ) ] at hθ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ] ;
              · ring;
          intros θ hθ
          rw [h_deriv_neg θ hθ]
          have h_tan_pos : 0 < Real.tan θ := by
            exact Real.tan_pos_of_pos_of_lt_pi_div_two ( lt_trans ( by positivity ) hθ.1 ) ( lt_of_lt_of_le hθ.2 ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) )
          have h_cot_pos : 0 < Real.cos θ / Real.sin θ := by
            exact div_pos ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos, hθ.1, show ( Real.pi : ℝ ) / ( n + 3 ) > 0 by positivity ], by linarith [ Real.pi_pos, hθ.2, show ( Real.pi : ℝ ) / ( n + 2 ) < Real.pi / 2 by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ] ⟩ ) ( Real.sin_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos, hθ.1, show ( Real.pi : ℝ ) / ( n + 3 ) > 0 by positivity ], by linarith [ Real.pi_pos, hθ.2, show ( Real.pi : ℝ ) / ( n + 2 ) < Real.pi by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ] ⟩ )
          have h_cot_neg : Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) < 0 := by
            refine' div_neg_of_neg_of_pos ( Real.cos_neg_of_pi_div_two_lt_of_lt _ _ ) ( Real.sin_pos_of_pos_of_lt_pi _ _ );
            · rw [ Set.mem_Ioo ] at hθ;
              rw [ div_lt_iff₀ ] at hθ <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ];
            · nlinarith [ hθ.1, hθ.2, Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
            · exact mul_pos ( by positivity ) ( lt_trans ( by positivity ) hθ.1 );
            · nlinarith [ hθ.1, hθ.2, Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ]
          have h_term_neg : -(n : ℝ) * Real.tan θ + (n + 1) * Real.cos ((n + 1) * θ) / Real.sin ((n + 1) * θ) - Real.cos θ / Real.sin θ < 0 := by
            ring_nf at *; nlinarith;
          exact mul_neg_of_pos_of_neg (mul_pos (pow_pos (mul_pos zero_lt_two (Real.cos_pos_of_mem_Ioo ⟨by
          linarith [ Real.pi_pos, hθ.1, div_nonneg Real.pi_pos.le ( by positivity : 0 ≤ ( n : ℝ ) + 3 ) ], by
            exact hθ.2.trans_le ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] )⟩)) _) (div_pos (Real.sin_pos_of_mem_Ioo ⟨by
          exact mul_pos ( by positivity ) ( lt_trans ( by positivity ) hθ.1 ), by
            nlinarith [ hθ.1, hθ.2, Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ]⟩) (Real.sin_pos_of_mem_Ioo ⟨by
          exact lt_trans ( by positivity ) hθ.1, by
            exact hθ.2.trans_le ( div_le_self Real.pi_pos.le ( by linarith ) )⟩))) h_term_neg;
        intros x hx y hy hxy;
        have := exists_deriv_eq_slope ( f := fun θ => ( 2 * Real.cos θ ) ^ n * ( Real.sin ( ( n + 1 ) * θ ) / Real.sin θ ) ) hxy;
        contrapose! this;
        norm_num +zetaDelta at *;
        exact ⟨ ContinuousOn.mul ( ContinuousOn.pow ( continuousOn_const.mul ( Real.continuousOn_cos ) ) _ ) ( ContinuousOn.div ( Continuous.continuousOn ( Real.continuous_sin.comp ( by continuity ) ) ) ( Real.continuousOn_sin ) fun θ hθ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by linarith [ Real.pi_pos, hθ.1, show 0 < θ from by linarith [ Real.pi_pos, hθ.1, show 0 < Real.pi / ( n + 3 ) from by positivity ] ] ) ( by linarith [ Real.pi_pos, hθ.2, show θ < Real.pi from by linarith [ Real.pi_pos, hθ.2, show Real.pi / ( n + 2 ) < Real.pi from by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ] ] ) ) ), fun θ hθ => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( DifferentiableAt.pow ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_cos ) ) _ ) ( DifferentiableAt.div ( DifferentiableAt.sin ( differentiableAt_id.const_mul _ ) ) ( Real.differentiableAt_sin ) ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by linarith [ Real.pi_pos, hθ.1, show 0 < θ from by linarith [ Real.pi_pos, hθ.1, show 0 < Real.pi / ( n + 3 ) from by positivity ] ] ) ( by linarith [ Real.pi_pos, hθ.2, show θ < Real.pi from by linarith [ Real.pi_pos, hθ.2, show Real.pi / ( n + 2 ) < Real.pi from by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ] ] ) ) ) ) ), fun θ hθ₁ hθ₂ => by rw [ eq_div_iff ] <;> nlinarith [ h_deriv_neg θ ( by linarith ) ( by linarith ) ] ⟩

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
      -- Let's choose any two points $y_1$ and $y_2$ in the interval $[R_{n,lower}, R_{n,upper}]$ with $y_1 < y_2$.
      intro y1 hy1 y2 hy2 hlt;
      -- Since $g$ is strictly decreasing, we have $θ1 > θ2$.
      obtain ⟨θ1, hθ1⟩ : ∃ θ1 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), y1 = 4 * (Real.cos θ1) ^ 2 := by
        -- Since $y1 \in [R_{n,lower}, R_{n,upper}]$, we can find $\theta_1 \in [\pi/(n+3), \pi/(n+2)]$ such that $y1 = 4 \cos^2 \theta_1$.
        have h_cos_sq : ∃ θ1 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * (Real.cos θ1) ^ 2 = y1 := by
          apply_rules [ intermediate_value_Icc' ] <;> norm_num [ ratioLower, ratioUpper ] at *;
          · gcongr ; linarith;
          · exact Continuous.continuousOn ( by continuity );
          · tauto;
        aesop
      obtain ⟨θ2, hθ2⟩ : ∃ θ2 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), y2 = 4 * (Real.cos θ2) ^ 2 := by
        -- Since $y2$ is in the interval $[R_{n,lower}, R_{n,upper}]$, we can find $\theta2$ in $[\pi/(n+3), \pi/(n+2)]$ such that $y2 = 4 \cos^2 \theta2$.
        have hθ2_exists : ∃ θ2 ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), Real.cos θ2 ^ 2 = y2 / 4 := by
          apply_rules [ intermediate_value_Icc' ];
          · grind;
          · exact Continuous.continuousOn ( Real.continuous_cos.pow 2 );
          · constructor <;> norm_num [ ratioLower, ratioUpper ] at * <;> linarith;
        exact ⟨ hθ2_exists.choose, hθ2_exists.choose_spec.1, by linarith [ hθ2_exists.choose_spec.2 ] ⟩
      have hθ1θ2 : θ1 > θ2 := by
        contrapose! hlt;
        exact hθ2.2.symm ▸ hθ1.2.symm ▸ mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.2 ] ⟩ ) ( Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ1.1.1 ] ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ), hθ2.1.2 ] ) hlt ) 2 ) zero_le_four;
      -- Since $f$ is strictly decreasing, we have $f(θ1) < f(θ2)$.
      have hfθ1θ2 : (2 * Real.cos θ1) ^ n * (Real.sin ((n + 1) * θ1) / Real.sin θ1) < (2 * Real.cos θ2) ^ n * (Real.sin ((n + 1) * θ2) / Real.sin θ2) := by
        have := tightPoly_trig_strictAntiOn hn;
        exact this hθ2.1 hθ1.1 hθ1θ2;
      convert hfθ1θ2 using 1;
      · rw [ hθ1.2, tightPoly_eq_trig ] ; aesop;
        exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ1.1.1 ) ( lt_of_le_of_lt hθ1.1.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) );
      · rw [ hθ2.2, tightPoly_eq_trig ];
        · norm_cast;
        · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by exact lt_of_lt_of_le ( by positivity ) hθ2.1.1 ) ( by exact lt_of_le_of_lt hθ2.1.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) )

/-- In the `n`-step regime, there is a unique `R` in the bracket
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
  ·
    let n : ℕ := nSteps B
    have hn : 1 ≤ n := (nSteps_spec (B := B) hB).1
    have hBn : InStepRange B n := (nSteps_spec (B := B) hB).2
    exact Classical.choose (existsUnique_ratio_of_inStepRange (B := B) (n := n) hn hBn)
  ·
    exact 1

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
      · rintro ⟨ i, hi₁, hi₂, hi₃ ⟩ ; exact ⟨ by split_ifs at hi₁ <;> linarith [ show 1 ≤ s.x 0 from s.one_le, show s.x ( i - 1 ) ≥ 1 from Nat.recOn ( i - 1 ) ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ], by linarith [ show s.x i ≤ s.x n from s.mono ( Nat.le_of_lt_succ hi₂ ) ] ⟩ ;
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
          refine' le_trans _ ( le_iSup₂_of_le 0 ( Nat.zero_lt_succ _ ) _ ) <;> norm_num [ hy1 ];
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
        exact ENNReal.ofReal_le_ofReal ( by exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun a _ => s.nonneg a ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ) );
        linarith [ s.one_le, h_strict.monotone ( Nat.zero_le n ) ];
      · -- Consider the sequence $y_m \downarrow x_{i-1}$ with $y_m \in (x_{i-1}, x_i]$.
        obtain ⟨y_m, hy_m⟩ : ∃ y_m : ℕ → ℝ, (∀ m, y_m m ∈ Set.Ioc (s.x (i - 1)) (s.x i)) ∧ Filter.Tendsto y_m Filter.atTop (nhds (s.x (i - 1))) := by
          use fun m => s.x (i - 1) + (s.x i - s.x (i - 1)) / (m + 2);
          exact ⟨ fun m => ⟨ lt_add_of_pos_right _ <| div_pos ( sub_pos.mpr <| h_strict <| Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ) <| by positivity, by rw [ add_div', div_le_iff₀ ] <;> nlinarith [ h_strict <| Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ] ⟩, by simpa using tendsto_const_nhds.add <| tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 ⟩;
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
        exact le_trans ( hy_m.1 m |>.2 ) ( h_n ▸ h_strict.monotone ( Nat.le_of_lt_succ hi ) )

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
        gcongr ; linarith [ s.nonneg k, s.nonneg ( k + 1 ) ];
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
        · by_cases hk0 : k = 0 <;> simp_all
          · exact ⟨ 0, Nat.zero_lt_succ _, Or.inl rfl, le_rfl ⟩;
          · exact ⟨ k, le_rfl, hk, by cases lt_or_gt_of_ne h_eq <;> [ exact Or.inr ‹_› ; exact Or.inl <| by linarith! [ s.mono <| Nat.sub_le k 1 ] ], le_rfl ⟩

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
        · exact OrderTop.bddAbove (Set.range fun y => boundedScore s B y)

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
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
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
      · rw [ Real.sin_two_mul ] ; ring;
        aesop;
      · -- Applying the recurrence relation for tightPoly, we have:
        have h_rec : tightPoly (n + 2) (4 * Real.cos θ ^ 2) = 4 * Real.cos θ ^ 2 * (tightPoly (n + 1) (4 * Real.cos θ ^ 2) - tightPoly n (4 * Real.cos θ ^ 2)) := by
          exact?;
        rw [ h_rec, ih _ <| Nat.lt_succ_self _, ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ];
        norm_num [ add_mul, Real.sin_add, Real.cos_add, pow_succ' ] ; ring;
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
        split_ifs <;> simp_all +decide [ tightPoly_diff_sign ];
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
      · exact?;
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
        exact?
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
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.sub_sub ];
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
      exact?

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
The value of the 0-th breakpoint B_0 is 1.
-/
lemma stepBreakpoint_zero : stepBreakpoint 0 = 1 := by
  unfold stepBreakpoint; norm_num

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
