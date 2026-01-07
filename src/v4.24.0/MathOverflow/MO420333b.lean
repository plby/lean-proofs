import Mathlib

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
