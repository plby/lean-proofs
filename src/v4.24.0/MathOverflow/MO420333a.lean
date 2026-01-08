import Mathlib

set_option linter.style.longLine false

set_option maxHeartbeats 0

open Classical

/-
A Lean 4 formalization of the game:

* Unknown real `y ≥ 1`.
* A strategy is an increasing sequence of nonnegative reals with `x 0 ≥ 1`,
  and which eventually reaches any `y ≥ 1`.
* The game ends at the first index `n` with `y ≤ x n`.
* The score is `(∑ i ≤ n, x i) / y`.
* We minimize the worst-case score: `inf_x sup_{y≥1} score(x,y)`.

We put scores in `ℝ≥0∞` (ENNReal) so that `iInf`/`iSup` are available.
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

/-
If a monotone sequence $x_n \ge 1$ satisfies $\sum_{i=0}^{n+1} x_i \le W x_n$, then $W \ge 4$.
-/
lemma strategy_imp_four_le (x : ℕ → ℝ) (W : ℝ)
  (h_pos : ∀ n, 0 ≤ x n) (h_x0 : 1 ≤ x 0) (h_mono : Monotone x)
  (h_cond : ∀ n, ∑ i ∈ Finset.range (n + 2), x i ≤ W * x n) :
  4 ≤ W := by
    -- Let $S_n = \sum_{i=0}^n x_i$ and $z_n = S_n / x_n$. Note the index shift in definition compared to thought process, let's stick to the one in the problem.
    set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), x i
    set z : ℕ → ℝ := fun n => S n / x n

    -- Then $S_{n+1} = S_n + x_{n+1}$.
    -- So $S_n + x_{n+1} \le W x_n \implies x_{n+1} \le W x_n - S_n = x_n (W - z_n)$.
    have h_x_succ : ∀ n, x (n + 1) ≤ x n * (W - z n) := by
      intro n; specialize h_cond n; rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( show 0 < x n from Nat.recOn n ( by linarith ) fun n ihn => by linarith [ h_mono n.le_succ ] ) ) ] ; rw [ Finset.sum_range_succ ] at h_cond; linarith;
    -- Since $x_{n+1} \ge x_n > 0$, we have $1 \le W - z_n$, so $z_n \le W - 1$.
    have h_z_le : ∀ n, z n ≤ W - 1 := by
      intro n; nlinarith [ h_pos n, h_pos ( n + 1 ), h_mono n.le_succ, h_x_succ n, show 1 ≤ x n from Nat.recOn n ( by linarith ) fun n ihn => by linarith [ h_mono n.le_succ ] ] ;
    -- Now consider $z_{n+1} = S_{n+1} / x_{n+1} = (S_n + x_{n+1}) / x_{n+1} = S_n / x_{n+1} + 1$.
    -- $z_{n+1} = (S_n / x_n) (x_n / x_{n+1}) + 1 = z_n (x_n / x_{n+1}) + 1$.
    -- Since $x_{n+1} \le x_n (W - z_n)$, we have $x_n / x_{n+1} \ge 1 / (W - z_n)$.
    -- So $z_{n+1} \ge z_n / (W - z_n) + 1 = (z_n + W - z_n) / (W - z_n) = W / (W - z_n)$.
    have h_z_succ : ∀ n, z (n + 1) ≥ W / (W - z n) := by
      intro n
      have h_z_succ_step : z (n + 1) = z n * (x n / x (n + 1)) + 1 := by
        simp +zetaDelta at *;
        rw [ div_mul_div_cancel₀ ( ne_of_gt <| lt_of_lt_of_le ( by positivity ) <| h_mono <| Nat.zero_le _ ) ] ; rw [ Finset.sum_range_succ ] ; rw [ div_add_one, div_eq_div_iff ] <;> nlinarith [ h_pos n, h_pos ( n + 1 ), h_mono n.le_succ, h_x0, h_x_succ n, h_z_le n, show x n > 0 from lt_of_lt_of_le ( by positivity ) <| h_mono <| Nat.zero_le _ ] ;
      -- Since $x_{n+1} \le x_n (W - z_n)$, we have $x_n / x_{n+1} \ge 1 / (W - z_n)$ by taking the reciprocal of both sides.
      have h_reciprocal : x n / x (n + 1) ≥ 1 / (W - z n) := by
        rw [ ge_iff_le, div_le_div_iff₀ ] <;> nlinarith [ h_pos n, h_pos ( n + 1 ), h_mono n.le_succ, h_x_succ n, h_z_le n, show 0 < x n from Nat.recOn n ( by linarith ) fun n ihn => by linarith [ h_mono n.le_succ ] ];
      simp_all +decide [ div_eq_mul_inv ];
      nlinarith [ h_z_le n, h_reciprocal, inv_mul_cancel₀ ( show W - z n ≠ 0 from by linarith [ h_z_le n ] ), show 0 ≤ z n from div_nonneg ( Finset.sum_nonneg fun _ _ => h_pos _ ) ( h_pos _ ) ];
    -- Since $W < 4$, the polynomial $t^2 - Wt + W$ has negative discriminant and is always positive.
    by_contra h_contra
    have h_discriminant : W^2 - 4 * W < 0 := by
      nlinarith [ show 0 < W by have := h_cond 0; norm_num [ Finset.sum_range_succ ] at this; nlinarith [ h_pos 0, h_pos 1 ] ];
    -- So $t(W-t) < W$ for all $t$.
    -- Thus $t < W / (W - t) = f(t)$ for all $t < W$.
    -- In particular, since $z_n \le W - 1 < W$, we have $z_n < f(z_n) \le z_{n+1}$.
    -- So $z_n$ is strictly increasing.
    have h_z_inc : StrictMono z := by
      have h_z_lt_f : ∀ n, z n < W / (W - z n) := by
        intro n; rw [ lt_div_iff₀ ] <;> nlinarith [ h_z_le n, sq_nonneg ( W - 2 * z n ) ] ;
      exact strictMono_nat_of_lt_succ fun n => lt_of_lt_of_le ( h_z_lt_f n ) ( h_z_succ n );
    -- Since $z_n$ is strictly increasing and bounded above by $W - 1$, it converges to some limit $L \le W - 1$.
    obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto z Filter.atTop (nhds L) ∧ L ≤ W - 1 := by
      exact ⟨ _, tendsto_atTop_isLUB h_z_inc.monotone ( isLUB_ciSup ⟨ W - 1, Set.forall_mem_range.mpr h_z_le ⟩ ), by exact ciSup_le h_z_le ⟩;
    -- The inequality $z_{n+1} \ge f(z_n)$ implies $L \ge f(L)$.
    have hL_ge_fL : L ≥ W / (W - L) := by
      exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.div tendsto_const_nhds ( tendsto_const_nhds.sub hL.1 ) ( by nlinarith ) ) ( hL.1.comp ( Filter.tendsto_add_atTop_nat 1 ) ) fun n => h_z_succ n;
    rw [ ge_iff_le, div_le_iff₀ ] at hL_ge_fL <;> nlinarith [ sq_nonneg ( L - W / 2 ) ]

/- Main statement: the smallest possible worst-case score is `4`. -/
theorem gameValue_eq_four : gameValue = (4 : ENNReal) := by
  -- First, we show that the infimum is at most 4.
  have h_upper : ⨅ s : Strategy, worstCaseScore s ≤ 4 := by
    -- Let's choose any strategy `s` and show that its worst-case score is at most 4.
    have h_le_four : ∃ s : Strategy, worstCaseScore s ≤ 4 := by
      fconstructor;
      constructor;
      case w.x => exact fun n => 2 ^ n;
      all_goals norm_num [ Monotone ];
      exact fun a b h => pow_le_pow_right₀ ( by norm_num ) h;
      exact fun { y } hy => pow_unbounded_of_one_lt y one_lt_two |> Exists.imp fun n hn => le_of_lt hn;
      refine' iSup_le _;
      intro y
      simp [score, partialSum, hitIndex];
      rw [ geom_sum_eq ] <;> norm_num;
      rw [ div_le_iff₀ ] <;> norm_num;
      · rcases k : Nat.find ( show ∃ n : ℕ, ( y : ℝ ) ≤ 2 ^ n from by exact pow_unbounded_of_one_lt _ one_lt_two |> Exists.imp fun n hn => le_of_lt hn ) with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        · linarith [ y.2 ];
        · norm_num [ Nat.find_eq_iff ] at *;
          linarith [ k.2 _ <| Nat.lt_succ_self _ ];
      · linarith [ y.2 ]
    generalize_proofs at *;
    exact le_trans ( ciInf_le ⟨ 0, Set.forall_mem_range.mpr fun s => by exact zero_le _ ⟩ h_le_four.choose ) h_le_four.choose_spec;
  -- Next, we show that the infimum is at least 4.
  have h_lower : ∀ s : Strategy, worstCaseScore s ≥ 4 := by
    -- Let's choose any strategy $s$ and derive a contradiction if $worstCaseScore s < 4$.
    intro s
    by_contra h_contra;
    -- Let $W = \text{worstCaseScore } s$. Since $W < 4$, $W$ is finite, say $W = w \in \mathbb{R}$.
    obtain ⟨w, hw⟩ : ∃ w : ℝ, worstCaseScore s = ENNReal.ofReal w ∧ w < 4 := by
      use ENNReal.toReal (worstCaseScore s);
      rw [ ENNReal.ofReal_toReal ];
      · simp +zetaDelta at *;
        convert ENNReal.toReal_strict_mono _ h_contra;
        decide +revert;
      · aesop;
    -- We claim that for all $n$, $S_{n+1} \le w x_n$.
    have h_claim : ∀ n, ∑ i ∈ Finset.range (n + 2), s.x i ≤ w * s.x n := by
      intro n
      have h_score : ∀ y : {y : ℝ // 1 ≤ y}, y.1 ≤ s.x (hitIndex s y) → (∑ i ∈ Finset.range (hitIndex s y + 1), s.x i) / y.1 ≤ w := by
        intro y hy
        have h_score : score s y ≤ ENNReal.ofReal w := by
          exact hw.1 ▸ le_iSup ( fun y : { y : ℝ // 1 ≤ y } => score s y ) y;
        unfold score at h_score;
        rwa [ ENNReal.ofReal_le_ofReal_iff ] at h_score;
        exact le_of_not_gt fun h => by rw [ ENNReal.ofReal_eq_zero.mpr h.le ] at h_score; exact absurd h_score ( by exact not_le_of_gt ( ENNReal.ofReal_pos.mpr ( div_pos ( show 0 < partialSum s ( hitIndex s y ) from Finset.sum_pos ( fun _ _ => lt_of_lt_of_le zero_lt_one ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) ) ( by norm_num ) ) ( show 0 < ( y : ℝ ) from lt_of_lt_of_le zero_lt_one y.2 ) ) ) ) ;
      -- Let $k > n$ be the first index such that $x_k > x_n$.
      obtain ⟨k, hk⟩ : ∃ k > n, s.x k > s.x n ∧ ∀ m, n < m → m < k → s.x m = s.x n := by
        have h_unbounded : ∀ M : ℝ, ∃ k, s.x k > M := by
          exact fun M => by rcases s.hits ( show 1 ≤ Max.max M 1 + 1 by linarith [ le_max_left M 1, le_max_right M 1 ] ) with ⟨ k, hk ⟩ ; exact ⟨ k, by linarith [ le_max_left M 1, le_max_right M 1 ] ⟩ ;
        obtain ⟨ k, hk ⟩ := h_unbounded ( s.x n );
        -- Let $k$ be the smallest index greater than $n$ such that $s.x k > s.x n$.
        obtain ⟨k, hk₁, hk₂⟩ : ∃ k > n, s.x k > s.x n ∧ ∀ m, n < m → m < k → s.x m ≤ s.x n := by
          exact ⟨ Nat.find ( ⟨ k, by linarith [ show n < k from Nat.lt_of_not_ge fun h => by linarith [ s.mono h ] ], hk ⟩ : ∃ k > n, s.x k > s.x n ), Nat.find_spec ( ⟨ k, by linarith [ show n < k from Nat.lt_of_not_ge fun h => by linarith [ s.mono h ] ], hk ⟩ : ∃ k > n, s.x k > s.x n ) |>.1, Nat.find_spec ( ⟨ k, by linarith [ show n < k from Nat.lt_of_not_ge fun h => by linarith [ s.mono h ] ], hk ⟩ : ∃ k > n, s.x k > s.x n ) |>.2, by aesop ⟩;
        exact ⟨ k, hk₁, hk₂.1, fun m hm₁ hm₂ => le_antisymm ( hk₂.2 m hm₁ hm₂ ) ( s.mono hm₁.le ) ⟩;
      -- Consider targets $y$ approaching $x_{k-1}$ from above, i.e., $y \in (x_{k-1}, x_k]$.
      have h_target : ∀ y : ℝ, s.x n < y ∧ y ≤ s.x k → (∑ i ∈ Finset.range (k + 1), s.x i) / y ≤ w := by
        intros y hy
        have h_hit : hitIndex s ⟨y, by
          linarith [ s.nonneg n, s.one_le, show 1 ≤ s.x n from Nat.recOn n ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ]⟩ = k := by
          all_goals generalize_proofs at *;
          refine' le_antisymm _ _;
          · exact Nat.find_min' _ hy.2;
          · refine' le_of_not_gt fun h => _;
            have := Nat.find_spec ( s.hits ‹_› );
            linarith [ hk.2.2 ( Nat.find ( s.hits ‹_› ) ) ( Nat.lt_of_not_ge fun h => by linarith [ Nat.find_spec ( s.hits ‹_› ), s.mono h ] ) h ]
        generalize_proofs at *;
        specialize h_score ⟨ y, by linarith ⟩ ; aesop;
      -- Taking the limit as $y \to x_{k-1}^+$, we get $S_k \le w x_{k-1} = w x_n$.
      have h_limit : (∑ i ∈ Finset.range (k + 1), s.x i) / s.x n ≤ w := by
        have h_limit : Filter.Tendsto (fun y : ℝ => (∑ i ∈ Finset.range (k + 1), s.x i) / y) (nhdsWithin (s.x n) (Set.Ioi (s.x n))) (nhds ((∑ i ∈ Finset.range (k + 1), s.x i) / s.x n)) := by
          exact tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( ne_of_gt <| lt_of_lt_of_le zero_lt_one <| s.one_le.trans <| s.mono <| Nat.zero_le _ );
        exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by linarith, by linarith ⟩ ) fun y hy => h_target y ⟨ hy.1, hy.2.le ⟩ );
      rw [ div_le_iff₀ ] at h_limit;
      · exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => s.nonneg _ ) h_limit;
      · linarith [ s.nonneg n, s.one_le, show 1 ≤ s.x n from Nat.recOn n ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ];
    exact hw.2.not_ge <| strategy_imp_four_le s.x w s.nonneg s.one_le s.mono h_claim;
  exact le_antisymm h_upper ( le_iInf fun s => h_lower s )

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

/-- Convenience: the 2-step optimal first guess `a(B) = (1 + √(1 + 4B))/2`. -/
noncomputable def twoStepFirst (B : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * B)) / 2

/-
A strategy that guesses `B` at step 0, and `B+n` at step `n >= 1`. This is valid for `B >= 1`.
-/
noncomputable def strategyB (B : ℝ) (hB : 1 ≤ B) : Strategy :=
  { x := fun n => if n = 0 then B else B + n
    nonneg := by
      exact fun n => by split_ifs <;> positivity;
    one_le := by
      -- Since $B \geq 1$, we have $1 \leq B$.
      simp [hB]
    mono := by
      -- To prove monotonicity, we need to show that for any $n \leq m$, the value at $n$ is less than or equal to the value at $m$.
      intro n m hnm
      aesop
    hits := by
      exact fun { y } hy => ⟨ ⌈y⌉₊, by rw [ if_neg ( Nat.ne_of_gt ( Nat.ceil_pos.mpr ( by linarith ) ) ) ] ; linarith [ Nat.le_ceil y ] ⟩ }

/-
The bounded worst case score of `strategyB` is at most `B`.
-/
theorem strategyB_bounded_score_le (B : ℝ) (hB : 1 ≤ B) :
    boundedWorstCaseScore (strategyB B hB) B ≤ ENNReal.ofReal B := by
  -- Let's choose any $y \in [1, B]$.
  have h_score_le_B : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, boundedScore (strategyB B hB) B y ≤ ENNReal.ofReal B := by
    intros y
    obtain ⟨hy1, hy2⟩ := y.property;
    -- The partial sum at the hit index is B.
    have h_partial_sum : partialSum (strategyB B hB) (hitIndex (strategyB B hB) ⟨y.val, hy1⟩) = B := by
      -- By definition of `hitIndex`, we have `hitIndex (strategyB B hB) ⟨y.val, hy1⟩ = 0`.
      have h_hit_index : hitIndex (strategyB B hB) ⟨y.val, hy1⟩ = 0 := by
        exact le_antisymm ( Nat.find_le <| by aesop ) ( Nat.zero_le _ );
      unfold partialSum; aesop;
    exact ENNReal.ofReal_le_ofReal ( by rw [ h_partial_sum, div_le_iff₀ ] <;> nlinarith! );
  exact iSup_le h_score_le_B

/-
If `B <= 2`, then for any strategy `s`, the bounded worst case score is at least `B`.
-/
theorem boundedWorstCaseScore_ge_of_B_le_two {B : ℝ} (hB1 : 1 ≤ B) (hB2 : B ≤ 2) (s : Strategy) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal B := by
  -- Consider two cases: $s.x 0 \ge B$ and $s.x 0 < B$.
  by_cases h_case : s.x 0 ≥ B;
  · refine' le_trans _ ( le_ciSup _ ⟨ 1, by linarith, by linarith ⟩ );
    · unfold boundedScore score;
      unfold partialSum;
      norm_num [ Finset.sum_range_succ' ];
      exact ENNReal.ofReal_le_ofReal ( by linarith [ show 0 ≤ ∑ k ∈ Finset.range ( hitIndex s ⟨ 1, by linarith ⟩ ), s.x ( k + 1 ) from Finset.sum_nonneg fun _ _ => s.nonneg _ ] );
    · simp +zetaDelta at *;
  · by_cases h_case2 : s.x 1 ≥ B;
    · -- Since $s.x 1 \ge B$, we can choose $y \in (s.x 0, B]$.
      obtain ⟨y, hy⟩ : ∃ y ∈ Set.Ioo (s.x 0) B, ENNReal.ofReal ((s.x 0 + s.x 1) / y) ≥ ENNReal.ofReal B := by
        exact ⟨ ( s.x 0 + B ) / 2, ⟨ by linarith, by linarith ⟩, ENNReal.ofReal_le_ofReal <| by rw [ le_div_iff₀ ] <;> nlinarith [ s.nonneg 0, s.nonneg 1 ] ⟩;
      -- Since $y \in (s.x 0, B]$, we have $hitIndex s y = 1$.
      have h_hitIndex : hitIndex s ⟨y, by linarith [hy.1.1, s.one_le]⟩ = 1 := by
        refine' le_antisymm _ _ <;> norm_num [ hitIndex ];
        · exact ⟨ 1, by norm_num, by linarith [ hy.1.2 ] ⟩;
        · linarith [ hy.1.1 ];
      refine' le_trans hy.2 ( le_trans _ ( le_ciSup _ ⟨ y, by linarith [ hy.1.1, s.one_le ], hy.1.2.le ⟩ ) );
      · rw [ boundedScore ];
        rw [ show score s ⟨ y, by linarith [ hy.1.1, s.one_le ] ⟩ = ENNReal.ofReal ( ( ∑ i ∈ Finset.range ( hitIndex s ⟨ y, by linarith [ hy.1.1, s.one_le ] ⟩ + 1 ), s.x i ) / y ) by rfl, h_hitIndex ] ; norm_num [ Finset.sum_range_succ ];
      · simp +zetaDelta at *;
    · -- Since $s.x 0 < B$ and $s.x 1 < B$, we have $s.x 0 + s.x 1 + s.x 2 \ge s.x 0 + s.x 1 + s.x 1 = s.x 0 + 2s.x 1$.
      have h_sum : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, y.val ∈ Set.Ioc (s.x 1) B → boundedScore s B y ≥ ENNReal.ofReal ((s.x 0 + 2 * s.x 1) / y.val) := by
        intro y hy
        have h_hitIndex : hitIndex s ⟨y.val, by
          exact y.2.1⟩ ≥ 2 := by
          all_goals generalize_proofs at *;
          refine' Nat.le_of_not_lt fun h => _;
          interval_cases _ : hitIndex s ⟨ y, by assumption ⟩ <;> simp_all +decide [ hitIndex ];
          · linarith [ s.mono zero_le_one ];
          · grind
        generalize_proofs at *;
        -- Since $hitIndex s ⟨y.val, by ...⟩ ≥ 2$, we have $partialSum s (hitIndex s ⟨y.val, by ...⟩) ≥ s.x 0 + s.x 1 + s.x 2$.
        have h_partialSum : partialSum s (hitIndex s ⟨y.val, by
          linarith [ y.2.1 ]⟩) ≥ s.x 0 + s.x 1 + s.x 1 := by
          exact le_trans ( by norm_num [ Finset.sum_range_succ ] ; linarith [ s.mono ( show 0 ≤ 1 by norm_num ), s.mono ( show 1 ≤ 2 by norm_num ) ] ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.succ_le_succ h_hitIndex ) ) fun _ _ _ => s.nonneg _ )
        generalize_proofs at *;
        refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_right h_partialSum <| inv_nonneg.2 <| by linarith ) ; ring_nf ; aesop;
      -- Taking the limit as $y \to s.x 1^+$, we get $\lim_{y \to s.x 1^+} \frac{s.x 0 + 2s.x 1}{y} = \frac{s.x 0 + 2s.x 1}{s.x 1} = \frac{s.x 0}{s.x 1} + 2$.
      have h_limit : Filter.Tendsto (fun y : ℝ => ENNReal.ofReal ((s.x 0 + 2 * s.x 1) / y)) (nhdsWithin (s.x 1) (Set.Ioi (s.x 1))) (nhds (ENNReal.ofReal ((s.x 0 + 2 * s.x 1) / s.x 1))) := by
        exact ENNReal.tendsto_ofReal ( tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( by linarith [ s.nonneg 0, s.nonneg 1, s.one_le, s.mono zero_le_one ] ) );
      -- Since $\frac{s.x 0}{s.x 1} + 2 \ge B$, we have $\lim_{y \to s.x 1^+} \frac{s.x 0 + 2s.x 1}{y} \ge B$.
      have h_limit_ge_B : ENNReal.ofReal ((s.x 0 + 2 * s.x 1) / s.x 1) ≥ ENNReal.ofReal B := by
        refine' ENNReal.ofReal_le_ofReal _;
        rw [ le_div_iff₀ ] <;> nlinarith [ s.nonneg 0, s.nonneg 1, s.one_le, s.mono zero_le_one ];
      refine le_trans h_limit_ge_B <| le_of_tendsto h_limit ?_;
      norm_num +zetaDelta at *;
      filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show s.x 1 < B from h_case2 ⟩ ] with y hy using le_trans ( h_sum y ( by linarith [ hy.1, show 1 ≤ s.x 1 from by linarith [ s.one_le, s.mono zero_le_one ] ] ) ( by linarith [ hy.2 ] ) hy.1 ( by linarith [ hy.2 ] ) ) ( le_iSup_of_le ⟨ y, by linarith [ hy.1, show 1 ≤ s.x 1 from by linarith [ s.one_le, s.mono zero_le_one ] ], by linarith [ hy.2 ] ⟩ le_rfl )

/- When `B ≤ 2`, the bounded game value is `B`. -/
theorem boundedGameValue_eq_of_B_le_two
    {B : ℝ} (hB1 : 1 ≤ B) (hB2 : B ≤ 2) :
    boundedGameValue B = ENNReal.ofReal B := by
  -- First, we show that the bounded game value is at most B.
  have h_upper_bound : boundedGameValue B ≤ ENNReal.ofReal B := by
    exact le_trans ( iInf_le _ ( strategyB B hB1 ) ) ( strategyB_bounded_score_le B hB1 );
  refine' le_antisymm h_upper_bound _;
  exact le_iInf fun s => boundedWorstCaseScore_ge_of_B_le_two hB1 hB2 s

/-- When `B ≤ 2`, an optimal strategy can choose `B` as its first guess. -/
theorem exists_optimalStrategy_firstGuess_eq_B_of_B_le_two
    {B : ℝ} (hB1 : 1 ≤ B) (hB2 : B ≤ 2) :
    ∃ s : Strategy, IsOptimalBounded B s ∧ s.x 0 = B := by
  -- Let's choose the strategy where the first guess is $B$.
  use ⟨fun n => if n = 0 then B else B + n, by
    exact fun n => by positivity;, by
    norm_num [ hB1 ], by
    exact fun n m hnm => by cases n <;> cases m <;> norm_num at * <;> linarith;, by
    exact fun { y } hy => ⟨ ⌈y - B⌉₊ + 1, by norm_num; linarith [ Nat.le_ceil ( y - B ) ] ⟩⟩
  generalize_proofs at *;
  constructor <;> norm_num [ IsOptimalBounded ];
  rw [ boundedGameValue_eq_of_B_le_two hB1 hB2 ];
  refine' le_antisymm _ _;
  · refine' iSup_le _;
    intro i; erw [ ENNReal.ofReal_le_ofReal_iff ] <;> norm_num [ partialSum ];
    · rcases i with ⟨ y, hy₁, hy₂ ⟩ ; rcases hy₂.eq_or_lt with rfl | hy₂' <;> norm_num [ Finset.sum_range_succ' ] at *;
      · unfold hitIndex;
        rw [ show Nat.find ( show ∃ n : ℕ, y ≤ if n = 0 then y else y + ( n : ℝ ) from ⟨ 0, by norm_num ⟩ ) = 0 from Nat.find_eq_iff ( by aesop ) |>.2 ⟨ by norm_num, by aesop ⟩ ] ; norm_num ; rw [ div_le_iff₀ ] <;> nlinarith;
      · rw [ show hitIndex _ ⟨ y, hy₁ ⟩ = 0 from _ ] ; norm_num;
        · rw [ div_le_iff₀ ] <;> nlinarith;
        · unfold hitIndex; aesop;
    · linarith;
  · refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num, by linarith ⟩ ) <;> norm_num [ boundedScore ];
    unfold score; norm_num [ partialSum ];
    gcongr ; norm_num [ Finset.sum_range_succ' ];
    exact Finset.sum_nonneg fun _ _ => by positivity;

/-
A 2-step strategy that guesses `twoStepFirst B` then `B`, then increments. Valid for `B >= 2`.
-/
noncomputable def twoStepStrategy (B : ℝ) (hB : 2 ≤ B) : Strategy :=
  { x := fun n => if n = 0 then twoStepFirst B else if n = 1 then B else B + (n - 1)
    nonneg := by
      intro n; split_ifs <;> norm_num [ twoStepFirst ] ; nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.sq_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;
      · linarith;
      · linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ‹_› ) ) ( Ne.symm ‹_› ) ]
    one_le := by
      simp +zetaDelta at *;
      unfold twoStepFirst; nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.sq_sqrt ( by linarith : 0 ≤ 1 + 4 * B ) ] ;
    mono := by
      refine' fun n m hnm => _;
      rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> norm_num at *;
      · unfold twoStepFirst; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;
      · unfold twoStepFirst; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;
      · positivity;
      · linarith
    hits := by
      intro y hy;
      -- Let's choose $n$ such that $B + (n - 1) \geq y$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, B + (n - 1) ≥ y := by
        exact ⟨ ⌊y - B + 1⌋₊ + 1, by push_cast; linarith [ Nat.lt_floor_add_one ( y - B + 1 ) ] ⟩;
      use n + 2;
      grind }

/-
Equation satisfied by `twoStepFirst B`: `x^2 - x - B = 0`.
-/
lemma twoStepFirst_eqn {B : ℝ} (hB : 1 ≤ B) : (twoStepFirst B) ^ 2 - (twoStepFirst B) - B = 0 := by
  unfold twoStepFirst; linarith [ Real.mul_self_sqrt ( by linarith : 0 ≤ 1 + 4 * B ) ] ;

/-
The bounded worst case score of the 2-step strategy is at most `twoStepFirst B`.
-/
lemma twoStepStrategy_le {B : ℝ} (hB : 2 ≤ B) :
    boundedWorstCaseScore (twoStepStrategy B hB) B ≤ ENNReal.ofReal (twoStepFirst B) := by
      refine' iSup_le _;
      intro y;
      unfold boundedScore score partialSum;
      -- Let's consider the two cases: $y \leq a$ and $y > a$.
      by_cases hy : y.val ≤ twoStepFirst B;
      · -- Since $y \leq a$, we have $hitIndex = 0$.
        have h_hitIndex_zero : hitIndex (twoStepStrategy B hB) ⟨y.val, y.property.left⟩ = 0 := by
          unfold hitIndex; aesop;
        rw [ h_hitIndex_zero ] ; norm_num;
        exact ENNReal.ofReal_le_ofReal ( div_le_self ( by exact le_of_lt ( by exact div_pos ( add_pos_of_pos_of_nonneg zero_lt_one ( Real.sqrt_nonneg _ ) ) zero_lt_two ) ) ( by linarith [ y.2.1 ] ) );
      · -- Since $y > a$, we have $hitIndex = 1$.
        have h_hitIndex : hitIndex (twoStepStrategy B hB) ⟨y.val, y.property.left⟩ = 1 := by
          refine' Nat.find_eq_iff _ |>.2 ⟨ _, _ ⟩ <;> aesop;
        rw [ h_hitIndex ];
        rw [ ENNReal.ofReal_le_ofReal_iff ] <;> norm_num [ Finset.sum_range_succ ];
        · rw [ div_le_iff₀ ] <;> norm_num [ twoStepStrategy ];
          · unfold twoStepFirst at *;
            nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by positivity ), y.2.2 ];
          · linarith [ y.2.1 ];
        · exact div_nonneg ( add_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) zero_le_two

/-
Algebraic inequality: `max x (1 + B / x) ≥ twoStepFirst B`.
-/
lemma max_x_one_plus_B_div_x_ge {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) :
    max x (1 + B / x) ≥ twoStepFirst B := by
      field_simp;
      rw [ le_max_iff ];
      exact or_iff_not_imp_left.mpr fun h => by rw [ le_div_iff₀ hx ] ; nlinarith [ twoStepFirst_eqn hB, Real.sqrt_nonneg ( 1 + 4 * B ), Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by positivity ) ] ;

/-
The bounded worst case score is at least the first guess `s.x 0`.
-/
lemma boundedWorstCaseScore_ge_x0 (s : Strategy) (B : ℝ) (hB : 1 ≤ B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (s.x 0) := by
      refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num, by linarith ⟩ );
      · refine' ENNReal.ofReal_le_ofReal _;
        exact le_div_iff₀ ( by norm_num ) |>.2 ( by linarith! [ show s.x 0 ≤ ∑ i ∈ Finset.range ( hitIndex s ⟨ 1, by norm_num ⟩ + 1 ), s.x i from Finset.single_le_sum ( fun i _ => s.nonneg i ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) ] );
      · refine' ⟨ ⊤, Set.forall_mem_range.2 fun y => le_top ⟩

/-
If `s.x 0 < B`, the bounded worst case score is at least `1 + s.x 1 / s.x 0`.
-/
lemma boundedWorstCaseScore_ge_one_plus_x1_div_x0 (s : Strategy) (B : ℝ) (hB : 1 ≤ B) (h_x0_lt_B : s.x 0 < B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (1 + s.x 1 / s.x 0) := by
      -- Consider the target $y = s.x 0 + \epsilon$ where $\epsilon$ is a small positive number.
      have h_eps : ∀ ε > 0, ε < B - s.x 0 → ENNReal.ofReal ((∑ i ∈ Finset.range (1 + 1), s.x i) / (s.x 0 + ε)) ≤ boundedWorstCaseScore s B := by
        intro ε hε_pos hε_lt
        have h_y : s.x 0 + ε ∈ Set.Icc 1 B := by
          constructor <;> linarith [ s.one_le ];
        refine' le_trans _ ( le_ciSup _ ⟨ s.x 0 + ε, h_y.1, h_y.2 ⟩ );
        · refine' ENNReal.ofReal_le_ofReal _;
          gcongr;
          · linarith [ h_y.1 ];
          · refine' Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.succ_le_succ _ ) ) fun _ _ _ => s.nonneg _;
            unfold hitIndex; aesop;
        · exact?;
      -- Taking the limit as $\epsilon$ approaches $0$ from the right, we get the desired inequality.
      have h_limit : Filter.Tendsto (fun ε => ENNReal.ofReal ((∑ i ∈ Finset.range (1 + 1), s.x i) / (s.x 0 + ε))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (1 + s.x 1 / s.x 0))) := by
        convert ENNReal.tendsto_ofReal ( Filter.Tendsto.div ( tendsto_const_nhds ) ( tendsto_const_nhds.add ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) using 2 <;> norm_num [ Finset.sum_range_succ ];
        · rw [ add_div, div_self ( ne_of_gt ( lt_of_lt_of_le zero_lt_one ( s.one_le ) ) ) ];
        · linarith [ s.one_le ];
      exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by linarith, by linarith ⟩ ) fun ε hε => h_eps ε hε.1 hε.2 )

/-
For `B >= 2`, `B` is greater than or equal to `twoStepFirst B`.
-/
lemma B_ge_twoStepFirst {B : ℝ} (hB : 2 ≤ B) : B ≥ twoStepFirst B := by
  unfold twoStepFirst;
  nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ]

/-
If the second guess `s.x 1` is at least `B`, the score is at least `twoStepFirst B`.
-/
lemma x1_ge_B_imp_score_ge (s : Strategy) (B : ℝ) (hB : 2 ≤ B) (h1 : s.x 1 ≥ B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (twoStepFirst B) := by
      by_cases h2 : s.x 0 ≥ B;
      · refine' le_trans _ ( boundedWorstCaseScore_ge_x0 s B ( by linarith ) );
        exact ENNReal.ofReal_le_ofReal ( by rw [ twoStepFirst ] ; nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] );
      · -- Since $s.x 0 < B$, we have $W \ge 1 + B / s.x 0$.
        have h3 : boundedWorstCaseScore s B ≥ ENNReal.ofReal (1 + B / s.x 0) := by
          refine' le_trans _ ( boundedWorstCaseScore_ge_one_plus_x1_div_x0 s B ( by linarith ) ( by linarith ) );
          gcongr;
          exact s.nonneg 0;
        -- Since $s.x 0 \ge 1 > 0$, we can apply `max_x_one_plus_B_div_x_ge`.
        have h4 : max (s.x 0) (1 + B / s.x 0) ≥ twoStepFirst B := by
          apply max_x_one_plus_B_div_x_ge;
          · linarith [ s.one_le ];
          · linarith;
        refine' le_trans _ ( max_le ( boundedWorstCaseScore_ge_x0 s B ( by linarith ) ) h3 );
        rw [ ← ENNReal.ofReal_max ] ; exact ENNReal.ofReal_le_ofReal h4

/-
Upper bound on `twoStepFirst B` when `B ≤ 2 + √5`.
-/
lemma twoStepFirst_le_bound {B : ℝ} (hB : B ≤ 2 + Real.sqrt 5) :
    twoStepFirst B ≤ (3 + Real.sqrt 5) / 2 := by
      refine' div_le_iff₀' ( by positivity ) |>.2 _;
      -- By simplifying, we can see that this inequality holds for $B \leq 2 + \sqrt{5}$.
      have h_sqrt : Real.sqrt (1 + 4 * B) ≤ 2 + Real.sqrt 5 := by
        rw [ Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      linarith

/-
The function `x^3 - 2x^2` is increasing for `x >= 2`.
-/
lemma cubic_increasing {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x^3 - 2*x^2 ≤ y^3 - 2*y^2 := by
  nlinarith [ sq_nonneg ( x - y ), mul_le_mul_of_nonneg_left hxy ( sub_nonneg_of_le hx ) ]

/-
Algebraic inequality for `a` in a specific range.
-/
lemma cubic_bound_at_a {a : ℝ} (ha_ge_two : 2 ≤ a) (ha_le : a ≤ (3 + Real.sqrt 5) / 2) : a^3 - 2*a^2 ≤ a^2 - a := by
  nlinarith [ mul_le_mul_of_nonneg_left ha_le ( sub_nonneg.mpr ha_ge_two ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

/-
Algebraic bound on `x2` given bounds on ratios involving `W`.
-/
lemma x2_le_cubic_W {x0 x1 x2 W : ℝ} (hx0 : 0 < x0) (hx1 : 0 < x1) (hW : 2 ≤ W)
    (h_x0_le : x0 ≤ W) (h_x1_le : W ≥ 1 + x1 / x0) (h_x2_le : W ≥ (x0 + x1 + x2) / x1) :
    x2 ≤ W^3 - 2*W^2 := by
      -- From $W \ge 1 + x_1/x_0$, we have $x_1 \le (W-1)x_0$.
      have hx1_le : x1 ≤ (W - 1) * x0 := by
        nlinarith [ mul_div_cancel₀ x1 hx0.ne' ];
      rw [ ge_iff_le, div_le_iff₀ ] at h_x2_le <;> nlinarith [ sq_nonneg ( W - 2 ) ]

/-
If `s.x 1 < B` and `s.x 2 >= B`, then the score is at least `twoStepFirst B`.
-/
lemma x2_ge_B_imp_score_ge (s : Strategy) (B : ℝ) (hB : 2 ≤ B) (hB' : B ≤ 2 + Real.sqrt 5)
    (h1 : s.x 1 < B) (h2 : s.x 2 ≥ B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (twoStepFirst B) := by
      -- Let $W = boundedWorstCaseScore s B$. Assume for contradiction $W < ENNReal.ofReal (twoStepFirst B)$.
      by_contra h_contra
      obtain ⟨W, hW⟩ : ∃ W, boundedWorstCaseScore s B = ENNReal.ofReal W ∧ W < twoStepFirst B := by
        norm_num +zetaDelta at *;
        cases h : boundedWorstCaseScore s B ; aesop;
        rw [ ENNReal.lt_ofReal_iff_toReal_lt ] at h_contra <;> aesop;
      -- Since $W < twoStepFirst B$ and $twoStepFirst B \ge 2$, we have $W \ge 2$.
      have hW_ge_two : 2 ≤ W := by
        have hW_ge_two : W ≥ 1 + s.x 1 / s.x 0 := by
          have hw_ge_1_plus_x1_div_x0 : ENNReal.ofReal (1 + s.x 1 / s.x 0) ≤ boundedWorstCaseScore s B := by
            apply boundedWorstCaseScore_ge_one_plus_x1_div_x0 s B (by linarith) (by
            linarith [ s.mono zero_le_one ]);
          rw [hW.left] at hw_ge_1_plus_x1_div_x0;
          rw [ ENNReal.ofReal_le_ofReal_iff ] at hw_ge_1_plus_x1_div_x0 <;> try linarith [ show 0 ≤ s.x 1 / s.x 0 from div_nonneg ( s.nonneg 1 ) ( s.nonneg 0 ) ];
          exact le_of_not_gt fun h => by rw [ ENNReal.ofReal_eq_zero.mpr h.le ] at hw_ge_1_plus_x1_div_x0; exact absurd hw_ge_1_plus_x1_div_x0 ( by norm_num; linarith [ div_nonneg ( show 0 ≤ s.x 1 from s.nonneg 1 ) ( show 0 ≤ s.x 0 from s.nonneg 0 ) ] ) ;
        linarith [ show s.x 1 / s.x 0 ≥ 1 by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith [ s.nonneg 0, s.nonneg 1, s.mono ( show 0 ≤ 1 by norm_num ), s.one_le ] ];
      -- Since $W \ge 2$, we have $W \ge 1 + s.x 1 / s.x 0$ and $W \ge (s.x 0 + s.x 1 + s.x 2) / s.x 1$.
      have hW_ge_one_plus_x1_div_x0 : W ≥ 1 + s.x 1 / s.x 0 := by
        have hW_ge_one_plus_x1_div_x0 : boundedWorstCaseScore s B ≥ ENNReal.ofReal (1 + s.x 1 / s.x 0) := by
          apply boundedWorstCaseScore_ge_one_plus_x1_div_x0;
          · linarith;
          · exact lt_of_le_of_lt ( s.mono ( by norm_num ) ) h1;
        rw [hW.left] at hW_ge_one_plus_x1_div_x0;
        rw [ ge_iff_le, ENNReal.ofReal_le_ofReal_iff ] at hW_ge_one_plus_x1_div_x0 <;> linarith
      have hW_ge_x0_plus_x1_plus_x2_div_x1 : W ≥ (s.x 0 + s.x 1 + s.x 2) / s.x 1 := by
        have hW_ge_x0_plus_x1_plus_x2_div_x1 : ∀ y ∈ Set.Ioc (s.x 1) B, (s.x 0 + s.x 1 + s.x 2) / y ≤ W := by
          intros y hy
          have h_score : score s ⟨y, by
            linarith [ hy.1, hy.2, show 1 ≤ s.x 1 from by linarith [ s.one_le, s.mono zero_le_one ] ]⟩ ≤ ENNReal.ofReal W := by
            all_goals generalize_proofs at *;
            exact hW.1 ▸ le_iSup ( fun y : { y : ℝ // 1 ≤ y ∧ y ≤ B } => boundedScore s B y ) ⟨ y, by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩
          generalize_proofs at *;
          unfold score at h_score;
          -- Since $y \in (s.x 1, B]$, we have $hitIndex s ⟨y, pf✝⟩ = 2$.
          have h_hitIndex : hitIndex s ⟨y, by
            linarith⟩ = 2 := by
            refine' le_antisymm _ _ <;> norm_num [ hitIndex ];
            · exact ⟨ 2, by norm_num, by linarith [ hy.2 ] ⟩;
            · intro m hm; interval_cases m <;> linarith [ hy.1, hy.2, s.mono ( show 0 ≤ 1 by norm_num ), s.mono ( show 1 ≤ 2 by norm_num ) ] ;
          generalize_proofs at *;
          simp_all +decide [ Finset.sum_range_succ ];
          rw [ ENNReal.ofReal_le_ofReal_iff ] at h_score <;> norm_num [ Finset.sum_range_succ, partialSum ] at * <;> nlinarith [ mul_div_cancel₀ ( s.x 0 + s.x 1 + s.x 2 ) ( by linarith : y ≠ 0 ) ];
        have hW_ge_x0_plus_x1_plus_x2_div_x1 : Filter.Tendsto (fun y => (s.x 0 + s.x 1 + s.x 2) / y) (nhdsWithin (s.x 1) (Set.Ioi (s.x 1))) (nhds ((s.x 0 + s.x 1 + s.x 2) / s.x 1)) := by
          exact tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( by linarith [ show 0 < s.x 1 from lt_of_lt_of_le ( show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one ( s.one_le ) ) ( s.mono ( by norm_num ) ) ] );
        exact le_of_tendsto hW_ge_x0_plus_x1_plus_x2_div_x1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by linarith, by linarith ⟩ ) fun y hy => ‹∀ y ∈ Set.Ioc ( s.x 1 ) B, ( s.x 0 + s.x 1 + s.x 2 ) / y ≤ W› y <| Set.Ioo_subset_Ioc_self hy );
      -- Applying `x2_le_cubic_W` with $x_0, x_1, x_2, W$.
      have hx2_le_cubic_W : s.x 2 ≤ W^3 - 2*W^2 := by
        have hx2_le_cubic_W : s.x 0 ≤ W ∧ s.x 1 ≤ W * s.x 0 - s.x 0 ∧ s.x 2 ≤ W * s.x 1 - s.x 0 - s.x 1 := by
          have hx0_le_W : s.x 0 ≤ W := by
            have := hW.1 ▸ boundedWorstCaseScore_ge_x0 s B ( by linarith );
            rw [ ge_iff_le, ENNReal.ofReal_le_ofReal_iff ] at this <;> linarith [ s.nonneg 0 ]
          have hx1_le_Wx0_minus_x0 : s.x 1 ≤ W * s.x 0 - s.x 0 := by
            nlinarith [ show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one ( s.one_le ), div_mul_cancel₀ ( s.x 1 ) ( show s.x 0 ≠ 0 from ne_of_gt ( lt_of_lt_of_le zero_lt_one ( s.one_le ) ) ) ]
          have hx2_le_Wx1_minus_x0_minus_x1 : s.x 2 ≤ W * s.x 1 - s.x 0 - s.x 1 := by
            rw [ ge_iff_le, div_le_iff₀ ] at hW_ge_x0_plus_x1_plus_x2_div_x1 <;> linarith [ s.nonneg 0, s.nonneg 1, s.nonneg 2, s.one_le, s.mono zero_le_one, s.mono one_le_two ]
          exact ⟨hx0_le_W, hx1_le_Wx0_minus_x0, hx2_le_Wx1_minus_x0_minus_x1⟩;
        nlinarith [ sq_nonneg ( W - 2 ), mul_le_mul_of_nonneg_left hW_ge_two ( show 0 ≤ s.x 0 by linarith [ s.nonneg 0 ] ) ];
      -- Since $2 \le W < twoStepFirst B$, by `cubic_increasing`, $W^3 - 2W^2 < twoStepFirst B^3 - 2twoStepFirst B^2$.
      have hW_cubic_lt_twoStepFirst_cubic : W^3 - 2*W^2 < twoStepFirst B^3 - 2*twoStepFirst B^2 := by
        nlinarith [ sq_nonneg ( W - twoStepFirst B ), mul_le_mul_of_nonneg_left hW.2.le ( sub_nonneg.2 hW_ge_two ) ];
      -- By `twoStepFirst_le_bound`, $twoStepFirst B^3 - 2twoStepFirst B^2 \le twoStepFirst B^2 - twoStepFirst B$.
      have h_twoStepFirst_cubic_le_twoStepFirst_sq_minus_twoStepFirst : twoStepFirst B^3 - 2*twoStepFirst B^2 ≤ twoStepFirst B^2 - twoStepFirst B := by
        apply cubic_bound_at_a;
        · exact le_trans hW_ge_two hW.2.le;
        · unfold twoStepFirst; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), Real.sq_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;
      nlinarith [ twoStepFirst_eqn ( show 1 ≤ B by linarith ) ]

/-
The cubic `W^3 - 3W^2 + W` is negative for `2 <= W < (3 + √5)/2`.
-/
lemma cubic_neg_of_W_lt_phi {W : ℝ} (hW_ge : 2 ≤ W) (hW_lt : W < (3 + Real.sqrt 5) / 2) :
    W^3 - 3*W^2 + W < 0 := by
      have h_poly_neg : W * (W^2 - 3 * W + 1) < 0 := by
        exact mul_neg_of_pos_of_neg ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] );
      linarith

/-
Algebraic bound on `x3` given bounds on ratios involving `W`.
-/
lemma x3_le_cubic_W {x0 x1 x2 x3 W : ℝ} (hx0 : 0 < x0) (hx1 : 0 < x1) (hx2 : 0 < x2) (hW : 2 ≤ W)
    (h_x0_le : x0 ≤ W) (h_x1_le : W ≥ 1 + x1 / x0) (h_x2_le : W ≥ (x0 + x1 + x2) / x1)
    (h_x3_le : W ≥ (x0 + x1 + x2 + x3) / x2) :
    x3 ≤ (W^3 - 3*W^2 + W) * x0 := by
      -- From $W \ge 1 + x_1/x_0$, we have $x_1 \le (W-1)x_0$.
      have hx1_le : x1 ≤ (W - 1) * x0 := by
        nlinarith [ mul_div_cancel₀ x1 hx0.ne' ];
      rw [ ge_iff_le, div_le_iff₀ ] at * <;> nlinarith [ mul_le_mul_of_nonneg_left hx1_le <| show 0 ≤ W - 1 by linarith ]

/-
If `s.x 1 < B`, the bounded worst case score is at least `(s.x 0 + s.x 1 + s.x 2) / s.x 1`.
-/
lemma boundedWorstCaseScore_ge_sum_div_x1 (s : Strategy) (B : ℝ) (hB : 1 ≤ B) (h_x1_lt_B : s.x 1 < B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2) / s.x 1) := by
      -- Consider $y \in (s.x 1, B]$. Since $s.x 1 < B$, such $y$ exist.
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y, s.x 1 < y ∧ y ≤ B := by
        exact ⟨ B, h_x1_lt_B, le_rfl ⟩;
      -- Since $y > s.x 1$, we have $hitIndex(s, y) \ge 2$.
      have h_hitIndex_ge_two : hitIndex s ⟨y, by linarith [s.one_le, s.mono (show 1 ≥ 0 by linarith)]⟩ ≥ 2 := by
                                                                              -- Since $y > s.x 1$, we have $hitIndex(s, y) \ge 2$ by the definition of `hitIndex`.
                                                                              by_contra h_contra;
                                                                              interval_cases _ : hitIndex s ⟨ y, by linarith [ s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ] ⟩ <;> simp_all +decide [ hitIndex ];
                                                                              · linarith [ s.mono ( show 0 ≤ 1 by norm_num ) ];
                                                                              · grind;
      -- Since $y > s.x 1$, we have $score(s, y) \geq \frac{s.x 0 + s.x 1 + s.x 2}{y}$.
      have h_score_ge : score s ⟨y, by linarith [s.one_le, s.mono (show 1 ≥ 0 by linarith)]⟩ ≥ ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2) / y) := by
                                                                    have h_score_ge : ∑ i ∈ Finset.range (hitIndex s ⟨y, by linarith [s.one_le, s.mono (show 1 ≥ 0 by linarith)]⟩ + 1), s.x i ≥ s.x 0 + s.x 1 + s.x 2 := by
                                                                                                                                                          rcases n : hitIndex s ⟨ y, by linarith [ s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ] ⟩ with ( _ | _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ' ];
                                                                                                                                                          · linarith;
                                                                                                                                                          · linarith [ show 0 ≤ ∑ k ∈ Finset.range ‹_›, s.x ( k + 1 + 1 + 1 + 1 ) from Finset.sum_nonneg fun _ _ => s.nonneg _, show s.x 3 ≥ 0 from s.nonneg 3 ];
                                                                    refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right h_score_ge <| by linarith [ s.nonneg 0, s.nonneg 1, s.nonneg 2 ] );
                                                                    norm_num;
      -- Taking the limit as $y \downarrow s.x 1$, we get the desired bound.
      have h_limit : Filter.Tendsto (fun y => ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2) / y)) (nhdsWithin (s.x 1) (Set.Ioi (s.x 1))) (nhds (ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2) / s.x 1))) := by
        exact ENNReal.tendsto_ofReal ( tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( by linarith [ s.nonneg 1, s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ] ) );
      refine' le_of_tendsto h_limit _;
      filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hy₁ ⟩ ] with y hy;
      refine' le_trans _ ( le_ciSup _ ⟨ y, by linarith [ hy.1, s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ], by linarith [ hy.2, hy₂ ] ⟩ );
      · -- Since $y > s.x 1$, we have $hitIndex(s, y) \ge 2$, so the partial sum includes at least $x_0, x_1, x_2$.
        have h_hitIndex_ge_two : hitIndex s ⟨y, by linarith [hy.1, s.one_le, s.mono (show 1 ≥ 0 by norm_num)]⟩ ≥ 2 := by
                                                                                      refine' Nat.le_of_not_lt fun h => _;
                                                                                      interval_cases _ : hitIndex s ⟨ y, by linarith [ hy.1, s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ] ⟩ <;> simp_all +decide [ hitIndex ];
                                                                                      · linarith [ hy.1, hy.2, s.mono ( show 0 ≤ 1 by norm_num ) ];
                                                                                      · grind;
        have h_partial_sum_ge : ∑ i ∈ Finset.range (hitIndex s ⟨y, by linarith [hy.1, s.one_le, s.mono (show 1 ≥ 0 by norm_num)]⟩ + 1), s.x i ≥ s.x 0 + s.x 1 + s.x 2 := by
                                                                                                          have h_partial_sum_ge : ∑ i ∈ Finset.range (hitIndex s ⟨y, by linarith [hy.1, s.one_le, s.mono (show 1 ≥ 0 by norm_num)]⟩ + 1), s.x i ≥ ∑ i ∈ Finset.range 3, s.x i := by
                                                                                                                                                                                                            exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => s.nonneg _;
                                                                                                          simpa [ Finset.sum_range_succ ] using h_partial_sum_ge;
        refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right h_partial_sum_ge <| by linarith [ hy.1, s.one_le, s.mono ( show 1 ≥ 0 by norm_num ) ] );
        norm_num;
      · refine' ⟨ ⊤, Set.forall_mem_range.mpr fun y => _ ⟩ ; aesop

/-
If `s.x 2 < B`, the bounded worst case score is at least `(s.x 0 + s.x 1 + s.x 2 + s.x 3) / s.x 2`.
-/
lemma boundedWorstCaseScore_ge_sum_div_x2 (s : Strategy) (B : ℝ) (hB : 1 ≤ B) (h_x2_lt_B : s.x 2 < B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2 + s.x 3) / s.x 2) := by
      -- Consider $y \in (s.x 2, B]$.
      have h_y_exists : ∃ y, s.x 2 < y ∧ y ≤ B := by
        use B;
      -- For $y > s.x 2$, $hitIndex(s, y) \ge 3$ because $s.x 0 \le s.x 1 \le s.x 2 < y$.
      obtain ⟨y, hy1, hy2⟩ : ∃ y, s.x 2 < y ∧ y ≤ B := h_y_exists
      have h_hitIndex_ge_3 : ∀ y' : {y : ℝ // 1 ≤ y ∧ y ≤ B}, y'.1 > s.x 2 → boundedScore s B y' ≥ ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2 + s.x 3) / y'.1) := by
        intros y' hy'_gt_x2
        have h_hitIndex_ge_3 : hitIndex s ⟨y', by
          exact y'.2.1⟩ ≥ 3 := by
          all_goals generalize_proofs at *;
          contrapose! hy'_gt_x2;
          exact le_trans ( show ( y' : ℝ ) ≤ s.x ( hitIndex s ⟨ y', by assumption ⟩ ) from Nat.find_spec ( s.hits <| by assumption ) ) ( s.mono <| by linarith )
        generalize_proofs at *;
        have h_partial_sum_ge : ∑ i ∈ Finset.range (hitIndex s ⟨y'.val, by
          linarith [ y'.2.1 ]⟩ + 1), s.x i ≥ ∑ i ∈ Finset.range 4, s.x i := by
          exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => s.nonneg _
        generalize_proofs at *;
        refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right h_partial_sum_ge <| by linarith );
        norm_num [ Finset.sum_range_succ ];
      -- Taking the limit as $y \downarrow s.x 2$, we get the bound.
      have h_limit : Filter.Tendsto (fun y' : ℝ => ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2 + s.x 3) / y')) (nhdsWithin (s.x 2) (Set.Ioi (s.x 2))) (nhds (ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2 + s.x 3) / s.x 2))) := by
        exact ENNReal.tendsto_ofReal ( tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( ne_of_gt ( show 0 < s.x 2 from lt_of_lt_of_le ( by norm_num ) ( s.one_le.trans ( s.mono ( Nat.zero_le _ ) ) ) ) ) );
      refine' le_of_tendsto h_limit _;
      simp +zetaDelta at *;
      filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hy1 ⟩ ] with x hx using le_trans ( h_hitIndex_ge_3 x ( by linarith [ hx.1, show 1 ≤ s.x 2 from by linarith [ s.one_le, s.mono ( show 0 ≤ 2 by norm_num ) ] ] ) ( by linarith [ hx.2 ] ) hx.1 ) ( le_iSup_of_le ⟨ x, by linarith [ hx.1, show 1 ≤ s.x 2 from by linarith [ s.one_le, s.mono ( show 0 ≤ 2 by norm_num ) ] ], by linarith [ hx.2 ] ⟩ le_rfl )

/-
If `s.x 1 < B` and `s.x 2 < B`, the score is at least `(3 + √5) / 2`.
-/
lemma x2_lt_B_imp_score_ge_phi (s : Strategy) (B : ℝ) (hB : 2 ≤ B)
    (h1 : s.x 1 < B) (h2 : s.x 2 < B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal ((3 + Real.sqrt 5) / 2) := by
      -- By contradiction, assume $W < (3+\sqrt{5})/2$.
      by_contra h_contra
      have hW_lt : boundedWorstCaseScore s B < ENNReal.ofReal ((3 + Real.sqrt 5) / 2) := by
        exact lt_of_not_ge h_contra;
      -- Let $W = boundedWorstCaseScore s B$.
      set W := boundedWorstCaseScore s B;
      -- First, we establish $W \ge 2$.
      have hW_ge_two : 2 ≤ ENNReal.toReal W := by
        have hW_ge_two : 1 + s.x 1 / s.x 0 ≤ ENNReal.toReal W := by
          have := boundedWorstCaseScore_ge_one_plus_x1_div_x0 s B ( by linarith );
          specialize this ( by linarith [ s.mono ( show 0 ≤ 1 by norm_num ), s.mono ( show 1 ≤ 2 by norm_num ) ] ) ; rw [ ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] at this <;> aesop;
        linarith [ show s.x 1 / s.x 0 ≥ 1 from by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith [ s.nonneg 0, s.nonneg 1, s.one_le, s.mono zero_le_one ] ];
      -- Next, we collect the inequalities needed for `x3_le_cubic_W`.
      have h_ineq1 : s.x 0 ≤ ENNReal.toReal W := by
        have := boundedWorstCaseScore_ge_x0 s B ( by linarith );
        rw [ ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] at this <;> aesop
      have h_ineq2 : ENNReal.toReal W ≥ 1 + s.x 1 / s.x 0 := by
        have h_ineq2 : W ≥ ENNReal.ofReal (1 + s.x 1 / s.x 0) := by
          apply_rules [ boundedWorstCaseScore_ge_one_plus_x1_div_x0 ];
          · linarith;
          · linarith [ show s.x 0 ≤ s.x 1 from s.mono ( by norm_num ) ];
        rw [ ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] at h_ineq2 <;> aesop
      have h_ineq3 : ENNReal.toReal W ≥ (s.x 0 + s.x 1 + s.x 2) / s.x 1 := by
        have h_ineq3 : ENNReal.ofReal ((s.x 0 + s.x 1 + s.x 2) / s.x 1) ≤ W := by
          apply boundedWorstCaseScore_ge_sum_div_x1 s B (by linarith) h1;
        rw [ ENNReal.ofReal_le_iff_le_toReal ] at h_ineq3 <;> aesop
      have h_ineq4 : ENNReal.toReal W ≥ (s.x 0 + s.x 1 + s.x 2 + s.x 3) / s.x 2 := by
        have := boundedWorstCaseScore_ge_sum_div_x2 s B ( by linarith ) h2;
        rw [ ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] at this <;> aesop;
      -- Applying `x3_le_cubic_W`, we get $s.x 3 \le (W^3 - 3W^2 + W) s.x 0$.
      have h_x3_le : s.x 3 ≤ (ENNReal.toReal W ^ 3 - 3 * ENNReal.toReal W ^ 2 + ENNReal.toReal W) * s.x 0 := by
        apply_rules [ x3_le_cubic_W ];
        · linarith [ s.one_le ];
        · linarith [ s.nonneg 0, s.nonneg 1, s.nonneg 2, s.one_le, s.mono zero_le_one, s.mono one_le_two ];
        · linarith [ s.nonneg 0, s.nonneg 1, s.nonneg 2, s.one_le, s.mono ( show 0 ≤ 1 by norm_num ), s.mono ( show 1 ≤ 2 by norm_num ) ];
      -- Since $2 \le W < (3+\sqrt{5})/2$, by `cubic_neg_of_W_lt_phi`, $W^3 - 3W^2 + W < 0$.
      have h_cubic_neg : ENNReal.toReal W ^ 3 - 3 * ENNReal.toReal W ^ 2 + ENNReal.toReal W < 0 := by
        apply cubic_neg_of_W_lt_phi;
        · linarith;
        · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] at hW_lt <;> aesop;
      nlinarith [ show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one s.one_le, show 0 ≤ s.x 3 from s.nonneg 3 ]

/-
For any strategy, the bounded worst case score is at least `twoStepFirst B`.
-/
lemma boundedWorstCaseScore_ge_twoStep {B : ℝ} (hB : 2 < B) (hB' : B ≤ 2 + Real.sqrt 5) (s : Strategy) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal (twoStepFirst B) := by
      by_cases h1 : s.x 1 < B <;> by_cases h2 : s.x 2 < B <;> simp_all +decide;
      · refine' le_trans _ ( x2_lt_B_imp_score_ge_phi s B hB.le h1 h2 );
        exact ENNReal.ofReal_le_ofReal ( twoStepFirst_le_bound hB' );
      · convert x2_ge_B_imp_score_ge s B ( by linarith ) ( by linarith ) h1 h2 |> le_trans _ using 1;
        norm_num;
      · -- Apply the lemma that states if the second guess is at least B, then the score is at least twoStepFirst B.
        apply x1_ge_B_imp_score_ge s B (by linarith) (by linarith);
      · have := x1_ge_B_imp_score_ge s B ( by linarith ) h1;
        exact this

/- When `2 < B ≤ 2 + √5`, the bounded game value is `(1 + √(1 + 4B))/2`. -/
theorem boundedGameValue_eq_twoStep
    {B : ℝ} (hB : 2 < B) (hB' : B ≤ 2 + Real.sqrt 5) :
    boundedGameValue B = ENNReal.ofReal (twoStepFirst B) := by
  refine' le_antisymm _ _;
  · refine' le_trans ( ciInf_le _ _ ) _;
    exact?;
    exact twoStepStrategy B hB.le;
    exact?;
  · refine' le_iInf fun s => _;
    exact?

/-- When `2 < B ≤ 2 + √5`, an optimal strategy can pick `(1 + √(1 + 4B))/2` then `B`. -/
theorem exists_optimalStrategy_twoStep
    {B : ℝ} (hB : 2 < B) (hB' : B ≤ 2 + Real.sqrt 5) :
    ∃ s : Strategy,
      IsOptimalBounded B s ∧
      s.x 0 = twoStepFirst B ∧
      s.x 1 = B := by
  -- Let's choose any strategy `s` that starts with `twoStepFirst B` and then `B`.
  obtain ⟨s, hs⟩ : ∃ s : Strategy, s.x 0 = twoStepFirst B ∧ s.x 1 = B := by
    -- Define the strategy $s$ with $s.x 0 = twoStepFirst B$ and $s.x 1 = B$.
    use ⟨fun n => if n = 0 then twoStepFirst B else if n = 1 then B else B + n, by
      field_simp;
      intro n; split_ifs <;> linarith [ show 0 ≤ twoStepFirst B from div_nonneg ( add_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) zero_le_two ] ;, by
      exact le_div_iff₀' ( by positivity ) |>.2 ( by nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.sq_sqrt ( show 0 ≤ 1 + 4 * B by positivity ) ] ), by
      refine' monotone_nat_of_le_succ _;
      rintro ( _ | _ | n ) <;> norm_num;
      unfold twoStepFirst; nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.sq_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ] ;, by
      intro y hy; use ⌈y⌉₊ + 2; norm_num; split_ifs <;> linarith [ Nat.le_ceil y ] ;⟩
    generalize_proofs at *;
    aesop;
  have h_score : boundedWorstCaseScore s B ≤ ENNReal.ofReal (twoStepFirst B) := by
    -- For any $y \in [1, B]$, we have $\text{score}(s, y) \leq \text{twoStepFirst } B$.
    have h_score_le : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, score s ⟨y.1, y.2.1⟩ ≤ ENNReal.ofReal (twoStepFirst B) := by
      intro y
      have hy_le_B : y.val ≤ B := by
        exact y.2.2
      have hy_ge_1 : 1 ≤ y.val := by
        exact y.2.1
      have h_hit_index : hitIndex s ⟨y.val, hy_ge_1⟩ ≤ 1 := by
        unfold hitIndex; aesop;
      have h_partial_sum : partialSum s (hitIndex s ⟨y.val, hy_ge_1⟩) ≤ twoStepFirst B * y.val := by
        interval_cases _ : hitIndex s ⟨ y.val, hy_ge_1 ⟩ <;> simp_all +decide [ partialSum ];
        · exact le_mul_of_one_le_right ( by exact div_nonneg ( add_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) zero_le_two ) hy_ge_1;
        · norm_num [ Finset.sum_range_succ, hs ];
          unfold twoStepFirst at *;
          -- Since $y \geq a$, we have $y \geq \frac{1 + \sqrt{1 + 4B}}{2}$.
          have hy_ge_a : (y.val : ℝ) ≥ (1 + Real.sqrt (1 + 4 * B)) / 2 := by
            unfold hitIndex at *;
            simp_all +decide [ Nat.find_eq_iff ];
            linarith;
          nlinarith [ Real.sqrt_nonneg ( 1 + 4 * B ), Real.mul_self_sqrt ( show 0 ≤ 1 + 4 * B by linarith ) ]
      have h_score : score s ⟨y.val, hy_ge_1⟩ ≤ ENNReal.ofReal (twoStepFirst B) := by
        exact ENNReal.ofReal_le_ofReal ( div_le_iff₀ ( by positivity ) |>.2 h_partial_sum )
      exact h_score;
    exact iSup_le h_score_le;
  refine' ⟨ s, _, hs ⟩;
  refine' le_antisymm _ _;
  · refine' le_trans h_score _;
    rw [ boundedGameValue_eq_twoStep hB hB' ];
  · exact ciInf_le_of_le ⟨ 0, Set.forall_mem_range.mpr fun _ => zero_le _ ⟩ s ( le_rfl )

def f3 (x : ℝ) := x^2 * (x - 2)

lemma f3_mono : StrictMonoOn f3 (Set.Ici 2) := by
  exact fun x hx y hy hxy => mul_lt_mul'' ( by nlinarith [ Set.mem_Ici.mp hx, Set.mem_Ici.mp hy ] ) ( by nlinarith [ Set.mem_Ici.mp hx, Set.mem_Ici.mp hy ] ) ( by nlinarith [ Set.mem_Ici.mp hx, Set.mem_Ici.mp hy ] ) ( by nlinarith [ Set.mem_Ici.mp hx, Set.mem_Ici.mp hy ] )

lemma exists_root_f3 {B : ℝ} (hB : 2 + Real.sqrt 5 < B) (hB' : B ≤ 9) :
    ∃ x, 2 < x ∧ x ≤ 3 ∧ f3 x = B := by
      -- By the Intermediate Value Theorem, since $f_3$ is continuous and strictly increasing on $[2, \infty)$, and $f_3(2) < B \leq f_3(3)$, there exists a unique $x \in [2, 3]$ such that $f_3(x) = B$.
      have h_ivt : ∃ x ∈ Set.Icc 2 3, f3 x = B := by
        apply_rules [ intermediate_value_Icc ] <;> norm_num;
        · exact Continuous.continuousOn ( by exact Continuous.mul ( continuous_pow 2 ) ( continuous_id.sub continuous_const ) );
        · -- Since $f3(2) = 0$ and $f3(3) = 9$, we have $0 \leq B$ and $B \leq 9$.
          simp [f3];
          constructor <;> linarith [ Real.sqrt_nonneg 5 ];
      exact h_ivt.imp fun x hx => ⟨ lt_of_le_of_ne hx.1.1 ( by rintro rfl; norm_num [ f3 ] at hx; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ), hx.1.2, hx.2 ⟩

noncomputable def strategy3_seq (x B : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then x else if n = 1 then x * (x - 1) else B + (n - 2)

lemma strategy3_seq_nonneg (x B : ℝ) (hx : 1 ≤ x) (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ strategy3_seq x B n := by
      rcases n with ( _ | _ | n ) <;> simp +arith +decide [ *, strategy3_seq ];
      · -- Since $x \geq 1$, we have $0 \leq x$.
        exact le_trans (by norm_num) hx;
      · -- Since $x \geq 1$, both $x$ and $x - 1$ are non-negative, so their product is non-negative.
        apply mul_nonneg; exact le_trans (by norm_num) hx; exact sub_nonneg_of_le hx;
      · -- Since $B \geq 0$ and $n \geq 0$, their sum $B + n$ is also non-negative.
        apply add_nonneg hB (Nat.cast_nonneg n)

lemma strategy3_seq_mono (x B : ℝ) (hx : 2 < x) (hxB : x^2 * (x - 2) = B)
    (h_mono_cond : x^2 - 3*x + 1 ≥ 0) :
    Monotone (strategy3_seq x B) := by
      -- For n ≥ 2, the sequence is strictly increasing because each term is larger than the previous one.
      have h_mono_ge_two : ∀ n ≥ 2, strategy3_seq x B n ≥ strategy3_seq x B (n - 1) := by
        intros n hn_ge_two
        simp [strategy3_seq];
        rcases n with ( _ | _ | _ | n ) <;> norm_num at * ; nlinarith;
        split_ifs <;> linarith;
      -- For the case when n is 0 or 1, we need to check the first two terms.
      have h_mono_zero_one : strategy3_seq x B 0 ≤ strategy3_seq x B 1 := by
        unfold strategy3_seq; norm_num; nlinarith;
      refine' monotone_nat_of_le_succ fun n => _;
      exact if hn : n = 0 then by aesop else h_mono_ge_two _ ( Nat.succ_le_succ ( Nat.pos_of_ne_zero hn ) )

lemma strategy3_seq_hits (x B : ℝ) (hB : 1 ≤ B) (y : ℝ) (hy : 1 ≤ y) :
    ∃ n, y ≤ strategy3_seq x B n := by
      -- Since $B \geq 1$, we can choose $n$ such that $B + n \geq y$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, B + n ≥ y := by
        exact ⟨ ⌈y - B⌉₊, by linarith [ Nat.le_ceil ( y - B ) ] ⟩;
      use n + 2;
      -- By definition of `strategy3_seq`, we have `strategy3_seq x B (n + 2) = B + (n + 2) * (B - x) / (2 * B - 1)`.
      simp [strategy3_seq];
      -- Since $B + n \geq y$ by hypothesis, we can conclude that $y \leq B + n$.
      exact hn

lemma x_mono_cond_of_B {x B : ℝ} (hx : 2 < x) (hxB : x^2 * (x - 2) = B) (hB : 2 + Real.sqrt 5 < B) :
    x^2 - 3*x + 1 ≥ 0 := by
      nlinarith [ sq_nonneg ( x - ( 3 + Real.sqrt 5 ) / 2 ), Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

noncomputable def strategy3 (x B : ℝ)
    (hx : 2 < x)
    (hB : 2 + Real.sqrt 5 < B)
    (hxB : x^2 * (x - 2) = B) : Strategy :=
  { x := strategy3_seq x B
    nonneg := by
      apply strategy3_seq_nonneg
      · linarith
      · linarith [Real.sqrt_nonneg 5]
    one_le := by
      dsimp [strategy3_seq]
      linarith
    mono := by
      apply strategy3_seq_mono x B hx hxB
      apply x_mono_cond_of_B hx hxB hB
    hits := by
      apply strategy3_seq_hits
      linarith [Real.sqrt_nonneg 5] }

noncomputable def MaxReach (W : ℝ) : ℕ → ℝ
| 0 => W
| 1 => W^2 - W
| (n + 2) => W * MaxReach W (n + 1) - W * MaxReach W n

lemma MaxReach_0 (W : ℝ) : MaxReach W 0 = W := rfl
lemma MaxReach_1 (W : ℝ) : MaxReach W 1 = W^2 - W := rfl
lemma MaxReach_2 (W : ℝ) : MaxReach W 2 = W^3 - 2*W^2 := by
  rw [MaxReach, MaxReach_1, MaxReach_0]
  ring
lemma MaxReach_3 (W : ℝ) : MaxReach W 3 = W^4 - 3*W^3 + W^2 := by
  rw [MaxReach, MaxReach_2, MaxReach_1]
  ring

lemma MaxReach_sum (W : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), MaxReach W i = W * MaxReach W n := by
  induction' n with n ih
  · rw [Finset.sum_range_succ, Finset.sum_range_one, MaxReach_0, MaxReach_1]
    ring
  · rw [Finset.sum_range_succ, ih]
    rw [MaxReach]
    ring

lemma strategy3_boundedScore_le {x B : ℝ}
    (hx : 2 < x)
    (hB : 2 + Real.sqrt 5 < B)
    (hxB : x^2 * (x - 2) = B) :
    boundedWorstCaseScore (strategy3 x B hx hB hxB) B ≤ ENNReal.ofReal x := by
      -- By definition of boundedWorstCaseScore, we need to show that for any y in [1, B], the score is at most x.
      have h_score_le_x : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, score (strategy3 x B hx hB hxB) ⟨y.val, y.property.1⟩ ≤ ENNReal.ofReal x := by
        intro y
        obtain ⟨n, hn⟩ : ∃ n, y.val ≤ strategy3_seq x B n ∧ ∀ m < n, strategy3_seq x B m < y.val := by
          have h_exists_n : ∃ n, y.val ≤ strategy3_seq x B n := by
            exact strategy3_seq_hits x B ( by linarith [ y.2.1, y.2.2, Real.sqrt_nonneg 5 ] ) y.1 y.2.1;
          exact ⟨ Nat.find h_exists_n, Nat.find_spec h_exists_n, fun m mn => not_le.1 fun contra => Nat.find_min h_exists_n mn contra ⟩;
        -- By definition of `score`, we need to show that $\sum_{i=0}^{n} x_i \leq x \cdot y$.
        have h_sum_le_xy : ∑ i ∈ Finset.range (n + 1), strategy3_seq x B i ≤ x * y.val := by
          rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range_succ', strategy3_seq ] at *;
          · nlinarith [ y.2.1 ];
          · nlinarith [ y.2.1, y.2.2 ];
          · have := hn.2 0; have := hn.2 1; have := hn.2 ( n + 1 ) ; norm_num at *;
            rcases n with ( _ | n ) <;> norm_num [ Finset.sum_add_distrib ] at *;
            · nlinarith [ sq_nonneg ( x - 2 ), Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
            · bound;
        -- By definition of `score`, we have `score (strategy3 x B hx hB hxB) ⟨y.val, y.property.1⟩ = ENNReal.ofReal ((∑ i ∈ Finset.range (n + 1), strategy3_seq x B i) / y.val)`.
        have h_score_def : score (strategy3 x B hx hB hxB) ⟨y.val, y.property.1⟩ = ENNReal.ofReal ((∑ i ∈ Finset.range (n + 1), strategy3_seq x B i) / y.val) := by
          -- By definition of `score`, we have `score (strategy3 x B hx hB hxB) ⟨y.val, y.property.1⟩ = ENNReal.ofReal ((∑ i ∈ Finset.range (n + 1), strategy3_seq x B i) / y.val)`.
          simp [score, hitIndex];
          rw [ show Nat.find ( strategy3 x B hx hB hxB |> Strategy.hits <| y.2.1 ) = n from _ ];
          · rfl;
          · rw [ Nat.find_eq_iff ] ; aesop;
        exact h_score_def ▸ ENNReal.ofReal_le_ofReal ( by rw [ div_le_iff₀ ] <;> nlinarith [ y.2.1 ] );
      exact iSup_le fun y => h_score_le_x y

lemma partialSum_le_x_mul_xk {s : Strategy} {B x : ℝ} {k : ℕ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 0 < x) (hk : s.x k < B) :
    partialSum s (k + 1) ≤ x * s.x k := by
  -- We want to show S_{k+1} <= x * s.x k.
  -- Assume for contradiction S_{k+1} > x * s.x k.
  -- Then there exists epsilon > 0 such that S_{k+1} > x * (s.x k + epsilon).
  -- We can pick y in (s.x k, s.x k + epsilon) such that y < B.
  -- Then hitIndex s y >= k + 1.
  -- So score s y >= S_{k+1} / y > x * (s.x k + epsilon) / y > x.
  -- This contradicts h_sup.
  apply le_of_forall_pos_le_add
  intro ε hε
  by_cases h_cond : x * s.x k < partialSum s (k + 1)
  · -- If the inequality is strict in the other direction, we can find a contradiction.
    -- But we are proving <=.
    -- Actually, let's just prove it by contradiction directly.
    -- Let $\delta = \text{partialSum } s (k+1) - x \cdot s.x_k$.
    set δ := partialSum s (k + 1) - x * s.x k with hδ_def
    have hδ_pos : 0 < δ := by
      exact sub_pos_of_lt h_cond;
    -- Choose $y$ such that $s.x_k < y < \min(B, s.x_k + \delta/x)$.
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y, s.x k < y ∧ y < min B (s.x k + δ / x) := by
      exact exists_between <| lt_min hk <| lt_add_of_pos_right _ <| div_pos hδ_pos hx;
    -- Since $y > s.x_k$, the hit index for $y$ is at least $k+1$.
    have h_hit_index : hitIndex s ⟨y, by
      linarith [ s.one_le, show 1 ≤ s.x k from Nat.recOn k ( by linarith [ s.one_le ] ) fun n ihn => by linarith [ s.mono n.le_succ ] ]⟩ ≥ k + 1 := by
      all_goals generalize_proofs at *;
      contrapose! hy₁;
      exact le_trans ( Nat.find_spec ( s.hits ‹_› ) ) ( s.mono ( Nat.le_of_lt_succ hy₁ ) )
    generalize_proofs at *;
    -- Thus, the score for $y$ is at least $\frac{\text{partialSum } s (k+1)}{y}$.
    have h_score_ge : score s ⟨y, by
      linarith⟩ ≥ ENNReal.ofReal ((partialSum s (k + 1)) / y) := by
      all_goals generalize_proofs at *;
      refine' ENNReal.ofReal_le_ofReal _;
      gcongr;
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => s.nonneg _
    generalize_proofs at *;
    -- We have $\frac{\text{partialSum } s (k+1)}{y} > \frac{x \cdot s.x_k + \delta}{s.x_k + \delta/x} = x$.
    have h_score_gt_x : ENNReal.ofReal ((partialSum s (k + 1)) / y) > ENNReal.ofReal x := by
      simp +zetaDelta at *;
      rw [ ENNReal.ofReal_lt_ofReal_iff ] <;> nlinarith [ mul_div_cancel₀ ( partialSum s ( k + 1 ) - x * s.x k ) hx.ne', mul_div_cancel₀ ( partialSum s ( k + 1 ) ) ( by linarith : y ≠ 0 ) ];
    simp +zetaDelta at *;
    exact False.elim <| h_sup.not_le <| le_trans h_score_gt_x.le <| le_trans h_score_ge <| le_iSup_of_le ⟨ y, by linarith, by linarith ⟩ <| by aesop;
  · -- If x * s.x k >= partialSum s (k + 1), then we are done.
    push_neg at h_cond
    linarith

lemma x0_lt_of_boundedWorstCaseScore_lt {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 1 ≤ x) (hB : 1 ≤ B) :
    s.x 0 < x := by
      contrapose! h_sup;
      refine' le_trans _ ( le_ciSup _ ⟨ 1, by norm_num, by linarith ⟩ );
      · refine' ENNReal.ofReal_le_ofReal _;
        rw [ le_div_iff₀ ] <;> norm_num;
        exact le_trans h_sup ( Finset.single_le_sum ( fun i _ => s.nonneg i ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) );
      · bound

lemma x_succ_le_of_boundedWorstCaseScore_lt {s : Strategy} {B x : ℝ} {k : ℕ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 0 < x) (hk : s.x k < B) :
    s.x (k + 1) ≤ x * s.x k - partialSum s k := by
      -- By definition of partial sum, we have partialSum s (k + 1) = partialSum s k + s.x (k + 1).
      have h_partialSum_succ : partialSum s (k + 1) = partialSum s k + s.x (k + 1) := by
        -- By definition of partial sum, we can split the sum into the sum up to k and the (k+1)th term.
        simp [partialSum, Finset.sum_range_succ];
      have h_partialSum_le : partialSum s (k + 1) ≤ x * s.x k := by
        apply partialSum_le_x_mul_xk h_sup hx hk;
      linarith

lemma s_x_1_le {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) :
    s.x 1 ≤ (x - 1) * s.x 0 := by
  have h_sum : partialSum s 1 ≤ x * s.x 0 :=
    partialSum_le_x_mul_xk h_sup (by linarith) h_x0
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_one] at h_sum
  linarith

lemma s_x_2_le {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) :
    s.x 2 ≤ (x - 1) * s.x 1 - s.x 0 := by
  have h_sum : partialSum s 2 ≤ x * s.x 1 :=
    partialSum_le_x_mul_xk h_sup (by linarith) h_x1
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h_sum
  linarith

lemma s_x_3_le {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) :
    s.x 3 ≤ (x - 1) * s.x 2 - s.x 1 - s.x 0 := by
  have h_sum : partialSum s 3 ≤ x * s.x 2 :=
    partialSum_le_x_mul_xk h_sup (by linarith) h_x2
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h_sum
  linarith

lemma s_x_4_le {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) (h_x3 : s.x 3 < B) :
    s.x 4 ≤ (x - 1) * s.x 3 - s.x 2 - s.x 1 - s.x 0 := by
  have h_sum : partialSum s 4 ≤ x * s.x 3 :=
    partialSum_le_x_mul_xk h_sup (by linarith) h_x3
  rw [partialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h_sum
  linarith

noncomputable def P (x : ℝ) : ℕ → ℝ
| 0 => 1
| 1 => x - 1
| n + 2 => x * P x (n + 1) - x * P x n

lemma P_0 (x : ℝ) : P x 0 = 1 := rfl
lemma P_1 (x : ℝ) : P x 1 = x - 1 := rfl
lemma P_2 (x : ℝ) : P x 2 = x^2 - 2*x := by
  rw [P, P_1, P_0]; ring
lemma P_3 (x : ℝ) : P x 3 = x^3 - 3*x^2 + x := by
  rw [P, P_2, P_1]; ring
lemma P_4 (x : ℝ) : P x 4 = x^4 - 4*x^3 + 3*x^2 := by
  rw [P, P_3, P_2]; ring

lemma P_4_nonpos {x : ℝ} (hx : 1 ≤ x) (hx3 : x ≤ 3) : P x 4 ≤ 0 := by
  -- Factorize the polynomial $P x 4$ as $x^2(x^2 - 4x + 3)$.
  have h_factor : P x 4 = x^2 * (x^2 - 4 * x + 3) := by
    exact P_4 x ▸ by ring;
  -- Since $x \in [1, 3]$, we know that $x^2 - 4x + 3 \leq 0$.
  have h_quad_nonpos : x^2 - 4 * x + 3 ≤ 0 := by
    nlinarith;
  -- Since $x^2$ is non-negative for $x \in [1, 3]$, and $x^2 - 4x + 3 \leq 0$, their product is non-positive.
  rw [h_factor]
  apply mul_nonpos_of_nonneg_of_nonpos
  apply pow_two_nonneg
  exact h_quad_nonpos

lemma s_x_4_upper_bound {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) (h_x3 : s.x 3 < B) :
    s.x 4 ≤ (x^3 - 3*x^2 + x) * s.x 1 - (x^2 - x) * s.x 0 := by
      have h_sub : s.x 4 ≤ (x - 1) * s.x 3 - s.x 2 - s.x 1 - s.x 0 := by
        convert s_x_4_le h_sup hx hB h_x0 h_x1 h_x2 h_x3 using 1;
      have h_sub2 : s.x 3 ≤ (x - 1) * s.x 2 - s.x 1 - s.x 0 := by
        apply s_x_3_le h_sup hx hB h_x0 h_x1 h_x2
      have h_sub1 : s.x 2 ≤ (x - 1) * s.x 1 - s.x 0 := by
        exact s_x_2_le h_sup hx hB h_x0 h_x1
      have h_sub0 : s.x 1 ≤ (x - 1) * s.x 0 := by
        exact s_x_1_le h_sup hx hB h_x0
      have h_sub3 : s.x 4 ≤ (x - 1) * ((x - 1) * s.x 2 - s.x 1 - s.x 0) - s.x 2 - s.x 1 - s.x 0 := by
        exact h_sub.trans ( by nlinarith )
      have h_sub4 : s.x 4 ≤ (x - 1) * ((x - 1) * ((x - 1) * s.x 1 - s.x 0) - s.x 1 - s.x 0) - ((x - 1) * s.x 1 - s.x 0) - s.x 1 - s.x 0 := by
        exact h_sub3.trans ( by nlinarith [ mul_le_mul_of_nonneg_left h_sub1 ( sub_nonneg.mpr hx.le ) ] )
      linarith [h_sub4]

lemma P_0_lt_B {x B : ℝ} (hx : 2.618 < x) (hxB : x^2 * (x - 2) = B) : P x 0 < B := by
  -- Since $P x 0 = 1$ and $B = x^2 * (x - 2)$, we need to show that $1 < x^2 * (x - 2)$.
  have h_P0_lt_B : 1 < x^2 * (x - 2) := by
    -- Since $x > 2.618$, we can calculate $x^2 * (x - 2)$ and show it is greater than 1.
    norm_num at hx ⊢
    nlinarith [sq_nonneg (x - 2)];
  -- Since $P x 0 = 1$ and $B = x^2 * (x - 2)$, we can directly use $h_P0_lt_B$ to conclude $1 < B$.
  rw [←hxB]
  exact h_P0_lt_B

lemma P_1_lt_B {x B : ℝ} (hx : 2.618 < x) (hxB : x^2 * (x - 2) = B) : P x 1 < B := by
  -- Substitute $P x 1 = x - 1$ into the inequality.
  have h_P1 : P x 1 = x - 1 := by
    -- By definition of $P$, we know that $P x 1 = x - 1$.
    apply P_1;
  nlinarith [ sq_nonneg ( x - 2 ) ]

lemma P_2_lt_B {x B : ℝ} (hx : 2 < x) (hxB : x^2 * (x - 2) = B) : P x 2 < B := by
  -- Substitute the definitions of $P x 2$ and $B$ into the inequality.
  have hP2_lt_B : x^2 - 2 * x < x^2 * (x - 2) := by
    -- Since $x > 2$, we can factor the inequality as $x^2(x - 2) - x(x - 2) > 0$, which simplifies to $(x - 2)(x^2 - x) > 0$.
    have h_factor : (x - 2) * (x^2 - x) > 0 := by
      -- Since $x > 2$, both $(x - 2)$ and $(x^2 - x)$ are positive.
      apply mul_pos; exact sub_pos.mpr hx; exact sub_pos.mpr (by nlinarith);
    linarith;
  -- Substitute the definitions of $P x 2$ and $B$ into the inequality to conclude.
  convert hP2_lt_B using 1;
  · -- By definition of $P$, we know that $P x 2 = x * P x 1 - x * P x 0$.
    have hP2_def : P x 2 = x * P x 1 - x * P x 0 := by
      rfl;
    rw [ hP2_def, P_1, P_0 ] ; ring;
  · -- By definition of $B$, we have $B = x^2 * (x - 2)$.
    rw [hxB]

lemma P_3_lt_B {x B : ℝ} (hx : 2 < x) (hxB : x^2 * (x - 2) = B) : P x 3 < B := by
  -- By definition of $P$, we know that $P 3 x = x^3 - 3x^2 + x$.
  have hP3_def : P x 3 = x^3 - 3 * x^2 + x := by
    -- By definition of $P$, we know that $P x 3 = x^3 - 3x^2 + x$ follows directly from the definition.
    rw [P_3];
  nlinarith [ sq_nonneg ( x - 2 ) ]

lemma s_x_3_le_P_3_mul_x0 {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) :
    s.x 3 ≤ P x 3 * s.x 0 := by
      -- By combining the inequalities from the partial sums and the definitions of P, we can conclude that s.x 3 ≤ P x 3 * s.x 0.
      have h_combined : s.x 3 ≤ (x - 1) * s.x 2 - s.x 1 - s.x 0 ∧ s.x 2 ≤ (x - 1) * s.x 1 - s.x 0 ∧ s.x 1 ≤ (x - 1) * s.x 0 := by
        refine' ⟨ _, _, _ ⟩;
        · apply s_x_3_le h_sup hx hB h_x0 h_x1 h_x2;
        · convert s_x_2_le h_sup hx hB h_x0 h_x1;
        · apply s_x_1_le h_sup hx hB h_x0;
      rw [ show P x 3 = x^3 - 3*x^2 + x by exact P_3 x ];
      nlinarith [ sq_nonneg ( x - 2 ), mul_le_mul_of_nonneg_left hx.le ( show 0 ≤ s.x 0 from s.nonneg 0 ) ]

lemma s_x_4_le_P_4_mul_x0 {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) (h_x3 : s.x 3 < B)
    (hP3 : 0 ≤ P x 3) :
    s.x 4 ≤ P x 4 * s.x 0 := by
      -- Since $s.x 0$ is non-negative and $P x 3$ is positive, we can apply the inequality $x_{n+2} \le x x_{n+1} - x s_{n+1}$ iteratively.
      have hp3_pos : 0 < P x 3 := by
        -- Since $x > 2$, we have $x^3 - 3x^2 + x > 0$.
        have h_pos : x^3 - 3 * x^2 + x > 0 := by
          by_contra h_neg;
          -- If $x \leq 3$, then $P x 3 = x^3 - 3x^2 + x \leq 0$, which contradicts $hP3$.
          have h_contra : x ≤ 3 := by
            nlinarith [ sq_nonneg ( x - 2 ) ];
          have h_contra : s.x 4 ≤ 0 := by
            have h_contra : s.x 4 ≤ (x^3 - 3*x^2 + x) * s.x 1 - (x^2 - x) * s.x 0 := by
              convert s_x_4_upper_bound h_sup hx hB h_x0 h_x1 h_x2 h_x3 using 1;
            exact h_contra.trans ( by nlinarith [ s.nonneg 0, s.nonneg 1, s.nonneg 2, s.nonneg 3, s.nonneg 4, mul_le_mul_of_nonneg_left ‹x ≤ 3› ( show 0 ≤ s.x 0 by linarith [ s.nonneg 0 ] ), mul_le_mul_of_nonneg_left ‹x ≤ 3› ( show 0 ≤ s.x 1 by linarith [ s.nonneg 1 ] ) ] );
          exact h_contra.not_lt <| lt_of_lt_of_le ( show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one <| s.one_le ) <| s.mono <| by norm_num;
        exact h_pos.trans_le ( by rw [ show P x 3 = x ^ 3 - 3 * x ^ 2 + x by exact P_3 x ] );
      have := s_x_4_upper_bound h_sup hx hB h_x0 h_x1 h_x2 h_x3;
      -- Substitute the upper bound for $s.x_1$ into the inequality.
      have h_sub : s.x 4 ≤ (x^3 - 3*x^2 + x) * ((x - 1)*s.x 0) - (x^2 - x)*s.x 0 := by
        refine le_trans this ?_;
        gcongr;
        · by_contra h_neg;
          exact hp3_pos.not_le ( by rw [ show P x 3 = x^3 - 3*x^2 + x by exact P_3 x ] ; nlinarith );
        · exact s_x_1_le h_sup hx hB h_x0;
      convert h_sub using 1 ; rw [ show P x 4 = x ^ 4 - 4 * x ^ 3 + 3 * x ^ 2 by exact P_4 x ] ; ring

lemma s_x_4_le_P_4_mul_x0_new {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) (h_x2 : s.x 2 < B) (h_x3 : s.x 3 < B)
    (hP3 : 0 ≤ P x 3) :
    s.x 4 ≤ P x 4 * s.x 0 := by
  have h4 := s_x_4_upper_bound h_sup hx hB h_x0 h_x1 h_x2 h_x3
  have h1 := s_x_1_le h_sup hx hB h_x0
  rw [P_3] at hP3
  calc s.x 4 ≤ (x^3 - 3*x^2 + x) * s.x 1 - (x^2 - x) * s.x 0 := h4
    _ ≤ (x^3 - 3*x^2 + x) * ((x - 1) * s.x 0) - (x^2 - x) * s.x 0 := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left h1 hP3
    _ = ((x^3 - 3*x^2 + x) * (x - 1) - (x^2 - x)) * s.x 0 := by ring
    _ = (x^4 - 4*x^3 + 3*x^2) * s.x 0 := by ring
    _ = P x 4 * s.x 0 := by rw [P_4]

lemma P_mul_x_le_B {x B : ℝ} (hx : 2 < x) (hx3 : x ≤ 3) (hxB : x^2 * (x - 2) = B)
    (hx_gold : x^2 - 3*x + 1 ≥ 0) :
    ∀ k ∈ ({0, 1, 2, 3} : Set ℕ), P x k * x ≤ B := by
      -- By calculating each P x k and multiplying by x, we can verify the inequalities.
      simp [P];
      -- By calculating each P x k and multiplying by x, we can verify the inequalities for each k.
      apply And.intro;
      · nlinarith [ sq_nonneg ( x - 2 ) ];
      · -- By simplifying, we can see that each of these inequalities holds for $x$ in the given range.
        apply And.intro;
        · nlinarith;
        · constructor <;> nlinarith [ mul_le_mul_of_nonneg_left hx3 ( sq_nonneg ( x - 2 ) ) ]

lemma s_x_2_le_P_2_mul_x0 {s : Strategy} {B x : ℝ}
    (h_sup : boundedWorstCaseScore s B < ENNReal.ofReal x)
    (hx : 2 < x) (hB : 1 ≤ B) (h_x0 : s.x 0 < B) (h_x1 : s.x 1 < B) :
    s.x 2 ≤ P x 2 * s.x 0 := by
  have h2 := s_x_2_le h_sup hx hB h_x0 h_x1
  have h1 := s_x_1_le h_sup hx hB h_x0
  calc s.x 2 ≤ (x - 1) * s.x 1 - s.x 0 := h2
    _ ≤ (x - 1) * ((x - 1) * s.x 0) - s.x 0 := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (x^2 - 2*x) * s.x 0 := by ring
    _ = P x 2 * s.x 0 := by rw [P_2]

lemma x_gt_phi2_of_B_gt {x B : ℝ} (hx : 2 < x) (hxB : x^2 * (x - 2) = B) (hB_gt : 2 + Real.sqrt 5 < B) :
    (3 + Real.sqrt 5) / 2 < x := by
      -- Since $f(x) = x^2(x - 2)$ is increasing for $x > 2$, and $f((3 + \sqrt{5})/2) = 2 + \sqrt{5}$, we have $x > (3 + \sqrt{5})/2$.
      have h_inc : StrictMonoOn (fun x : ℝ => x^2 * (x - 2)) (Set.Ioi 2) := by
        exact fun x hx y hy hxy => by norm_num at *; nlinarith [ mul_pos ( sub_pos.mpr hxy ) ( sub_pos.mpr hx ), mul_pos ( sub_pos.mpr hxy ) ( sub_pos.mpr hy ) ] ;
      exact h_inc.lt_iff_lt ( show 2 < ( 3 + Real.sqrt 5 ) / 2 by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( show 2 < x by linarith ) |>.1 ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] )

lemma boundedWorstCaseScore_ge_x {B x : ℝ} (s : Strategy)
    (hx : 2 < x) (hx3 : x ≤ 3) (hxB : x^2 * (x - 2) = B)
    (hB_gt : 2 + Real.sqrt 5 < B) :
    boundedWorstCaseScore s B ≥ ENNReal.ofReal x := by
      -- Since $x^2 - 3x + 1 \geq 0$, we have $x^2 - 3x + 1 \geq 0$.
      have h_poly_nonneg : x^2 - 3 * x + 1 ≥ 0 := by
        exact x_mono_cond_of_B hx hxB hB_gt;
      -- Since $x^2 - 3x + 1 \geq 0$, we have $P x 4 \leq 0$.
      have h_P4_nonpos : P x 4 ≤ 0 := by
        exact P_4_nonpos ( by linarith ) hx3;
      -- Since $P x 4 \leq 0$, we have $s.x 4 \leq 0$.
      have h_s_x4_nonpos : ∀ {s : Strategy}, boundedWorstCaseScore s B < ENNReal.ofReal x → s.x 4 ≤ 0 := by
        intros s hs
        have h_s_x4_le_P4_mul_x0 : s.x 4 ≤ P x 4 * s.x 0 := by
          apply s_x_4_le_P_4_mul_x0_new hs hx (by linarith [Real.sqrt_nonneg 5]) (by
          exact lt_of_lt_of_le ( x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ) ( by nlinarith [ Real.sqrt_nonneg 5 ] )) (by
          have := x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] );
          have := s_x_1_le hs hx ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ; nlinarith [ s.mono zero_le_one ] ;) (by
          have h_s_x2_lt_B : s.x 2 ≤ P x 2 * s.x 0 := by
            apply s_x_2_le_P_2_mul_x0 hs hx (by
            nlinarith [ Real.sqrt_nonneg 5 ]) (by
            exact lt_of_lt_of_le ( x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ) ( by nlinarith [ Real.sqrt_nonneg 5 ] )) (by
            have := x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] );
            have := s_x_1_le hs hx ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ; nlinarith [ s.mono zero_le_one ] ;);
          have h_P2_mul_x0_lt_B : P x 2 * s.x 0 < B := by
            have h_P2_mul_x0_lt_B : P x 2 * x ≤ B := by
              rw [ show P x 2 = x^2 - 2*x by
                    field_simp;
                    exact show P x 2 = x * ( x - 2 ) from by rw [ show P x 2 = x * P x 1 - x * P x 0 from rfl ] ; rw [ show P x 1 = x - 1 from rfl ] ; rw [ show P x 0 = 1 from rfl ] ; ring; ] ; nlinarith;
            have h_s_x0_lt_x : s.x 0 < x := by
              apply x0_lt_of_boundedWorstCaseScore_lt hs (by
              linarith) (by
              nlinarith [ Real.sqrt_nonneg 5 ]);
            have h_P2_mul_x0_lt_B : P x 2 * s.x 0 < P x 2 * x := by
              exact mul_lt_mul_of_pos_left h_s_x0_lt_x ( by rw [ show P x 2 = x^2 - 2*x from P_2 x ] ; nlinarith );
            linarith;
          linarith) (by
          have h_s_x3_lt_B : s.x 3 < B := by
            have h_s_x3_le_P3_mul_x0 : s.x 3 ≤ P x 3 * s.x 0 := by
              apply s_x_3_le_P_3_mul_x0 hs hx (by linarith [Real.sqrt_nonneg 5]) (by
              exact lt_of_lt_of_le ( x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ) ( by nlinarith [ Real.sqrt_nonneg 5 ] )) (by
              have := x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] );
              have := s_x_1_le hs hx ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ; nlinarith [ s.mono zero_le_one ] ;) (by
              have h_s_x2_lt_B : s.x 2 ≤ P x 2 * s.x 0 := by
                apply s_x_2_le_P_2_mul_x0 hs hx (by
                nlinarith [ Real.sqrt_nonneg 5 ]) (by
                exact lt_of_lt_of_le ( x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ) ( by nlinarith [ Real.sqrt_nonneg 5 ] )) (by
                have := x0_lt_of_boundedWorstCaseScore_lt hs ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5 ] );
                have := s_x_1_le hs hx ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ( by nlinarith [ Real.sqrt_nonneg 5 ] ) ; nlinarith [ s.mono zero_le_one ] ;);
              have h_P2_mul_x0_lt_B : P x 2 * s.x 0 < B := by
                have h_P2_mul_x0_lt_B : P x 2 * x ≤ B := by
                  rw [ show P x 2 = x^2 - 2*x by
                        field_simp;
                        exact show P x 2 = x * ( x - 2 ) from by rw [ show P x 2 = x * P x 1 - x * P x 0 from rfl ] ; rw [ show P x 1 = x - 1 from rfl ] ; rw [ show P x 0 = 1 from rfl ] ; ring; ] ; nlinarith;
                have h_s_x0_lt_x : s.x 0 < x := by
                  apply x0_lt_of_boundedWorstCaseScore_lt hs (by
                  linarith) (by
                  nlinarith [ Real.sqrt_nonneg 5 ]);
                have h_P2_mul_x0_lt_B : P x 2 * s.x 0 < P x 2 * x := by
                  exact mul_lt_mul_of_pos_left h_s_x0_lt_x ( by rw [ show P x 2 = x^2 - 2*x from P_2 x ] ; nlinarith );
                linarith;
              linarith)
            have h_P3_mul_x0_lt_B : P x 3 * s.x 0 < B := by
              have h_P3_mul_x0_lt_B : P x 3 * x ≤ B := by
                field_simp;
                rw [ P_3 ];
                nlinarith [ mul_le_mul_of_nonneg_left hx3 ( sq_nonneg ( x - 2 ) ) ];
              have h_s_x0_lt_x : s.x 0 < x := by
                apply x0_lt_of_boundedWorstCaseScore_lt hs (by linarith) (by linarith [Real.sqrt_nonneg 5]);
              have h_P3_pos : 0 < P x 3 := by
                rw [ show P x 3 = x^3 - 3*x^2 + x by
                      exact P_3 x ];
                nlinarith only [ hx, hx3, h_poly_nonneg, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), hB_gt, hxB ];
              nlinarith [ s.nonneg 0 ]
            linarith;
          exact h_s_x3_lt_B) (by
          rw [ show P x 3 = x^3 - 3*x^2 + x by exact P_3 x ] ; nlinarith [ sq_nonneg ( x - 2 ) ]);
        exact h_s_x4_le_P4_mul_x0.trans ( mul_nonpos_of_nonpos_of_nonneg h_P4_nonpos ( s.nonneg 0 ) );
      contrapose! h_s_x4_nonpos;
      use s;
      exact ⟨ h_s_x4_nonpos, by linarith [ s.nonneg 4, show 0 < s.x 4 from lt_of_lt_of_le ( show 0 < s.x 0 from lt_of_lt_of_le zero_lt_one ( s.one_le ) ) ( s.mono ( by norm_num ) ) ] ⟩

/- When `2 + √5 < B ≤ 9`, an optimal strategy can be 3-step:
    first pick some `x` with `x^2*(x-2)=B`, then `x*(x-1)`, then `B`. -/
theorem exists_optimalStrategy_threeStep
    {B : ℝ} (hB : 2 + Real.sqrt 5 < B) (hB' : B ≤ 9) :
    ∃ (x : ℝ) (s : Strategy),
      x^2 * (x - 2) = B ∧
      IsOptimalBounded B s ∧
      s.x 0 = x ∧
      s.x 1 = x * (x - 1) ∧
      s.x 2 = B := by
  obtain ⟨ x, hx ⟩ := exists_root_f3 hB hB';
  use x, strategy3 x B hx.left hB hx.right.right;
  refine' ⟨ hx.2.2, le_antisymm _ _, _, _, _ ⟩;
  · exact le_iInf fun s => le_trans ( strategy3_boundedScore_le hx.1 hB hx.2.2 ) ( boundedWorstCaseScore_ge_x s hx.1 hx.2.1 hx.2.2 hB );
  · exact ciInf_le ⟨ 0, Set.forall_mem_range.mpr fun s => zero_le _ ⟩ _;
  · exact rfl;
  · exact rfl;
  · exact show strategy3_seq x B 2 = B from by unfold strategy3_seq; norm_num;

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
## Sanity-check special cases (the first few breakpoints)
-/

theorem stepBreakpoint_zero : stepBreakpoint 0 = (1 : ℝ) := by
  -- By definition of `stepBreakpoint`, we have `stepBreakpoint 0 = (2 * Real.cos (Real.pi / 3)) ^ 1`.
  simp [stepBreakpoint]

theorem stepBreakpoint_one : stepBreakpoint 1 = (2 : ℝ) := by
  -- By definition of stepBreakpoint, we have stepBreakpoint 1 = (2 * Real.cos (Real.pi / 4))^2.
  simp [stepBreakpoint];
  -- Simplifying the expression inside the square: $(2 * (\sqrt{2} / 2))^2 = (\sqrt{2})^2 = 2$.
  ring_nf;
  -- By definition of square root, we know that $(\sqrt{2})^2 = 2$.
  norm_num

theorem stepBreakpoint_two : stepBreakpoint 2 = 2 + Real.sqrt 5 := by
  -- By definition of `stepBreakpoint`, we have `stepBreakpoint 2 = (2 * Real.cos (Real.pi / 5)) ^ 3`.
  simp [stepBreakpoint];
  grind

theorem stepBreakpoint_three : stepBreakpoint 3 = (9 : ℝ) := by
  -- By definition of `stepBreakpoint`, we have `stepBreakpoint 3 = (2 * Real.cos (Real.pi / 6)) ^ 4`.
  simp [stepBreakpoint];
  -- Simplify the expression inside the parentheses: $2 * (\sqrt{3} / 2) = \sqrt{3}$.
  ring_nf;
  -- We know that $(\sqrt{3})^2 = 3$, so squaring both sides gives $(\sqrt{3})^4 = 3^2 = 9$.
  norm_num [ show ( Real.sqrt 3 ) ^ 4 = ( Real.sqrt 3 ^ 2 ) ^ 2 by ring ]

/-!
## Closed form for `tightPoly` (Chebyshev / trig expression)
-/

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

/-!
## Existence of a step-count for each `B` (algorithmic "find n by comparing to breakpoints")
-/

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

/-!
## Solving for the optimal worst-case ratio `R` in the `n`-step regime
-/

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

/-!
## Optimal value and optimal strategy in the `n`-step regime
-/

/-- In the `n`-step regime, the bounded game value equals `R`, where `R` is the (bracketed) root
of `tightPoly n R = B`. -/
theorem boundedGameValue_eq_of_inStepRange
    {B : ℝ} {n : ℕ} (hn : 1 ≤ n) (hBn : InStepRange B n) :
    ∃ R : ℝ,
      ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧
      tightPoly n R = B ∧
      boundedGameValue B = ENNReal.ofReal R := by
  sorry

theorem sum_tightPoly_eq (k : ℕ) (R : ℝ) :
    ∑ i ∈ Finset.range (k + 1), tightPoly (i + 1) R = R * tightPoly k R := by
      induction k <;> simp_all +decide [ Finset.sum_range_succ ];
      · exact show R = R * 1 from by ring;
      · rw [ show tightPoly ( _ + 1 + 1 ) R = R * ( tightPoly ( _ + 1 ) R - tightPoly _ R ) from rfl ] ; ring

theorem tightPoly_pos_of_inStepRange
    {n k : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR_lo : ratioLower n ≤ R)
    (hR_hi : R ≤ ratioUpper n)
    (hk : k ≤ n) :
    0 < tightPoly k R := by
      -- Rewrite `R` as `R = 4 * (Real.cos θ)^2` for some `θ` in `[π/(n+3), π/(n+2)]`.
      obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : ℝ, Real.pi / (n + 3) ≤ θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ) ^ (2 : ℕ) := by
        unfold ratioLower ratioUpper at *;
        -- By the intermediate value theorem, since $R$ is between $4 \cos^2(\pi/(n+2))$ and $4 \cos^2(\pi/(n+3))$, there exists some $\theta \in [\pi/(n+3), \pi/(n+2)]$ such that $4 \cos^2(\theta) = R$.
        have h_ivt : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * Real.cos θ ^ 2 = R := by
          apply_rules [ intermediate_value_Icc' ] <;> norm_num;
          · gcongr ; norm_num;
          · exact Continuous.continuousOn ( by continuity );
          · aesop;
        aesop;
      rw [ hθ₂.2 ];
      rw [ tightPoly_eq_trig ];
      · refine' mul_pos ( pow_pos _ _ ) ( div_pos _ _ );
        · exact mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by rw [ div_le_iff₀ ] at hθ₁ <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ le_div_iff₀ ] at hθ₂ <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ );
        · refine' Real.sin_pos_of_pos_of_lt_pi _ _ <;> norm_num;
          · exact mul_pos ( by positivity ) ( lt_of_lt_of_le ( by positivity ) hθ₁ );
          · rw [ le_div_iff₀ ] at * <;> nlinarith [ Real.pi_pos, show ( k : ℝ ) ≤ n by norm_cast ];
        · exact Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ₁ ) ( lt_of_le_of_lt hθ₂.1 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) );
      · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ₁ ) ( lt_of_le_of_lt hθ₂.1 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) )

theorem tightPoly_mono_of_inStepRange
    {n k : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hR_lo : ratioLower n ≤ R)
    (hR_hi : R ≤ ratioUpper n)
    (hk : k < n) :
    tightPoly k R ≤ tightPoly (k + 1) R := by
      -- Let $\theta$ be such that $R = 4 \cos^2 \theta$ with $\theta \in [\pi/(n+3), \pi/(n+2)]$.
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi / (n + 2) ∧ R = 4 * (Real.cos θ)^2 := by
        unfold ratioLower ratioUpper at *;
        refine' ⟨ Real.arccos ( Real.sqrt ( R / 4 ) ), _, _, _ ⟩ <;> norm_num at *;
        · rw [ div_lt_one, Real.sqrt_lt' ] <;> nlinarith [ Real.cos_sq' ( Real.pi / ( n + 3 ) ), Real.sin_pos_of_pos_of_lt_pi ( show 0 < Real.pi / ( n + 3 ) from by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ];
        · -- Since $\cos(\theta)$ is decreasing in the interval $[0, \pi]$, we have $\cos(\pi / (n + 2)) \leq \sqrt{R} / 2$.
          have h_cos_le : Real.cos (Real.pi / (n + 2)) ≤ Real.sqrt R / 2 := by
            nlinarith [ Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 2 ) ) ] ), Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], show Real.pi / ( n + 2 ) ≤ Real.pi / 2 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ];
          contrapose! h_cos_le;
          rw [ ← Real.cos_arccos ( show -1 ≤ Real.sqrt R / 2 by linarith [ Real.sqrt_nonneg R ] ) ( show Real.sqrt R / 2 ≤ 1 by nlinarith [ Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 2 ) ) ] ), Real.cos_sq_le_one ( Real.pi / ( n + 3 ) ) ] ) ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith [ Real.pi_pos, Real.arccos_le_pi ( Real.sqrt R / 2 ) ] ) h_cos_le;
        · rw [ Real.cos_arccos ] <;> nlinarith [ Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 2 ) ) ] ), Real.cos_sq_le_one ( Real.pi / ( n + 2 ) ), Real.cos_sq_le_one ( Real.pi / ( n + 3 ) ) ];
      -- Using `tightPoly_eq_trig`, we can rewrite the inequality in terms of $\theta$.
      have h_ineq : (2 * Real.cos θ) ^ k * (Real.sin ((k + 1) * θ) / Real.sin θ) ≤ (2 * Real.cos θ) ^ (k + 1) * (Real.sin ((k + 2) * θ) / Real.sin θ) := by
        have h_ineq : Real.sin ((k + 1) * θ) ≤ 2 * Real.cos θ * Real.sin ((k + 2) * θ) := by
          -- Using the identity $2 \cos \theta \sin((k+2)\theta) = \sin((k+3)\theta) + \sin((k+1)\theta)$.
          have h_identity : 2 * Real.cos θ * Real.sin ((k + 2) * θ) = Real.sin ((k + 3) * θ) + Real.sin ((k + 1) * θ) := by
            rw [ show ( ( k : ℝ ) + 3 ) * θ = ( ( k : ℝ ) + 2 ) * θ + θ by ring, show ( ( k : ℝ ) + 1 ) * θ = ( ( k : ℝ ) + 2 ) * θ - θ by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;
          exact h_identity.symm ▸ le_add_of_nonneg_left ( Real.sin_nonneg_of_nonneg_of_le_pi ( by nlinarith ) ( by rw [ le_div_iff₀ ( by positivity ) ] at *; nlinarith [ Real.pi_pos, show ( k : ℝ ) + 2 ≤ n + 1 by norm_cast; linarith ] ) );
        convert mul_le_mul_of_nonneg_left h_ineq ( show 0 ≤ ( 2 * Real.cos θ ) ^ k / Real.sin θ by exact div_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by rw [ le_div_iff₀ <| by positivity ] at *; nlinarith [ Real.pi_pos ] ⟩ ) ) _ ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by rw [ le_div_iff₀ <| by positivity ] at *; nlinarith [ Real.pi_pos ] ⟩ ) ) using 1 <;> ring;
      convert h_ineq using 1 <;> push_cast [ hθ.2.2 ] <;> ring_nf;
      · convert tightPoly_eq_trig k θ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hθ.1 ( by rw [ le_div_iff₀ ] at * <;> nlinarith [ Real.pi_pos, ( by norm_cast : ( k :ℝ ) + 1 ≤ n ) ] ) ) ) using 1 ; ring_nf;
        push_cast; ring_nf;
      · convert tightPoly_eq_trig ( 1 + k ) θ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hθ.1 ( by rw [ le_div_iff₀ <| by positivity ] at *; nlinarith [ Real.pi_pos ] ) ) ) using 1 ; ring_nf;
        push_cast; ring_nf;

theorem ratioLower_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ ratioLower n := by
  -- Since $n \geq 1$, we have $\frac{\pi}{n+2} \leq \frac{\pi}{3}$.
  have h_pi_div_n2_le_pi_div_3 : Real.pi / (n + 2) ≤ Real.pi / 3 := by
    gcongr ; norm_cast ; linarith;
  -- Since $\cos$ is decreasing on $[0, \pi/2]$, we have $\cos(\pi/(n+2)) \geq \cos(\pi/3) = 1/2$.
  have h_cos_pi_div_n2_ge_cos_pi_div_3 : Real.cos (Real.pi / (n + 2)) ≥ Real.cos (Real.pi / 3) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) h_pi_div_n2_le_pi_div_3;
  norm_num [ ratioLower ] at * ; nlinarith [ Real.cos_sq' ( Real.pi / 3 ) ]

noncomputable def makeOptimalStrategy
    {n : ℕ} {R B : ℝ}
    (hn : 1 ≤ n)
    (hR_lo : ratioLower n ≤ R)
    (hR_hi : R ≤ ratioUpper n)
    (hB : tightPoly n R = B) :
    Strategy :=
  { x := fun k => if k < n then tightPoly (k + 1) R else B + (k - n + 1)
    nonneg := by
      intro k; split_ifs;
      · by_contra h_neg;
        exact h_neg <| le_of_lt <| tightPoly_pos_of_inStepRange hn hR_lo hR_hi <| by linarith;
      · -- Since $B = \text{tightPoly } n R$ and $\text{tightPoly } n R$ is positive for $n \geq 1$, we have $B > 0$.
        have hB_pos : 0 < B := by
          exact hB ▸ tightPoly_pos_of_inStepRange hn hR_lo hR_hi le_rfl;
        linarith [ show ( k : ℝ ) ≥ n by norm_cast; linarith ]
    one_le := by
      -- Since $n \geq 1$, we have $R \geq 1$ by $ratioLower_ge_one$.
      have hR_ge_one : 1 ≤ R := by
        exact le_trans ( ratioLower_ge_one n hn ) hR_lo;
      aesop
    mono := by
      refine' monotone_nat_of_le_succ _;
      intro k; split_ifs <;> try linarith;
      · apply_rules [ tightPoly_mono_of_inStepRange ];
      · cases lt_or_eq_of_le ( Nat.le_of_not_lt ‹¬k + 1 < n› ) <;> first | linarith | aesop;
      · norm_num
    hits := by
      exact fun { y } hy => ⟨ ⌊y - B⌋₊ + n, by rw [ if_neg ( by linarith [ Nat.lt_floor_add_one ( y - B ) ] ) ] ; push_cast; linarith [ Nat.lt_floor_add_one ( y - B ) ] ⟩ }

theorem partialSum_makeOptimalStrategy_eq
    {n : ℕ} {R B : ℝ}
    (hn : 1 ≤ n)
    (hR_lo : ratioLower n ≤ R)
    (hR_hi : R ≤ ratioUpper n)
    (hB : tightPoly n R = B)
    (k : ℕ) (hk : k < n) :
    partialSum (makeOptimalStrategy hn hR_lo hR_hi hB) k = R * tightPoly k R := by
      rw [ ← sum_tightPoly_eq ];
      exact Finset.sum_congr rfl fun i hi => if_pos <| by linarith [ Finset.mem_range.mp hi ] ;

theorem hitIndex_lt_n_of_le_B
    {n : ℕ} {R B : ℝ}
    (hn : 1 ≤ n)
    (hR_lo : ratioLower n ≤ R)
    (hR_hi : R ≤ ratioUpper n)
    (hB : tightPoly n R = B)
    (y : {y : ℝ // 1 ≤ y ∧ y ≤ B}) :
    hitIndex (makeOptimalStrategy hn hR_lo hR_hi hB) ⟨y.1, y.2.1⟩ < n := by
      refine' Nat.lt_of_le_of_lt ( Nat.find_min' _ _ ) _;
      exact n - 1;
      · unfold makeOptimalStrategy;
        grind;
      · exact Nat.pred_lt ( ne_bot_of_gt hn )

/- In the `n`-step regime, there exists an optimal strategy whose initial segment is
`p₁(R), p₂(R), …, pₙ(R)=B`. -/
theorem exists_optimalStrategy_tight_of_inStepRange
    {B : ℝ} {n : ℕ} (hn : 1 ≤ n) (hBn : InStepRange B n) :
    ∃ R : ℝ,
      ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧
      tightPoly n R = B ∧
      ∃ s : Strategy,
        IsOptimalBounded B s ∧
        StartsWithTightNSteps s n R B := by
  obtain ⟨ R, hR₁, hR₂, hR₃, hR₄ ⟩ := boundedGameValue_eq_of_inStepRange hn hBn;
  use R;
  refine' ⟨ hR₁, hR₂, hR₃, makeOptimalStrategy hn hR₁ hR₂ hR₃, _, _ ⟩;
  · -- By definition of `IsOptimalBounded`, we need to show that the bounded worst-case score of `s` is equal to the bounded game value.
    have h_eq : boundedWorstCaseScore (makeOptimalStrategy hn hR₁ hR₂ hR₃) B = boundedGameValue B := by
      have h_score_le_R : ∀ y : {y : ℝ // 1 ≤ y ∧ y ≤ B}, score (makeOptimalStrategy hn hR₁ hR₂ hR₃) ⟨y.1, y.2.1⟩ ≤ ENNReal.ofReal R := by
        intro y
        obtain ⟨k, hk⟩ : ∃ k : ℕ, hitIndex (makeOptimalStrategy hn hR₁ hR₂ hR₃) ⟨y.1, y.2.1⟩ = k ∧ k < n := by
          exact ⟨ _, rfl, hitIndex_lt_n_of_le_B hn hR₁ hR₂ hR₃ y ⟩;
        -- By definition of `partialSum`, we have `partialSum (makeOptimalStrategy hn hR₁ hR₂ hR₃) k = R * tightPoly k R`.
        have h_partialSum : partialSum (makeOptimalStrategy hn hR₁ hR₂ hR₃) k = R * tightPoly k R := by
          convert partialSum_makeOptimalStrategy_eq hn hR₁ hR₂ hR₃ k hk.2;
        -- By definition of `score`, we have `score (makeOptimalStrategy hn hR₁ hR₂ hR₃) ⟨y.1, y.2.1⟩ = ENNReal.ofReal ((R * tightPoly k R) / y.1)`.
        have h_score : score (makeOptimalStrategy hn hR₁ hR₂ hR₃) ⟨y.1, y.2.1⟩ = ENNReal.ofReal ((R * tightPoly k R) / y.1) := by
          unfold score; aesop;
        rcases k with ( _ | k ) <;> simp_all
        · exact ENNReal.ofReal_le_ofReal ( by rw [ show tightPoly 0 R = 1 by rfl ] ; rw [ mul_one ] ; exact div_le_self ( by linarith [ show 0 ≤ R by exact le_trans ( by exact mul_nonneg zero_le_four ( sq_nonneg _ ) ) hR₁ ] ) ( by linarith [ y.2.1 ] ) );
        · -- Since $k + 1 < n$, we have $tightPoly (k + 1) R < y.1$.
          have h_tightPoly_lt_y : tightPoly (k + 1) R < y.1 := by
            have h_tightPoly_lt_y : (makeOptimalStrategy hn hR₁ hR₂ hR₃).x k < y.1 := by
              have h_tightPoly_lt_y : (makeOptimalStrategy hn hR₁ hR₂ hR₃).x k < y.1 := by
                have h_hitIndex : hitIndex (makeOptimalStrategy hn hR₁ hR₂ hR₃) ⟨y.1, y.2.1⟩ = k + 1 := hk.left
                contrapose! h_hitIndex;
                exact ne_of_lt ( Nat.lt_succ_of_le ( Nat.find_min' _ h_hitIndex ) );
              exact h_tightPoly_lt_y;
            convert h_tightPoly_lt_y using 1;
            exact Eq.symm ( if_pos ( by linarith ) );
          refine' ENNReal.ofReal_le_ofReal _;
          rw [ div_le_iff₀ ] <;> nlinarith [ y.2.1, show 0 ≤ R by exact le_trans ( by exact mul_nonneg zero_le_four ( sq_nonneg _ ) ) hR₁ ];
      refine' le_antisymm _ _;
      · exact le_trans ( iSup_le fun y => h_score_le_R y ) ( by aesop );
      · refine' iInf_le _ _;
    exact h_eq;
  · refine' ⟨ _, _ ⟩;
    · intro k hk;
      exact if_pos ( by omega );
    · unfold makeOptimalStrategy; aesop;

/-!
## Combined "recipe" statement: for a given `B`, pick `n`, solve for `R`, then read off the guesses.
-/

/-- Full packaged statement for `B > 1`:
there is an `n` (the step-count), a unique `R` (the optimal worst-case ratio),
and an optimal strategy whose guesses start `p₁(R), p₂(R), …, pₙ(R)=B`. -/
theorem exists_optimalSolution_for_B
    {B : ℝ} (hB : 1 < B) :
    ∃ n : ℕ, 1 ≤ n ∧ InStepRange B n ∧
      (∃! R : ℝ, ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧ tightPoly n R = B) ∧
      ∃ R : ℝ,
        ratioLower n ≤ R ∧ R ≤ ratioUpper n ∧
        tightPoly n R = B ∧
        boundedGameValue B = ENNReal.ofReal R ∧
        ∃ s : Strategy, IsOptimalBounded B s ∧ StartsWithTightNSteps s n R B := by
  obtain ⟨ n, hn₁, hn₂ ⟩ := exists_stepCount_of_one_lt hB;
  refine' ⟨ n, hn₁, hn₂, existsUnique_ratio_of_inStepRange hn₁ hn₂, _ ⟩;
  -- Apply the existence of a step-count n and a unique R in the bracket.
  obtain ⟨R, hR₁, hR₂⟩ := existsUnique_ratio_of_inStepRange hn₁ hn₂
  obtain ⟨R', hR'₁, hR'₂⟩ := boundedGameValue_eq_of_inStepRange hn₁ hn₂
  obtain ⟨s, hs₁, hs₂⟩ := exists_optimalStrategy_tight_of_inStepRange hn₁ hn₂
  use R';
  grind

/-!
## Step-count `n(B)` and first guess `x(B)` as functions of `B`
-/

-- These names are assumed to exist from the previous framework:
-- `stepBreakpoint`, `InStepRange`, `ratioLower`, `ratioUpper`, `tightPoly`,
-- `exists_stepCount_of_one_lt`, `existsUnique_ratio_of_inStepRange`.

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

/-!
## The two limits
-/

open Topology

/-- `lim_{B→∞} B^{1/n(B)} = 2`. -/
theorem tendsto_growthBase_atTop :
    Filter.Tendsto growthBase Filter.atTop (𝓝 (2 : ℝ)) := by
  -- Let's choose any ε > 0. We need to find a B such that for all B' ≥ B, |growthBase B' - 2| < ε.
  have h_eps_delta : ∀ ε > 0, ∃ B : ℝ, ∀ B' ≥ B, |growthBase B' - 2| < ε := by
    -- By definition of $n(B)$, we know that $B_{n(B)-1} < B \leq B_{n(B)}$.
    have h_nB_bounds : ∀ B > 1, (2 * Real.cos (Real.pi / (nSteps B + 2))) ^ (nSteps B) < B ∧ B ≤ (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ (nSteps B + 1) := by
      intro B hB
      obtain ⟨hnB, hB_bounds⟩ := nSteps_spec hB;
      convert hB_bounds using 1;
      unfold InStepRange; norm_cast;
      unfold stepBreakpoint; rcases nSteps B with ( _ | _ | n ) <;> norm_num at *;
      grind;
    -- Taking the $n(B)$-th root of the bounds, we get $2 \cos(\pi/(n(B)+2)) < B^{1/n(B)} \leq (2 \cos(\pi/(n(B)+3)))^{(n(B)+1)/n(B)}$.
    have h_root_bounds : ∀ B > 1, 2 * Real.cos (Real.pi / (nSteps B + 2)) < Real.rpow B (1 / (nSteps B : ℝ)) ∧ Real.rpow B (1 / (nSteps B : ℝ)) ≤ (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ ((nSteps B + 1) / (nSteps B : ℝ)) := by
      intro B hB
      obtain ⟨h_left, h_right⟩ := h_nB_bounds B hB
      have h_root_left : 2 * Real.cos (Real.pi / (nSteps B + 2)) < Real.rpow B (1 / (nSteps B : ℝ)) := by
        contrapose! h_left;
        convert pow_le_pow_left₀ ( Real.rpow_nonneg ( by positivity ) _ ) h_left ( nSteps B ) using 1 ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ B ) ];
        rw [ inv_mul_cancel₀ ( Nat.cast_ne_zero.mpr <| by linarith [ nSteps_spec hB ] ), Real.rpow_one ]
      have h_root_right : Real.rpow B (1 / (nSteps B : ℝ)) ≤ (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ ((nSteps B + 1) / (nSteps B : ℝ)) := by
        have h_root_right : Real.rpow B (1 / (nSteps B : ℝ)) ≤ Real.rpow ((2 * Real.cos (Real.pi / (nSteps B + 3))) ^ (nSteps B + 1)) (1 / (nSteps B : ℝ)) := by
          exact Real.rpow_le_rpow ( by positivity ) h_right ( by positivity );
        norm_num +zetaDelta at *;
        convert h_root_right using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ⟩ ) ) ] ; push_cast ; ring_nf
      exact ⟨h_root_left, h_root_right⟩;
    -- As $B \to \infty$, $n(B) \to \infty$ as well, so we can apply the fact that $\cos(\pi/(n+2)) \to 1$ and $\cos(\pi/(n+3)) \to 1$.
    have h_cos_limit : Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 2))) Filter.atTop (nhds 2) ∧ Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 3))) Filter.atTop (nhds 2) := by
      exact ⟨ le_trans ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| by norm_num, le_trans ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) <| by norm_num ⟩;
    -- Since $n(B) \to \infty$ as $B \to \infty$, we can apply the fact that $\cos(\pi/(n+2)) \to 1$ and $\cos(\pi/(n+3)) \to 1$.
    have h_nB_inf : Filter.Tendsto (fun B : ℝ => nSteps B) Filter.atTop Filter.atTop := by
      refine' Filter.tendsto_atTop_atTop.mpr fun x => _;
      use ( 2 * Real.cos ( Real.pi / ( x + 3 ) ) ) ^ ( x + 1 ) + 1;
      intro a ha;
      by_cases ha1 : 1 < a;
      · have := nSteps_spec ha1;
        contrapose! ha;
        refine' lt_of_le_of_lt _ ( lt_add_of_pos_right _ zero_lt_one );
        refine' le_trans ( h_nB_bounds a ha1 |>.2 ) _;
        refine' le_trans _ ( pow_le_pow_left₀ _ _ _ );
        rotate_left;
        exact 2 * Real.cos ( Real.pi / ( nSteps a + 3 ) );
        · exact mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( nSteps a : ℝ ) ≥ 1 by norm_cast; linarith ], by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( nSteps a : ℝ ) ≥ 1 by norm_cast; linarith ] ⟩ );
        · exact mul_le_mul_of_nonneg_left ( Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( nSteps a : ℝ ) + 3 ≥ 3 by linarith, show ( x : ℝ ) + 3 ≥ 3 by linarith ] ) ( by gcongr ) ) zero_le_two;
        · exact pow_le_pow_right₀ ( by nlinarith [ show 1 ≤ 2 * Real.cos ( Real.pi / ( nSteps a + 3 ) ) from by nlinarith [ show Real.cos ( Real.pi / ( nSteps a + 3 ) ) ≥ 1 / 2 from by rw [ ← Real.cos_pi_div_three ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( nSteps a : ℝ ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ Real.pi ( by positivity : ( nSteps a + 3 : ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( nSteps a : ℝ ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ Real.pi ( by positivity : ( nSteps a + 3 : ℝ ) ≠ 0 ) ] ) ] ] ) ( by linarith );
      · linarith [ pow_pos ( show 0 < 2 * Real.cos ( Real.pi / ( x + 3 ) ) by exact mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by rw [ lt_div_iff₀ ] <;> nlinarith [ Real.pi_pos ], by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ⟩ ) ) ( x + 1 ) ];
    -- Applying the fact that the composition of continuous functions is continuous, we get the desired result.
    have h_cont : Filter.Tendsto (fun B : ℝ => (2 * Real.cos (Real.pi / (nSteps B + 3))) ^ ((nSteps B + 1) / (nSteps B : ℝ))) Filter.atTop (nhds 2) := by
      have h_cont : Filter.Tendsto (fun n : ℕ => (2 * Real.cos (Real.pi / (n + 3))) ^ ((n + 1) / (n : ℝ))) Filter.atTop (nhds 2) := by
        have h_exp_limit : Filter.Tendsto (fun n : ℕ => ((n + 1) / (n : ℝ))) Filter.atTop (nhds 1) := by
          norm_num [ add_div ];
          simpa using Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat );
        simpa using h_cos_limit.2.rpow h_exp_limit;
      exact h_cont.comp h_nB_inf;
    have h_squeeze : Filter.Tendsto (fun B : ℝ => Real.rpow B (1 / (nSteps B : ℝ))) Filter.atTop (nhds 2) := by
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' ( h_cos_limit.1.comp h_nB_inf ) h_cont _ _;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with B hB using le_of_lt ( h_root_bounds B hB |>.1 );
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with B hB using h_root_bounds B hB |>.2;
    exact fun ε ε_pos => by rcases Metric.tendsto_atTop.mp h_squeeze ε ε_pos with ⟨ B, hB ⟩ ; exact ⟨ B, fun B' hB' => by simpa [ growthBase ] using hB B' hB' ⟩ ;
  exact Metric.tendsto_atTop.mpr h_eps_delta

/-- `lim_{B→∞} x(B) = 4`. -/
theorem tendsto_firstGuess_atTop :
    Filter.Tendsto firstGuess Filter.atTop (𝓝 (4 : ℝ)) := by
  sorry
