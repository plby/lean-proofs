/-

This is a Lean formalization of a solution to MathOverflow question
508681:

https://mathoverflow.net/questions/508681/a-two-player-stochastic-game-fight-or-draw

The original question was asked by Nate River.

The solution here is by ChatGPT-5.4 Pro (from OpenAI).


The proof was formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Formalization of the optimal strategy and game value for the game described.

We define the constants `r` and `c`, and the functions `w`, `D`, and `g` as in the text.
We define the Bellman operator `C_r`.
We prove that `w` satisfies the Bellman equation (Lemma 3).
We prove that the Bellman equation has a unique uniformly bounded solution (Lemma 2).
We define `W_star` as the constant sequence of functions equal to `w` and prove it is the unique uniformly bounded solution.
We define `game_value` as the integral of `w` over [0, 1] and prove it equals `3 - 2 * sqrt 2`.
-/

import Mathlib

/-
Definitions of constants r and c from the text.
-/
noncomputable def r : Real := Real.sqrt 2 - 1

noncomputable def c : Real := 2 * r - 1

/-
Definitions of functions w, D, and g from the text.
-/
noncomputable def w (x : Real) : Real :=
  if x < r then c else 2 * x - 1

noncomputable def D (k : Nat) (x : Real) : Real :=
  if x < r then 2 * (x ^ (k + 1) / r ^ k) - 1 else 2 * x - 1

noncomputable def g (x : Real) : Real :=
  if x < r then -1 else (2 * x - 1 - r) / (1 - r)

/-
Definition of the operator C_r from the text.
-/
noncomputable def C_r (f : Real → Real) (x : Real) : Real :=
  x * ((1 - r) * g x + r * f x) + ∫ u in x..1, ((1 - r) * g u + r * f u)

/-
Lemma 3: The function w satisfies the Bellman equation w(x) = max(D_k(x), C_r w(x)) for all k and x in [0,1].
-/
theorem lemma_candidate (k : Nat) (x : Real) (hx : 0 ≤ x ∧ x ≤ 1) :
  w x = max (D k x) (C_r w x) := by
    unfold w D C_r;
    -- Let's simplify the integral expression for $C_r(w(x))$.
    have h_integral : ∫ u in x..1, ((1 - r) * g u + r * (if u < r then c else 2 * u - 1)) = if x < r then (∫ u in x..r, ((1 - r) * (-1) + r * c)) + (∫ u in r..1, ((1 - r) * ((2 * u - 1 - r) / (1 - r)) + r * (2 * u - 1))) else (∫ u in x..1, ((1 - r) * ((2 * u - 1 - r) / (1 - r)) + r * (2 * u - 1))) := by
      split_ifs <;> simp_all +decide [ g ];
      · -- Split the integral into two parts: from $x$ to $r$ and from $r$ to $1$.
        have h_split : ∫ u in x..1, (if u < r then r - 1 else (1 - r) * ((2 * u - 1 - r) / (1 - r))) + (if u < r then r * c else r * (2 * u - 1)) = (∫ u in x..r, (if u < r then r - 1 else (1 - r) * ((2 * u - 1 - r) / (1 - r))) + (if u < r then r * c else r * (2 * u - 1))) + (∫ u in r..1, (if u < r then r - 1 else (1 - r) * ((2 * u - 1 - r) / (1 - r))) + (if u < r then r * c else r * (2 * u - 1))) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable ];
          · apply_rules [ Continuous.if, Continuous.add, Continuous.mul, continuous_id, continuous_const ];
            · erw [ frontier_Iio ] ; norm_num;
              grind;
            · erw [ frontier_Iio ] ; norm_num;
              exact Or.inl rfl;
          · apply_rules [ Continuous.if, Continuous.add, Continuous.mul, continuous_id, continuous_const ];
            · erw [ frontier_Iio ] ; norm_num;
              grind;
            · erw [ frontier_Iio ] ; norm_num;
              exact Or.inl rfl;
        rw [ h_split, intervalIntegral.integral_of_le, intervalIntegral.integral_of_le ] <;> try linarith [ show r ≤ 1 by exact sub_le_iff_le_add'.mpr <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ] ;
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => by rw [ if_pos hu.2, if_pos hu.2 ] ] ; rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; rw [ ← intervalIntegral.integral_of_le ( by linarith [ show r ≤ 1 by exact sub_le_iff_le_add'.mpr <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ] ) ] ; norm_num ; ring_nf;
        rw [ intervalIntegral.integral_of_le ( by linarith [ show r ≤ 1 by exact sub_le_iff_le_add'.mpr <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ] ), MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => by rw [ if_neg hu.1.not_gt, if_neg hu.1.not_gt ] ; ring;
      · refine' intervalIntegral.integral_congr fun u hu => _;
        split_ifs <;> linarith [ Set.mem_Icc.mp ( by rwa [ Set.uIcc_of_le ( by linarith ) ] at hu ) ];
    split_ifs at * <;> simp_all +decide [ mul_div_cancel₀, show ( 1 - r ) ≠ 0 from by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ];
    · rw [ max_eq_right ];
      · unfold r c g; norm_num [ mul_comm ] ; ring_nf;
        rw [ if_pos ‹_› ] ; norm_num [ pow_three ] ; ring_nf;
        rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
      · unfold g c; norm_num [ mul_comm ] ; ring_nf; norm_num;
        rw [ if_pos ‹_› ] ; ring_nf;
        norm_num [ show r = Real.sqrt 2 - 1 by rfl ] at *;
        -- Simplify the inequality.
        have h_simp : x ^ k * ((Real.sqrt 2 - 1) ^ k)⁻¹ ≤ 1 := by
          exact div_le_one_of_le₀ ( pow_le_pow_left₀ ( by linarith ) ( by linarith ) _ ) ( pow_nonneg ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) _ );
        nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_pos ( Real.sqrt_pos.mpr zero_lt_two ) 3 ];
    · rw [ if_neg ( by linarith ) ] ; ring_nf; norm_num [ mul_comm ] ; ring_nf ; norm_num [ show r = Real.sqrt 2 - 1 from rfl ] ;
      unfold g; split_ifs ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
      rw [ show r = Real.sqrt 2 - 1 by rfl ] at *;
      nlinarith [ mul_div_cancel₀ ( 2 * x - 1 - ( Real.sqrt 2 - 1 ) ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] : ( 1 - ( Real.sqrt 2 - 1 ) ) ≠ 0 ), Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), mul_le_mul_of_nonneg_left ‹Real.sqrt 2 - 1 ≤ x› ( Real.sqrt_nonneg 2 ) ]

/-
Definitions of is_solution and is_uniformly_bounded from Lemma 2.
-/
def is_solution (W : ℕ → ℝ → ℝ) : Prop :=
  ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = max (D k x) (C_r (W (k + 1)) x)

def is_uniformly_bounded (W : ℕ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ k x, 0 ≤ x ∧ x ≤ 1 → |W k x| ≤ M

/-
Lemma: The operator C_r satisfies a contraction property: if |f - h| <= delta, then |C_r f - C_r h| <= r * delta.
-/
theorem C_r_contraction (f h : ℝ → ℝ) (δ : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (hh : IntervalIntegrable h MeasureTheory.volume 0 1)
    (h_diff : ∀ x, 0 ≤ x ∧ x ≤ 1 → |f x - h x| ≤ δ) :
    ∀ x, 0 ≤ x ∧ x ≤ 1 → |C_r f x - C_r h x| ≤ r * δ := by
      intro x hx;
      -- By definition of $C_r$, we have:
      have h_def : C_r f x - C_r h x = r * x * (f x - h x) + r * ∫ u in x..1, (f u - h u) := by
        unfold C_r; ring_nf;
        rw [ ← intervalIntegral.integral_sub ] ; rw [ ← intervalIntegral.integral_const_mul ] ; congr ; ext u ; ring;
        · -- Since $g$ is piecewise linear, it is integrable on $[x, 1]$.
          have hg_integrable : IntervalIntegrable g MeasureTheory.MeasureSpace.volume x 1 := by
            apply_rules [ Monotone.intervalIntegrable ];
            intro x y hxy;
            unfold g; split_ifs <;> try linarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ; ; ring_nf ;
            · nlinarith [ inv_pos.mpr ( show 0 < 1 - r by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ), mul_inv_cancel₀ ( show ( 1 - r ) ≠ 0 by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 by rfl ];
            · exact div_le_div_of_nonneg_right ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 from rfl ] );
          have hf_integrable : IntervalIntegrable f MeasureTheory.MeasureSpace.volume x 1 := by
            apply_rules [ hf.mono_set, Set.Icc_subset_Icc ] <;> aesop;
          exact IntervalIntegrable.add ( IntervalIntegrable.add ( hg_integrable.const_mul _ |> IntervalIntegrable.neg ) ( hf_integrable.const_mul _ ) ) hg_integrable;
        · -- Since $g$ is piecewise linear, it is integrable on any interval.
          have hg_integrable : IntervalIntegrable g MeasureTheory.MeasureSpace.volume 0 1 := by
            apply_rules [ Monotone.intervalIntegrable ];
            intro x y hxy;
            unfold g; split_ifs <;> try linarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ; ; ring_nf ;
            · nlinarith [ inv_pos.mpr ( show 0 < 1 - r by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ), mul_inv_cancel₀ ( show ( 1 - r ) ≠ 0 by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 by rfl ];
            · exact div_le_div_of_nonneg_right ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 from rfl ] );
          have hg_integrable : IntervalIntegrable (fun u => g u) MeasureTheory.MeasureSpace.volume x 1 := by
            apply_rules [ hg_integrable.mono_set, Set.Icc_subset_Icc ] <;> aesop;
          have hg_integrable : IntervalIntegrable (fun u => h u) MeasureTheory.MeasureSpace.volume x 1 := by
            apply_rules [ hh.mono_set, Set.Icc_subset_Icc ] <;> aesop;
          exact IntervalIntegrable.add ( IntervalIntegrable.add ( IntervalIntegrable.neg ( IntervalIntegrable.const_mul ‹_› _ ) ) ( IntervalIntegrable.const_mul hg_integrable _ ) ) ‹_›;
      -- Using the bound |f(u) - h(u)| <= delta, we get:
      have h_integral_bound : |∫ u in x..1, (f u - h u)| ≤ δ * (1 - x) := by
        rw [ intervalIntegral.integral_of_le hx.2 ];
        refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
        exacts [ fun _ => δ, Filter.Eventually.of_forall fun _ => norm_nonneg _, Continuous.integrableOn_Ioc ( by continuity ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun u hu => h_diff u ⟨ by linarith [ hu.1 ], by linarith [ hu.2 ] ⟩, by simp +decide [ mul_comm, hx.2 ] ];
      rw [ abs_le ];
      constructor <;> nlinarith [ abs_le.mp ( h_diff x hx ), abs_le.mp h_integral_bound, show 0 ≤ r by exact sub_nonneg.mpr <| Real.le_sqrt_of_sq_le <| by norm_num, mul_nonneg ( show 0 ≤ r by exact sub_nonneg.mpr <| Real.le_sqrt_of_sq_le <| by norm_num ) hx.1 ]

/-
Lemma: If the difference between W1 and W2 at step k+1 is bounded by D_val, then at step k it is bounded by r * D_val.
-/
theorem lemma_uniqueness_step (W1 W2 : ℕ → ℝ → ℝ) (k : ℕ) (D_val : ℝ)
    (h1 : is_solution W1) (h2 : is_solution W2)
    (hW1_int : IntervalIntegrable (W1 (k + 1)) MeasureTheory.volume 0 1)
    (hW2_int : IntervalIntegrable (W2 (k + 1)) MeasureTheory.volume 0 1)
    (h_bound : ∀ x, 0 ≤ x ∧ x ≤ 1 → |W1 (k + 1) x - W2 (k + 1) x| ≤ D_val) :
    ∀ x, 0 ≤ x ∧ x ≤ 1 → |W1 k x - W2 k x| ≤ r * D_val := by
      intro x hx
      have h_diff : abs (W1 k x - W2 k x) ≤ abs (C_r (W1 (k + 1)) x - C_r (W2 (k + 1)) x) := by
        rw [ h1 k x hx, h2 k x hx ] ; cases max_cases ( D k x ) ( C_r ( W1 ( k + 1 ) ) x ) <;> cases max_cases ( D k x ) ( C_r ( W2 ( k + 1 ) ) x ) <;> cases abs_cases ( C_r ( W1 ( k + 1 ) ) x - C_r ( W2 ( k + 1 ) ) x ) <;> cases abs_cases ( Max.max ( D k x ) ( C_r ( W1 ( k + 1 ) ) x ) - Max.max ( D k x ) ( C_r ( W2 ( k + 1 ) ) x ) ) <;> linarith;
      generalize_proofs at *; (
      exact h_diff.trans ( C_r_contraction _ _ _ hW1_int hW2_int h_bound x hx ) |> le_trans <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 from rfl ] ;)

/-
Lemma 2: The Bellman equation has at most one uniformly bounded solution (assuming integrability).
-/
theorem lemma_uniqueness (W1 W2 : ℕ → ℝ → ℝ) (h1 : is_solution W1) (h2 : is_solution W2)
    (hb1 : is_uniformly_bounded W1) (hb2 : is_uniformly_bounded W2)
    (hW1_int : ∀ k, IntervalIntegrable (W1 k) MeasureTheory.volume 0 1)
    (hW2_int : ∀ k, IntervalIntegrable (W2 k) MeasureTheory.volume 0 1) :
    ∀ k x, 0 ≤ x ∧ x ≤ 1 → W1 k x = W2 k x := by
      -- By induction on $k$, we can show that $|W1_k(x) - W2_k(x)| \leq r^m D$ for all $x \in [0,1]$ and $m \geq 0$.
      have h_induction : ∀ k m : ℕ, ∀ x : ℝ, (0 ≤ x ∧ x ≤ 1 → abs (W1 k x - W2 k x) ≤ r ^ m * (hb1.choose + hb2.choose)) := by
        intro k m x hx
        induction' m with m ih generalizing k x;
        · simpa using le_trans ( abs_sub _ _ ) ( add_le_add ( hb1.choose_spec k x hx ) ( hb2.choose_spec k x hx ) );
        · exact le_trans ( lemma_uniqueness_step W1 W2 k ( r ^ m * ( hb1.choose + hb2.choose ) ) h1 h2 ( hW1_int _ ) ( hW2_int _ ) ( fun x hx => ih _ _ hx ) x hx ) ( by rw [ pow_succ', mul_assoc ] );
      -- Since $r < 1$, we have $r^m \to 0$ as $m \to \infty$.
      have h_r_pow_zero : Filter.Tendsto (fun m => r ^ m * (hb1.choose + hb2.choose)) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( show 0 ≤ r by exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num ) <| show r < 1 by rw [ r ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) tendsto_const_nhds;
      exact fun k x hx => by simpa [ sub_eq_zero ] using le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_r_pow_zero fun m => h_induction k m x hx ) ( abs_nonneg _ ) ;

/-
The function w is uniformly bounded.
-/
theorem w_is_uniformly_bounded : is_uniformly_bounded (fun _ => w) := by
  -- Choose M = 1 which bounds the absolute value of any x in [0,1] since w(x) = c if x < r, and 2x - 1 if r <= x <= 1.
  use 1
  simp [w];
  -- Since $c = 2r - 1$ and $r = \sqrt{2} - 1$, we have $c = 2(\sqrt{2} - 1) - 1 = 2\sqrt{2} - 3$.
  have hc : c = 2 * Real.sqrt 2 - 3 := by
    unfold c r; ring;
  have hc_abs : |c| ≤ 1 := by
    exact abs_le.mpr ⟨ by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ], by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩
  have hr_abs : ∀ x ∈ Set.Icc 0 1, x ≥ r → |2 * x - 1| ≤ 1 := by
    exact fun x hx hx' => abs_le.mpr ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩
  have hw_abs : ∀ x ∈ Set.Icc 0 1, |w x| ≤ 1 := by
    unfold w; aesop;
  aesop

/-
Theorem: W_star (defined as w for all k) is the unique uniformly bounded solution to the Bellman equation.
-/
noncomputable def W_star (_ : ℕ) (x : ℝ) : ℝ := w x

theorem unique_solution :
    is_solution W_star ∧ is_uniformly_bounded W_star ∧
    ∀ W, is_solution W → is_uniformly_bounded W →
    (∀ k, IntervalIntegrable (W k) MeasureTheory.volume 0 1) →
    ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = W_star k x := by
      unfold W_star;
      use fun k x hx => lemma_candidate k x hx;
      refine' ⟨ _, fun W hW hW' hW'' k x hx => _ ⟩;
      · exact w_is_uniformly_bounded;
      · apply lemma_uniqueness W ( fun _ => w ) hW ( fun k x hx => lemma_candidate k x hx ) hW' ( w_is_uniformly_bounded ) hW'' ( fun k => by exact (by
        rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le ];
        · refine' MeasureTheory.Integrable.mono' _ _ _ <;> norm_num [ w ];
          refine' fun x => 2 + |c| + 1;
          · norm_num +zetaDelta at *;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_Iio ) measurable_const ( measurable_id'.const_mul _ |> Measurable.sub <| measurable_const ) );
          · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => abs_le.mpr ⟨ by split_ifs <;> cases abs_cases c <;> linarith [ hx.1, hx.2 ], by split_ifs <;> cases abs_cases c <;> linarith [ hx.1, hx.2 ] ⟩ );
        · norm_num) ) k x hx

/-
The value of the game is 3 - 2*sqrt(2).
-/
noncomputable def game_value : ℝ := ∫ x in 0..1, w x

theorem game_value_eq : game_value = 3 - 2 * Real.sqrt 2 := by
  -- The integral of $w(x)$ over $[0,1]$ can be computed as the sum of the integrals over $[0,r]$ and $[r,1]$.
  have h_integral : ∫ x in (0 : ℝ)..1, w x = (∫ x in (0 : ℝ)..r, w x) + (∫ x in (r : ℝ)..1, w x) := by
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable ] <;> unfold w <;> apply_rules [ Continuous.if, continuous_const ];
    · erw [ frontier_Iio ] ; norm_num [ r ] ; ring_nf;
      unfold c r; ring;
    · continuity;
    · erw [ frontier_Iio ] ; norm_num [ r ] ; ring_nf;
      unfold c r; ring;
    · continuity;
  -- Evaluate the integrals over the intervals $[0,r]$ and $[r,1]$.
  have h_eval : (∫ x in (0 : ℝ)..r, w x) + (∫ x in (r : ℝ)..1, w x) = (∫ x in (0 : ℝ)..r, c) + (∫ x in (r : ℝ)..1, (2 * x - 1)) := by
    refine' congrArg₂ ( · + · ) _ _;
    · rw [ intervalIntegral.integral_of_le, intervalIntegral.integral_of_le ];
      · rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => if_pos hx.2;
      · exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num;
      · exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num;
    · refine' intervalIntegral.integral_congr fun x hx => _;
      exact if_neg ( by rw [ Set.uIcc_of_le ( show r ≤ 1 by rw [ show r = Real.sqrt 2 - 1 by rfl ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ] at hx; exact hx.1.not_gt );
  convert h_integral.trans h_eval using 1 ; norm_num [ mul_comm ] ; ring_nf;
  unfold c r; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
