import ErdosProblems.Erdos768.LowerBound
import ErdosProblems.Erdos768.SubsetProductCount

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — the counting core of the constructive lower bound (Section 5)

We assemble the constructive lower bound `lower_bound_subsequence` from:
* the analytic layer estimates already proved (`primeLayer_card_lower`,
  `fourth_moment_cleaning`);
* the counting form of the subset-product lemma (`subset_product_count`);

The random selection of one prime from each cleaned layer is realised as a count
over `Fintype.piFinset` of the cleaned layers, and the subset-product bound
controls the number of tuples that fail to produce, for each prime factor, a
witness divisor.
-/

open scoped Classical BigOperators
open Finset Filter

namespace Erdos768

/-- The exceptional ("bad") primes `ℬ = ⋃_j ℬ_j` removed in the cleaning step. -/
noncomputable def badSet (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 r).biUnion (fun j =>
    (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
      (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
        (primeLayer r j).card / (20 * (r : ℝ)) < ‖∑ q ∈ primeLayer r j, χ q‖))

/-- The cleaned prime layer `𝒫_j^* = 𝒫_j ∖ ℬ`. -/
noncomputable def cleanLayer (r j : ℕ) : Finset ℕ := primeLayer r j \ badSet r

/-
**Size of the exceptional set.**  `|ℬ| = exp(o(r))`: for every `ε > 0`,
eventually `|ℬ| ≤ e^{εr}`.
-/
lemma badSet_card_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp (ε * r) := by
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, ((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧ (primeLayer r j).card / (20 * (r : ℝ)) < ‖∑ q ∈ primeLayer r j, χ q‖)).card ≤ Real.exp ((ε / 2) * r) := by
    convert! fourth_moment_cleaning ( ε / 2 ) ( half_pos hε ) using 1;
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, (badSet r).card ≤ r * Real.exp ((ε / 2) * r) := by
    filter_upwards [ h_card_bound, Filter.eventually_ge_atTop 1 ] with r hr₁ hr₂;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    simpa using! Finset.sum_le_sum hr₁;
  have h_card_bound : ∀ᶠ r : ℕ in Filter.atTop, (r : ℝ) ≤ Real.exp ((ε / 2) * r) := by
    have h_card_bound : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.exp ((ε / 2) * r)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{\epsilon}{2} r$, therefore the limit becomes $\lim_{y \to \infty} \frac{y}{e^y}$.
      suffices h_lim_y : Filter.Tendsto (fun y : ℝ => y / Real.exp y) Filter.atTop (nhds 0) by
        have := h_lim_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( by positivity : 0 < ε / 2 ) );
        convert! this.const_mul ( 2 / ε ) using 2 <;> norm_num [ Function.comp, mul_div, mul_comm, hε.ne' ];
      simpa [ Real.exp_neg ] using! Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
    filter_upwards [ h_card_bound.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by rw [ div_lt_one ( Real.exp_pos _ ) ] at hr; linarith;
  filter_upwards [ ‹∀ᶠ r : ℕ in atTop, ( # ( badSet r ) : ℝ ) ≤ r * Real.exp ( ε / 2 * r ) ›, h_card_bound ] with r hr₁ hr₂ using le_trans hr₁ <| by rw [ show ε * r = ε / 2 * r + ε / 2 * r by ring ] ; rw [ Real.exp_add ] ; nlinarith [ Real.exp_pos ( ε / 2 * r ) ] ;

/-
**Exponential lower bound on the raw layer sizes.**  For every `ε > 0`,
eventually in `r`, every layer has `M_j ≥ e^{(α-ε)r}`.
-/
lemma layer_card_ge_exp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      Real.exp ((alphaParam - ε) * r) ≤ ((primeLayer r j).card : ℝ) := by
  -- By definition of $uParam$, we know that for large enough $r$, $uParam r 1 \geq 1$.
  have h_uParam1_ge_1 : ∀ᶠ r in Filter.atTop, 1 ≤ uParam r 1 := by
    have h_uParam1_ge_1 : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
      unfold uParam vParam deltaParam;
      -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * Real.log r / (r : ℝ) - 8 * alphaParam / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds (alphaParam)) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ one_sub_div ( by positivity ) ] ; ring );
      -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      norm_num [ mul_div_assoc ] at *;
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    have := h_uParam1_ge_1.eventually ( lt_mem_nhds <| show alphaParam > 1 / 2 by exact Real.log_two_gt_d9.trans_le' <| by norm_num );
    filter_upwards [ this, Filter.eventually_gt_atTop 2 ] with r hr₁ hr₂ using by rw [ lt_div_iff₀ ( by positivity ) ] at hr₁; nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ;
  -- By definition of $deltaParam$, we know that for large enough $r$, $deltaParam r \in (0, 1)$.
  have h_deltaParam_lt_1 : ∀ᶠ r in Filter.atTop, deltaParam r ∈ Set.Ioo 0 1 := by
    norm_num [ deltaParam ];
    obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp ( show Filter.Tendsto ( fun r : ℕ => 8 * alphaParam / Real.log r ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) 1 zero_lt_one ; use N + 2 ; intros ;
    exact ⟨ div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( by norm_cast; linarith ) ), by linarith [ abs_lt.mp ( hN _ ( by linarith ) ) ] ⟩;
  -- By definition of $uParam$, we know that for large enough $r$, $uParam r j \geq uParam r 1$.
  have h_uParam_ge_uParam1 : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≥ uParam r 1 := by
    filter_upwards [ h_deltaParam_lt_1 ] with r hr j hj;
    unfold uParam; norm_num; nlinarith [ hr.1, hr.2, show ( j : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( r : ℝ ) ≥ j by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
  -- By definition of $B$, we know that for large enough $r$, $B r / r \to \alphaParam$.
  have h_B_div_r_tendsto : Filter.Tendsto (fun r : ℕ => (Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1)) / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
    -- We'll use the fact that $uParam r 1 \sim \alpha r$ and $\log(2 * uParam r 1) \sim \log r$.
    have h_uParam1 : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ)) Filter.atTop (nhds alphaParam) := by
      unfold uParam vParam deltaParam;
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ)) - 8 * alphaParam / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds alphaParam) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] );
      -- We'll use the fact that $\frac{\log r}{r} \to 0$ as $r \to \infty$.
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    -- We'll use the fact that $\log(2 * uParam r 1) \sim \log r$.
    have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (2 * uParam r 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (uParam r 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => Real.log (uParam r 1) / (uParam r 1) * (uParam r 1 / (r : ℝ))) Filter.atTop (nhds 0) := by
          have h_log_uParam1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
            suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          convert! h_log_uParam1.comp ( show Filter.Tendsto ( fun r : ℕ => uParam r 1 ) Filter.atTop ( Filter.atTop ) from ?_ ) |> Filter.Tendsto.mul <| h_uParam1 using 2 <;> norm_num;
          have h_uParam1_inf : Filter.Tendsto (fun r : ℕ => uParam r 1 / (r : ℝ) * (r : ℝ)) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.pos_mul_atTop;
            exacts [ show 0 < alphaParam by exact Real.log_pos one_lt_two, h_uParam1, tendsto_natCast_atTop_atTop ];
          exact h_uParam1_inf.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ div_mul_cancel₀ _ ( by positivity ) ] );
        refine h_log_uParam1.congr' ( by filter_upwards [ h_uParam1_ge_1 ] with r hr using by rw [ div_mul_div_cancel₀ ( by linarith ) ] );
      have h_log_uParam1 : Filter.Tendsto (fun r : ℕ => (Real.log 2 + Real.log (uParam r 1)) / (r : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using! Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_uParam1;
      refine h_log_uParam1.congr' ( by filter_upwards [ h_uParam1_ge_1 ] with r hr using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
    -- We'll use the fact that $\log(1 - \exp(-\deltaParam r)) \sim \log(\deltaParam r)$.
    have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (1 - Real.exp (-deltaParam r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (deltaParam r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (8 * alphaParam / Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
          have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log (8 * alphaParam) / (r : ℝ) - Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
            have h_log_log_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
              have h_log_log_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
                -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
                suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
              refine' squeeze_zero_norm' _ h_log_log_r;
              filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos <| Real.log_pos <| by norm_cast; linarith ) <| by norm_num ) <| by positivity;
            simpa using! Filter.Tendsto.sub ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_log_r;
          refine h_log_deltaParam.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr ) ] ; ring );
        convert! h_log_deltaParam using 1;
      have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => (Real.log (1 - Real.exp (-deltaParam r)) - Real.log (deltaParam r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => Real.log ((1 - Real.exp (-deltaParam r)) / deltaParam r)) Filter.atTop (nhds 0) := by
          have h_log_deltaParam : Filter.Tendsto (fun r : ℕ => (1 - Real.exp (-deltaParam r)) / deltaParam r) Filter.atTop (nhds 1) := by
            have h_log_deltaParam : Filter.Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              simpa [ div_eq_inv_mul ] using! HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( hasDerivAt_const 0 1 ) ( HasDerivAt.exp ( hasDerivAt_neg 0 ) ) );
            refine' h_log_deltaParam.comp _;
            rw [ tendsto_nhdsWithin_iff ];
            exact ⟨ tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ), h_deltaParam_lt_1.mono fun r hr => hr.1 ⟩;
          simpa using! Filter.Tendsto.log h_log_deltaParam;
        have := h_log_deltaParam.div_atTop tendsto_natCast_atTop_atTop;
        refine' this.congr' ( by filter_upwards [ h_deltaParam_lt_1 ] with r hr using by rw [ Real.log_div ( by exact ne_of_gt <| sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr.1 ) ( by exact ne_of_gt hr.1 ) ] );
      convert! h_log_deltaParam.add ‹Tendsto ( fun r : ℕ => Real.log ( deltaParam r ) / ( r : ℝ ) ) atTop ( nhds 0 ) › using 2 <;> ring;
    convert! h_log_deltaParam.add ( h_uParam1.sub h_log_uParam1 ) using 2 <;> ring;
  -- By definition of $B$, we know that for large enough $r$, $B r \geq (\alphaParam - \epsilon) r$.
  have h_B_ge : ∀ᶠ r in Filter.atTop, Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1) ≥ (alphaParam - ε) * (r : ℝ) := by
    have := h_B_div_r_tendsto.eventually ( lt_mem_nhds <| show alphaParam > alphaParam - ε by linarith );
    filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ lt_div_iff₀ ( Nat.cast_pos.mpr hr₂ ) ] at hr₁; linarith;
  filter_upwards [ h_B_ge, h_uParam1_ge_1, h_deltaParam_lt_1, h_uParam_ge_uParam1, primeLayer_card_lower ] with r hr₁ hr₂ hr₃ hr₄ hr₅ j hj₁;
  refine le_trans ?_ ( hr₅ j hj₁ );
  rw [ le_div_iff₀ ];
  · have h_exp_log : Real.exp (Real.log (1 - Real.exp (-deltaParam r)) + uParam r 1 - Real.log (2 * uParam r 1)) ≤ (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) := by
      rw [ Real.exp_sub, Real.exp_add, Real.exp_log ( show 0 < 1 - Real.exp ( -deltaParam r ) from sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr₃.1 ), Real.exp_log <| show 0 < 2 * uParam r 1 from mul_pos zero_lt_two <| by linarith ];
      rw [ div_le_div_iff₀ ] <;> try linarith [ hr₄ j hj₁ ];
      rw [ mul_assoc, mul_assoc ];
      rw [ mul_le_mul_iff_right₀ ( sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr₃.1 ) ];
      rw [ ← div_le_div_iff₀ ] <;> try linarith [ hr₄ j hj₁ ];
      have h_exp_log : ∀ x y : ℝ, 1 ≤ x → x ≤ y → Real.exp x / x ≤ Real.exp y / y := by
        intros x y hx hy
        have h_deriv_pos : ∀ x : ℝ, 1 < x → deriv (fun x => Real.exp x / x) x > 0 := by
          intro x hx; norm_num [ Real.differentiableAt_exp, ne_of_gt ( zero_lt_one.trans hx ) ];
          exact div_pos ( by nlinarith [ Real.exp_pos x, Real.add_one_le_exp x ] ) ( sq_pos_of_pos ( by linarith ) );
        by_contra h_contra;
        have := exists_deriv_eq_slope ( f := fun x => Real.exp x / x ) ( show x < y from hy.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
        exact absurd ( this ( ContinuousOn.div ( Real.continuousOn_exp ) continuousOn_id fun x hx => by linarith [ hx.1 ] ) ( DifferentiableOn.div ( Real.differentiable_exp.differentiableOn ) differentiableOn_id fun x hx => by linarith [ hx.1 ] ) ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; have := h_deriv_pos c ( by linarith ) ; rw [ hcd, div_eq_mul_inv ] at this; nlinarith [ inv_mul_cancel₀ ( by linarith : ( y - x ) ≠ 0 ) ] );
      convert! mul_le_mul_of_nonneg_left ( h_exp_log ( uParam r 1 ) ( uParam r j ) hr₂ ( hr₄ j hj₁ ) ) ( show ( 0 : ℝ ) ≤ 1 / 2 by norm_num ) using 1 <;> ring;
    rw [ le_div_iff₀ ( mul_pos zero_lt_two ( by linarith [ hr₄ j hj₁ ] ) ) ] at h_exp_log;
    exact le_trans ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr hr₁ ) ( mul_nonneg zero_le_two ( by linarith [ hr₄ j hj₁ ] ) ) ) h_exp_log;
  · linarith [ hr₄ j hj₁ ]

/-
The cleaned layers are eventually nonempty, uniformly in `j`.
-/
lemma cleanLayer_card_pos :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < (cleanLayer r j).card := by
  -- Use `layer_card_ge_exp` and `badSet_card_small` to find `r ≥ R`, apply `Finset.le_card_sdiff`.
  have h:
    ∀ᶠ r : ℕ in atTop,
      ((badSet r).card : ℝ) < Real.exp ((alphaParam / 2) * r) := by
        have := badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four );
        filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using lt_of_le_of_lt hr₁ ( Real.exp_lt_exp.mpr <| by nlinarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two, show ( r : ℝ ) ≥ 1 by exact_mod_cast hr₂ ] )
  have h' :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      Real.exp ((alphaParam / 2) * r) ≤ ((primeLayer r j).card : ℝ) := by
        convert! layer_card_ge_exp ( alphaParam / 2 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_two ) using 2 ; ring_nf;
  filter_upwards [ h, h' ] with r hr₁ hr₂ j hj₁; specialize hr₂ j hj₁; simp_all +decide only [card_pos] ;
  contrapose! hr₁;
  exact hr₂.trans ( mod_cast Finset.card_le_card <| Finset.subset_iff.mpr fun x hx => by rw [ Finset.ext_iff ] at hr₁; specialize hr₁ x; aesop )

/-- Unit of `q` modulo `p` (junk value `1` when `q` is not a unit mod `p`). -/
noncomputable def unitOf (p q : ℕ) : (ZMod p)ˣ :=
  if h : IsUnit ((q : ℕ) : ZMod p) then h.unit else 1

/-- The `j`-th cleaned layer re-indexed by `Fin r` (so `j = k+1 ∈ [1,r]`). -/
noncomputable def LF (r : ℕ) (k : Fin r) : Finset ℕ := cleanLayer r (k.val + 1)

/-- Tuple `s` is *good for index `i`* if some nonempty subset of the **other**
coordinates multiplies to `1 (mod s i)` — a Sylow witness for the factor `s i`. -/
def subProdGoodP (r : ℕ) (s : Fin r → ℕ) : Prop :=
  ∀ i : Fin r, ∃ J : Finset (Fin r), J.Nonempty ∧ i ∉ J ∧ (∏ k ∈ J, s k) % (s i) = 1

/-- Tuple `s` is *bad for index `i`* if no nonempty subset of the other
coordinates multiplies to `1 (mod s i)`. -/
def badForI (r : ℕ) (i : Fin r) (s : Fin r → ℕ) : Prop :=
  ∀ J : Finset (Fin r), J.Nonempty → i ∉ J → (∏ k ∈ J, s k) % (s i) ≠ 1

/-- **Bridge.**  A nonprincipal additive character of `(ℤ/pℤ)ˣ` (written
additively) is the restriction of a nonprincipal Dirichlet character mod `p`. -/
lemma dirichlet_of_addChar {p : ℕ} [Fact p.Prime]
    (χ : AddChar (Additive (ZMod p)ˣ) ℂ) (hχ : χ ≠ 1) :
    ∃ ψ : DirichletCharacter ℂ p, ψ ≠ 1 ∧
      ∀ a : (ZMod p)ˣ, ψ (a : ZMod p) = χ (Additive.ofMul a) := by
  set u : (ZMod p)ˣ →* ℂ := χ.toMonoidHom with hu
  have hval : ∀ a : (ZMod p)ˣ,
      (MulChar.ofUnitHom u.toHomUnits) (a : ZMod p) = χ (Additive.ofMul a) := by
    intro a
    rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits, hu]
    exact AddChar.toMonoidHom_apply χ (Additive.ofMul a)
  refine ⟨MulChar.ofUnitHom u.toHomUnits, ?_, hval⟩
  intro h
  apply hχ
  ext x
  have hx : χ x =
      (MulChar.ofUnitHom u.toHomUnits) ((Additive.toMul x : (ZMod p)ˣ) : ZMod p) := by
    rw [hval]; rfl
  rw [hx, h]
  simp

/-
**Dirichlet-character clean Fourier bound.**  If `p ∈ 𝒫_i^*` then for every
layer `j` and every nonprincipal `ψ (mod p)`, `‖∑_{q∈𝒫_j^*} ψ(q)‖ ≤ |𝒫_j^*|/(10r)`.
-/
lemma cleanLayer_dirichlet_fourier :
    ∀ᶠ r : ℕ in atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i,
      ∀ j ∈ Finset.Icc 1 r, ∀ ψ : DirichletCharacter ℂ p, ψ ≠ 1 →
        ‖∑ q ∈ cleanLayer r j, ψ q‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
  -- Let `α := alphaParam = Real.log 2`.
  set α := alphaParam with hα_def
  have hα_pos : 0 < α := Real.log_pos one_lt_two;
  -- Gather eventual hypotheses.
  obtain ⟨hr₁, hr₂⟩ : (∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp ((α / 4) * r)) ∧ (∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.exp ((3 * α / 4) * r) ≤ ((primeLayer r j).card : ℝ)) := by
    constructor;
    · exact badSet_card_small ( α / 4 ) ( by positivity );
    · have := Erdos768.layer_card_ge_exp ( α / 4 ) ( by positivity );
      grind;
  obtain ⟨hr₃, hr₄⟩ : (∀ᶠ r : ℕ in atTop, 2 * (10 * r + 1) ≤ Real.exp ((α / 2) * r)) ∧ (∀ᶠ r : ℕ in atTop, 0 ≤ deltaParam r) := by
    have hr₃ : Filter.Tendsto (fun r : ℕ => (2 * (10 * r + 1) : ℝ) / Real.exp ((α / 2) * r)) Filter.atTop (nhds 0) := by
      -- We can factor out the constant $2$ and use the fact that $\frac{r}{e^{cr}}$ tends to $0$ as $r$ tends to infinity for any $c > 0$.
      have h_factor : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.exp ((α / 2) * r)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{\alpha}{2} r$, therefore the limit becomes $\lim_{y \to \infty} \frac{y}{e^y}$.
        suffices h_lim_y : Filter.Tendsto (fun y : ℝ => y / Real.exp y) Filter.atTop (nhds 0) by
          have := h_lim_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < α / 2 by positivity ) );
          convert! this.const_mul ( 2 / α ) using 2 <;> norm_num [ Function.comp, mul_div, mul_comm, hα_pos.ne' ];
        simpa [ Real.exp_neg ] using! Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      convert! h_factor.const_mul 20 |> Filter.Tendsto.add <| tendsto_inv_atTop_zero.comp ( Real.tendsto_exp_atTop.comp <| tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < α / 2 by positivity ) ) |> Filter.Tendsto.const_mul 2 using 2 <;> ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    exact ⟨ by filter_upwards [ hr₃.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by rw [ div_lt_one ( Real.exp_pos _ ) ] at hr; exact_mod_cast hr.le, by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using div_nonneg ( mul_nonneg ( by norm_num ) hα_pos.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩;
  filter_upwards [ hr₁, hr₂, hr₃, hr₄, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ hr₃ hr₄ hr₅;
  intro i hi p hp j hj ψ hψ
  have h₁ : ‖∑ q ∈ primeLayer r j, (ψ q : ℂ)‖ ≤ ((primeLayer r j).card : ℝ) / (20 * r) := by
    have h₁ : p ∈ Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊ ∧ Nat.Prime p := by
      simp_all +decide only [mem_Icc];
      refine' le_trans hp.1.1.2 _;
      refine' Nat.floor_mono <| Real.exp_le_exp.mpr _;
      exact sub_le_self _ ( mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr hi.2 ) hr₄ );
    have h₂ : p ∉ badSet r := by
      exact Finset.mem_sdiff.mp hp |>.2;
    contrapose! h₂;
    exact Finset.mem_biUnion.mpr ⟨ j, hj, Finset.mem_filter.mpr ⟨ h₁.1, h₁.2, ψ, hψ, h₂ ⟩ ⟩
  have h₂ : ‖∑ q ∈ (primeLayer r j ∩ badSet r), (ψ q : ℂ)‖ ≤ (badSet r).card := by
    refine' le_trans ( norm_sum_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show ‖ψ x‖ ≤ 1 from _ ) _;
    · convert! ψ.norm_le_one x using 1;
    · norm_num;
      exact Finset.card_le_card fun x hx => by aesop;
  have h₃ : ‖∑ q ∈ cleanLayer r j, (ψ q : ℂ)‖ ≤ ((primeLayer r j).card : ℝ) / (20 * r) + (badSet r).card := by
    convert! le_trans ( norm_sub_le _ _ ) ( add_le_add h₁ h₂ ) using 1;
    rw [ ← Finset.sum_sdiff ( show primeLayer r j ∩ badSet r ⊆ primeLayer r j from Finset.inter_subset_left ) ];
    simp +decide [ cleanLayer ];
  have h₄ : ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - (badSet r).card := by
    simp +decide only [ge_iff_le, tsub_le_iff_right];
    exact_mod_cast by rw [ Finset.card_sdiff_add_card ] ; exact Finset.card_le_card fun x hx => by aesop;
  have h₅ : 2 * (10 * r + 1) * (badSet r).card ≤ (primeLayer r j).card := by
    have h₅ : 2 * (10 * r + 1) * (badSet r).card ≤ Real.exp ((α / 2) * r) * Real.exp ((α / 4) * r) := by
      exact mul_le_mul hr₃ hr₁ ( by positivity ) ( by positivity );
    have h₆ : Real.exp ((α / 2) * r) * Real.exp ((α / 4) * r) ≤ Real.exp ((3 * α / 4) * r) := by
      rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
    exact_mod_cast h₅.trans ( h₆.trans ( hr₂ j hj ) );
  rw [ le_div_iff₀ ( by positivity ) ] at *;
  rw [ div_add', le_div_iff₀ ] at h₃ <;> nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast, show ( 2 * ( 10 * r + 1 ) * #(badSet r) : ℝ ) ≤ #(primeLayer r j) by exact_mod_cast h₅ ]

/-
**Additive-character clean Fourier bound.**  For `p ∈ 𝒫_i^*` and `j ≠ i`,
the pushforward Fourier coefficient of uniform-on-`𝒫_j^*` is `≤ 1/(10r)`.
-/
lemma cleanLayer_addChar_fourier :
    ∀ᶠ r : ℕ in atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i,
      ∀ j ∈ Finset.Icc 1 r, j ≠ i →
        ∀ χ : AddChar (Additive (ZMod p)ˣ) ℂ, χ ≠ 1 →
          ‖∑ q ∈ cleanLayer r j, χ (Additive.ofMul (unitOf p q))‖
            ≤ (1 / (10 * r)) * ((cleanLayer r j).card : ℝ) := by
  -- By combining the results from cleanLayer_dirichlet_fourier and dirichlet_of_addChar, we can conclude the proof.
  have h_combined : ∀ᶠ r in Filter.atTop, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i, ∀ j ∈ Finset.Icc 1 r, j ≠ i → ∀ χ : AddChar (Additive (ZMod p)ˣ) ℂ, χ ≠ 1 → ‖∑ q ∈ cleanLayer r j, χ (Additive.ofMul (unitOf p q))‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ r ≥ N₁, ∀ i ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r i, ∀ j ∈ Finset.Icc 1 r, j ≠ i → ∀ ψ : DirichletCharacter ℂ p, ψ ≠ 1 → ‖∑ q ∈ cleanLayer r j, ψ q‖ ≤ ((cleanLayer r j).card : ℝ) / (10 * r) := by
      have := @cleanLayer_dirichlet_fourier;
      exact Filter.eventually_atTop.mp ( this.mono fun r hr i hi p hp j hj hj' ψ hψ => hr i hi p hp j hj ψ hψ );
    refine' Filter.eventually_atTop.mpr ⟨ N₁ + 2, fun r hr i hi p hp j hj hij χ hχ => _ ⟩;
    have h_p_prime : Nat.Prime p := by
      exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp hp |>.1 ) |>.2.1;
    have h_q_prime : ∀ q ∈ cleanLayer r j, Nat.Prime q ∧ q ≠ p := by
      intros q hq
      have hq_prime : Nat.Prime q := by
        exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.1
      have hq_ne_p : q ≠ p := by
        intro hqp
        have h_interval : Real.exp (uParam r j - deltaParam r) < q ∧ q ≤ Real.exp (uParam r j) ∧ Real.exp (uParam r i - deltaParam r) < p ∧ p ≤ Real.exp (uParam r i) := by
          unfold cleanLayer at hp hq; simp_all +decide [ primeLayer ] ;
          exact ⟨ le_trans ( Nat.cast_le.mpr hq.1 ) ( Nat.floor_le ( Real.exp_nonneg _ ) ), le_trans ( Nat.cast_le.mpr hp.1.1.2 ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) ⟩;
        have h_interval_disjoint : uParam r j - deltaParam r ≥ uParam r i ∨ uParam r i - deltaParam r ≥ uParam r j := by
          unfold uParam deltaParam; ring_nf;
          cases lt_or_gt_of_ne hij <;> first | left; nlinarith [ show ( i : ℝ ) + 1 ≤ j by exact_mod_cast ‹_›, show ( alphaParam : ℝ ) * ( Real.log r ) ⁻¹ > 0 by exact mul_pos ( show ( alphaParam : ℝ ) > 0 by exact Real.log_pos one_lt_two ) ( inv_pos.mpr ( Real.log_pos ( show ( r : ℝ ) > 1 by norm_cast; linarith ) ) ) ] | right; nlinarith [ show ( j : ℝ ) + 1 ≤ i by exact_mod_cast ‹_›, show ( alphaParam : ℝ ) * ( Real.log r ) ⁻¹ > 0 by exact mul_pos ( show ( alphaParam : ℝ ) > 0 by exact Real.log_pos one_lt_two ) ( inv_pos.mpr ( Real.log_pos ( show ( r : ℝ ) > 1 by norm_cast; linarith ) ) ) ] ;
        cases h_interval_disjoint <;> simp_all +decide; all_goals linarith [ Real.exp_le_exp.mpr ‹_› ]
      exact ⟨hq_prime, hq_ne_p⟩;
    obtain ⟨ψ, hψ1, hψval⟩ : ∃ ψ : DirichletCharacter ℂ p, ψ ≠ 1 ∧ ∀ a : (ZMod p)ˣ, ψ (a : ZMod p) = χ (Additive.ofMul a) := by
      have := Fact.mk h_p_prime; exact dirichlet_of_addChar χ hχ |> fun ⟨ ψ, hψ1, hψval ⟩ => ⟨ ψ, hψ1, fun a => hψval a ▸ rfl ⟩ ;
    convert! hN₁ r ( by linarith ) i hi p hp j hj hij ψ hψ1 using 1;
    refine' congr_arg Norm.norm ( Finset.sum_congr rfl fun q hq => _ );
    have h_unit : IsUnit ((q : ℕ) : ZMod p) := by
      have := Fact.mk h_p_prime; exact IsUnit.mk0 _ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => h_q_prime q hq |>.2 <| by have := Nat.prime_dvd_prime_iff_eq h_p_prime ( h_q_prime q hq |>.1 ) ; tauto ) ;
    convert! hψval ( h_unit.unit ) |> Eq.symm using 1;
    unfold unitOf; aesop;
  exact h_combined.mono fun r hr i hi p hp j hj hij χ hχ => by convert! hr i hi p hp j hj hij χ hχ using 1 ; ring;

/-
A prime lies in at most one cleaned layer: the layer index is determined by the
prime (the layer intervals are pairwise disjoint).
-/
lemma layer_index_unique :
    ∀ᶠ r : ℕ in atTop, ∀ a ∈ Finset.Icc 1 r, ∀ b ∈ Finset.Icc 1 r, ∀ q : ℕ,
      q ∈ cleanLayer r a → q ∈ cleanLayer r b → a = b := by
  refine' Filter.eventually_atTop.mpr ⟨ 2, fun r hr => _ ⟩;
  intro a ha b hb q hqa hqb;
  -- By definition of `cleanLayer`, we know that `q` is in `primeLayer r a` and `primeLayer r b`.
  have hq_primeLayer_a : q ∈ primeLayer r a := by
    exact Finset.mem_sdiff.mp hqa |>.1
  have hq_primeLayer_b : q ∈ primeLayer r b := by
    exact Finset.mem_sdiff.mp hqb |>.1;
  unfold primeLayer at *; simp_all +decide [ Finset.mem_filter ] ;
  -- Since $a \neq b$, without loss of generality, assume $a < b$.
  wlog hlt : a < b generalizing a b;
  · grind +suggestions;
  · -- Since $a < b$, we have $uParam r a \leq uParam r b - deltaParam r$.
    have h_uParam_le : uParam r a ≤ uParam r b - deltaParam r := by
      unfold uParam; ring_nf;
      nlinarith [ show ( a : ℝ ) + 1 ≤ b by norm_cast, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ];
    contrapose! hq_primeLayer_b;
    exact fun _ => le_trans ( Nat.cast_le.mpr hq_primeLayer_a.1.2 ) ( Nat.floor_le ( Real.exp_nonneg _ ) |> le_trans <| Real.exp_le_exp.mpr h_uParam_le )

/-- Each element of a cleaned layer `𝒫_j^*` (with `j ∈ [1,r]`) is a prime `≤ e^{u_j}`. -/
lemma mem_cleanLayer_le_exp {r j q : ℕ} (h : q ∈ cleanLayer r j) :
    Nat.Prime q ∧ (q : ℝ) ≤ Real.exp (uParam r j) := by
  have h' : q ∈ primeLayer r j := (Finset.mem_sdiff.mp h).1
  rw [primeLayer, Finset.mem_filter, Finset.mem_Icc] at h'
  exact ⟨h'.2.1, le_trans (Nat.cast_le.mpr h'.1.2) (Nat.floor_le (Real.exp_nonneg _))⟩

/-
The good tuples embed into `𝒜 ∩ [1, e^{L_r}]`, so their number is `≤ A(e^{L_r})`.
-/
lemma good_le_Acount :
    ∀ᶠ r : ℕ in atTop,
      (((Fintype.piFinset (LF r)).filter
          (fun s => SylowDivisor (∏ k, s k))).card : ℝ)
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  filter_upwards [ layer_index_unique, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
  -- Fix an `r` large enough so that `layer_index_unique` holds.
  have h_mapsTo : ∀ s ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)), (∏ k, s k) ∈ Finset.Icc 1 ⌊Real.exp (Lr r)⌋₊ := by
    intro s hs; refine' Finset.mem_Icc.mpr ⟨ _, _ ⟩ <;> norm_num at *;
    · exact Finset.prod_pos fun i _ => Nat.Prime.pos ( by have := hs.1 i; exact ( mem_cleanLayer_le_exp this ) |>.1 );
    · refine' Nat.le_floor _;
      -- By definition of `Lr`, we know that $\prod_{k=1}^r \exp(u_r(k)) = \exp(L_r)$.
      have h_prod_exp : ∏ k : Fin r, Real.exp (uParam r (k.val + 1)) = Real.exp (Lr r) := by
        rw [ ← Real.exp_sum, Lr ];
        erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, Finset.sum_range ];
      rw [ ← h_prod_exp, Nat.cast_prod ];
      exact Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun i _ => by simpa using! mem_cleanLayer_le_exp ( hs.1 i ) |>.2;
  have h_injOn : ∀ s s' : Fin r → ℕ, s ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)) → s' ∈ (Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k)) → (∏ k, s k) = (∏ k, s' k) → s = s' := by
    intros s s' hs hs' hprod
    have h_prime_div : ∀ k : Fin r, ∃ l : Fin r, s k = s' l := by
      intro k
      have h_div : s k ∣ ∏ k, s' k := by
        exact hprod ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ );
      have h_prime_div : Nat.Prime (s k) := by
        simp +zetaDelta at *;
        exact mem_cleanLayer_le_exp ( hs.1 k ) |>.1;
      have := h_prime_div.dvd_iff_not_coprime.mp h_div;
      contrapose! this;
      exact Nat.Coprime.prod_right fun l _ => h_prime_div.coprime_iff_not_dvd.mpr fun h => this l <| by have := Nat.prime_dvd_prime_iff_eq h_prime_div ( show Nat.Prime ( s' l ) from by
                                                                                                                                                          simp +zetaDelta at *;
                                                                                                                                                          exact mem_cleanLayer_le_exp ( hs'.1 l ) |>.1 ) ; tauto;
    choose f hf using h_prime_div;
    have h_inj : ∀ k : Fin r, f k = k := by
      intros k
      have h_eq : s k ∈ cleanLayer r (k.val + 1) ∧ s' (f k) ∈ cleanLayer r ((f k).val + 1) := by
        simp +zetaDelta at *;
        exact ⟨ hs.1 k, hs'.1 ( f k ) ⟩;
      grind;
    exact funext fun k => by simpa [ h_inj ] using! hf k;
  refine' mod_cast _;
  refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun s : Fin r → ℕ => ∏ k, s k ) ( Finset.filter ( fun s : Fin r → ℕ => SylowDivisor ( ∏ k, s k ) ) ( Fintype.piFinset ( LF r ) ) ) ⊆ Finset.filter SylowDivisor ( Finset.Icc 1 ⌊Real.exp ( Lr r ) ⌋₊ ) from _ );
  · rw [ Finset.card_image_of_injOn fun s hs s' hs' h => h_injOn s s' hs hs' h ];
  · grind +qlia

/-
The subset-product-good tuples are a subset of the Sylow-good tuples.
-/
lemma subProd_le_good :
    ∀ᶠ r : ℕ in atTop,
      (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ)
        ≤ (((Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k))).card : ℝ) := by
  refine' Filter.Eventually.of_forall fun r => Nat.cast_le.mpr _;
  refine Finset.card_le_card ?_;
  intro s hs;
  simp_all +decide only [mem_filter, Fintype.mem_piFinset];
  -- By definition of `LF`, we know that each `s k` is prime.
  have h_prime : ∀ k, Nat.Prime (s k) := by
    intro k; specialize hs; have := hs.1 k; simp_all +decide [ LF, cleanLayer, primeLayer ] ;
  intro P hP hP_div
  obtain ⟨i, hi⟩ : ∃ i, P ∣ s i := by
    simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
  obtain ⟨ J, hJ₁, hJ₂, hJ₃ ⟩ := hs.2 i;
  refine' ⟨ ∏ k ∈ J, s k, _, _, _ ⟩;
  · apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.subset_univ ];
  · exact lt_of_lt_of_le ( Nat.Prime.one_lt ( h_prime _ ) ) ( Nat.le_of_dvd ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( h_prime _ ) ) ( Finset.dvd_prod_of_mem _ hJ₁.choose_spec ) );
  · rw [ Nat.dvd_prime ( h_prime i ) ] at hi ; aesop

/-
Complement/union bound: the good tuples are at least the total minus the sum
of the per-index bad counts.
-/
lemma good_ge_prod_sub_bad (r : ℕ) :
    (∏ k : Fin r, ((LF r k).card : ℝ))
        - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
      ≤ (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ) := by
  rw [ sub_le_iff_le_add ];
  rw_mod_cast [ ← Fintype.card_piFinset ];
  have h_complement : (Fintype.piFinset (LF r)).filter (fun s => ¬subProdGoodP r s) ⊆ Finset.biUnion Finset.univ (fun i => (Fintype.piFinset (LF r)).filter (badForI r i)) := by
    unfold subProdGoodP badForI; simp +contextual [ Finset.subset_iff ] ;
  have := Finset.card_mono h_complement; simp_all +decide only [Fintype.card_piFinset, ge_iff_le] ;
  exact this.trans ( add_le_add ( Finset.card_biUnion_le ) ( by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ) ) |> le_trans <| by simp +decide [ add_comm ] ;

/-
**Product ≡ 1 (mod p) ↔ additive subset-sum vanishes.**  If every factor is a
unit mod the prime `p`, the product is `≡ 1` iff the images sum to `0`.
-/
lemma prod_mod_eq_one_iff_sum_zero {p : ℕ} [Fact p.Prime] {α : Type*}
    (J : Finset α) (g : α → ℕ) (hg : ∀ x ∈ J, IsUnit ((g x : ℕ) : ZMod p)) :
    (∏ x ∈ J, g x) % p = 1 ↔ ∑ x ∈ J, Additive.ofMul (unitOf p (g x)) = 0 := by
  constructor <;> intro h;
  · -- Apply the fact that the product of the elements in J is congruent to 1 modulo p to conclude the sum is zero.
    have h_sum_zero : ((∏ x ∈ J, (g x : ZMod p)) = 1) := by
      simpa [ ← ZMod.natCast_eq_zero_iff ] using! congr_arg ( fun x : ℕ => x : ℕ → ZMod p ) h;
    convert! congr_arg ( fun x : ( ZMod p ) ˣ => Additive.ofMul x ) ( show ∏ x ∈ J, unitOf p ( g x ) = 1 from ?_ ) using 1;
    refine' Units.ext _;
    convert! h_sum_zero using 1;
    induction J using Finset.induction <;> simp_all +decide [ Finset.prod_insert, unitOf ];
  · -- By definition of `unitOf`, we know that `unitOf p (g x)` is the multiplicative inverse of `g x` modulo `p`.
    have h_unit : (∏ x ∈ J, (unitOf p (g x) : (ZMod p)ˣ)) = 1 := by
      convert! congr_arg ( fun x : Additive ( ( ZMod p ) ˣ ) => x.toMul ) h using 1;
    have h_mod : (∏ x ∈ J, (g x : ZMod p)) = 1 := by
      convert! congr_arg ( fun x : ( ZMod p ) ˣ => ( x : ZMod p ) ) h_unit using 1;
      simp +decide only [Units.coe_prod];
      refine' Finset.prod_congr rfl fun x hx => _ ; aesop;
    rw [ ← ZMod.val_natCast, Nat.cast_prod, h_mod, ZMod.val_one ]

/-
**Fiber count identity.**  Fixing the value at `i` to a prime `p` (all other
coordinates being coprime to `p`), the tuples bad for `i` correspond to the
tuples over the remaining coordinates whose images admit no vanishing nonempty
subset-sum.
-/
lemma badForI_count_eq {r : ℕ} (i : Fin r) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ LF r i)
    (hcop : ∀ (k' : {k : Fin r // k ≠ i}), ∀ q ∈ LF r k'.1, IsUnit ((q : ℕ) : ZMod p)) :
    ((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card
      = ((Fintype.piFinset (fun k' : {k : Fin r // k ≠ i} => LF r k'.1)).filter
          (fun t => ∀ J : Finset {k : Fin r // k ≠ i}, J.Nonempty →
            ∑ k' ∈ J, Additive.ofMul (unitOf p (t k')) ≠ 0)).card := by
  refine' Finset.card_bij ( fun s hs => fun k => s k ) _ _ _;
  · simp +zetaDelta only [mem_filter, Fintype.mem_piFinset, ne_eq, Subtype.forall, and_imp] at *;
    intro a ha hbad hap; refine' ⟨ fun k hk => ha k, _ ⟩ ; intro J hJ; contrapose! hbad; simp_all +decide [ badForI ] ;
    use J.image Subtype.val; simp_all +decide [ Finset.prod_image ] ;
    convert! prod_mod_eq_one_iff_sum_zero J ( fun k' => a k'.1 ) ( fun k' hk' => ?_ ) |>.2 hbad using 1;
    exact isUnit_iff_ne_zero.mpr ( hcop _ k'.2 _ ( ha _ ) );
  · simp +contextual [ funext_iff, Finset.mem_filter ];
    grind;
  · intro t ht; use fun k => if h : k = i then p else t ⟨ k, h ⟩ ; simp_all +decide only [ne_eq, Subtype.coe_eta, dite_eq_ite, mem_filter, Fintype.mem_piFinset, ↓reduceDIte,
    and_true, exists_prop] ;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · aesop;
    · intro J hJ₁ hJ₂; simp_all +decide ;
      convert! ht.2 ( Finset.subtype ( fun k => k ≠ i ) J ) _ using 1;
      · rw [ ← prod_mod_eq_one_iff_sum_zero ];
        · convert! Iff.rfl using 2;
          refine' congr_arg ( · % p ) ( Finset.prod_bij ( fun x hx => x ) _ _ _ _ ) <;> simp +decide;
          · exact fun x hx => ⟨ hx, by rintro rfl; exact hJ₂ hx ⟩;
          · grobner;
        · exact fun x hx => isUnit_iff_ne_zero.mpr ( hcop _ x.2 _ ( ht.1 _ _ ) );
      · exact ⟨ ⟨ hJ₁.choose, fun h => hJ₂ <| h ▸ hJ₁.choose_spec ⟩, Finset.mem_subtype.mpr hJ₁.choose_spec ⟩;
    · grind

/-
`exp(v) · r^{10} = 2^{r-1}` (from `v = (log 2)(r-1) - 10 log r`).
-/
lemma exp_vParam_mul (r : ℕ) (hr : 1 ≤ r) :
    Real.exp (vParam r) * (r : ℝ) ^ 10 = 2 ^ (r - 1) := by
  unfold vParam alphaParam;
  rw [ Real.exp_sub, Real.exp_mul, Real.exp_log ] <;> norm_num;
  rw [ div_mul_eq_mul_div, div_eq_iff ] <;> first | positivity | cases r <;> norm_num [ ← Real.log_rpow, Real.exp_log ] at *;
  rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast ; norm_num

/-
Every element of `LF r i` is a prime that is `≤ e^{v}` (eventually in `r`).
-/
lemma LF_mem_le_exp_vParam :
    ∀ᶠ r : ℕ in atTop, ∀ i : Fin r, ∀ p ∈ LF r i,
      Nat.Prime p ∧ (p : ℝ) ≤ Real.exp (vParam r) := by
  -- By definition of `cleanLayer`, every element in `cleanLayer r (i.val + 1)` is a prime that is `≤ e^{v}`.
  have h_cleanLayer_le_exp : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, ∀ p ∈ cleanLayer r j, Nat.Prime p ∧ (p : ℝ) ≤ Real.exp (vParam r) := by
    refine' Filter.eventually_atTop.mpr ⟨ 8, fun r hr => _ ⟩;
    intro j hj p hp
    have h_exp : Real.exp (uParam r j) ≤ Real.exp (vParam r) := by
      unfold uParam;
      norm_num +zetaDelta at *;
      exact mul_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hj.2 ) ) ( div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) );
    exact ⟨ mem_cleanLayer_le_exp hp |>.1, le_trans ( mod_cast mem_cleanLayer_le_exp hp |>.2 ) h_exp ⟩;
  filter_upwards [ h_cleanLayer_le_exp ] with r hr i p hp using hr ( i.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt i ], by linarith [ Fin.is_lt i ] ⟩ ) p hp

/-
**Per-`p` subset-product bound.**  There is an absolute `C` with, eventually,
for every `i` and `p ∈ LF r i`, the number of tuples bad for `i` with `s i = p` is
`≤ C·r^{-10}·∏_{k≠i}|𝒫_k^*|`.
-/
set_option maxHeartbeats 1600000 in
lemma badForI_perp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop, ∀ i : Fin r, ∀ p ∈ LF r i,
      (((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card : ℝ)
        ≤ C / (r : ℝ) ^ 10 * (∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ)) := by
  by_contra h;
  obtain ⟨Λ₀, C₁, hΛ₀, hC₁, hspc⟩ := subset_product_count_fintype;
  refine' h ⟨ C₁, hC₁, _ ⟩;
  filter_upwards [ layer_index_unique, LF_mem_le_exp_vParam, cleanLayer_addChar_fourier, cleanLayer_card_pos, Filter.eventually_ge_atTop ⌈Λ₀⌉₊, Filter.eventually_ge_atTop 2 ] with r hr₁ hr₂ hr₃ hr₄ hr₅ hr₆;
  intro i p hp;
  have hp2 : (p : ℝ) ≤ Real.exp (vParam r) := (hr₂ i p hp).2
  have hpprime : Nat.Prime p := (hr₂ i p hp).1
  have : Fact p.Prime := ⟨hpprime⟩
  have hp_ge2 : 2 ≤ p := hpprime.two_le
  have hpr : ((p : ℝ) - 1) * (r : ℝ) ^ 10 ≤ 2 ^ (r - 1) := by
    have := exp_vParam_mul r ( by linarith );
    nlinarith [ show ( p : ℝ ) ≥ 2 by norm_cast, show ( r : ℝ ) ^ 10 ≥ 0 by positivity ];
  have hcop : ∀ k' : {k : Fin r // k ≠ i}, ∀ q ∈ LF r k'.1, IsUnit ((q : ℕ) : ZMod p) := by
    intros k' q hq
    have hq_prime : Nat.Prime q := by
      exact hr₂ _ _ hq |>.1
    have hq_ne_p : q ≠ p := by
      contrapose! hr₁;
      use k'.val + 1, by
        exact Finset.mem_Icc.mpr ⟨ Nat.succ_pos _, Nat.succ_le_of_lt k'.1.2 ⟩, i.val + 1, by
        exact Finset.mem_Icc.mpr ⟨ Nat.succ_pos _, Nat.succ_le_of_lt i.2 ⟩, q, by
        convert! hq using 1, by
        convert! hp using 1, by
        exact fun h => k'.2 <| Fin.ext <| by simpa [ Fin.ext_iff ] using! h;
    have hq_coprime : Nat.gcd q p = 1 := by
      exact hq_prime.coprime_iff_not_dvd.mpr fun h => hq_ne_p <| Nat.prime_dvd_prime_iff_eq hq_prime hpprime |>.1 h
    exact ZMod.isUnit_iff_coprime q p |>.2 hq_coprime;
  have := hspc ( Additive ( ZMod p ) ˣ ) { k : Fin r // k ≠ i } ( fun k' => LF r k'.1 ) ( fun k' q => Additive.ofMul ( unitOf p q ) ) ( 1 / ( 10 * r ) ) ?_ ?_ ?_ ?_;
  · convert! this.trans _ using 1;
    · rw [ badForI_count_eq i p hp hcop ];
      congr! 3;
    · rw [ show Fintype.card ( Additive ( ZMod p ) ˣ ) = p - 1 from ?_, show Fintype.card { k : Fin r // k ≠ i } = r - 1 from ?_ ];
      · rw [ Nat.cast_pred hpprime.pos ];
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
        convert! mul_le_mul_of_nonneg_left hpr ( show 0 ≤ C₁ * ∏ k' : { k : Fin r // k ≠ i }, ( # ( LF r k'.1 ) : ℝ ) by exact mul_nonneg hC₁.le <| Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) using 1 ; ring;
      · simp +decide;
      · simp +decide [ Nat.totient_prime hpprime ];
  · exact fun k' => Finset.card_pos.mp ( hr₄ _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt k'.1 ], by linarith [ Fin.is_lt k'.1 ] ⟩ );
  · intro k' χ hχ;
    convert! hr₃ ( i.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt i ], by linarith [ Fin.is_lt i ] ⟩ ) p hp ( k'.val + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Fin.is_lt k'.val ], by linarith [ Fin.is_lt k'.val ] ⟩ ) ( by simpa [ Fin.ext_iff ] using! k'.2 ) χ hχ using 1;
  · rw [ mul_one_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ Finset.filter_ne' ]; all_goals linarith;
  · simp +decide only [ne_eq, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique,
    Fintype.card_additive, ZMod.card_units_eq_totient];
    rw [ le_div_iff₀ ] <;> norm_num [ hpprime.pos ];
    · refine le_trans ?_ hpr;
      rw [ mul_comm ] ; gcongr;
      · exact sub_nonneg_of_le ( mod_cast hpprime.pos );
      · exact le_trans ( Nat.le_ceil _ ) ( mod_cast Nat.le_trans hr₅ ( Nat.le_self_pow ( by norm_num ) _ ) );
    · linarith

/-
Splitting off the value at `i`: `|𝒫_i^*| · ∏_{k≠i}|𝒫_k^*| = ∏_k |𝒫_k^*|`.
-/
lemma LF_prod_split (r : ℕ) (i : Fin r) :
    ((LF r i).card : ℝ) * (∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ))
      = ∏ k : Fin r, ((LF r k).card : ℝ) := by
  rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ), mul_comm ];
  refine' congrArg₂ _ ( Finset.prod_bij ( fun x hx => x.val ) _ _ _ _ ) rfl <;> simp +decide

/-- **Subset-product bound per index.**  There is an absolute `C` with, eventually,
for every `i`, the number of tuples bad for `i` is `≤ C·r^{-10}·∏_k|𝒫_k^*|`. -/
lemma badForI_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop, ∀ i : Fin r,
      (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
        ≤ C / (r : ℝ) ^ 10 * (∏ k : Fin r, ((LF r k).card : ℝ)) := by
  obtain ⟨C, hC, hperp⟩ := badForI_perp_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hperp, Filter.eventually_gt_atTop 0] with r hperp hr0
  intro i
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  set Q : ℝ := ∏ k' : {k : Fin r // k ≠ i}, ((LF r k'.1).card : ℝ) with hQ
  have hQnn : (0 : ℝ) ≤ Q := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  -- partition by value at `i`
  have hmaps : ∀ s ∈ (Fintype.piFinset (LF r)).filter (badForI r i), s i ∈ LF r i := by
    intro s hs
    exact (Fintype.mem_piFinset.mp (Finset.mem_of_mem_filter s hs)) i
  have hpart :
      ((Fintype.piFinset (LF r)).filter (badForI r i)).card
        = ∑ p ∈ LF r i,
            ((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    ext s
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    tauto
  rw [hpart, Nat.cast_sum]
  calc ∑ p ∈ LF r i,
          (((Fintype.piFinset (LF r)).filter (fun s => badForI r i s ∧ s i = p)).card : ℝ)
        ≤ ∑ p ∈ LF r i, (C / (r : ℝ) ^ 10 * Q) :=
          Finset.sum_le_sum (fun p hp => by rw [hQ]; exact hperp i p hp)
      _ = ((LF r i).card : ℝ) * (C / (r : ℝ) ^ 10 * Q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = C / (r : ℝ) ^ 10 * (((LF r i).card : ℝ) * Q) := by ring
      _ = C / (r : ℝ) ^ 10 * (∏ k : Fin r, ((LF r k).card : ℝ)) := by
          rw [hQ, LF_prod_split]

/-
Reindexing the `Fin r` product to the `Icc 1 r` product.
-/
lemma prod_LF_eq (r : ℕ) :
    (∏ k : Fin r, ((LF r k).card : ℝ))
      = ∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) := by
  erw [ Finset.prod_Ico_eq_prod_range ];
  simp +decide [ add_comm, Finset.prod_range, LF ]

/-- **Combinatorial lower bound (the crux).**  There is an absolute constant `C`
so that, eventually in `r`,
`A(e^{L_r}) ≥ (1 - C/r⁹) · ∏_j |𝒫_j^*|`. -/
lemma clean_count_crux :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop,
      (1 - C / (r : ℝ) ^ 9) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ))
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  obtain ⟨C, hC, hbad⟩ := badForI_card_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [good_le_Acount, subProd_le_good, hbad, Filter.eventually_gt_atTop 0]
    with r hgood hsub hbadr hr0
  have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  set P : ℝ := ∏ k : Fin r, ((LF r k).card : ℝ) with hP
  have hPpos : (0 : ℝ) ≤ P := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum : ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
      ≤ C / (r : ℝ) ^ 9 * P := by
    calc ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ)
        ≤ ∑ _i : Fin r, (C / (r : ℝ) ^ 10 * P) := Finset.sum_le_sum (fun i _ => hbadr i)
      _ = (r : ℝ) * (C / (r : ℝ) ^ 10 * P) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ = C / (r : ℝ) ^ 9 * P := by
          rw [show (r : ℝ) ^ 10 = (r : ℝ) ^ 9 * r by ring]
          field_simp
  have hcompl := good_ge_prod_sub_bad r
  rw [← hP] at hcompl
  have key : (1 - C / (r : ℝ) ^ 9) * P ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
    have h1 : (1 - C / (r : ℝ) ^ 9) * P
        ≤ P - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ) := by
      nlinarith [hsum]
    calc (1 - C / (r : ℝ) ^ 9) * P
        ≤ P - ∑ i : Fin r, (((Fintype.piFinset (LF r)).filter (badForI r i)).card : ℝ) := h1
      _ ≤ (((Fintype.piFinset (LF r)).filter (subProdGoodP r)).card : ℝ) := hcompl
      _ ≤ (((Fintype.piFinset (LF r)).filter (fun s => SylowDivisor (∏ k, s k))).card : ℝ) := hsub
      _ ≤ (Acount (Real.exp (Lr r)) : ℝ) := hgood
  rwa [hP, prod_LF_eq r] at key

/-
**Log-sum lower bound for the raw layers.**  There is a constant `K` with,
eventually, `∑_j log M_j ≥ L_r - r·log r - r·log log r - K·r`.
-/
set_option maxHeartbeats 1000000 in
lemma primeLayer_log_sum_lower :
    ∃ K : ℝ, ∀ᶠ r : ℕ in atTop,
      Lr r - (r : ℝ) * Real.log r - (r : ℝ) * Real.log (Real.log r) - K * (r : ℝ)
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ) := by
  by_contra h_contra;
  -- By combining the results from `primeLayer_card_lower` and `layer_card_ge_exp`, we can derive the required inequality.
  have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ) ≥ Real.log (1 - Real.exp (-deltaParam r)) + uParam r j - Real.log (2 * uParam r j) := by
    have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) ≤ ((primeLayer r j).card : ℝ) := by
      convert! primeLayer_card_lower using 1;
    have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) := by
      have h_combined : ∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1 := by
        have h_combined : Filter.Tendsto deltaParam Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        have h_combined : ∀ᶠ r in atTop, 0 < deltaParam r := by
          exact Filter.eventually_atTop.mpr ⟨ 2, fun r hr => div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr ) ) ⟩;
        exact h_combined.and ( ‹Tendsto deltaParam atTop ( nhds 0 ) ›.eventually ( gt_mem_nhds zero_lt_one ) );
      have h_combined : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < uParam r j := by
        have h_combined : ∀ᶠ r in atTop, 0 < vParam r - (r : ℝ) * deltaParam r := by
          have h_combined : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
            unfold vParam;
            ring_nf;
            -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
            have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
              -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
              suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
              norm_num;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
            have h_const : Filter.Tendsto (fun r : ℕ => Real.log 2 * ((r : ℝ) * (r : ℝ)⁻¹))
                Filter.atTop (nhds (Real.log 2)) := by
              apply tendsto_const_nhds.congr'
              filter_upwards [Filter.eventually_ne_atTop 0] with r hr
              have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
              simp [hr']
            simpa [alphaParam, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm, mul_left_comm] using!
              h_const.add ((tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log 2)).sub
                (h_log_r_div_r.mul_const 10))
          have h_combined : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ)) - deltaParam r) Filter.atTop (nhds (alphaParam - 0)) := by
            refine' h_combined.sub _;
            exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          have := h_combined.eventually ( lt_mem_nhds <| show alphaParam - 0 > 0 from sub_pos.mpr <| by exact Real.log_pos <| by norm_num );
          filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ div_sub', lt_div_iff₀ ] at hr₁ <;> first | positivity | linarith;
        filter_upwards [ h_combined, ‹∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1› ] with r hr₁ hr₂ j hj using by unfold uParam; nlinarith [ hr₂.1, hr₂.2, show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
      filter_upwards [ ‹∀ᶠ r in atTop, 0 < deltaParam r ∧ deltaParam r < 1›, h_combined ] with r hr₁ hr₂ using fun j hj => div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hr₁.1 ) ) ) ( Real.exp_pos _ ) ) ( mul_pos zero_lt_two ( hr₂ j hj ) );
    filter_upwards [ h_combined, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, ( 1 - Real.exp ( -deltaParam r ) ) * Real.exp ( uParam r j ) / ( 2 * uParam r j ) ≤ ↑ ( # ( primeLayer r j ) ) › ] with r hr₁ hr₂ j hj;
    have := Real.log_le_log ( hr₁ j hj ) ( hr₂ j hj ) ; simp_all +decide ;
    rw [ Real.log_div ( by specialize hr₁ j hj.1 hj.2; aesop ) ( by specialize hr₁ j hj.1 hj.2; aesop ), Real.log_mul ( by specialize hr₁ j hj.1 hj.2; aesop ) ( by specialize hr₁ j hj.1 hj.2; aesop ), Real.log_exp ] at this ; linarith;
  -- Similarly, we can derive the required inequality for the second part.
  have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (2 * uParam r j) ≤ Real.log r + Real.log (2 * alphaParam) := by
    have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 2 * uParam r j ≤ 2 * alphaParam * r := by
      have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ alphaParam * r := by
        have h_uParam_le : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ vParam r := by
          have h_uParam_le : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, deltaParam r ≥ 0 := by
            norm_num [ deltaParam ];
            exact ⟨ 2, fun n hn j hj₁ hj₂ => div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by norm_num ) ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩;
          filter_upwards [ h_uParam_le ] with r hr j hj using sub_le_self _ ( mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr <| Finset.mem_Icc.mp hj |>.2 ) <| hr j hj )
        filter_upwards [ h_uParam_le, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ j hj ; refine le_trans ( hr₁ j hj ) ?_ ; norm_num [ vParam, alphaParam ] ; ring_nf ;
        nlinarith [ Real.log_pos one_lt_two, Real.log_nonneg ( show ( r : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      filter_upwards [ h_combined2 ] with r hr using fun j hj => by linarith [ hr j hj ] ;
    have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < uParam r j := by
      have h_combined2 : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, 0 < vParam r - ((r : ℝ) - j) * deltaParam r := by
        have h_vParam_pos : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold vParam; norm_num [ alphaParam ] ; ring_nf;
          -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          have h_const : Filter.Tendsto (fun r : ℕ => Real.log 2 * ((r : ℝ) * (r : ℝ)⁻¹))
              Filter.atTop (nhds (Real.log 2)) := by
            apply tendsto_const_nhds.congr'
            filter_upwards [Filter.eventually_ne_atTop 0] with r hr
            have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
            simp [hr']
          simpa [alphaParam, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm, mul_left_comm] using!
            h_const.add ((tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log 2)).sub
              (h_log_r_div_r.mul_const 10))
        have h_deltaParam_pos : Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        have h_combined2 : ∀ᶠ r in atTop, vParam r / (r : ℝ) > deltaParam r := by
          have := h_vParam_pos.sub h_deltaParam_pos;
          filter_upwards [ this.eventually ( lt_mem_nhds <| show alphaParam - 0 > 0 from sub_pos.mpr <| by exact Real.log_pos <| by norm_num ) ] with r hr using by linarith;
        filter_upwards [ h_combined2, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
        intro j hj; rw [ gt_iff_lt, lt_div_iff₀ ( by positivity ) ] at hr₁; nlinarith [ show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( j : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hj ], show ( r : ℝ ) ≥ 1 by norm_cast, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hr₂ ) ) ] ;
      exact h_combined2;
    filter_upwards [ ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * uParam r j ≤ 2 * alphaParam * ↑r›, h_combined2 ] with r hr₁ hr₂;
    intro j hj; rw [ ← Real.log_mul ( by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ) ( by norm_num [ alphaParam ] ) ] ; exact Real.log_le_log ( by linarith [ hr₂ j hj ] ) ( by linarith [ hr₁ j hj ] ) ;
  -- By combining the results from `primeLayer_card_lower` and `layer_card_ge_exp`, we can derive the required inequality for the first part.
  have h_combined1 : ∀ᶠ r in atTop, Real.log (1 - Real.exp (-deltaParam r)) ≥ -Real.log (Real.log r) + (Real.log (8 * alphaParam) - 1) := by
    -- By definition of $deltaParam$, we know that $deltaParam r = 8 * alphaParam / Real.log r$.
    have h_deltaParam : ∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1 := by
      norm_num [ deltaParam ];
      refine' ⟨ ⌈Real.exp ( 8 * alphaParam ) ⌉₊ + 1, fun n hn => ⟨ _, _ ⟩ ⟩;
      · exact div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ Nat.ceil_pos.mpr ( Real.exp_pos ( 8 * alphaParam ) ) ] ) ) );
      · rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith [ Nat.ceil_pos.mpr <| Real.exp_pos <| 8 * alphaParam ] ) ];
        have := Nat.lt_of_ceil_lt hn ; rw [ one_mul ] ; exact Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by linarith;
    -- Using the inequality $1 - e^{-\delta} \geq \delta / e$ for $\delta \in (0, 1]$, we get $\log(1 - e^{-\delta}) \geq \log(\delta / e) = \log \delta - 1$.
    have h_log_ineq : ∀ᶠ r in atTop, Real.log (1 - Real.exp (-deltaParam r)) ≥ Real.log (deltaParam r) - 1 := by
      filter_upwards [ h_deltaParam ] with r hr;
      rw [ ge_iff_le, sub_le_iff_le_add, Real.log_le_iff_le_exp ];
      · rw [ Real.exp_add, Real.exp_log ( sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hr.1 ) ];
        have := Real.add_one_le_exp ( deltaParam r );
        rw [ Real.exp_neg ];
        nlinarith [ hr.1, hr.2, Real.add_one_le_exp 1, Real.exp_pos ( deltaParam r ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( deltaParam r ) ) ), Real.exp_le_exp.2 hr.2 ];
      · linarith [ hr.1 ];
    filter_upwards [ h_log_ineq, h_deltaParam, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ hr₃;
    convert! hr₁ using 1 ; rw [ show deltaParam r = 8 * alphaParam / Real.log r by rfl ] ; rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr₃ ) ] ; ring;
  refine' h_contra ⟨ 1 - Real.log ( 8 * alphaParam ) + Real.log ( 2 * alphaParam ), _ ⟩;
  filter_upwards [ h_combined, h_combined2, h_combined1 ] with r hr₁ hr₂ hr₃;
  have := Finset.sum_le_sum hr₁;
  simp_all +decide [ Finset.sum_add_distrib, Lr ];
  have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.Icc 1 r ) => hr₂ i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ; norm_num at * ; nlinarith;

/-
**Cleaning is negligible in the log-sum.**  Eventually,
`∑_j log|𝒫_j^*| ≥ ∑_j log M_j - 1`.
-/
set_option maxHeartbeats 1000000 in
lemma clean_ge_primeLayer_log_sum :
    ∀ᶠ r : ℕ in atTop,
      (∑ j ∈ Finset.Icc 1 r, Real.log ((primeLayer r j).card : ℝ)) - 1
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * (Real.exp ((alphaParam / 4) * r)) / (Real.exp ((3 * alphaParam / 4) * r)) := by
    have h_log_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * ((badSet r).card : ℝ) / ((primeLayer r j).card : ℝ) := by
      have h_log_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) / 2 := by
        have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - Real.exp ((alphaParam / 4) * r) := by
          have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ) ≥ ((primeLayer r j).card : ℝ) - ((badSet r).card : ℝ) := by
            refine' Filter.Eventually.of_forall fun r j hj => _;
            simp +decide only [ge_iff_le, tsub_le_iff_right];
            exact_mod_cast le_trans ( Finset.card_le_card ( show primeLayer r j ⊆ primeLayer r j \ badSet r ∪ badSet r from fun x hx => by by_cases hx' : x ∈ badSet r <;> aesop ) ) ( Finset.card_union_le _ _ );
          filter_upwards [ h_card_bound, badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four ) ] with r hr₁ hr₂ using fun j hj => le_trans ( sub_le_sub_left hr₂ _ ) ( hr₁ j hj );
        have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((primeLayer r j).card : ℝ) ≥ Real.exp ((3 * alphaParam / 4) * r) := by
          convert! layer_card_ge_exp ( alphaParam / 4 ) ( by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] ) using 1;
          grind;
        have h_card_bound : ∀ᶠ r : ℕ in atTop, Real.exp ((alphaParam / 4) * r) ≤ (1 / 2) * Real.exp ((3 * alphaParam / 4) * r) := by
          have h_card_bound : ∀ᶠ r : ℕ in atTop, Real.exp ((alphaParam / 4) * r) ≤ Real.exp ((3 * alphaParam / 4) * r - Real.log 2) := by
            norm_num [ alphaParam ];
            exact ⟨ 2, fun n hn => by nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) ≥ 2 by norm_cast ] ⟩;
          filter_upwards [ h_card_bound ] with r hr using hr.trans_eq ( by rw [ Real.exp_sub, Real.exp_log ( by positivity ) ] ; ring );
        filter_upwards [ ‹∀ᶠ r : ℕ in atTop, ∀ j ∈ Icc 1 r, ↑ ( # ( cleanLayer r j ) ) ≥ ↑ ( # ( primeLayer r j ) ) - Real.exp ( alphaParam / 4 * ↑r ) ›, ‹∀ᶠ r : ℕ in atTop, ∀ j ∈ Icc 1 r, ↑ ( # ( primeLayer r j ) ) ≥ Real.exp ( 3 * alphaParam / 4 * ↑r ) ›, h_card_bound ] with r hr₁ hr₂ hr₃ using fun j hj => by linarith [ hr₁ j hj, hr₂ j hj, hr₃ ] ;
      filter_upwards [ h_log_bound ] with r hr j hj;
      by_cases h : ( primeLayer r j ).card = 0 <;> simp_all +decide only [ge_iff_le, tsub_le_iff_right];
      · exact Real.log_natCast_nonneg _;
      · have h_log_bound : Real.log ((cleanLayer r j).card : ℝ) ≥ Real.log ((primeLayer r j).card : ℝ) - 2 * ((primeLayer r j).card - (cleanLayer r j).card : ℝ) / ((primeLayer r j).card : ℝ) := by
          have h_log_bound : Real.log ((cleanLayer r j).card / (primeLayer r j).card : ℝ) ≥ -2 * (1 - (cleanLayer r j).card / (primeLayer r j).card : ℝ) := by
            have h_log_bound : ∀ x : ℝ, 1 / 2 ≤ x ∧ x ≤ 1 → Real.log x ≥ -2 * (1 - x) := by
              exact fun x hx => by nlinarith [ Real.log_inv x ▸ Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < x ) ), mul_inv_cancel₀ ( ne_of_gt ( by linarith : 0 < x ) ) ] ;
            apply h_log_bound;
            exact ⟨ by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ] ; have := hr j hj.1 hj.2; norm_num at *; linarith, by rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ] ; have := Finset.card_le_card <| show cleanLayer r j ⊆ primeLayer r j from Finset.sdiff_subset; norm_num at *; linarith ⟩;
          rw [ Real.log_div ] at h_log_bound <;> norm_num at *;
          · convert! h_log_bound using 1 ; ring_nf;
            rw [ mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Classical.choose_spec <| Finset.nonempty_of_ne_empty h ) ] ; ring;
          · exact Finset.Nonempty.ne_empty ( Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ) ) ( by norm_num ) ) ( hr j hj.1 hj.2 ) ) ) );
          · assumption;
        have h_card_bound : (cleanLayer r j).card + (badSet r).card ≥ (primeLayer r j).card := by
          rw [ ← Finset.card_union_add_card_inter ];
          exact le_add_right ( Finset.card_le_card fun x hx => by unfold cleanLayer; aesop );
        field_simp at *;
        rw [ add_div', le_div_iff₀ ] <;> nlinarith [ hr j hj.1 hj.2, show ( primeLayer r j |> Finset.card : ℝ ) > 0 from Nat.cast_pos.mpr ( Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ), show ( cleanLayer r j |> Finset.card : ℝ ) + ( badSet r |> Finset.card : ℝ ) ≥ ( primeLayer r j |> Finset.card : ℝ ) from mod_cast h_card_bound, mul_div_cancel₀ ( 2 * ( ( primeLayer r j |> Finset.card : ℝ ) - ( cleanLayer r j |> Finset.card : ℝ ) ) ) ( show ( primeLayer r j |> Finset.card : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty h ) ];
    have h_card_bound : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r, ((primeLayer r j).card : ℝ) ≥ Real.exp ((3 * alphaParam / 4) * r) := by
      convert! layer_card_ge_exp ( alphaParam / 4 ) ( by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] ) using 1;
      grind +qlia;
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ r : ℕ in atTop, ((badSet r).card : ℝ) ≤ Real.exp ((alphaParam / 4) * r) := by
      have := badSet_card_small ( alphaParam / 4 ) ( by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_four );
      exact ⟨ 1, zero_lt_one, this ⟩;
    refine' ⟨ C₁, hC₁.1, _ ⟩;
    filter_upwards [ h_log_bound, h_card_bound, hC₁.2 ] with r hr₁ hr₂ hr₃ j hj using le_trans ( sub_le_sub_left ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hr₂ j hj, hr₃, Real.exp_pos ( 3 * alphaParam / 4 * r ), Real.exp_pos ( alphaParam / 4 * r ) ] ) _ ) ( hr₁ j hj );
  have h_sum_bound : ∀ᶠ r : ℕ in atTop, 2 * r * (Real.exp ((alphaParam / 4) * r)) / (Real.exp ((3 * alphaParam / 4) * r)) ≤ 1 := by
    have h_sum_bound : Filter.Tendsto (fun r : ℕ => 2 * (r : ℝ) * Real.exp (-(alphaParam / 2) * r)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{\alpha}{2} r$, therefore the expression becomes $\frac{4}{\alpha} y e^{-y}$.
      suffices h_y : Filter.Tendsto (fun y : ℝ => (4 / alphaParam) * y * Real.exp (-y)) Filter.atTop (nhds 0) by
        convert! h_y.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( show 0 < alphaParam / 2 by exact div_pos ( Real.log_pos one_lt_two ) zero_lt_two ) ) using 2 ; norm_num ; ring_nf;
        norm_num [ alphaParam ];
      simpa [ mul_assoc ] using! Filter.Tendsto.const_mul ( 4 / alphaParam ) ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    filter_upwards [ h_sum_bound.eventually ( gt_mem_nhds zero_lt_one ) ] with r hr using by convert! hr.le using 1; rw [ mul_div_assoc, ← Real.exp_sub ] ; ring_nf;
  filter_upwards [ hC₁.2, h_sum_bound ] with r hr₁ hr₂;
  refine' le_trans _ ( Finset.sum_le_sum hr₁ );
  norm_num [ mul_div_assoc ] at * ; linarith

/-
**The target rate dominates the second-order terms.**  For every constant `K`
and every `ε > 0`, eventually,
`r·log r + r·log log r + K·r ≤ (c₀ + ε)·√{L_r}·log L_r`.
-/
set_option maxHeartbeats 1000000 in
lemma rate_dominates (K : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      (r : ℝ) * Real.log r + (r : ℝ) * Real.log (Real.log r) + K * (r : ℝ)
        ≤ (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r) := by
  -- Prove that `Lr r / r^2 → alphaParam` as `r → ∞`.
  have h1 : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
    -- We'll use the fact that $vParam r / r \to \alpha$ and $\deltaParam r * (r - 1) / (2r) \to 0$ as $r \to \infty$.
    have h_vParam : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
      unfold vParam; ring_nf; norm_num [ alphaParam ] ;
      -- We'll use the fact that $\frac{\log r}{r} \to 0$ as $r \to \infty$.
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      have h_const : Filter.Tendsto (fun r : ℕ => Real.log 2 * ((r : ℝ) * (r : ℝ)⁻¹))
          Filter.atTop (nhds (Real.log 2)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ne_atTop 0] with r hr
        have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
        simp [hr']
      simpa [alphaParam, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm, mul_left_comm] using!
        h_const.add ((tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log 2)).sub
          (h_log_r_div_r.mul_const 10))
    have h_deltaParam : Filter.Tendsto (fun r : ℕ => deltaParam r * (r - 1) / (2 * (r : ℝ))) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\deltaParam r = 8 * alphaParam / \log r$.
      suffices h_deltaParam_simplified : Filter.Tendsto (fun r : ℕ => (8 * alphaParam / Real.log r) * (1 - 1 / (r : ℝ)) / 2) Filter.atTop (nhds 0) by
        refine h_deltaParam_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ show deltaParam r = 8 * alphaParam / Real.log r by rfl ] ; rw [ one_sub_div ( by positivity ) ] ; ring );
      simpa using! Filter.Tendsto.div_const ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) 2;
    convert! h_vParam.sub h_deltaParam using 2 <;> norm_num [ Lr_closed ] ; ring_nf;
    grind;
  -- Prove that `Real.log (Lr r) / Real.log r → 2` as `r → ∞`.
  have h3 : Filter.Tendsto (fun r : ℕ => Real.log (Lr r) / Real.log r) Filter.atTop (nhds 2) := by
    -- Use the fact that $\log(L_r) = \log((L_r / r^2) * r^2) = \log(L_r / r^2) + 2 \log(r)$.
    have h_log : Filter.Tendsto (fun r : ℕ => (Real.log (Lr r / (r : ℝ) ^ 2) + 2 * Real.log r) / Real.log r) Filter.atTop (nhds 2) := by
      have h_log : Filter.Tendsto (fun r : ℕ => Real.log (Lr r / (r : ℝ) ^ 2) / Real.log r) Filter.atTop (nhds 0) := by
        convert! Filter.Tendsto.div_atTop ( Filter.Tendsto.log h1 _ ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) using 1 ; norm_num [ alphaParam ];
      simpa [ add_div ] using! h_log.add_const 2 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_div_cancel_right₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
    refine h_log.congr' ?_;
    filter_upwards [ h1.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two ) ] with r hr;
    rw [ Real.log_div ] <;> norm_num;
    · aesop;
    · rintro rfl; norm_num at hr;
  -- Prove that `Real.log (Real.log r) / Real.log (Lr r) → 0` and `1 / Real.log (Lr r) → 0` as `r → ∞`.
  have h4 : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log (Lr r)) Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log r) Filter.atTop (nhds 0) := by
      -- Let $y = \log r$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
    have := h4.div h3;
    simpa using! this two_ne_zero |> fun h => h.congr' ( by filter_upwards [ h3.eventually_ne two_ne_zero ] with x hx using by rw [ Pi.div_apply, div_div_div_cancel_right₀ ( by aesop ) ] )
  have h5 : Filter.Tendsto (fun r : ℕ => 1 / Real.log (Lr r)) Filter.atTop (nhds 0) := by
    refine' tendsto_const_nhds.div_atTop _;
    exact Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( Lr_tendsto_atTop.eventually_ge_atTop x ) with ⟨ r, hr ⟩ ; exact ⟨ r, fun n hn => hr n hn ⟩ ;
  -- Prove that `(r*log r + r*log log r + K*r)/D r → c₀` as `r → ∞`.
  have h6 : Filter.Tendsto (fun r : ℕ => (r * Real.log r + r * Real.log (Real.log r) + K * r) / (Real.sqrt (Lr r) * Real.log (Lr r))) Filter.atTop (nhds (c₀)) := by
    -- Prove that `(r/Real.sqrt (Lr r)) → 1/Real.sqrt alphaParam` as `r → ∞`.
    have h2 : Filter.Tendsto (fun r : ℕ => (r : ℝ) / Real.sqrt (Lr r)) Filter.atTop (nhds (1 / Real.sqrt alphaParam)) := by
      have h2 : Filter.Tendsto (fun r : ℕ => Real.sqrt (Lr r / (r : ℝ) ^ 2)) Filter.atTop (nhds (Real.sqrt alphaParam)) := by
        exact Filter.Tendsto.sqrt h1;
      convert! h2.inv₀ _ using 1 <;> norm_num [ alphaParam ];
      positivity;
    convert! Filter.Tendsto.add ( Filter.Tendsto.add ( h2.mul ( h3.inv₀ ( by positivity ) ) ) ( h2.mul h4 ) ) ( h2.const_mul K |> Filter.Tendsto.mul <| h5 ) using 2 <;> ring_nf! ; norm_num [ c₀ ] ; ring!;
    unfold c₀ alphaParam; ring;
  have := h6.eventually ( gt_mem_nhds <| show c₀ < c₀ + ε by linarith );
  filter_upwards [ this, Lr_tendsto_atTop.eventually_gt_atTop 1, h3.eventually ( lt_mem_nhds one_lt_two ) ] with r hr₁ hr₂ hr₃;
  rw [ div_lt_iff₀ ] at hr₁ <;> nlinarith [ show 0 < Real.sqrt ( Lr r ) * Real.log ( Lr r ) by exact mul_pos ( Real.sqrt_pos.mpr ( by positivity ) ) ( Real.log_pos hr₂ ) ]

/-- **Asymptotic size of the cleaned product.**  For every `ε > 0`, eventually,
`∑_j log|𝒫_j^*| ≥ L_r - (c₀ + ε)·√{L_r}·log L_r`. -/
lemma clean_product_asymp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Lr r - (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r)
        ≤ ∑ j ∈ Finset.Icc 1 r, Real.log ((cleanLayer r j).card : ℝ) := by
  obtain ⟨K, hK⟩ := primeLayer_log_sum_lower
  filter_upwards [hK, clean_ge_primeLayer_log_sum, rate_dominates (K + 1) ε hε,
    Filter.eventually_ge_atTop 1]
    with r hr₁ hr₂ hr₃ hr₄
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr₄
  nlinarith [hr₁, hr₂, hr₃, hr]

/-
**Theorem 5.3 along the subsequence `x = e^{L_r}`.**  For every `ε > 0`,
eventually in `r`,
`A(e^{L_r}) ≥ e^{L_r} · exp(-(c₀ + ε)·√{L_r}·log L_r)`.
-/
theorem lower_bound_subsequence (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Real.exp (Lr r) *
          Real.exp (-(c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r))
        ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
  obtain ⟨ C, hC, hcrux ⟩ := clean_count_crux;
  -- Use `clean_product_asymp` to bound the product of the sizes of the clean layers.
  have h_prod_bound : ∀ᶠ r : ℕ in atTop,
      (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) ≥ Real.exp (Lr r - (c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) := by
        have := clean_product_asymp ( ε / 2 ) ( half_pos hε );
        filter_upwards [ this, cleanLayer_card_pos ] with r hr₁ hr₂ using le_trans ( Real.exp_le_exp.mpr hr₁ ) ( by rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( Nat.cast_pos.mpr <| hr₂ _ ‹_› ) ] );
  -- Use `cleanLayer_card_pos` to bound the size of the bad set.
  have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
      (1 - C / (r : ℝ) ^ 9) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) ≥
      (1 / 2) * (∏ j ∈ Finset.Icc 1 r, ((cleanLayer r j).card : ℝ)) := by
        have h_bad_set_bound : ∀ᶠ r : ℕ in atTop, C / (r : ℝ) ^ 9 ≤ 1 / 2 := by
          exact Filter.eventually_atTop.mpr ⟨ ⌈C * 2⌉₊ + 1, fun r hr => by rw [ div_le_div_iff₀ ] <;> norm_num <;> nlinarith [ Nat.le_ceil ( C * 2 ), show ( r : ℝ ) ≥ ⌈C * 2⌉₊ + 1 by exact_mod_cast hr, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 2, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 3, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 4, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 5, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 6, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 7, pow_pos ( show ( r : ℝ ) > 0 by norm_cast; linarith ) 8 ] ⟩;
        filter_upwards [ h_bad_set_bound, h_prod_bound ] with r hr₁ hr₂ using mul_le_mul_of_nonneg_right ( by linarith ) ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ );
  -- Use `Lr_tendsto_atTop` to bound the size of the bad set.
  have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
      (1 / 2) * Real.exp (Lr r - (c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) ≥
      Real.exp (Lr r - (c₀ + ε) * Real.sqrt (Lr r) * Real.log (Lr r)) := by
        have h_bad_set_bound : ∀ᶠ r : ℕ in atTop,
            (ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r) ≥ Real.log 2 := by
              have h_bad_set_bound : Filter.Tendsto (fun r : ℕ => Real.sqrt (Lr r) * Real.log (Lr r)) Filter.atTop Filter.atTop := by
                have h_bad_set_bound : Filter.Tendsto (fun r : ℕ => Lr r) Filter.atTop Filter.atTop := by
                  convert! Lr_tendsto_atTop using 1;
                exact Filter.Tendsto.atTop_mul_atTop₀ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| h_bad_set_bound ) ( Real.tendsto_log_atTop.comp h_bad_set_bound );
              filter_upwards [ h_bad_set_bound.eventually_gt_atTop ( Real.log 2 / ( ε / 2 ) ) ] with r hr using by nlinarith [ mul_div_cancel₀ ( Real.log 2 ) ( by positivity : ( ε / 2 ) ≠ 0 ) ] ;
        filter_upwards [ h_bad_set_bound ] with r hr;
        rw [ show ( 1 / 2 : ℝ ) = Real.exp ( -Real.log 2 ) by norm_num [ Real.exp_neg, Real.exp_log ] ] ; rw [ ← Real.exp_add ] ; ring_nf at * ; norm_num at *;
        linarith;
  filter_upwards [ hcrux, h_prod_bound, ‹∀ᶠ r : ℕ in atTop, ( 1 - C / ( r : ℝ ) ^ 9 ) * ∏ j ∈ Icc 1 r, ( # ( cleanLayer r j ) : ℝ ) ≥ 1 / 2 * ∏ j ∈ Icc 1 r, ( # ( cleanLayer r j ) : ℝ ) ›, h_bad_set_bound ] with r hr₁ hr₂ hr₃ hr₄ using by rw [ ← Real.exp_add ] ; ring_nf at *; linarith;

end Erdos768
