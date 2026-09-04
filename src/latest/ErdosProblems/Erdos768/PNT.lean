import Mathlib
import ErdosProblems.Erdos49.PNT.MediumPNT

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Prime number theorem with error term, and primes in logarithmic intervals

This file discharges `Erdos768.primes_in_log_interval` (Lemma 2.8 of the paper).

The paper's proof has two layers:

* **Layer A (elementary reduction).** Given the prime number theorem with a
  power-saving error term
  `π(y) = li(y) + O(y · e^{-c (log y)^{1/10}})`,
  the logarithmic-interval count follows by an elementary calculus estimate.
  This layer is developed here as `count_eq_primeCounting_diff`,
  `main_term_ratio_tendsto`, `error_over_denom_tendsto`, and assembled in
  `primes_in_log_interval_proof`.

* **Layer B (the analytic input).** The error-term PNT itself, recorded as
  `pnt_li_error`.  It is derived from `MediumPNT` (the prime number theorem for
  the Chebyshev `ψ` function with error `O(x · e^{-c (log x)^{1/10}})`, from the
  `PrimeNumberTheoremAnd` project) via the elementary passage `ψ → θ → π → li`,
  using the Chebyshev machinery in `Mathlib.NumberTheory.Chebyshev`.

  Note on the error exponent: the strongest error-term PNT that is currently
  available in formalised form is the medium-strength one with exponent
  `(log y)^{1/10}` (via `MediumPNT`); this is what `pnt_li_error` records.  Any
  fixed positive power of `log y` in the exponent is more than enough for Layer A
  (the denominator there is only polynomial in `log y`), so this suffices for the
  Erdős 768 argument.
-/

open scoped Classical BigOperators Topology Nat.Prime
open Filter Asymptotics

namespace Erdos768

/-- The main term `∫₂ʸ dt / log t` (a shifted logarithmic integral, `li(y) - li(2)`). -/
noncomputable def li2 (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-!
### Bridge lemmas: from `MediumPNT` (about `ψ`) to `pnt_li_error` (about `π - li`)

All error terms below use the family `errBound c x = x · e^{-c (log x)^{1/10}}`.
-/

/-
Monotonicity of the error family in the constant: a larger constant gives a
smaller bound, hence `errBound c₁ = O(errBound c₂)` when `c₂ ≤ c₁`.
-/
lemma errBound_isBigO_of_le {c₁ c₂ : ℝ} (_hc₂ : 0 ≤ c₂) (h : c₂ ≤ c₁) :
    (fun x : ℝ => x * Real.exp (-c₁ * Real.log x ^ ((1 : ℝ) / 10)))
      =O[atTop] (fun x : ℝ => x * Real.exp (-c₂ * Real.log x ^ ((1 : ℝ) / 10))) := by
  refine' Asymptotics.isBigO_iff.mpr _;
  refine' ⟨ 1, _ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx ; rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; norm_num;
  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ Real.rpow_nonneg ( Real.log_nonneg hx ) ( 1 / 10 : ℝ ) ] ) ( by positivity )

/-
Constants are `O` of the error family (which tends to `+∞`).
-/
lemma one_isBigO_errBound {c : ℝ} (_hc : 0 < c) :
    (fun _ : ℝ => (1 : ℝ))
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  -- We'll use the fact that $x * \exp(-c * (\log x)^{1/10})$ tends to infinity as $x$ tends to infinity.
  have h_tendsto : Filter.Tendsto (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) Filter.atTop Filter.atTop := by
    have := x_ε_to_inf c ( show ( 1 : ℝ ) / 10 < 1 by norm_num );
    convert! this using 1;
  rw [ Asymptotics.isBigO_iff ];
  exact ⟨ 1, by filter_upwards [ h_tendsto.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; linarith ⟩

/-
`2√x · log x` is negligible compared with the error family.
-/
lemma sqrt_mul_log_isBigO_errBound {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => 2 * Real.sqrt x * Real.log x)
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  have h_exp : Filter.Tendsto (fun x : ℝ => (2 * Real.sqrt x * Real.log x) / (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) Filter.atTop (nhds 0) := by
    -- Simplify the expression inside the limit.
    suffices h_simplified : Filter.Tendsto (fun x : ℝ => 2 * Real.log x * Real.exp (Real.log x / 2 - Real.log x + c * (Real.log x) ^ ((1 : ℝ) / 10))) Filter.atTop (nhds 0) by
      refine h_simplified.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring_nf ; norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log hx ] ; ring_nf;
      rw [ ← Real.exp_neg ] ; rw [ Real.exp_neg, Real.exp_mul, Real.exp_log hx ] ; ring_nf;
      rw [ ← Real.sqrt_eq_rpow ] ; rw [ ← Real.sqrt_div_self ] ; ring;
    -- Let $y = \log x$, therefore the expression becomes $2y \exp(-y/2 + c y^{1/10})$.
    suffices h_log : Filter.Tendsto (fun y : ℝ => 2 * y * Real.exp (-y / 2 + c * y ^ ((1 : ℝ) / 10))) Filter.atTop (nhds 0) by
      convert! h_log.comp ( Real.tendsto_log_atTop ) using 2 ; norm_num ; ring_nf;
      norm_num;
    -- We can factor out $y$ and use the fact that $e^{-y/2 + cy^{1/10}}$ tends to $0$ faster than any polynomial growth.
    suffices h_factor : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y / 4)) Filter.atTop (nhds 0) by
      -- We can bound the expression $y \exp(-y/2 + cy^{1/10})$ above by $y \exp(-y/4)$ for sufficiently large $y$.
      have h_bound : ∃ Y : ℝ, ∀ y > Y, y * Real.exp (-y / 2 + c * y ^ (1 / 10 : ℝ)) ≤ y * Real.exp (-y / 4) := by
        -- We can choose $Y$ such that for all $y > Y$, $c * y^{1/10} \leq y / 4$.
        obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ y > Y, c * y ^ (1 / 10 : ℝ) ≤ y / 4 := by
          -- We can choose $Y$ such that for all $y > Y$, $c \leq y^{9/10} / 4$.
          obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ y > Y, c ≤ y ^ (9 / 10 : ℝ) / 4 := by
            exact ⟨ ( c * 4 ) ^ ( 10 / 9 : ℝ ), fun y hy => by rw [ le_div_iff₀ ( by positivity ) ] ; exact le_trans ( by rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) hy.le ( by positivity ) ) ⟩;
          exact ⟨ Max.max Y 1, fun y hy => by have := hY y ( lt_of_le_of_lt ( le_max_left _ _ ) hy ) ; rw [ show ( 9 / 10 : ℝ ) = 1 - 1 / 10 by norm_num, Real.rpow_sub ( by linarith [ le_max_right Y 1 ] ) ] at this; norm_num at * ; nlinarith [ Real.rpow_pos_of_pos ( by linarith [ le_max_right Y 1 ] : 0 < y ) ( 1 / 10 : ℝ ), mul_div_cancel₀ ( y : ℝ ) ( ne_of_gt ( Real.rpow_pos_of_pos ( by linarith [ le_max_right Y 1 ] : 0 < y ) ( 1 / 10 : ℝ ) ) ) ] ⟩;
        exact ⟨ Max.max Y 1, fun y hy => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith [ hY y <| lt_of_le_of_lt ( le_max_left _ _ ) hy ] ) <| by linarith [ le_max_right Y 1 ] ⟩;
      refine' squeeze_zero_norm' _ ( by simpa using! h_factor.const_mul 2 );
      filter_upwards [ Filter.eventually_gt_atTop h_bound.choose, Filter.eventually_gt_atTop 0 ] with y hy₁ hy₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; linarith [ h_bound.choose_spec y hy₁ ] ;
    -- Let $z = \frac{y}{4}$, so we can rewrite the limit as $\lim_{z \to \infty} 4z e^{-z}$.
    suffices h_lim_z : Filter.Tendsto (fun z : ℝ => 4 * z * Real.exp (-z)) Filter.atTop (nhds 0) by
      convert! h_lim_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 4 : ℝ ) ⁻¹ ) ) using 2 ; norm_num ; ring_nf;
    simpa [ mul_assoc ] using! Filter.Tendsto.const_mul 4 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
  rw [ Asymptotics.isBigO_iff' ];
  obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp h_exp 1 zero_lt_one;
  refine' ⟨ 1, zero_lt_one, Filter.eventually_atTop.mpr ⟨ Max.max N 2, fun x hx => _ ⟩ ⟩ ; specialize hN x ( le_trans ( le_max_left _ _ ) hx ) ; norm_num at *;
  rw [ div_lt_one ( mul_pos ( abs_pos.mpr ( by linarith ) ) ( Real.exp_pos _ ) ) ] at hN ; linarith

/-
**`θ` has the same power-saving error as `ψ`.**  From `MediumPNT` and the
elementary bound `|ψ - θ| ≤ 2√x log x`.
-/
lemma theta_sub_id_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => Chebyshev.theta x - x)
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨ c, hc, hψ ⟩ := MediumPNT;
  refine' ⟨ c, hc, _ ⟩;
  have hθ : (fun x => Chebyshev.theta x - Chebyshev.psi x) =O[atTop] (fun x => 2 * Real.sqrt x * Real.log x) := by
    refine' Asymptotics.IsBigO.of_bound 1 _;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ one_mul ] ; exact le_trans ( by simpa [ abs_sub_comm ] using! Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx ) ( le_abs_self _ ) ;
  convert! hθ.trans ( sqrt_mul_log_isBigO_errBound hc ) |> Asymptotics.IsBigO.add <| hψ using 1;
  aesop

/-
Integration by parts for the logarithmic integral:
`∫₂ˣ dt/log t = x/log x - 2/log 2 + ∫₂ˣ dt/log² t`.
-/
lemma li2_eq_sub_add_integral {x : ℝ} (hx : 2 ≤ x) :
    li2 x = x / Real.log x - 2 / Real.log 2
      + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have h_parts : ∀ t ∈ Set.Icc (2 : ℝ) x, deriv (fun t => t / Real.log t) t = 1 / Real.log t - 1 / (Real.log t)^2 := by
    intro t ht; norm_num [ show t ≠ 0 by linarith [ ht.1 ], show Real.log t ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ], Real.differentiableAt_log, div_eq_mul_inv ] ; ring;
  have h_parts : ∫ t in (2:ℝ)..x, deriv (fun t => t / Real.log t) t = (x / Real.log x) - (2 / Real.log 2) := by
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    · rfl;
    · exact fun t ht => DifferentiableAt.div ( differentiableAt_id ) ( Real.differentiableAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) );
    · rw [ Set.uIcc_of_le hx ];
      exact ContinuousOn.congr ( by exact ContinuousOn.sub ( continuousOn_const.div ( Real.continuousOn_log.mono <| by norm_num ) fun t ht => ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ] ) <| continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by norm_num ) 2 ) fun t ht => ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ ht.1 ] ) h_parts
  generalize_proofs at *; (
  rw [ ← h_parts, intervalIntegral.integral_congr fun t ht => ‹∀ t ∈ Set.Icc 2 x, deriv ( fun t => t / Real.log t ) t = 1 / Real.log t - 1 / Real.log t ^ 2› t <| by simpa [ hx ] using! ht ] ; ring_nf;
  rw [ intervalIntegral.integral_sub ] <;> norm_num [ li2 ];
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using! ht ) ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using! ht ) ] ) ) ) ) ..;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using! ht ) ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using! ht ) ] ) ) ) ) ) ..)

/-
The exact formula for `π - li` in terms of `θ - id`, obtained by combining
Abel summation (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`) with the
integration by parts `li2_eq_sub_add_integral`.
-/
lemma primeCounting_sub_li2_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - li2 x
      = (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
  convert! congr_arg₂ ( · - · ) ( Chebyshev.primeCounting_eq_theta_div_log_add_integral hx ) ( li2_eq_sub_add_integral hx ) using 1 ; ring_nf!;
  rw [ intervalIntegral.integral_sub ] ; ring_nf!;
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases h : t = 0 <;> simp [h]
  · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
    have := Chebyshev.integrableOn_theta_div_id_mul_log_sq x; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ] ;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact ContinuousOn.mul ( ContinuousOn.mul continuousOn_id ( ContinuousOn.inv₀ continuousOn_id fun t ht => by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ContinuousOn.pow ( ContinuousOn.inv₀ ( Real.continuousOn_log.mono <| by norm_num [ hx ] ) fun t ht => ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith ) _ )

/-
`√x` is negligible compared with the error family.
-/
lemma sqrt_isBigO_errBound {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.sqrt x)
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  have h_sqrt : (fun x => Real.sqrt x) =O[atTop] (fun x => 2 * Real.sqrt x * Real.log x) := by
    rw [ Asymptotics.isBigO_iff ];
    use 1; filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ Real.norm_of_nonneg ( Real.sqrt_nonneg x ), Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( Real.sqrt_nonneg x ) ) ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ; nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith [ Real.add_one_le_exp 1 ] ), Real.add_one_le_exp 1, Real.log_exp 1, Real.log_le_log ( by positivity ) hx.le ] ;
  exact h_sqrt.trans ( by simpa using! sqrt_mul_log_isBigO_errBound hc )

/-
**Head of the error integral** `[2, √x]`: the integrand is `O(1/log² t)` via
the crude bound `θ t ≤ log 4 · t`, so the integral is `O(√x)`.
-/
lemma integral_head_isBigO_sqrt :
    (fun x : ℝ => ∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
      =O[atTop] (fun x : ℝ => Real.sqrt x) := by
  refine' Asymptotics.isBigO_iff.mpr _;
  refine' ⟨ ( Real.log 4 + 1 ) / ( Real.log 2 ) ^ 2, _ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop 4 ] with x hx ; norm_num at *;
  -- By definition of $C$, we know that for all $t \in [2, \sqrt{x}]$, $|(Chebyshev.theta t - t) / (t * (Real.log t)^2)| \leq C$.
  have h_bound : ∀ t ∈ Set.Icc 2 (Real.sqrt x), |(Chebyshev.theta t - t) / (t * (Real.log t)^2)| ≤ (Real.log 4 + 1) / (Real.log 2)^2 := by
    intros t ht
    have h_theta_le : Chebyshev.theta t ≤ Real.log 4 * t := by
      exact Chebyshev.theta_le_log4_mul_x ( by linarith [ ht.1 ] )
    have h_abs : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
      rw [ abs_le ];
      constructor <;> nlinarith [ show 0 ≤ Chebyshev.theta t from Chebyshev.theta_nonneg t, show 0 < t from by linarith [ ht.1 ], show 0 < Real.log 4 from Real.log_pos ( by norm_num ) ]
    have h_div : |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ (Real.log 4 + 1) / (Real.log t) ^ 2 := by
      rw [ abs_div, abs_of_nonneg ( show 0 ≤ t * Real.log t ^ 2 by exact mul_nonneg ( by linarith [ ht.1 ] ) ( sq_nonneg _ ) ) ];
      rw [ div_le_div_iff₀ ] <;> nlinarith [ ht.1, ht.2, show 0 < t * Real.log t ^ 2 by exact mul_pos ( by linarith [ ht.1 ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ ht.1 ] ) ) ) ]
    have h_log_bound : Real.log t ≥ Real.log 2 := by
      exact Real.log_le_log ( by norm_num ) ht.1
    have h_final : (Real.log 4 + 1) / (Real.log t) ^ 2 ≤ (Real.log 4 + 1) / (Real.log 2) ^ 2 := by
      gcongr
    exact le_trans h_div h_final;
  rw [ intervalIntegral.integral_of_le ( Real.le_sqrt_of_sq_le ( by linarith ) ) ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun t => ( Real.log 4 + 1 ) / Real.log 2 ^ 2;
  · exact Filter.Eventually.of_forall fun t => norm_nonneg _;
  · norm_num;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_bound t <| Set.Ioc_subset_Icc_self ht;
  · norm_num [ mul_comm, abs_of_nonneg ( Real.sqrt_nonneg x ) ];
    exact mul_le_mul_of_nonneg_left ( max_le_iff.mpr ⟨ by linarith [ Real.sqrt_nonneg x ], by linarith [ Real.sqrt_nonneg x ] ⟩ ) ( by positivity )

/-
**Tail of the error integral** `[√x, x]`: here `|θ t - t| ≤ K t e^{-c(log t)^{1/10}}`
with `e^{-c(log t)^{1/10}}` decreasing, bounded by `e^{-c(½ log x)^{1/10}} =
e^{-c' (log x)^{1/10}}`, and `1/log² t ≤ 4/log² x`; integrating over a length `≤ x`
gives the power-saving bound.
-/
lemma integral_tail_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∫ t in Real.sqrt x..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc⟩ : ∃ c, 0 < c ∧ (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    convert! theta_sub_id_isBigO using 1;
  obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, ∀ t ≥ Real.sqrt x, |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ K * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 := by
    obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, ∀ t ≥ Real.sqrt x, |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * (Real.log t) ^ ((1 : ℝ) / 10)) := by
      obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, |Chebyshev.theta x - x| ≤ K * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
        have := hc.2.exists_pos;
        obtain ⟨ K, hK₁, hK₂ ⟩ := this; use K, hK₁; filter_upwards [ hK₂.bound, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂; simp_all +decide [ mul_assoc, abs_of_pos ] ;
      obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hK;
      exact ⟨ K, hKpos, Filter.eventually_atTop.mpr ⟨ M ^ 2, fun x hx => fun t ht => hM t <| by nlinarith [ Real.sqrt_nonneg x, Real.mul_self_sqrt ( show 0 ≤ x by nlinarith ) ] ⟩ ⟩;
    refine' ⟨ K, hKpos, _ ⟩;
    filter_upwards [ hK, Filter.eventually_gt_atTop 4 ] with x hx₁ hx₂;
    intro t ht
    have h_abs : |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) := by
      refine le_trans ( hx₁ t ht ) ?_;
      exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonpos_left ( Real.rpow_le_rpow ( Real.log_nonneg <| Real.le_sqrt_of_sq_le <| by linarith ) ( Real.log_le_log ( by positivity ) ht ) <| by positivity ) <| by linarith ) <| mul_nonneg hKpos.le <| by linarith [ Real.sqrt_nonneg x ] ;
    rw [ abs_div, abs_of_nonneg ( show 0 ≤ t * Real.log t ^ 2 by exact mul_nonneg ( by linarith [ Real.sqrt_nonneg x ] ) ( sq_nonneg _ ) ) ];
    rw [ div_le_div_iff₀ ];
    · refine le_trans ( mul_le_mul_of_nonneg_right h_abs ( sq_nonneg _ ) ) ?_;
      ring_nf;
      exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| Real.le_sqrt_of_sq_le <| by linarith ) ( Real.log_le_log ( Real.sqrt_pos.mpr <| by linarith ) ht ) _ ) <| mul_nonneg ( mul_nonneg hKpos.le <| by linarith [ Real.sqrt_nonneg x ] ) <| Real.exp_nonneg _;
    · exact mul_pos ( by linarith [ Real.sqrt_pos.mpr ( show 0 < x by linarith ) ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.sqrt_pos.mpr ( show 0 < x by linarith ), Real.lt_sqrt_of_sq_lt ( by linarith : 1 ^ 2 < x ) ] ) ) );
    · exact sq_pos_of_pos <| Real.log_pos <| Real.lt_sqrt_of_sq_lt <| by linarith;
  -- Using the bound from hK, we can show that the integral is O(x * exp(-c' * (log x)^(1/10))).
  have h_integral_bound : ∀ᶠ x in atTop, |∫ t in (Real.sqrt x)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ K * x * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 := by
    filter_upwards [ hK, Filter.eventually_gt_atTop 4 ] with x hx hx';
    rw [ intervalIntegral.integral_of_le ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ) ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun t => K * Real.exp ( -c * Real.log ( Real.sqrt x ) ^ ( 1 / 10 : ℝ ) ) / Real.log ( Real.sqrt x ) ^ 2;
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using hx t ht.1.le;
    · norm_num [ mul_assoc, mul_div_assoc ];
      rw [ max_eq_left ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ x by linarith ) ] ) ] ; ring_nf ; norm_num;
      positivity;
  -- Simplify the expression using the properties of exponents and logarithms.
  have h_simplify : ∀ᶠ x in atTop, K * x * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 ≤ (4 * K) * x * Real.exp (-c * (1 / 2) ^ ((1 : ℝ) / 10) * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 2 ) ] with x hx₁ hx₂;
    rw [ Real.log_sqrt ( by positivity ) ] ; ring_nf ; norm_num;
    rw [ Real.mul_rpow ( by linarith [ Real.log_pos hx₁ ] ) ( by linarith [ Real.log_pos hx₁ ] ) ] ; ring_nf ; norm_num;
    exact mul_le_of_le_one_right ( by exact mul_nonneg ( mul_nonneg hKpos.le ( by positivity ) ) ( Real.exp_nonneg _ ) ) ( inv_le_one_of_one_le₀ ( by nlinarith [ Real.log_exp 2, Real.log_le_log ( by positivity ) hx₂.le ] ) );
  refine' ⟨ c * ( 1 / 2 ) ^ ( 1 / 10 : ℝ ), by exact mul_pos hc.1 ( Real.rpow_pos_of_pos ( by norm_num ) _ ), _ ⟩;
  rw [ Asymptotics.isBigO_iff ];
  use 4 * K;
  filter_upwards [ h_integral_bound, h_simplify, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
  convert! hx₁.trans hx₂ using 1 ; norm_num [ abs_of_pos ( zero_lt_one.trans hx₃ ) ] ; ring

/-
**The error integral is power-saving.**  Split at `√x` into
`integral_head_isBigO_sqrt` (which is `O(√x) = O(errBound)` via
`sqrt_isBigO_errBound`) and `integral_tail_isBigO`.
-/
lemma integral_theta_sub_id_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  -- Apply the lemma that states the integral tail is O(errBound c) for some c.
  obtain ⟨c, hc_pos, hc_tail⟩ := integral_tail_isBigO
  use c, hc_pos;
  -- By definition of $f$, we know that for $x \geq 4$, $f(x) = \int_2^{\sqrt{x}} \frac{\theta(t) - t}{t (\log t)^2} \, dt + \int_{\sqrt{x}}^x \frac{\theta(t) - t}{t (\log t)^2} \, dt$.
  have h_split : ∀ x ≥ 4, ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) = (∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) + (∫ t in (Real.sqrt x)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) := by
    intro x hx
    have h_integrable : IntervalIntegrable (fun t => (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) MeasureTheory.volume 2 x := by
      apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( |Chebyshev.theta t - t| ) / ( 2 * ( Real.log 2 ) ^ 2 );
      · refine' MeasureTheory.Integrable.div_const _ _;
        refine' MeasureTheory.Integrable.abs _;
        refine' MeasureTheory.Integrable.sub _ _;
        · refine' ( MonotoneOn.integrableOn_isCompact _ _ );
          · exact CompactIccSpace.isCompact_Icc;
          · exact fun a ha b hb hab => Chebyshev.theta_mono hab;
        · exact Continuous.integrableOn_Icc ( by continuity );
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul _ _;
        · exact Chebyshev.theta_mono.measurable.sub measurable_id
        · exact Measurable.inv ( measurable_id.mul ( Measurable.pow_const ( Real.measurable_log ) _ ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht;
        rw [ Real.norm_eq_abs, abs_div ];
        gcongr;
        rw [ abs_of_nonneg ( mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ ) ) ] ; exact mul_le_mul ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( pow_le_pow_left₀ ( Real.log_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( Real.log_le_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) 2 ) ( by positivity ) ( by cases Set.mem_uIcc.mp ht <;> linarith );
    have h2s : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
    have hsx : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact h_integrable.mono_set (by
        rw [Set.uIcc_of_le h2s, Set.uIcc_of_le (by linarith : 2 ≤ x)]
        exact Set.Icc_subset_Icc le_rfl hsx)
    · exact h_integrable.mono_set (by
        rw [Set.uIcc_of_le hsx, Set.uIcc_of_le (by linarith : 2 ≤ x)]
        exact Set.Icc_subset_Icc h2s le_rfl)
  -- Apply the lemma that states the integral head is O(sqrt(x)).
  have h_head : (fun x => ∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) =O[atTop] (fun x => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) := by
    exact Asymptotics.IsBigO.trans ( integral_head_isBigO_sqrt ) ( sqrt_isBigO_errBound hc_pos );
  rw [ Asymptotics.isBigO_iff ] at *;
  obtain ⟨ c₁, hc₁ ⟩ := h_head; obtain ⟨ c₂, hc₂ ⟩ := hc_tail; use c₁ + c₂; filter_upwards [ hc₁, hc₂, Filter.eventually_ge_atTop 4 ] with x hx₁ hx₂ hx₃; rw [ h_split x hx₃ ] ; exact le_trans ( norm_add_le _ _ ) ( by nlinarith [ abs_nonneg ( x * Real.exp ( -c * Real.log x ^ ( 1 / 10 : ℝ ) ) ) ] ) ;

/-
**Layer B: the prime number theorem with power-saving error term.**
There is an absolute constant `c > 0` with
`π(y) = li(y) + O(y · e^{-c (log y)^{1/10}})` as `y → ∞`.
-/
theorem pnt_li_error :
    ∃ c : ℝ, 0 < c ∧
      (fun y : ℝ => (Nat.primeCounting ⌊y⌋₊ : ℝ) - li2 y)
        =O[atTop] (fun y : ℝ => y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10))) := by
  obtain ⟨ c₁, hc₁_pos, hc₁ ⟩ := theta_sub_id_isBigO
  obtain ⟨ c₂, hc₂_pos, hc₂ ⟩ := integral_theta_sub_id_isBigO
  use min c₁ c₂
  constructor
  · exact lt_min hc₁_pos hc₂_pos
  ·
    -- By combining the results from the previous steps, we conclude the proof.
    have h_combined : (fun y => (Chebyshev.theta y - y) / Real.log y + 2 / Real.log 2 + ∫ t in (2 : ℝ)..y, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) =O[atTop] (fun y => y * Real.exp (-min c₁ c₂ * Real.log y ^ ((1:ℝ)/10))) := by
      refine' Asymptotics.IsBigO.add ( Asymptotics.IsBigO.add _ _ ) _;
      · refine' Asymptotics.IsBigO.trans _ ( hc₁.trans _ );
        · refine' Asymptotics.IsBigO.of_bound 1 _;
          filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div ] ; exact div_le_self ( abs_nonneg _ ) ( by rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ) ] ; exact Real.le_log_iff_exp_le ( by linarith [ Real.add_one_le_exp 1 ] ) |>.2 <| by linarith [ Real.add_one_le_exp 1 ] ) ;
        · exact errBound_isBigO_of_le ( by positivity ) ( min_le_left _ _ );
      · have := one_isBigO_errBound ( show 0 < min c₁ c₂ by positivity );
        convert! this.const_mul_left ( 2 / Real.log 2 ) using 2 ; ring;
      · refine' hc₂.trans _;
        exact errBound_isBigO_of_le ( by positivity ) ( min_le_right _ _ );
    refine' h_combined.congr' _ _;
    · filter_upwards [ Filter.eventually_ge_atTop 2 ] with y hy using by rw [ primeCounting_sub_li2_eq hy ] ;
    · rfl

/-
**Layer A, step 1 (combinatorial identity).**  The number of primes `p` with
`e^{u-d} < p ≤ e^u` equals `π(⌊e^u⌋) - π(⌊e^{u-d}⌋)`.
-/
lemma count_eq_primeCounting_diff (u d : ℝ) (hd : 0 ≤ d) :
    (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u - d) < (p : ℝ))).card : ℝ)
      = (Nat.primeCounting ⌊Real.exp u⌋₊ : ℝ)
          - (Nat.primeCounting ⌊Real.exp (u - d)⌋₊ : ℝ) := by
  rw [ eq_sub_iff_add_eq ];
  rw_mod_cast [ Nat.primeCounting, Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr 1 with x ; by_cases hx : x ≤ ⌊Real.exp ( u - d ) ⌋₊ <;> simp_all +decide only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    Order.lt_add_one_iff];
    · constructor
      · intro h
        refine ⟨le_trans hx (Nat.floor_mono (Real.exp_le_exp.2 (by linarith))), ?_⟩
        exact h.elim (fun h => h.2.1) (fun h => h.2)
      · intro h
        exact Or.inr ⟨trivial, h.2⟩
    · constructor
      · rintro (h | h)
        · exact ⟨h.1.2, h.2.1⟩
        · exact False.elim h.1
      · intro h
        refine Or.inl ⟨⟨?_, h.1⟩, h.2, ?_⟩
        · omega
        · exact Nat.lt_of_floor_lt (by omega)
  · norm_num [ Finset.disjoint_left ];
    intro a ha₁ ha₂ ha₃ ha₄ ha₅; rw [ Nat.le_floor_iff ( by positivity ) ] at *; linarith;

/-
**Layer A, step 2 (main-term ratio).**  With `u_n → ∞` and `u_n^{-2} ≤ δ_n ≤ 1`
eventually, the ratio of the main term difference `li2(e^u) - li2(e^{u-δ})` to
`(1 - e^{-δ}) e^u / u` tends to `1`.

Reason: `li2(e^u) - li2(e^{u-δ}) = ∫_{e^{u-δ}}^{e^u} dt/log t`.  For `t` in that
range `log t ∈ [u-δ, u]`, so the integral lies in
`[(e^u - e^{u-δ})/u, (e^u - e^{u-δ})/(u-δ)]`.  The lower endpoint equals the
denominator `(1 - e^{-δ}) e^u / u`, and the upper/lower ratio `u/(u-δ) → 1`.
-/
lemma main_term_ratio_tendsto
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n)))
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) := by
  -- By definition of `li2`, we know that `li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n)) = ∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t`.
  have h_fold : ∀ᶠ n in atTop, (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) = ∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t := by
    filter_upwards [ hδ, hu.eventually_gt_atTop 2 ] with n hn hn';
    unfold li2;
    rw [ sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ) ] ) ) );
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ) ] ) ) );
  -- For $t \in [e^{u_n - \delta_n}, e^{u_n}]$, we have $\log t \in [u_n - \delta_n, u_n]$, so $\frac{1}{\log t} \in [\frac{1}{u_n}, \frac{1}{u_n - \delta_n}]$.
  have h_bound : ∀ᶠ n in atTop, (∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t) ≥ ((1 - Real.exp (-δ n)) * Real.exp (u n)) / (u n) ∧ (∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t) ≤ ((1 - Real.exp (-δ n)) * Real.exp (u n)) / (u n - δ n) := by
    -- By definition of $li2$, we know that for $t \in [e^{u_n - \delta_n}, e^{u_n}]$, $\log t \in [u_n - \delta_n, u_n]$.
    have h_log_bound : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (Real.exp (u n - δ n)) (Real.exp (u n)), 1 / u n ≤ 1 / Real.log t ∧ 1 / Real.log t ≤ 1 / (u n - δ n) := by
      filter_upwards [ hu.eventually_gt_atTop 3, hδ ] with n hn hn';
      intro t ht; constructor <;> gcongr <;> nlinarith [ ht.1, ht.2, Real.add_one_le_exp ( u n - δ n ), Real.exp_pos ( u n - δ n ), Real.log_exp ( u n - δ n ), Real.log_le_log ( by positivity ) ht.1, Real.log_exp ( u n ), Real.log_le_log ( by linarith [ Real.exp_pos ( u n - δ n ), ht.1 ] ) ht.2 ] ;
    filter_upwards [ h_fold, h_log_bound, hu.eventually_gt_atTop 2, hδ ] with n hn hn' hn'' hn''' ; refine' ⟨ _, _ ⟩;
    · refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ fun t ht => hn' t ht |>.1 ) <;> norm_num;
      · rw [ show u n - δ n = u n + ( -δ n ) by ring, Real.exp_add ] ; ring_nf ; norm_num;
      · nlinarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ), show 1 < u n - δ n from by nlinarith [ inv_mul_cancel₀ ( by linarith : ( u n ) ≠ 0 ) ] ] ) ) );
    · refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ fun t ht => hn' t ht |>.2 ) _ <;> norm_num;
      · nlinarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ), inv_pos.mpr ( by linarith : 0 < u n ) ] ) ) );
      · rw [ show Real.exp ( u n - δ n ) = Real.exp ( u n ) * Real.exp ( -δ n ) by rw [ ← Real.exp_add ] ; ring_nf ] ; ring_nf ; norm_num;
  -- Dividing by $D = \frac{(1 - e^{-\delta_n}) e^{u_n}}{u_n}$ gives $1 \leq \frac{\int_{e^{u_n - \delta_n}}^{e^{u_n}} \frac{dt}{\log t}}{D} \leq \frac{u_n}{u_n - \delta_n}$.
  have h_div_bound : ∀ᶠ n in atTop, 1 ≤ ((li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-δ n)) * Real.exp (u n) / (u n))) ∧ ((li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-δ n)) * Real.exp (u n) / (u n))) ≤ (u n) / (u n - δ n) := by
    filter_upwards [ h_fold, h_bound, hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'' hn''';
    rw [ hn, le_div_iff₀, div_le_iff₀ ];
    · convert! And.intro hn'.1 hn'.2 using 1 <;> ring_nf;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans hn''' ) ];
    · exact div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( lt_of_lt_of_le ( by positivity ) hn''.1 ) ) ) ) ( Real.exp_pos _ ) ) ( by positivity );
    · exact div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( lt_of_lt_of_le ( by positivity ) hn''.1 ) ) ) ) ( Real.exp_pos _ ) ) ( by positivity );
  -- Since $\frac{u_n}{u_n - \delta_n} \to 1$ as $n \to \infty$, we can apply the squeeze theorem.
  have h_squeeze : Filter.Tendsto (fun n => (u n) / (u n - δ n)) Filter.atTop (nhds 1) := by
    -- We can divide the numerator and the denominator by $u_n$.
    suffices h_div : Filter.Tendsto (fun n => 1 / (1 - δ n / u n)) Filter.atTop (nhds 1) by
      refine h_div.congr' ( by filter_upwards [ hu.eventually_ne_atTop 0 ] with n hn; rw [ one_sub_div hn ] ; norm_num [ hn ] );
    -- Since $\delta_n / u_n \to 0$ as $n \to \infty$, we have $1 - \delta_n / u_n \to 1$.
    have h_delta_div_u_zero : Filter.Tendsto (fun n => δ n / u n) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / u n;
      · filter_upwards [ hδ, hu.eventually_gt_atTop 0 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( div_nonneg ( by nlinarith ) hn'.le ) ] ; exact div_le_div_of_nonneg_right ( by nlinarith ) hn'.le;
      · exact tendsto_const_nhds.div_atTop hu;
    simpa using! Filter.Tendsto.inv₀ ( h_delta_div_u_zero.const_sub 1 ) ( by norm_num );
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_squeeze ( Filter.eventually_of_mem h_div_bound fun n hn => hn.1 ) ( Filter.eventually_of_mem h_div_bound fun n hn => hn.2 )

/-
**Layer A, step 3 (error is negligible).**  The PNT error contribution divided
by the denominator `(1 - e^{-δ}) e^u / u` tends to `0`.

Reason: the two error terms are `O(e^u e^{-c√u})`, while the denominator is
`≥ (u^{-2}/2) e^u / u = e^u/(2u^3)` (since `δ ≥ u^{-2}`).  Their quotient is
`O(u^3 e^{-c√(u-1)}) → 0`.
-/
lemma error_over_denom_tendsto
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))
            - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ)
                - li2 (Real.exp (u n - δ n))))
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 0) := by
  revert hδ;
  intro hδ
  obtain ⟨c, hc₀, hc⟩ := pnt_li_error
  obtain ⟨K, hK⟩ := hc.exists_pos
  have h_num : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n))) - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n)))| ≤ 2 * K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10)) := by
    have h_num_bound : ∀ᶠ n in atTop, abs ((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n))) ≤ K * Real.exp (u n) * Real.exp (-c * (u n) ^ ((1:ℝ)/10)) ∧ abs ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n))) ≤ K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10)) := by
      have h_bound : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))| ≤ K * (Real.exp (u n)) * Real.exp (-c * (u n) ^ (1 / 10 : ℝ)) := by
        have := hK.2.bound;
        filter_upwards [ this.filter_mono ( Real.tendsto_exp_atTop.comp hu ) ] with n hn using by simpa [ mul_assoc, Real.exp_pos ] using! hn;
      have h_bound' : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n)))| ≤ K * (Real.exp (u n - δ n)) * Real.exp (-c * (u n - δ n) ^ (1 / 10 : ℝ)) := by
        have := hK.2;
        rw [ IsBigOWith ] at this;
        simp +zetaDelta only [one_div, neg_mul, eventually_atTop] at *;
        obtain ⟨ a, ha ⟩ := this;
        obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hu.eventually_ge_atTop ( Max.max a 2 + 1 ) );
        refine' ⟨ N + hδ.choose, fun n hn => _ ⟩ ; specialize ha ( Real.exp ( u n - δ n ) ) _;
        · have := hN n ( by linarith );
          linarith [ le_max_left a 2, le_max_right a 2, Real.add_one_le_exp ( u n - δ n ), hδ.choose_spec n ( by linarith ) ];
        · simp_all +decide [ mul_assoc, abs_of_nonneg, Real.exp_nonneg ];
      filter_upwards [ h_bound, h_bound', hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'' hn''';
      refine ⟨ hn, hn'.trans ?_ ⟩;
      norm_num [ mul_assoc, ← Real.exp_add ];
      exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show ( u n - δ n ) ^ ( 1 / 10 : ℝ ) ≥ ( u n - 1 ) ^ ( 1 / 10 : ℝ ) by exact Real.rpow_le_rpow ( by linarith ) ( by linarith ) ( by norm_num ) ] ) hK.1.le;
    filter_upwards [ h_num_bound, hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'';
    refine' le_trans ( abs_sub _ _ ) _;
    nlinarith [ show 0 < K * Real.exp ( u n ) by exact mul_pos hK.1 ( Real.exp_pos _ ), show Real.exp ( -c * u n ^ ( 1 / 10 : ℝ ) ) ≤ Real.exp ( -c * ( u n - 1 ) ^ ( 1 / 10 : ℝ ) ) by exact Real.exp_le_exp.mpr ( mul_le_mul_of_nonpos_left ( Real.rpow_le_rpow ( by linarith ) ( by linarith ) ( by norm_num ) ) ( by linarith ) ) ];
  have h_denom : ∀ᶠ n in atTop, (1 - Real.exp (-δ n)) * Real.exp (u n) / u n ≥ Real.exp (u n) / (2 * (u n)^3) := by
    have h_exp_bound : ∀ᶠ n in atTop, 1 - Real.exp (-δ n) ≥ δ n / 2 := by
      filter_upwards [ hδ, hu.eventually_gt_atTop 1 ] with n hn hn';
      nlinarith [ Real.exp_pos ( -δ n ), Real.exp_neg ( δ n ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( δ n ) ) ), Real.add_one_le_exp ( δ n ), Real.add_one_le_exp ( -δ n ) ];
    filter_upwards [ hδ, h_exp_bound, hu.eventually_gt_atTop 1 ] with n hn hn' hn'';
    field_simp at *;
    nlinarith [ sq_nonneg ( u n - 1 ) ];
  have h_ratio : Filter.Tendsto (fun n => (2 * K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10))) / (Real.exp (u n) / (2 * (u n)^3))) Filter.atTop (nhds 0) := by
    suffices h_simplify : Filter.Tendsto (fun n => 4 * K * (u n)^3 * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10))) Filter.atTop (nhds 0) by
      convert! h_simplify using 2 ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ];
    suffices h_w : Filter.Tendsto (fun w => 4 * K * (w ^ 10 + 1) ^ 3 * Real.exp (-c * w)) Filter.atTop (nhds 0) by
      have h_subst : Filter.Tendsto (fun n => (u n - 1) ^ ((1:ℝ)/10)) Filter.atTop Filter.atTop := by
        exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ hu;
      refine' squeeze_zero_norm' _ ( h_w.comp h_subst );
      filter_upwards [ hu.eventually_gt_atTop 1, h_subst.eventually_gt_atTop 1 ] with n hn hn' ; norm_num [ abs_of_nonneg, hn.le, hn'.le ];
      rw [ abs_of_pos hK.1, abs_of_pos ( by linarith ) ] ; gcongr;
      · linarith;
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith ) ] ; norm_num;
    suffices h_factor : Filter.Tendsto (fun w => 4 * K * w ^ 30 * Real.exp (-c * w) * (1 + 1 / w ^ 10) ^ 3) Filter.atTop (nhds 0) by
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with w hw using by rw [ show ( w ^ 10 + 1 ) ^ 3 = ( w ^ 10 ) ^ 3 * ( 1 + 1 / w ^ 10 ) ^ 3 by rw [ show ( w ^ 10 + 1 ) = w ^ 10 * ( 1 + 1 / w ^ 10 ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; ring ] ; ring );
    have h_exp : Filter.Tendsto (fun w => w ^ 30 * Real.exp (-c * w)) Filter.atTop (nhds 0) := by
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 30;
      have := this.comp ( Filter.tendsto_id.const_mul_atTop hc₀ );
      convert! this.div_const ( c ^ 30 ) using 2 <;> norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, hc₀.ne' ];
    simpa [ mul_assoc ] using! Filter.Tendsto.mul ( h_exp.const_mul ( 4 * K ) ) ( Filter.Tendsto.pow ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( by norm_num ) ) ) 3 );
  refine' squeeze_zero_norm' _ h_ratio;
  filter_upwards [ h_num, h_denom, hu.eventually_gt_atTop 0 ] with n hn hn' hn'' ; rw [ Real.norm_eq_abs, abs_div ] ; gcongr;
  · exact mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two hK.1.le ) ( Real.exp_nonneg _ ) ) ( Real.exp_nonneg _ );
  · exact le_trans hn' ( le_abs_self _ )

/-
**Layer A, assembled.**  Lemma 2.8, proved from the pieces above.
-/
theorem primes_in_log_interval_proof
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
            (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) := by
  -- By combining the results from the main term ratio and the error over the denominator, we can conclude the proof.
  have h_sum : Filter.Tendsto
      (fun n : ℕ =>
        (((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))
            - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n))))
            / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))
        + (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      Filter.atTop (nhds (0 + 1)) := by
        convert! Tendsto.add ( error_over_denom_tendsto u δ hu hδ ) ( main_term_ratio_tendsto u δ hu hδ ) using 1;
  simp_all +decide;
  refine h_sum.congr' ?_ ; filter_upwards [ Filter.eventually_ge_atTop hδ.choose ] with n hn ; rw [ count_eq_primeCounting_diff _ _ ( by linarith [ hδ.choose_spec n hn, inv_nonneg.2 ( sq_nonneg ( u n ) ) ] ) ] ; ring;

end Erdos768
