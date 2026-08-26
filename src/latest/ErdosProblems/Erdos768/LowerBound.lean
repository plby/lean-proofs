import ErdosProblems.Erdos768.Defs
import ErdosProblems.Erdos768.Analytic

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — the constructive lower bound (Section 5)

We select one prime from each of `r` disjoint logarithmic intervals.  A
fourth-moment argument based on the multiplicative large sieve removes a
negligible collection of exceptional primes, after which a subset-product second
moment shows that almost every selected tuple supplies, for each prime factor, a
witness divisor.  The resulting integer lies in `𝒜`, giving the lower bound along
the subsequence `x = e^{L_r}`.

The theorem `Erdos768.lower_bound` in `ErdosProblems.Erdos768.Main` follows from
`lower_bound_subsequence` by monotonicity of `A` and the (small) gaps
`L_{r+1} - L_r = O(√{L_r})`.
-/

open scoped Classical BigOperators
open Finset Filter

namespace Erdos768

/-- `α = log 2`. -/
noncomputable def alphaParam : ℝ := Real.log 2

/-- `v = α(r-1) - 10 log r`. -/
noncomputable def vParam (r : ℕ) : ℝ := alphaParam * ((r : ℝ) - 1) - 10 * Real.log r

/-- `δ = 8α / log r`. -/
noncomputable def deltaParam (r : ℕ) : ℝ := 8 * alphaParam / Real.log r

/-- `u_j = v - (r - j)δ`, the right endpoint of the `j`-th logarithmic layer. -/
noncomputable def uParam (r j : ℕ) : ℝ := vParam r - ((r : ℝ) - j) * deltaParam r

/-- `L_r = ∑_{j=1}^r u_j`, so every selected product is at most `e^{L_r}`. -/
noncomputable def Lr (r : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 r, uParam r j

/-
Closed form of `L_r`.  Since `u_j = v - (r-j)δ`, summing over `j = 1,…,r`
gives `L_r = r·v - δ·(r(r-1)/2)`.
-/
theorem Lr_closed (r : ℕ) :
    Lr r = (r : ℝ) * vParam r - deltaParam r * ((r : ℝ) * ((r : ℝ) - 1) / 2) := by
  convert! Finset.sum_sub_distrib ( fun j => vParam r ) ( fun j => ( r - j ) * deltaParam r ) using 1 ; ring_nf;
  any_goals exact Finset.image ( fun x : ℕ => x : ℕ → ℝ ) ( Finset.Icc 1 r );
  · rw [ Finset.sum_image ] <;> norm_num;
    exact Finset.sum_congr rfl fun x hx => by rw [ uParam ] ; ring;
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ] ; ring_nf;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num ; ring_nf;
    rw [ add_comm 1 r, ← Finset.mul_sum _ _ _ ] ; rw [ show ( ∑ x ∈ Finset.range ( r + 1 ), ( x : ℝ ) ) = r * ( r + 1 ) / 2 from Nat.recOn r ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ] ; ring;

/-
`L_r → ∞` as `r → ∞` (the leading term is `(log 2)·r²`).
-/
theorem Lr_tendsto_atTop : Filter.Tendsto Lr Filter.atTop Filter.atTop := by
  -- To show that $L_r \to \infty$, we can use the fact that the term $\alpha r^2$ dominates the other terms as $r \to \infty$.
  have h_dominate : Filter.Tendsto (fun r : ℕ => (Real.log 2) * r * (r - 1) - 10 * r * Real.log r - 4 * Real.log 2 * r * (r - 1) / Real.log r) Filter.atTop Filter.atTop := by
    -- We can factor out $r^2$ from the expression.
    suffices h_factor : Filter.Tendsto (fun r : ℕ => (Real.log 2) * (r : ℝ) ^ 2 * (1 - 1 / (r : ℝ) - 10 / (Real.log 2) * (Real.log r) / (r : ℝ) - 4 / (Real.log r) * (1 - 1 / (r : ℝ)))) Filter.atTop Filter.atTop by
      convert! h_factor using 2 ; ring_nf;
      by_cases h : ‹_› = 0 <;> simp +decide [ h, sq, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring;
    -- We'll use the fact that $1 - \frac{1}{r} - \frac{10}{\log 2} \cdot \frac{\log r}{r} - \frac{4}{\log r} \cdot (1 - \frac{1}{r})$ tends to $1$ as $r$ tends to infinity.
    have h_limit : Filter.Tendsto (fun r : ℕ => 1 - 1 / (r : ℝ) - 10 / Real.log 2 * (Real.log r) / (r : ℝ) - 4 / Real.log r * (1 - 1 / (r : ℝ))) Filter.atTop (nhds 1) := by
      -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      norm_num [ mul_div_assoc ];
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ) ( by norm_num );
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ zero_lt_one, Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.tendsto_pow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ), h_limit ];
  convert! h_dominate using 2 ; ring_nf;
  rw [ Lr_closed ] ; norm_num [ vParam, deltaParam, uParam ] ; ring_nf;
  unfold alphaParam; ring;

/-
Auxiliary limit: `((r+1)·log(r+1) − r·log r)/r → 0`.
-/
theorem gap_log_ratio_tendsto :
    Filter.Tendsto
      (fun r : ℕ => (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) - (r : ℝ) * Real.log r) / (r : ℝ))
      Filter.atTop (nhds 0) := by
  -- We'll use the fact that $\log(r+1) - \log(r) = \log\left(1 + \frac{1}{r}\right)$.
  suffices h_log : Filter.Tendsto (fun r : ℕ => (Real.log (1 + 1 / (r : ℝ)) + (Real.log (r + 1)) / (r : ℝ))) Filter.atTop (nhds 0) by
    refine h_log.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; rw [ one_add_div ( by positivity ) ] ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf;
    simpa [ hr.ne', mul_assoc, mul_comm, mul_left_comm ] using! by ring;
  -- We'll use the fact that $\frac{\log(r+1)}{r} \to 0$ as $r \to \infty$.
  have h_log_div_r : Filter.Tendsto (fun r : ℕ => Real.log (r + 1) / (r : ℝ)) Filter.atTop (nhds 0) := by
    -- We can use the fact that $\frac{\log(r+1)}{r} = \frac{\log(r)}{r} + \frac{\log(1 + \frac{1}{r})}{r}$.
    suffices h_log_r : Filter.Tendsto (fun r : ℕ => Real.log (r : ℝ) / (r : ℝ)) Filter.atTop (nhds 0) by
      -- We can use the fact that $\log(r+1) = \log(r) + \log(1 + 1/r)$.
      suffices h_log_r : Filter.Tendsto (fun r : ℕ => (Real.log (r : ℝ) + Real.log (1 + 1 / (r : ℝ))) / (r : ℝ)) Filter.atTop (nhds 0) by
        refine h_log_r.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ] );
      simpa [ add_div ] using! h_log_r.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
    -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
    suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
      exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
  convert! Filter.Tendsto.add ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) _ ) h_log_div_r using 2 <;> norm_num

/-
Auxiliary limit: `((r+1)r/log(r+1) − r(r−1)/log r)/r → 0`.
-/
theorem gap_invlog_ratio_tendsto :
    Filter.Tendsto
      (fun r : ℕ =>
        (((r : ℝ) + 1) * (r : ℝ) / Real.log ((r : ℝ) + 1)
          - (r : ℝ) * ((r : ℝ) - 1) / Real.log r) / (r : ℝ))
      Filter.atTop (nhds 0) := by
  -- Simplify the expression inside the limit:
  suffices h_simp : Filter.Tendsto (fun r : ℕ => (r + 1) / Real.log (r + 1) - (r - 1) / Real.log r) Filter.atTop (nhds 0) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ eq_div_iff ( by positivity ) ] ; ring );
  -- We'll use the fact that $\frac{r+1}{\log(r+1)} - \frac{r-1}{\log r}$ can be rewritten as $\frac{(r+1)\log r - (r-1)\log(r+1)}{\log(r+1)\log r}$.
  suffices h_rewrite : Filter.Tendsto (fun r : ℕ => ((r + 1) * Real.log r - (r - 1) * Real.log (r + 1)) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    refine h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ div_sub_div _ _ ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) ( ne_of_gt <| Real.log_pos <| by norm_cast ) ] ; ring );
  -- We'll use the fact that $\log(r+1) = \log r + \log(1 + 1/r)$ to simplify the expression.
  suffices h_log : Filter.Tendsto (fun r : ℕ => ((r + 1) * Real.log r - (r - 1) * (Real.log r + Real.log (1 + 1 / r))) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ one_add_div ( by positivity ), Real.log_div ( by positivity ) ( by positivity ) ] ; ring );
  -- Simplify the numerator: $(r + 1) \log r - (r - 1) (\log r + \log (1 + 1/r)) = 2 \log r - (r - 1) \log (1 + 1/r)$.
  suffices h_num : Filter.Tendsto (fun r : ℕ => (2 * Real.log r - (r - 1) * Real.log (1 + 1 / r)) / (Real.log (r + 1) * Real.log r)) Filter.atTop (nhds 0) by
    exact h_num.congr fun x => by ring;
  -- We'll use the fact that $\log(1 + 1/r) \approx 1/r$ for large $r$.
  have h_log_approx : Filter.Tendsto (fun r : ℕ => (r - 1) * Real.log (1 + 1 / r) / Real.log r) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $(r - 1) \log(1 + 1/r) \leq 1$ for all $r \geq 2$.
    have h_bound : ∀ r : ℕ, 2 ≤ r → (r - 1) * Real.log (1 + 1 / r) ≤ 1 := by
      intro r hr; have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( r : ℝ ) ) ) ; norm_num at *;
      nlinarith [ show ( r : ℝ ) ≥ 2 by norm_cast, inv_mul_cancel₀ ( by positivity : ( r : ℝ ) ≠ 0 ), Real.log_nonneg ( show ( 1 + ( r : ℝ ) ⁻¹ ) ≥ 1 by exact le_add_of_nonneg_right ( by positivity ) ) ];
    refine' squeeze_zero_norm' _ _;
    exacts [ fun n => 1 / Real.log n, Filter.eventually_atTop.mpr ⟨ 2, fun n hn => by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| Real.log_nonneg <| by norm_num ) <| Real.log_nonneg <| by norm_cast; linarith ) ] ; exact div_le_div_of_nonneg_right ( h_bound n hn ) <| Real.log_nonneg <| by norm_cast; linarith ⟩, tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ];
  -- We can factor out $\frac{1}{\log r}$ from the expression.
  suffices h_factor : Filter.Tendsto (fun r : ℕ => (2 - (r - 1) * Real.log (1 + 1 / r) / Real.log r) / Real.log (r + 1)) Filter.atTop (nhds 0) by
    refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using by rw [ sub_div' ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr ) ] ; ring );
  simpa using! Filter.Tendsto.div_atTop ( tendsto_const_nhds.sub h_log_approx ) ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop )

/-
The gap `L_{r+1} − L_r`, divided by `r`, tends to `2·log 2`.
-/
theorem Lr_gap_div_r_tendsto :
    Filter.Tendsto (fun r : ℕ => (Lr (r + 1) - Lr r) / (r : ℝ))
      Filter.atTop (nhds (2 * alphaParam)) := by
  -- By definition of $Lr$, we can write
  have hLr_def : ∀ r : ℕ, r ≥ 2 → (Lr (r + 1) - Lr r) = 2 * alphaParam * r - 10 * ((r + 1) * Real.log (r + 1) - r * Real.log r) - 4 * alphaParam * ((r + 1) * r / Real.log (r + 1) - r * (r - 1) / Real.log r) := by
    intro r hr; rw [ Lr_closed, Lr_closed ] ; ring_nf;
    unfold vParam deltaParam; push_cast; ring;
  -- Dividing both sides of the equation by $r$, we get
  have h_div_r : Filter.Tendsto (fun r : ℕ => (2 * alphaParam - 10 * (((r + 1) * Real.log (r + 1) - r * Real.log r) / (r : ℝ)) - 4 * alphaParam * (((r + 1) * r / Real.log (r + 1) - r * (r - 1) / Real.log r) / (r : ℝ)))) Filter.atTop (nhds (2 * alphaParam)) := by
    exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_const_nhds.mul gap_log_ratio_tendsto ) ) ( tendsto_const_nhds.mul gap_invlog_ratio_tendsto ) ) ( by norm_num );
  refine h_div_r.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with r hr; rw [ hLr_def r hr ] ; simp [ sub_div, mul_div_assoc, ne_of_gt ( zero_lt_two.trans_le hr ) ] )

/-
Eventual quadratic lower bound: `(log 2)/2 · r² ≤ L_r`.
-/
theorem Lr_lower_quad :
    ∀ᶠ r : ℕ in Filter.atTop, alphaParam / 2 * (r : ℝ) ^ 2 ≤ Lr r := by
  -- We'll use that `Lr r / r^2` tends to `alphaParam`.
  have h_tendsto : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
    -- We'll use the fact that $L_r = r \cdot v_r - \delta_r \cdot \frac{r(r-1)}{2}$ to simplify the expression.
    suffices h_simplify : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ) - deltaParam r * ((r - 1) / (2 * r)))) Filter.atTop (nhds (alphaParam)) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; rw [ Lr_closed ] ; ring_nf;
      grind;
    -- We'll use the fact that $v_r / r \to \alpha$ and $\delta_r \to 0$ as $r \to \infty$.
    have h_lim : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds alphaParam) ∧ Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
      constructor;
      · -- We can use the fact that `vParam r / r = alphaParam * (1 - 1/r) - 10 * (Real.log r / r)`.
        suffices h_suff : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ))) Filter.atTop (nhds (alphaParam)) by
          refine h_suff.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr ; unfold vParam ; ring_nf;
          norm_num [ hr.ne' ];
        -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
        have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
        convert! Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) using 2 ; norm_num;
      · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    simpa using! h_lim.1.sub ( h_lim.2.mul ( show Filter.Tendsto ( fun r : ℕ => ( r - 1 : ℝ ) / ( 2 * r ) ) Filter.atTop ( nhds ( 1 / 2 ) ) from by erw [ Metric.tendsto_nhds ] ; intro ε hε; exact Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹ * 2⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ by nlinarith [ Nat.le_ceil ( ε⁻¹ * 2 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 1 ) ( by norm_cast; linarith : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Nat.le_ceil ( ε⁻¹ * 2 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 1 ) ( by norm_cast; linarith : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ⟩ ) );
  filter_upwards [ h_tendsto.eventually ( lt_mem_nhds ( show alphaParam > alphaParam / 2 by exact div_lt_self ( Real.log_pos one_lt_two ) ( by norm_num ) ) ), Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by rw [ ← le_div_iff₀ ( by positivity ) ] ; linarith;

/-
`L_r` is eventually strictly increasing in `r`.
-/
theorem Lr_eventually_lt : ∀ᶠ r : ℕ in Filter.atTop, Lr r < Lr (r + 1) := by
  -- By definition of $Lr$, we know that $Lr (r + 1) - Lr r > 0$ for sufficiently large $r$.
  have h_diff_pos : ∀ᶠ r : ℕ in Filter.atTop, (Lr (r + 1) - Lr r) / (r : ℝ) > alphaParam := by
    exact Filter.Tendsto.eventually ( by exact Lr_gap_div_r_tendsto ) ( lt_mem_nhds <| by linarith [ show 0 < alphaParam by exact Real.log_pos one_lt_two ] );
  filter_upwards [ h_diff_pos, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ using by have := hr₁; rw [ gt_iff_lt ] at *; rw [ lt_div_iff₀ ( Nat.cast_pos.mpr hr₂ ) ] at *; nlinarith [ show 0 < alphaParam from Real.log_pos one_lt_two ] ;

/-
The gaps of `L_r` are negligible against the scale `√{L_r}·log L_r`:
`(L_{r+1} - L_r)/(√{L_r}·log L_r) → 0`.  Indeed `L_r ∼ (log 2)·r²`, so the gap is
`∼ 2(log 2)·r ∼ 2√{log 2}·√{L_r}`, while `√{L_r}·log L_r ∼ √{log 2}·r·(2 log r) → ∞`
faster.
-/
theorem Lr_gap_negligible :
    Filter.Tendsto
      (fun r : ℕ => (Lr (r + 1) - Lr r) / (Real.sqrt (Lr r) * Real.log (Lr r)))
      Filter.atTop (nhds 0) := by
  -- We'll use the fact that $L_r$ is eventually strictly increasing and grows quadratically.
  have h_Lr_growth : Filter.Tendsto (fun r => (Lr (r + 1) - Lr r) / (r : ℝ)) Filter.atTop (nhds (2 * alphaParam)) ∧ Filter.Tendsto (fun r => Real.sqrt (Lr r) / (r : ℝ)) Filter.atTop (nhds (Real.sqrt (alphaParam))) := by
    constructor;
    · convert! Lr_gap_div_r_tendsto using 1;
    · -- We'll use the fact that $L_r \sim \alpha r^2$ to show that $\sqrt{L_r} / r \to \sqrt{\alpha}$.
      have h_sqrt : Filter.Tendsto (fun r : ℕ => Lr r / (r : ℝ) ^ 2) Filter.atTop (nhds alphaParam) := by
        -- We'll use the fact that $L_r = r \cdot v_r - \delta_r \cdot \frac{r(r-1)}{2}$ to simplify the expression.
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => (vParam r / (r : ℝ) - deltaParam r * ((r - 1) / (2 * r)))) Filter.atTop (nhds (alphaParam)) by
          convert! h_simplify using 2;
          by_cases hr : ‹_› = 0 <;> simp +decide [ hr, Lr_closed, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sq ];
          grind;
        -- We'll use the fact that $v_r = \alpha(r-1) - 10 \log r$ and $\delta_r = \frac{8 \alpha}{\log r}$ to simplify the expression.
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => (alphaParam * (r - 1) - 10 * Real.log r) / (r : ℝ) - (8 * alphaParam / Real.log r) * ((r - 1) / (2 * r))) Filter.atTop (nhds (alphaParam)) by
          convert! h_simplify using 1;
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun r : ℕ => alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r) / (r : ℝ) - 4 * alphaParam * (1 - 1 / (r : ℝ)) / Real.log r) Filter.atTop (nhds (alphaParam)) by
          refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ one_sub_div ( by positivity ) ] ; ring );
        -- We'll use the fact that $\frac{\log r}{r} \to 0$ as $r \to \infty$.
        have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
        norm_num [ mul_div_assoc ] at *;
        exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( tendsto_const_nhds.mul ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num [ alphaParam ] );
      convert! h_sqrt.sqrt using 2;
      rw [ Real.sqrt_div' _ ( by positivity ), Real.sqrt_sq ( by positivity ) ];
  -- Using the fact that $L_r \to \infty$, we can simplify the expression.
  have h_simplify : Filter.Tendsto (fun r => (Lr (r + 1) - Lr r) / (r : ℝ) / (Real.sqrt (Lr r) / (r : ℝ)) * (1 / Real.log (Lr r))) Filter.atTop (nhds 0) := by
    convert! Filter.Tendsto.mul ( h_Lr_growth.1.div h_Lr_growth.2 _ ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| show Filter.Tendsto ( fun r : ℕ => Lr r ) Filter.atTop ( Filter.atTop ) from Lr_tendsto_atTop ) ) using 2 <;> norm_num;
    exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos one_lt_two;
  refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hr.ne' ] )

/-- The `j`-th prime layer `𝒫_j = { p prime : e^{u_j - δ} < p ≤ e^{u_j} }`. -/
noncomputable def primeLayer (r j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.exp (uParam r j)⌋₊).filter
    (fun p => Nat.Prime p ∧ Real.exp (uParam r j - deltaParam r) < (p : ℝ))

/-- Number of ordered factorizations `n = q₁·q₂` with `q₁, q₂ ∈ P`. -/
def bcount (P : Finset ℕ) (n : ℕ) : ℕ :=
  ((P ×ˢ P).filter (fun x => x.1 * x.2 = n)).card

/-
The product of two primes determines the unordered pair of prime factors.
-/
lemma prod_two_primes_eq {q1 q2 q3 q4 : ℕ} (h1 : q1.Prime) (h2 : q2.Prime)
    (h3 : q3.Prime) (h4 : q4.Prime) (h : q1 * q2 = q3 * q4) :
    (q3 = q1 ∧ q4 = q2) ∨ (q3 = q2 ∧ q4 = q1) := by
  have := h3.dvd_mul.mp ( h.symm ▸ dvd_mul_right _ _ );
  rcases this with ( h | h ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
  · aesop;
  · exact Or.inr ( by nlinarith [ h1.two_le, h2.two_le ] )

/-
Character-square identity: `(∑_{q∈P} χ q)² = ∑_n b(n) χ(n)`, where `b` counts
ordered factorizations, provided all products `q₁q₂` lie in `Icc 1 N`.  Uses complete
multiplicativity of the Dirichlet character.
-/
lemma char_sq_eq_bcount_sum (P : Finset ℕ) (N p : ℕ) (χ : DirichletCharacter ℂ p)
    (hPN : ∀ q1 ∈ P, ∀ q2 ∈ P, q1 * q2 ∈ Finset.Icc 1 N) :
    (∑ q ∈ P, χ q) ^ 2 = ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℂ) * χ n := by
  -- Apply the fact that the sum over the image of a function can be rewritten as a sum over the domain, grouped by the image.
  have h_image : ∑ q ∈ P, ∑ q' ∈ P, χ (q * q' : ℕ) = ∑ n ∈ Icc 1 N, ∑ q ∈ P, ∑ q' ∈ P, if q * q' = n then χ (n : ℕ) else 0 := by
    simp +decide only [← sum_product'];
    rw [ ← Finset.sum_filter ];
    refine' Finset.sum_bij ( fun x hx => ( x.1 * x.2, x.1, x.2 ) ) _ _ _ _ <;> aesop;
  simp_all +decide [ Finset.sum_ite, bcount ];
  convert! h_image using 2 <;> norm_num [ sq, Finset.sum_product ];
  · simp +decide only [sum_mul_sum];
  · simp +decide only [card_filter];
    erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_mul _ _ _ ]

/-
For a set of primes `P`, the second moment of the ordered-factorization count is
small: `∑_n b(n)² ≤ 2·|P|²` (each product of two primes has at most two ordered
factorizations into primes).
-/
lemma bcount_sq_sum_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((bcount P n : ℝ)) ^ 2 ≤ 2 * (P.card : ℝ) ^ 2 := by
  norm_cast;
  -- By definition of $bcount$, we know that $(bcount P n)^2$ counts the number of pairs $(q_1, q_2)$ and $(q_3, q_4)$ in $P$ such that $q_1 * q_2 = n$ and $q_3 * q_4 = n$.
  have h_count : ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℕ) ^ 2 ≤ Finset.card (Finset.filter (fun (p : ℕ × ℕ × ℕ × ℕ) => p.1 * p.2.1 = p.2.2.1 * p.2.2.2) (P ×ˢ P ×ˢ P ×ˢ P)) := by
    have h_count : ∑ n ∈ Finset.Icc 1 N, (bcount P n : ℕ) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, Finset.card (Finset.filter (fun (p : ℕ × ℕ × ℕ × ℕ) => p.1 * p.2.1 = n ∧ p.2.2.1 * p.2.2.2 = n) (P ×ˢ P ×ˢ P ×ˢ P)) := by
      refine Finset.sum_le_sum fun n hn => ?_;
      rw [ sq, bcount ];
      rw [ ← Finset.card_product ];
      refine' le_of_eq ( Finset.card_bij ( fun x hx => ( x.1.1, x.1.2, x.2.1, x.2.2 ) ) _ _ _ ) <;> aesop;
    refine le_trans h_count ?_;
    rw [ ← Finset.card_biUnion ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
  -- For each pair $(q_1, q_2)$ in $P$, there are at most 2 pairs $(q_3, q_4)$ in $P$ such that $q_1 * q_2 = q_3 * q_4$.
  have h_pair_count : ∀ q1 q2 : ℕ, q1 ∈ P → q2 ∈ P → Finset.card (Finset.filter (fun (p : ℕ × ℕ) => p.1 * p.2 = q1 * q2) (P ×ˢ P)) ≤ 2 := by
    intros q1 q2 hq1 hq2
    have h_pair_count : ∀ p : ℕ × ℕ, p ∈ Finset.filter (fun (p : ℕ × ℕ) => p.1 * p.2 = q1 * q2) (P ×ˢ P) → p = (q1, q2) ∨ p = (q2, q1) := by
      simp +zetaDelta at *;
      intro a b ha hb hab; have := prod_two_primes_eq ( hP a ha ) ( hP b hb ) ( hP q1 hq1 ) ( hP q2 hq2 ) hab; aesop;
    exact le_trans ( Finset.card_le_card ( show { p ∈ P ×ˢ P | p.1 * p.2 = q1 * q2 } ⊆ { ( q1, q2 ), ( q2, q1 ) } by intros p hp; simpa using! h_pair_count p hp ) ) ( Finset.card_insert_le _ _ );
  refine le_trans h_count ?_;
  rw [ show { p ∈ P ×ˢ P ×ˢ P ×ˢ P | p.1 * p.2.1 = p.2.2.1 * p.2.2.2 } = Finset.biUnion ( P ×ˢ P ) ( fun p => Finset.image ( fun q => ( p.1, p.2, q.1, q.2 ) ) ( Finset.filter ( fun q => q.1 * q.2 = p.1 * p.2 ) ( P ×ˢ P ) ) ) from ?_ ];
  · refine' le_trans ( Finset.card_biUnion_le ) _;
    exact le_trans ( Finset.sum_le_sum fun x hx => Finset.card_image_le.trans ( h_pair_count _ _ ( Finset.mem_product.mp hx |>.1 ) ( Finset.mem_product.mp hx |>.2 ) ) ) ( by norm_num [ sq, mul_comm ] );
  · ext ⟨a, b, c, d⟩; simp [Finset.mem_biUnion, Finset.mem_image];
    grind +splitImp

/-
**Fourth-moment large-sieve bound.**  Applying the multiplicative large sieve to
the ordered-factorization sequence `b_j` of the layer `𝒫_j`, and restricting to prime
moduli (where nonprincipal characters are primitive and `p/φ(p) ≥ 1`), gives
`∑_{p ≤ e^v} ∑_{χ≠1} |∑_{q∈𝒫_j} χ(q)|⁴ ≤ C·e^{2v}·M_j²` with an absolute constant.
-/
lemma fourth_moment_ls_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r j : ℕ), 2 ≤ r → j ∈ Finset.Icc 1 r →
      ∑ p ∈ (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter (fun p => Nat.Prime p),
        ∑ χ : DirichletCharacter ℂ p,
          (if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, χ q‖ ^ 4 else 0)
      ≤ C * Real.exp (2 * vParam r) * ((primeLayer r j).card : ℝ) ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := multiplicative_large_sieve;
  refine' ⟨ 8 * C, mul_pos ( by norm_num ) hC₀, fun r j hr₁ hr₂ => _ ⟩;
  -- Apply the large sieve with $N = \lfloor e^{u_j} \rfloor^2$ and $Q = \lfloor e^{v_r} \rfloor$.
  have h_large_sieve : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), (∑ χ : DirichletCharacter ℂ p, if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 else 0)) ≤ C * (⌊Real.exp (uParam r j)⌋₊ ^ 2 + ⌊Real.exp (vParam r)⌋₊ ^ 2) * (∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℝ) ^ 2) := by
    have h_large_sieve : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), (∑ χ : DirichletCharacter ℂ p, if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 else 0) ≤ (p : ℝ) / (Nat.totient p) * (∑ χ : DirichletCharacter ℂ p, if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n‖ ^ 2 else 0) := by
      intro p hp
      have h_char_sq : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖∑ q ∈ primeLayer r j, (χ q : ℂ)‖ ^ 4 = ‖∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n‖ ^ 2 := by
        intro χ hχ
        have h_char_sq : (∑ q ∈ primeLayer r j, (χ q : ℂ)) ^ 2 = ∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℂ) * χ n := by
          convert! char_sq_eq_bcount_sum ( primeLayer r j ) ( ⌊Real.exp ( uParam r j ) ⌋₊ ^ 2 ) p χ _ using 1;
          simp +zetaDelta at *;
          exact fun q1 hq1 q2 hq2 => ⟨ Nat.mul_pos ( Nat.Prime.pos ( by unfold primeLayer at hq1; aesop ) ) ( Nat.Prime.pos ( by unfold primeLayer at hq2; aesop ) ), by nlinarith [ show q1 ≤ ⌊Real.exp ( uParam r j ) ⌋₊ from by unfold primeLayer at hq1; aesop, show q2 ≤ ⌊Real.exp ( uParam r j ) ⌋₊ from by unfold primeLayer at hq2; aesop ] ⟩;
        rw [ ← h_char_sq, norm_pow ] ; ring;
      have h_char_sq : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → χ.IsPrimitive := by
        intro χ hχ_ne_one
        have h_conductor : χ.conductor = p := by
          have h_conductor : χ.conductor ∣ p := by
            grind +suggestions;
          rw [ Nat.dvd_prime ( Finset.mem_filter.mp hp |>.2 ) ] at h_conductor;
          haveI : NeZero p := ⟨(Finset.mem_filter.mp hp).2.ne_zero⟩
          exact h_conductor.resolve_left (fun hc =>
            hχ_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc))
        exact h_conductor;
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_le_sum fun χ _ => _;
      by_cases h : χ = 1 <;> simp_all +decide;
      · positivity;
      · exact le_mul_of_one_le_left ( sq_nonneg _ ) ( by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.totient_pos.mpr hp.2.pos ) ] ; norm_cast; linarith [ Nat.totient_le p ] );
    refine le_trans ( Finset.sum_le_sum h_large_sieve ) ?_;
    convert! hC ( ⌊Real.exp ( uParam r j ) ⌋₊ ^ 2 ) ⌊Real.exp ( vParam r ) ⌋₊ ( fun n => bcount ( primeLayer r j ) n ) |> le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_nonneg fun _ _ => by positivity ) ) using 1;
    norm_num;
  -- Bound the sum of squares of bcount by 2 times the square of the cardinality of primeLayer r j.
  have h_bcount_sq_sum : (∑ n ∈ Finset.Icc 1 (⌊Real.exp (uParam r j)⌋₊ ^ 2), (bcount (primeLayer r j) n : ℝ) ^ 2) ≤ 2 * (primeLayer r j).card ^ 2 := by
    convert! bcount_sq_sum_le ( primeLayer r j ) _ _ using 1;
    exact fun q hq => Finset.mem_filter.mp hq |>.2.1;
  -- Bound the sum of squares of bcount by 2 times the square of the cardinality of primeLayer r j, and use the fact that $vParam r \geq uParam r j$.
  have h_bound : (⌊Real.exp (uParam r j)⌋₊ ^ 2 + ⌊Real.exp (vParam r)⌋₊ ^ 2 : ℝ) ≤ 2 * Real.exp (2 * vParam r) := by
    have h_bound : (⌊Real.exp (uParam r j)⌋₊ : ℝ) ^ 2 ≤ Real.exp (2 * uParam r j) ∧ (⌊Real.exp (vParam r)⌋₊ : ℝ) ^ 2 ≤ Real.exp (2 * vParam r) := by
      exact ⟨ by rw [ two_mul, Real.exp_add ] ; exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) _ ) ( by norm_num [ sq, Real.exp_add ] ), by rw [ two_mul, Real.exp_add ] ; exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.exp_nonneg _ ) ) _ ) ( by norm_num [ sq, Real.exp_add ] ) ⟩;
    have h_bound : uParam r j ≤ vParam r := by
      unfold uParam vParam deltaParam alphaParam; norm_num;
      exact mul_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| Finset.mem_Icc.1 hr₂ |>.2 ) <| div_nonneg ( by positivity ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith;
    linarith [ Real.exp_le_exp.mpr ( mul_le_mul_of_nonneg_left h_bound zero_le_two ) ];
  refine le_trans h_large_sieve ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left h_bcount_sq_sum <| by positivity ) ?_;
  nlinarith [ show 0 ≤ C * ( primeLayer r j |> Finset.card : ℝ ) ^ 2 by positivity ]

/-
**Uniform prime number theorem in short logarithmic intervals.**  The
`(1+o(1))` in `primes_in_log_interval` is uniform over the range `u⁻² ≤ δ ≤ 1` as
`u → ∞`.  (Equivalent to the sequential statement; derived by extracting a bad
sequence.)
-/
lemma primes_in_log_interval_unif :
    ∀ ε : ℝ, 0 < ε → ∃ U : ℝ, ∀ u δ : ℝ, U ≤ u → u⁻¹ ^ 2 ≤ δ → δ ≤ 1 →
      |(((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
          (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-δ)) * Real.exp u / u) - 1| ≤ ε := by
  intro ε hε
  by_contra h_contra
  push_neg at h_contra
  generalize_proofs at *;
  choose! u δ hu hδ₁ hδ₂ hδ₃ using h_contra;
  convert! primes_in_log_interval ( fun n => u ( n : ℝ ) ) ( fun n => δ ( n : ℝ ) ) ?_ ?_ using 1 <;> norm_num at *;
  · exact fun h => absurd ( h.eventually ( Metric.ball_mem_nhds _ hε ) ) fun h' => by obtain ⟨ n, hn ⟩ := h'.exists; exact not_lt_of_ge ( le_of_lt ( hδ₃ n ) ) ( by simpa using! hn ) ;
  · exact Filter.tendsto_atTop_mono ( fun n => hu _ ) tendsto_natCast_atTop_atTop;
  · exact ⟨ 0, fun n hn => ⟨ hδ₁ _, hδ₂ _ ⟩ ⟩

/-
**Uniform lower bound on the layer sizes `M_j`.**  Eventually in `r`, every layer
`𝒫_j` (`1 ≤ j ≤ r`) has `M_j ≥ ½(1-e^{-δ}) e^{u_j}/u_j`.
-/
lemma primeLayer_card_lower :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j)
        ≤ ((primeLayer r j).card : ℝ) := by
  obtain ⟨U, hU⟩ : ∃ U : ℝ, ∀ u δ : ℝ, U ≤ u → u⁻¹ ^ 2 ≤ δ → δ ≤ 1 →
      (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
          (fun p => Nat.Prime p ∧ Real.exp (u - δ) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-δ)) * Real.exp u / u) ≥ 1 / 2 := by
            obtain ⟨ U, hU ⟩ := primes_in_log_interval_unif ( 1 / 2 ) ( by norm_num );
            exact ⟨ U, fun u δ hu hδ hδ' => by linarith [ abs_le.mp ( hU u δ hu hδ hδ' ) ] ⟩;
  -- Obtain the conditions on uParam r 1 and deltaParam r eventually.
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℕ, ∀ r ≥ R₁, uParam r 1 ≥ max U 1 := by
    have h_uParam_r1_tendsto : Filter.Tendsto (fun r : ℕ => uParam r 1) Filter.atTop Filter.atTop := by
      -- We'll use the fact that $uParam r 1 = vParam r - (r - 1) * deltaParam r$ and the definitions of $vParam$ and $deltaParam$.
      have h_uParam_r1 : ∀ r : ℕ, r ≥ 2 → uParam r 1 = alphaParam * ((r : ℝ) - 1) - 10 * Real.log r - ((r : ℝ) - 1) * (8 * alphaParam / Real.log r) := by
        unfold uParam vParam deltaParam; aesop;
      -- We'll use the fact that $uParam r 1$ is asymptotically equivalent to $alphaParam * r$.
      have h_uParam_r1_equiv : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
        -- We can divide the numerator and the denominator by $r$ and then take the limit as $r$ approaches infinity.
        have h_div : Filter.Tendsto (fun r : ℕ => (alphaParam * (1 - 1 / (r : ℝ)) - 10 * (Real.log r / (r : ℝ)) - (1 - 1 / (r : ℝ)) * (8 * alphaParam / Real.log r))) Filter.atTop (nhds (alphaParam)) := by
          -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num );
        refine h_div.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with r hr; rw [ h_uParam_r1 r hr ] ; simp [ show r ≠ 0 by linarith, sub_mul, mul_sub, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
      have h_uParam_r1_pos : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ) * (r : ℝ)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.pos_mul_atTop;
        exacts [ show 0 < alphaParam by exact Real.log_pos one_lt_two, h_uParam_r1_equiv, tendsto_natCast_atTop_atTop ];
      exact h_uParam_r1_pos.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ div_mul_cancel₀ _ ( by positivity ) ] );
    exact Filter.eventually_atTop.mp ( h_uParam_r1_tendsto.eventually_ge_atTop ( Max.max U 1 ) )
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℕ, ∀ r ≥ R₂, deltaParam r ≤ 1 := by
    have h_deltaParam_zero : Filter.Tendsto deltaParam Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    simpa using! h_deltaParam_zero.eventually ( ge_mem_nhds zero_lt_one )
  obtain ⟨R₃, hR₃⟩ : ∃ R₃ : ℕ, ∀ r ≥ R₃, (uParam r 1)⁻¹ ^ 2 ≤ deltaParam r := by
    have h_lim : Filter.Tendsto (fun r : ℕ => (uParam r 1)⁻¹ ^ 2 / deltaParam r) Filter.atTop (nhds 0) := by
      -- We'll use that $u \sim \alpha r$ and $\delta \sim 8\alpha / \log r$ to show that the limit is zero.
      have h_u_delta : Filter.Tendsto (fun r : ℕ => (uParam r 1)⁻¹ ^ 2 * (Real.log r) / (8 * alphaParam)) Filter.atTop (nhds 0) := by
        -- We'll use that $u \sim \alpha r$ to show that the limit is zero.
        have h_u : Filter.Tendsto (fun r : ℕ => (uParam r 1) / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold uParam vParam deltaParam alphaParam;
          -- We can divide the numerator and the denominator by $r$ and then take the limit as $r \to \infty$.
          suffices h_div : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (1 - 1 / (r : ℝ)) - 10 * Real.log r / (r : ℝ) - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r))) Filter.atTop (nhds (Real.log 2)) by
            refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', div_eq_mul_inv, mul_sub, sub_mul, mul_comm, mul_left_comm ] );
          -- We'll use the fact that $\frac{\log r}{r} \to 0$ as $r \to \infty$.
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          norm_num [ mul_div_assoc ];
          exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.mul h_log_r_div_r ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ) ( by norm_num );
        have h_log_r : Filter.Tendsto (fun r : ℕ => (Real.log r) / (r : ℝ) ^ 2) Filter.atTop (nhds 0) := by
          refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ) ] ;
        convert! h_log_r.mul ( h_u.inv₀ ( show alphaParam ≠ 0 by exact ne_of_gt ( Real.log_pos one_lt_two ) ) |> Filter.Tendsto.pow <| 2 ) |> Filter.Tendsto.div_const <| 8 * alphaParam using 2 <;> ring_nf;
        by_cases h : ‹_› = 0 <;> simp +decide [ h ];
      convert! h_u_delta using 2 ; norm_num [ deltaParam ] ; ring_nf;
      norm_num ; ring;
    have := h_lim.eventually ( gt_mem_nhds zero_lt_one );
    obtain ⟨ R₃, hR₃ ⟩ := Filter.eventually_atTop.mp this;
    exact ⟨ R₃ + 2, fun r hr => by have := hR₃ r ( by linarith ) ; rw [ div_lt_one ( show 0 < deltaParam r from div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( by norm_cast; linarith ) ) ) ] at this; linarith ⟩;
  refine' Filter.eventually_atTop.mpr ⟨ Max.max R₁ ( Max.max R₂ R₃ ), fun r hr j hj => _ ⟩ ; specialize hU ( uParam r j ) ( deltaParam r ) _ _ _ <;> simp_all +decide [ primeLayer ];
  · refine' le_trans ( hR₁ r hr.1 |>.1 ) _;
    unfold uParam; norm_num;
    nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
  · refine' le_trans _ ( hR₃ r hr.2.2 );
    gcongr;
    · exact sq_pos_of_pos ( by linarith [ hR₁ r hr.1 ] );
    · linarith [ hR₁ r hr.1 ];
    · unfold uParam; norm_num;
      nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
  · rw [ le_div_iff₀ ] at hU <;> norm_num at *;
    · convert! hU using 1 ; ring;
    · refine' div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr _ ) ) ( Real.exp_pos _ ) ) ( _ );
      · exact neg_neg_of_pos ( div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith, by rintro rfl; norm_num [ deltaParam ] at * ⟩ ) ) ) );
      · refine' lt_of_lt_of_le _ ( show uParam r j ≥ uParam r 1 from _ );
        · linarith [ hR₁ r hr.1 ];
        · unfold uParam; norm_num;
          nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( r : ℝ ) ≥ j by norm_cast; linarith, show ( deltaParam r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.log_nonneg one_le_two ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ]

/-
**Markov step.**  Combining `fourth_moment_ls_bound` with Markov's inequality,
the number of bad primes is `≤ C·(20r)⁴·e^{2v}/M²`.  (When `M = 0` both sides are
`0`, using the `x/0 = 0` convention.)
-/
lemma fourth_moment_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (r j : ℕ), 2 ≤ r → j ∈ Finset.Icc 1 r →
      (((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
          (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
            (primeLayer r j).card / (20 * (r : ℝ)) <
              ‖∑ q ∈ primeLayer r j, χ q‖)).card : ℝ)
        ≤ C * (20 * (r : ℝ)) ^ 4 * Real.exp (2 * vParam r)
            / ((primeLayer r j).card : ℝ) ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := fourth_moment_ls_bound;
  refine' ⟨ C, hC₀, _ ⟩;
  intro r j hr hj
  by_cases hM : (primeLayer r j).card = 0;
  · aesop;
  · rw [ le_div_iff₀ ( by positivity ) ];
    have h_markov : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), ∑ χ : DirichletCharacter ℂ p, (if χ ≠ 1 then ‖∑ q ∈ primeLayer r j, χ q‖ ^ 4 else 0)) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧ (primeLayer r j).card / (20 * r : ℝ) < ‖∑ q ∈ primeLayer r j, χ q‖) (Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊), ((primeLayer r j).card / (20 * r : ℝ)) ^ 4) := by
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      · obtain ⟨ χ, hχ₁, hχ₂ ⟩ := Finset.mem_filter.mp hp |>.2.2;
        exact le_trans ( pow_le_pow_left₀ ( by positivity ) hχ₂.le 4 ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_univ χ ) |> le_trans ( by aesop ) );
      · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2.1 ⟩;
      · exact fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity;
    simp_all +decide [ div_pow, mul_pow ];
    rw [ mul_div, div_le_iff₀ ] at h_markov <;> nlinarith [ hC r j hr hj.1 hj.2, show ( 0 : ℝ ) < 20 ^ 4 * r ^ 4 by positivity, show ( 0 : ℝ ) < ( primeLayer r j |> Finset.card ) ^ 2 by exact sq_pos_of_pos <| Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty hM ]

/-
**Asymptotic step.**  For every `ε > 0`, eventually in `r`, uniformly over
`j ∈ [1,r]`, `C·(20r)⁴·e^{2v}/M_j² ≤ e^{εr}` (all logarithmic factors are `o(r)`
by the layer-size lower bound `primeLayer_card_lower`).
-/
set_option maxHeartbeats 1600000 in
lemma fourth_moment_asymp (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      C * (20 * (r : ℝ)) ^ 4 * Real.exp (2 * vParam r)
          / ((primeLayer r j).card : ℝ) ^ 2
        ≤ Real.exp (ε * r) := by
  -- By primeLayer_card_lower, eventually ∀j∈[1,r], M ≥ L_j := (1-e^{-δ})e^{u}/(2u) where δ=deltaParam r.
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℕ, ∀ r ≥ R1, ∀ j ∈ Finset.Icc 1 r, (primeLayer r j).card ≥ ((1 / 2 * (deltaParam r) * Real.exp (uParam r j)) / (2 * uParam r j)) := by
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) * Real.exp (uParam r j) / (2 * uParam r j) ≤ ((primeLayer r j).card : ℝ) := by
      convert! primeLayer_card_lower using 1;
    have hL_lower_bound : ∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1 := by
      have hL_lower_bound : Filter.Tendsto (fun r : ℕ => deltaParam r) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      filter_upwards [ hL_lower_bound.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ using ⟨ by exact div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr₂ ) ), hr₁.le ⟩;
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≥ 1 := by
      have hL_lower_bound : ∀ᶠ r in atTop, vParam r ≥ 1 + deltaParam r * (r : ℝ) := by
        have hL_lower_bound : ∀ᶠ r in atTop, (alphaParam * ((r : ℝ) - 1) - 10 * Real.log r) ≥ 1 + (8 * alphaParam / Real.log r) * (r : ℝ) := by
          have hL_lower_bound : Filter.Tendsto (fun r : ℝ => (alphaParam * (r - 1) - 10 * Real.log r - 1 - 8 * alphaParam / Real.log r * r) / r) Filter.atTop (nhds (alphaParam)) := by
            have hL_lower_bound : Filter.Tendsto (fun r : ℝ => alphaParam - alphaParam / r - 10 * Real.log r / r - 1 / r - 8 * alphaParam / Real.log r) Filter.atTop (nhds (alphaParam)) := by
              have hL_lower_bound : Filter.Tendsto (fun r : ℝ => 10 * Real.log r / r) Filter.atTop (nhds 0) := by
                -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} 10y \log(1/y)$.
                suffices h_log_recip : Filter.Tendsto (fun y : ℝ => 10 * y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 10 );
              exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) hL_lower_bound ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ) ( by norm_num );
            refine hL_lower_bound.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by simp [ hr.ne', mul_sub, sub_div, mul_div_assoc ] );
          have := hL_lower_bound.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two );
          filter_upwards [ this, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ lt_div_iff₀ hx₂ ] at hx₁; linarith;
        exact hL_lower_bound.natCast_atTop.mono fun r hr => hr;
      filter_upwards [ hL_lower_bound, ‹∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1› ] with r hr₁ hr₂ j hj;
      unfold uParam at *; nlinarith [ hr₂.1, hr₂.2, show ( j : ℝ ) ≤ r by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ] ;
    have hL_lower_bound : ∀ᶠ r in atTop, ∀ j ∈ Finset.Icc 1 r, (1 - Real.exp (-deltaParam r)) ≥ deltaParam r / 2 := by
      filter_upwards [ ‹∀ᶠ r in atTop, deltaParam r ∈ Set.Ioc 0 1› ] with r hr j hj using by nlinarith [ hr.1, hr.2, Real.exp_pos ( -deltaParam r ), Real.exp_neg ( deltaParam r ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( deltaParam r ) ) ), Real.add_one_le_exp ( deltaParam r ), Real.add_one_le_exp ( -deltaParam r ) ] ;
    simp +zetaDelta at *;
    obtain ⟨ R1, hR1 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ j : ℕ, 1 ≤ j → j ≤ b → ( 1 - Real.exp ( -deltaParam b ) ) * Real.exp ( uParam b j ) / ( 2 * uParam b j ) ≤ ↑ ( # ( primeLayer b j ) ) ›; obtain ⟨ R2, hR2 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → 0 < deltaParam b ∧ deltaParam b ≤ 1›; obtain ⟨ R3, hR3 ⟩ := ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ j : ℕ, 1 ≤ j → j ≤ b → 1 ≤ uParam b j›; obtain ⟨ R4, hR4 ⟩ := hL_lower_bound; use Max.max R1 ( Max.max R2 ( Max.max R3 R4 ) ) ; intros r hr j hj₁ hj₂; specialize hR1 r ( le_trans ( le_max_left _ _ ) hr ) j hj₁ hj₂; specialize hR2 r ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hr ) ; specialize hR3 r ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hr ) j hj₁ hj₂; specialize hR4 r ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) hr ) j hj₁ hj₂;
    exact le_trans ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; nlinarith [ Real.exp_pos ( uParam r j ) ] ) hR1;
  -- By primeLayer_card_lower, eventually ∀j∈[1,r], M ≥ L_j := (1-e^{-δ})e^{u}/(2u) where δ=deltaParam r. Also eventually δ∈(0,1], u ≥ 1 (since u≥u_1→∞), and using 1-e^{-δ} ≥ δ/2 we get L_j ≥ δ e^{u}/(4u) > 0.
  have hR1_pos : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 0 < deltaParam r ∧ 0 < uParam r j := by
    have hR1_pos : ∀ᶠ r in Filter.atTop, 0 < deltaParam r ∧ 0 < uParam r 1 := by
      have hR1_pos : Filter.Tendsto (fun r : ℕ => uParam r 1) Filter.atTop Filter.atTop := by
        unfold uParam vParam deltaParam alphaParam;
        -- We'll use the fact that $Real.log r$ grows slower than $r$ to show that the expression tends to infinity.
        have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) / r) Filter.atTop (nhds (Real.log 2)) := by
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
          simpa [div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm, mul_left_comm] using!
            h_const.add ((tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log 2)).sub
              (h_log_r_div_r.mul_const 10))
        have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) - (r - 1) * (8 * Real.log 2 / Real.log r)) Filter.atTop Filter.atTop := by
          have h_log_growth : Filter.Tendsto (fun r : ℕ => (Real.log 2 * (r - 1) - 10 * Real.log r) / r - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r)) Filter.atTop (nhds (Real.log 2)) := by
            convert! h_log_growth.sub ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) using 2 ; norm_num
          have h_log_growth : Filter.Tendsto (fun r : ℕ => r * ((Real.log 2 * (r - 1) - 10 * Real.log r) / r - (1 - 1 / (r : ℝ)) * (8 * Real.log 2 / Real.log r))) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.atTop_mul_pos;
            exacts [ show 0 < Real.log 2 by positivity, tendsto_natCast_atTop_atTop, h_log_growth ];
          refine h_log_growth.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ mul_sub, mul_div_cancel₀ _ ( by positivity ) ] ; simp [ hr.ne', mul_sub, sub_mul, div_eq_mul_inv ] );
        aesop;
      filter_upwards [ hR1_pos.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂ using ⟨ div_pos ( mul_pos ( by norm_num ) ( Real.log_pos one_lt_two ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr hr₂ ) ), hr₁ ⟩;
    filter_upwards [ hR1_pos, Filter.eventually_ge_atTop 1 ] with r hr₁ hr₂ j hj₁;
    simp_all +decide [ uParam ];
    nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast; linarith, show ( j : ℝ ) ≤ r by norm_cast; linarith ];
  -- Step 2 (take logs; reduce to an r-only bound). Since the RHS-to-bound is positive, it is ≤ e^{εr} iff its log ≤ εr.
  have h_log_bound : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ ε * r := by
    -- Now 2v - 2u = 2(v-u) = 2((r:ℝ)-j)δ ≤ 2(r-1)δ ≤ 16 α r/log r (since δ = 8α/log r and (r-1)≤r).
    have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ Real.log C + 4 * Real.log (20 * r) + 16 * alphaParam * r / Real.log r + Real.log 16 + 2 * Real.log (vParam r) - 2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r) := by
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, Real.log (C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2)) ≤ Real.log C + 4 * Real.log (20 * r) + 2 * vParam r - 2 * Real.log (deltaParam r) + 2 * Real.log (uParam r j) - 2 * uParam r j + Real.log 16 := by
        filter_upwards [ hR1_pos, Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂;
        intro j hj; rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
        · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try linarith [ hr₁ j hj ];
          rw [ Real.log_mul, Real.log_mul ] <;> norm_num <;> try linarith [ hr₁ j hj ];
          rw [ show ( 16 : ℝ ) = 2 ^ 4 by norm_num, Real.log_pow ] ; norm_num [ Real.log_div ] ; ring_nf ; norm_num;
        · exact ⟨ hC.ne', hr₂.ne' ⟩;
        · exact ⟨ hC.ne', hr₂.ne' ⟩;
        · exact ⟨ ne_of_gt ( hr₁ j hj |>.1 ), ne_of_gt ( hr₁ j hj |>.2 ) ⟩;
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 2 * vParam r - 2 * uParam r j ≤ 16 * alphaParam * r / Real.log r := by
        filter_upwards [ hR1_pos ] with r hr j hj;
        unfold uParam deltaParam; ring_nf; norm_num;
        exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_num ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Finset.mem_Icc.mp hj ] ) ) ) );
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, -2 * Real.log (deltaParam r) = -2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r) := by
        filter_upwards [ hR1_pos, Filter.eventually_gt_atTop 1 ] with r hr₁ hr₂;
        intro j hj; rw [ show deltaParam r = 8 * alphaParam / Real.log r from rfl ] ; rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( by norm_num ) <| Real.log_pos one_lt_two ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hr₂ ) ] ; ring;
      have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, 2 * Real.log (uParam r j) ≤ 2 * Real.log (vParam r) := by
        have h_log_bound_step : ∀ᶠ r in Filter.atTop, ∀ j ∈ Finset.Icc 1 r, uParam r j ≤ vParam r := by
          simp +zetaDelta at *;
          exact ⟨ 1, fun r hr j hj₁ hj₂ => sub_le_self _ <| mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr hj₂ ) <| div_nonneg ( mul_nonneg ( by norm_num ) <| Real.log_nonneg one_le_two ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ⟩;
        filter_upwards [ h_log_bound_step, hR1_pos ] with r hr₁ hr₂ using fun j hj => mul_le_mul_of_nonneg_left ( Real.log_le_log ( hr₂ j hj |>.2 ) ( hr₁ j hj ) ) zero_le_two;
      filter_upwards [ ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, Real.log ( C * ( 20 * r ) ^ 4 * Real.exp ( 2 * vParam r ) / ( 1 / 2 * deltaParam r * Real.exp ( uParam r j ) / ( 2 * uParam r j ) ) ^ 2 ) ≤ Real.log C + 4 * Real.log ( 20 * r ) + 2 * vParam r - 2 * Real.log ( deltaParam r ) + 2 * Real.log ( uParam r j ) - 2 * uParam r j + Real.log 16›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * vParam r - 2 * uParam r j ≤ 16 * alphaParam * r / Real.log r›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, -2 * Real.log ( deltaParam r ) = -2 * Real.log ( 8 * alphaParam ) + 2 * Real.log ( Real.log r )›, ‹∀ᶠ r in atTop, ∀ j ∈ Icc 1 r, 2 * Real.log ( uParam r j ) ≤ 2 * Real.log ( vParam r )› ] with r hr₁ hr₂ hr₃ hr₄ using fun j hj => by linarith [ hr₁ j hj, hr₂ j hj, hr₃ j hj, hr₄ j hj ] ;
    -- Each summand divided by r tends to 0 — constants/r→0; log(20r)/r→0; (16α/log r)→0; log(vParam r)/r→0 (since vParam r ~ αr, log ~ log r, /r→0); log(log r)/r→0.
    have h_log_bound_step2 : Filter.Tendsto (fun r : ℕ => (Real.log C + 4 * Real.log (20 * r) + 16 * alphaParam * r / Real.log r + Real.log 16 + 2 * Real.log (vParam r) - 2 * Real.log (8 * alphaParam) + 2 * Real.log (Real.log r)) / (r : ℝ)) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\log(v_r) / r \to 0$ as $r \to \infty$.
      have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (vParam r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $v_r \sim \alpha r$ as $r \to \infty$.
        have h_v_r_sim : Filter.Tendsto (fun r : ℕ => vParam r / (r : ℝ)) Filter.atTop (nhds (alphaParam)) := by
          unfold vParam; norm_num [ alphaParam ] ; ring_nf;
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
          simpa [div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm, mul_left_comm] using!
            h_const.add ((tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log 2)).sub
              (h_log_r_div_r.mul_const 10))
        have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (vParam r / (r : ℝ)) / (r : ℝ)) Filter.atTop (nhds 0) := by
          simpa using! Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_v_r_sim <| by norm_num [ alphaParam ] ) tendsto_natCast_atTop_atTop;
        have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => (Real.log (vParam r / (r : ℝ)) + Real.log (r : ℝ)) / (r : ℝ)) Filter.atTop (nhds 0) := by
          have h_log_v_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (r : ℝ) / (r : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          simpa [ add_div ] using! Filter.Tendsto.add ‹Tendsto ( fun r : ℕ => Real.log ( vParam r / ( r : ℝ ) ) / ( r : ℝ ) ) atTop ( nhds 0 ) › h_log_v_r_div_r;
        refine h_log_v_r_div_r.congr' ?_;
        filter_upwards [ h_v_r_sim.eventually ( lt_mem_nhds <| show alphaParam > 0 from Real.log_pos one_lt_two ) ] with r hr using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] ; ring;
      -- We'll use the fact that $\log(\log r) / r \to 0$ as $r \to \infty$.
      have h_log_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\frac{\log \log r}{r}$ tends to $0$ as $r$ tends to infinity.
        have h_log_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (Real.log r) / Real.log r) Filter.atTop (nhds 0) := by
          have h_log_log_r_div_r : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
            suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          exact h_log_log_r_div_r.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine' squeeze_zero_norm' _ h_log_log_r_div_r;
        filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_left ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ( Real.log_pos <| by norm_num; linarith ) <| by linarith [ Real.log_le_sub_one_of_pos <| show 0 < ( n : ℝ ) by positivity ] ;
      -- We'll use the fact that $\log(20r) / r \to 0$ as $r \to \infty$.
      have h_log_20r_div_r : Filter.Tendsto (fun r : ℕ => Real.log (20 * r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_20r_div_r : Filter.Tendsto (fun r : ℕ => (Real.log 20 + Real.log r) / (r : ℝ)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
          simpa [ add_div ] using! Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) h_log_r_div_r;
        refine h_log_20r_div_r.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
      -- We'll use the fact that $16 * \alpha * r / \log r / r \to 0$ as $r \to \infty$.
      have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => 16 * alphaParam * r / Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        exact le_trans ( Filter.Tendsto.const_mul _ <| Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with r hr; aesop ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) <| by norm_num;
      ring_nf;
      simpa [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc ] using! Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( Real.log C ) ) ( h_log_r_div_r ) ) ( h_log_20r_div_r.const_mul 4 ) ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( Real.log 16 ) ) ) ( Filter.Tendsto.sub ( h_log_v_r_div_r.const_mul 2 ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const ( 2 * Real.log ( alphaParam * 8 ) ) ) ) ) ( h_log_log_r_div_r.const_mul 2 );
    filter_upwards [ h_log_bound_step, h_log_bound_step2.eventually ( gt_mem_nhds <| show 0 < ε by positivity ), Filter.eventually_gt_atTop 0 ] with r hr₁ hr₂ hr₃;
    exact fun j hj => le_trans ( hr₁ j hj ) ( by rw [ div_lt_iff₀ ( by positivity ) ] at hr₂; linarith );
  filter_upwards [ hR1_pos, h_log_bound, Filter.eventually_ge_atTop R1 ] with r hr₁ hr₂ hr₃;
  intro j hj
  specialize hr₂ j hj
  have h_exp_bound : C * (20 * r) ^ 4 * Real.exp (2 * vParam r) / ((1 / 2 * deltaParam r * Real.exp (uParam r j) / (2 * uParam r j)) ^ 2) ≤ Real.exp (ε * r) := by
    rwa [ Real.log_le_iff_le_exp ( div_pos ( mul_pos ( mul_pos hC ( pow_pos ( by norm_cast; linarith [ Finset.mem_Icc.mp hj ] ) _ ) ) ( Real.exp_pos _ ) ) ( sq_pos_of_pos ( div_pos ( mul_pos ( mul_pos ( by norm_num ) ( hr₁ j hj |>.1 ) ) ( Real.exp_pos _ ) ) ( mul_pos ( by norm_num ) ( hr₁ j hj |>.2 ) ) ) ) ) ] at hr₂;
  refine le_trans ?_ h_exp_bound;
  gcongr;
  · exact sq_pos_of_pos ( div_pos ( mul_pos ( mul_pos ( by norm_num ) ( hr₁ j hj |>.1 ) ) ( Real.exp_pos _ ) ) ( mul_pos zero_lt_two ( hr₁ j hj |>.2 ) ) );
  · exact div_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) ( le_of_lt ( hr₁ j hj |>.1 ) ) ) ( Real.exp_nonneg _ ) ) ( mul_nonneg zero_le_two ( le_of_lt ( hr₁ j hj |>.2 ) ) );
  · exact hR1 r hr₃ j hj

/-- **Lemma 5.1 (fourth-moment cleaning).**  For each layer `j`, the set `ℬ_j` of
primes `p ≤ e^v` admitting a nonprincipal character `χ (mod p)` with
`|∑_{q ∈ 𝒫_j} χ(q)| > M_j/(20r)` is of size `exp(o(r))`. -/
theorem fourth_moment_cleaning :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.Icc 1 r,
      (((Finset.Icc 1 ⌊Real.exp (vParam r)⌋₊).filter
          (fun p => Nat.Prime p ∧ ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
            (primeLayer r j).card / (20 * (r : ℝ)) <
              ‖∑ q ∈ primeLayer r j, χ q‖)).card : ℝ)
        ≤ Real.exp (ε * r) := by
  intro ε hε
  obtain ⟨C, hC, hcard⟩ := fourth_moment_card_le
  filter_upwards [fourth_moment_asymp C hC ε hε, Filter.eventually_ge_atTop 2]
    with r hasymp hr j hj
  exact le_trans (hcard r j hr hj) (hasymp j hj)

end Erdos768
