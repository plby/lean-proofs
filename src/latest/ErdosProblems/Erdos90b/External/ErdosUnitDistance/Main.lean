/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos90b.External.ErdosUnitDistance.PointCount

/-!
# The main theorem

The uniform-constant form of Erdős's unit-distance conjecture is false:
for every `C > 0` there are arbitrarily large `n` admitting `n`-point
planar sets with more than `n^(1 + C/log log n)` unit-distance pairs
(L. Alpöge, 2026).
-/

open scoped Classical

namespace Erdos

section Assembly

/-- [medium; pure real arithmetic]  **The final counting inequality.**
Suppose `n, ν` (point and unit-pair counts), `h` (class number) and the
parameters `g, t` satisfy the construction estimates below.  If moreover
`t` is large compared to `g log g` and to `log h / 2^g`, and `g` is large
compared to `C log t`, then `ν` beats `n^(1 + C/log log n)`.

The precise sufficient conditions encoded here:
with `d = 2^g`,
* `hpairs` forces `log (ν/n) ≥ (t·d/2)·log 2 - log h - d·log 2 - log 2 - d·log 64`,
  which is `≥ (t·d/4)·log 2` by `hth` (note `hth` gives `log h ≤ d·(t/8 - 8)`);
* `hlower` plus `hth` force `log n ≥ 0.2·t·d`, hence
  `log log n ≥ log d = g·log 2` (using `ht5`);
* `hMn` bounds `log n ≤ d·(log M + 7)`, so by `hgC`
  `C·log n / log log n ≤ C·d·(log M + 7)/(g·log 2) ≤ (t·d/40)·log 2 < (t·d/4)·log 2`.

Stated as a closed implication between real inequalities so that it can be
attacked independently of all geometry and number theory. -/
theorem key_inequality
    {C : ℝ} (hC : 0 < C) {g t : ℕ} {n ν h M : ℝ}
    (hn16 : 16 ≤ n) (hν : 0 < ν) (hh : 1 ≤ h) (hM : 3 ≤ M)
    -- construction estimates (d = 2^g as a real):
    (hlower : (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ n * h * 2 ^ 2 ^ g)
    (hupper : n ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g))
    (hpairs : (2 : ℝ) ^ (t * 2 ^ (g - 1)) * n ≤ h * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * ν)
    -- size conditions on the parameters:
    (hg1 : 1 ≤ g) (_ht5 : 5 ≤ t)
    (hth : (8 : ℝ) * (Real.log h / 2 ^ g + 8) ≤ t)
    (hgC : 40 * C * (Real.log M + 8) ≤ (t : ℝ) * g * Real.log 2 ^ 2)
    -- log M stands in for log (m t) ≤ c₁ t log t; the caller arranges sizes
    (hMn : Real.log n ≤ 2 * 2 ^ g * (Real.log 32 + Real.log M / 2)) :
    n ^ (1 + C / Real.log (Real.log n)) < ν := by
  -- Step 0: Rewrite `hth` as `(H)`.
  have hH : Real.log h ≤ (t : ℝ) * 2 ^ g / 8 - 8 * 2 ^ g := by
    nlinarith [ show ( 0 : ℝ ) < 2 ^ g by positivity, div_mul_cancel₀ ( Real.log h ) ( show ( 2 ^ g : ℝ ) ≠ 0 by positivity ) ];
  -- Step 1: Prove `Real.log n ≥ d`.
  have h_log_n_ge_d : Real.log n ≥ 2 ^ g := by
    -- Applying the logarithm to both sides of `hlower`.
    have h_log_lower : Real.log (2 ^ (t * 2 ^ (g - 1))) ≤ Real.log (n * h * 2 ^ (2 ^ g)) := by
      gcongr;
    rcases g with ( _ | g ) <;> simp_all +decide [ pow_succ, mul_assoc ];
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] at h_log_lower ; norm_num at *;
    nlinarith [ Real.log_two_gt_d9, show ( t : ℝ ) ≥ 5 by norm_cast, show ( 2 ^ g : ℝ ) ≥ 1 by exact one_le_pow₀ one_le_two, show ( Real.log h : ℝ ) ≥ 0 by exact Real.log_nonneg hh ];
  -- Step 2: Prove `Real.log (Real.log n) ≥ g * Real.log 2`.
  have h_log_log_n_ge_g_log_2 : Real.log (Real.log n) ≥ g * Real.log 2 := by
    simpa using Real.log_le_log ( by positivity ) h_log_n_ge_d;
  -- Step 3: Prove `Real.log ν ≥ Real.log n + (t * 2 ^ g / 4) * Real.log 2`.
  have h_log_nu_ge : Real.log ν ≥ Real.log n + (t * 2 ^ g / 4) * Real.log 2 := by
    have h_log_nu_ge : Real.log ν ≥ Real.log n + (t * 2 ^ g / 2) * Real.log 2 - Real.log h - 7 * 2 ^ g * Real.log 2 - Real.log 2 := by
      have h_log_nu_ge : Real.log (2 ^ (t * 2 ^ (g - 1)) * n) ≤ Real.log (h * 2 ^ (2 ^ g) * (2 * 64 ^ (2 ^ g)) * ν) := by
        exact Real.log_le_log ( by positivity ) hpairs;
      rw [ Real.log_mul, Real.log_mul, Real.log_mul ] at h_log_nu_ge <;> try positivity;
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ] at h_log_nu_ge ; norm_num at *;
      rw [ show ( 64 : ℝ ) = 2 ^ 6 by norm_num, Real.log_pow ] at h_log_nu_ge ; rcases g with ( _ | g ) <;> norm_num [ pow_succ' ] at * ; linarith;
    have h_log_2_bounds : 1 / 2 < Real.log 2 ∧ Real.log 2 < 1 := by
      exact ⟨ Real.log_two_gt_d9.trans_le' <| by norm_num, Real.log_two_lt_d9.trans_le <| by norm_num ⟩;
    nlinarith [ show ( t : ℝ ) ≥ 5 by norm_cast, show ( 2 : ℝ ) ^ g ≥ 2 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hg1 ), mul_le_mul_of_nonneg_left h_log_2_bounds.1.le ( show ( 0 : ℝ ) ≤ 2 ^ g by positivity ), mul_le_mul_of_nonneg_left h_log_2_bounds.2.le ( show ( 0 : ℝ ) ≤ 2 ^ g by positivity ) ];
  -- Step 5: Prove `(t * 2 ^ g / 4) * Real.log 2 > C * Real.log n / Real.log (Real.log n)`.
  have h_term_gt : (t * 2 ^ g / 4) * Real.log 2 > C * Real.log n / Real.log (Real.log n) := by
    -- Using the bounds from `hMn` and `h_log_log_n_ge_g_log_2`, we get:
    have h_bound : C * Real.log n / Real.log (Real.log n) ≤ C * (2 ^ g * (Real.log M + 10)) / (g * Real.log 2) := by
      gcongr;
      · exact mul_nonneg hC.le ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) ( by norm_num ) ) );
      · rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] at hMn ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, pow_pos ( zero_lt_two' ℝ ) g ];
    refine lt_of_le_of_lt h_bound ?_;
    rw [ div_lt_iff₀ ( by positivity ) ];
    nlinarith [ show 0 < ( 2 : ℝ ) ^ g by positivity, show 0 < ( t : ℝ ) * 2 ^ g by positivity, show 0 < ( g : ℝ ) * Real.log 2 by positivity, Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two, mul_le_mul_of_nonneg_left ( show ( Real.log M : ℝ ) ≥ 0 by exact Real.log_nonneg <| by linarith ) <| show 0 ≤ ( 2 : ℝ ) ^ g by positivity ];
  rw [ Real.rpow_def_of_pos ( by positivity ) ];
  rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; ring_nf at * ; linarith

private theorem exists_params (C : ℝ) (hC : 0 < C) (c₀ c₁ : ℝ)
    (hc₀ : 1 ≤ c₀) (hc₁ : 1 ≤ c₁) (N : ℕ) :
    ∃ g t : ℕ, 1 ≤ g ∧ 5 ≤ t ∧
      8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) ≤ (t : ℝ) ∧
      40 * C * (c₁ * (t : ℝ) * Real.log (t + 2) + 8) ≤
        (t : ℝ) * g * Real.log 2 ^ 2 ∧
      Real.log ((max N 16 : ℕ) : ℝ)
          + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2)
          + 2 ^ g * Real.log 2 ≤ (t : ℝ) * 2 ^ (g - 1) * Real.log 2 := by
  -- We need to find $g$ large enough so that $t = T g$ satisfies the required inequalities.
  have h_second : ∃ G : ℕ, ∀ g ≥ G, 40 * C * (c₁ * (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * (Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) + 8)) ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * g * (Real.log 2) ^ 2 := by
    -- We'll use that $Real.log (t + 2) = O(log(g + 2))$ and $t = O(g^2)$ to simplify the inequality.
    have h_simplify : ∃ G : ℕ, ∀ g ≥ G, Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) ≤ 2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) := by
      have h_simplify : ∃ G : ℕ, ∀ g ≥ G, Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2 ≤ (g + 2) ^ 2 * (8 * c₀ + 70) := by
        refine' ⟨ 8, fun g hg => _ ⟩ ; ring_nf;
        nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ 69 + c₀ * g * Real.log ( 2 + g ) * 8 + c₀ * Real.log ( 2 + g ) * 8 by exact add_nonneg ( add_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ) ) ( mul_nonneg ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 2 : ℝ ) + g ), mul_le_mul_of_nonneg_left ( show ( g : ℝ ) ≥ 8 by norm_cast ) ( show 0 ≤ c₀ by positivity ) ];
      obtain ⟨ G, hG ⟩ := h_simplify; use G; intro g hg; have := Real.log_le_log ( by positivity ) ( hG g hg ) ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] at this; norm_num at * ; linarith;
    -- Using the simplified inequality, we can bound the term involving the logarithm.
    obtain ⟨G, hG⟩ := h_simplify;
    have h_bound : ∃ G' : ℕ, ∀ g ≥ G', 40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8)) ≤ g * (Real.log 2) ^ 2 := by
      have h_bound : Filter.Tendsto (fun g : ℕ => (40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8))) / (g : ℝ)) Filter.atTop (nhds 0) := by
        -- We can factor out $g$ in the numerator and denominator and use the fact that $\frac{\log(g+2)}{g}$ tends to $0$ as $g$ tends to infinity.
        have h_log_div_g : Filter.Tendsto (fun g : ℕ => (Real.log (g + 2)) / (g : ℝ)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\frac{\log(g+2)}{g}$ tends to $0$ as $g$ tends to infinity.
          have h_log_div_g : Filter.Tendsto (fun g : ℕ => Real.log (g : ℝ) / (g : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring_nf );
            norm_num;
            apply tendsto_nhdsWithin_of_tendsto_nhds
            have h : Filter.Tendsto (fun y : ℝ => -(y * Real.log y)) (nhds 0)
                (nhds (-(0 * Real.log 0))) :=
              (Real.continuous_mul_log.neg.tendsto 0).congr'
                (Filter.Eventually.of_forall fun _ => rfl)
            simpa only [zero_mul, neg_zero] using h
          -- We can use the fact that $\frac{\log(g+2)}{g} = \frac{\log(g)}{g} + \frac{\log(1 + 2/g)}{g}$.
          have h_log_div_g_split : Filter.Tendsto (fun g : ℕ => (Real.log (g : ℝ) / (g : ℝ)) + (Real.log (1 + 2 / (g : ℝ)) / (g : ℝ))) Filter.atTop (nhds 0) := by
            simpa [div_eq_mul_inv] using h_log_div_g.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) tendsto_inv_atTop_nhds_zero_nat );
          refine h_log_div_g_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with g hg using by rw [ show ( g : ℝ ) + 2 = g * ( 1 + 2 / g ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring );
        convert h_log_div_g.const_mul ( 40 * C * c₁ * 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun g : ℕ => ( 40 * C * c₁ * ( Real.log ( 8 * c₀ + 70 ) + 8 ) ) / ( g : ℝ ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop using 2 <;> ring;
      have := h_bound.eventually ( gt_mem_nhds <| show 0 < Real.log 2 ^ 2 by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ G', hG' ⟩ ; exact ⟨ G' + 1, fun g hg => by have := hG' g ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
    obtain ⟨ G', hG' ⟩ := h_bound; use Max.max G G'; intros g hg; specialize hG g ( le_trans ( le_max_left _ _ ) hg ) ; specialize hG' g ( le_trans ( le_max_right _ _ ) hg ) ; norm_num at *;
    nlinarith [ show ( 0 : ℝ ) ≤ ⌈8 * ( c₀ * ( g + 1 ) * Real.log ( g + 2 ) + 8 ) + 5⌉₊ * c₁ * C by positivity ];
  obtain ⟨ G, hG ⟩ := h_second;
  -- Choose $g$ large enough so that the third inequality holds.
  obtain ⟨ G', hG' ⟩ : ∃ G' : ℕ, ∀ g ≥ G', Real.log (max N 16) + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) + 2 ^ g * Real.log 2 ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * 2 ^ (g - 1) * Real.log 2 := by
    -- Divide both sides by $2^{g-1}$ to simplify the inequality.
    suffices h_div : ∃ G' : ℕ, ∀ g ≥ G', Real.log (max N 16) / 2 ^ (g - 1) + 2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2 ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * Real.log 2 by
      obtain ⟨ G', hG' ⟩ := h_div; use G' + 1; intros g hg; specialize hG' g ( by linarith ) ; rcases g <;> norm_num [ pow_succ' ] at *;
      rw [ div_add', div_add', div_le_iff₀ ] at hG' <;> first | positivity | linarith;
    -- We'll use that $Real.log (max N 16) / 2 ^ (g - 1)$ tends to $0$ as $g$ tends to infinity.
    have h_log_div : Filter.Tendsto (fun g : ℕ => Real.log (max N 16) / 2 ^ (g - 1)) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 1 );
    -- We'll use that $2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2$ is bounded above.
    have h_bound : ∃ G' : ℕ, ∀ g ≥ G', 2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2 ≤ (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) * Real.log 2 - 2 * Real.log 2 := by
      use 16; intro g hg; ring_nf ;
      have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ show ( g : ℝ ) ≥ 16 by norm_cast, show ( c₀ : ℝ ) * Real.log ( 2 + g ) ≥ 0 by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ), show ( c₀ : ℝ ) * g * Real.log ( 2 + g ) ≥ 0 by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ] ;
    obtain ⟨ G', hG' ⟩ := h_bound;
    have := h_log_div.eventually ( gt_mem_nhds <| show 0 < 2 * Real.log 2 by positivity );
    obtain ⟨ G'', hG'' ⟩ := Filter.eventually_atTop.mp this;
    exact ⟨ Max.max G' G'', fun g hg => by nlinarith [ hG' g ( le_trans ( le_max_left _ _ ) hg ), hG'' g ( le_trans ( le_max_right _ _ ) hg ), Nat.le_ceil ( 8 * ( c₀ * ( g + 1 ) * Real.log ( g + 2 ) + 8 ) + 5 ), Real.log_pos one_lt_two ] ⟩;
  refine' ⟨ G + G' + 1, ⌈8 * ( c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) + 8 ) + 5⌉₊, _, _, _, _, _ ⟩ <;> norm_num;
  · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ show 0 ≤ c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ] ) );
  · linarith [ Nat.le_ceil ( 8 * ( c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) + 8 ) + 5 ) ];
  · convert! le_trans _ ( hG ( G + G' + 1 ) ( by linarith ) ) using 1 <;> push_cast <;> ring_nf;
    gcongr;
    exact le_trans ( le_mul_of_one_le_right ( by positivity ) hc₁ ) ( le_mul_of_one_le_right ( by positivity ) ( Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr ( by nlinarith [ show 0 ≤ c₀ * G * Real.log ( 3 + G + G' ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by linarith ) ), show 0 ≤ c₀ * G' * Real.log ( 3 + G + G' ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by linarith ) ), show 0 ≤ c₀ * Real.log ( 3 + G + G' ) by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ] ) ) ) );
  · exact_mod_cast hG' ( G + G' + 1 ) ( by linarith )

/-
**The uniform-constant form of Erdős's unit-distance conjecture is
false** (Alpöge, 2026): for every `C > 0` and every threshold `N` there
exist `n ≥ N` and an `n`-point set `P ⊆ ℝ²` with more than
`n^(1 + C / log log n)` unit-distance pairs.

[medium given everything above; glue + parameter choice]
Sketch: given `C` and `N`, let `c₀, c₁` be the constants of
`log_classNumber_Kf_le` and `log_m_le`.  Choose
`g = ⌈41·C·c₁·log (t+2) / (log 2)²⌉ + 1` and `t` large (depending on
`C, N, c₀, c₁`): then `hgC` holds since `log (m t) + 8 ≤ c₁·(t+8)·log (t+2)`,
and `hth` holds since `log h / 2^g ≤ c₀·(g+1)·log (g+2)` grows only like
`(log t)·(log log t)`.  Use `M = m t`, `h = classNumber (Kf g)`, and the
estimates from `exists_good_pointset`; `n ≥ N` and `n ≥ 16` follow from
the first estimate since `n ≥ 2^(t·2^(g-1)) / (h·2^(2^g)) → ∞` as
`t → ∞` for the chosen `g(t)`.
-/
/-- **The uniform-constant form of Erdős's unit-distance conjecture is
false** (Alpöge, 2026): for every `C > 0` and every threshold `N` there
exist `n ≥ N` and an `n`-point set `P ⊆ ℝ²` with more than
`n^(1 + C / log log n)` unit-distance pairs.

[medium given everything above; glue + parameter choice]
Sketch: given `C` and `N`, let `c₀, c₁` be the constants of
`log_classNumber_Kf_le` and `log_m_le`.  Choose
`g = ⌈41·C·c₁·log (t+2) / (log 2)²⌉ + 1` and `t` large (depending on
`C, N, c₀, c₁`): then `hgC` holds since `log (m t) + 8 ≤ c₁·(t+8)·log (t+2)`,
and `hth` holds since `log h / 2^g ≤ c₀·(g+1)·log (g+2)` grows only like
`(log t)·(log log t)`.  Use `M = m t`, `h = classNumber (Kf g)`, and the
estimates from `exists_good_pointset`; `n ≥ N` and `n ≥ 16` follow from
the first estimate since `n ≥ 2^(t·2^(g-1)) / (h·2^(2^g)) → ∞` as
`t → ∞` for the chosen `g(t)`. -/
theorem erdos_unit_distance_uniform_constant_false :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧
        (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDist P : ℝ) := by
  intro C hC N;
  -- Apply the `exists_params` theorem to obtain the required `g` and `t`.
  obtain ⟨g, t, hg1, ht5, h2, h3, h4⟩ := exists_params C hC (Classical.choose (log_classNumber_Kf_le)) (Classical.choose (log_m_le)) (Classical.choose_spec (log_classNumber_Kf_le)).left (Classical.choose_spec (log_m_le)).left (max N 16);
  obtain ⟨n, Q, hQcard, hL, hU, hP⟩ := exists_good_pointset g t hg1 (by omega : 1 ≤ t);
  -- Prove that $n \geq \max(N, 16)$.
  have hn_ge_max : (max (max N 16) 16 : ℝ) ≤ n := by
    have h_log : Real.log ((max (max N 16) 16 : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ (2 ^ g)) ≤ Real.log (2 ^ (t * 2 ^ (g - 1))) := by
      rw [ Real.log_mul, Real.log_mul ] <;> norm_num;
      · have := Classical.choose_spec ( log_classNumber_Kf_le ) |>.2 g;
        norm_num at * ; linarith;
      · positivity;
      · exact ne_of_gt ( NumberField.classNumber_pos _ );
      · exact ⟨ by positivity, by exact ne_of_gt <| NumberField.classNumber_pos _ ⟩;
    rw [ Real.log_le_log_iff ] at h_log <;> norm_cast at * <;> norm_num at *;
    · constructor <;> nlinarith [ show 0 < NumberField.classNumber ( Kf g ) * 2 ^ 2 ^ g by exact mul_pos ( Nat.cast_pos.mpr ( NumberField.classNumber_pos _ ) ) ( pow_pos ( by norm_num ) _ ), le_max_left N 16, le_max_right N 16 ];
    · grind +qlia;
  refine' ⟨ n, Q, _, hQcard, _ ⟩;
  · exact_mod_cast le_trans ( le_max_of_le_left ( le_max_left _ _ ) ) hn_ge_max;
  · apply_rules [ key_inequality ];
    any_goals linarith [ le_max_left ( max ( N : ℝ ) 16 ) 16, le_max_right ( max ( N : ℝ ) 16 ) 16 ];
    any_goals exact Nat.one_le_cast.mpr ( NumberField.classNumber_pos _ );
    · contrapose! hP;
      exact lt_of_le_of_lt ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) hP ) ( by exact mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by linarith [ show n > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hn_ge_max ) ] ) ) );
    · norm_cast;
      exact le_trans ( by decide ) ( m_ge t |> le_trans ( pow_le_pow_right₀ ( by decide ) ht5 ) );
    · have := Classical.choose_spec ( log_classNumber_Kf_le );
      nlinarith [ this.2 g, show ( 0 : ℝ ) < 2 ^ g by positivity, div_mul_cancel₀ ( Real.log ( NumberField.classNumber ( Kf g ) : ℝ ) ) ( show ( 2 : ℝ ) ^ g ≠ 0 by positivity ) ];
    · refine' le_trans _ h3;
      gcongr;
      exact Classical.choose_spec ( log_m_le ) |>.2 t;
    · refine' le_trans ( Real.log_le_log ( by linarith [ le_max_left ( max ( N : ℝ ) 16 ) 16, le_max_right ( max ( N : ℝ ) 16 ) 16 ] ) hU ) _;
      rw [ Real.log_pow, Real.log_mul, Real.log_sqrt ] <;> ring_nf <;> norm_num;
      · linarith;
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| p1_spec i |>.1

end Assembly

end Erdos
