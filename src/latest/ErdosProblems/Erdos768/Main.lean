import ErdosProblems.Erdos768.Defs
import ErdosProblems.Erdos768.Elementary
import ErdosProblems.Erdos768.Analytic
import ErdosProblems.Erdos768.LowerBound
import ErdosProblems.Erdos768.LowerBoundCount
import ErdosProblems.Erdos768.UpperBound

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — main theorem

This is the top-level file assembling Eric Li's resolution of Erdős Problem 768
(arXiv:2606.24872).  The main result is

`lim_{x→∞} log(x / A(x)) / (√(log x) · log log x) = 1 / (2√(log 2))`,

where `A(x)` counts the integers `n ≤ x` satisfying the Sylow divisor condition.

The two directions are:

* `Erdos768.lower_bound` (Theorem 5.3 in the paper): the constructive lower bound
  `A(x) ≥ x·exp(-(c₀+ε)·S(x))` eventually, for every `ε > 0`;
* `Erdos768.upper_bound` (Theorem 10.4 in the paper): the sieve upper bound
  `A(x) ≤ x·exp(-(c₀-ε)·S(x))` eventually, for every `ε > 0`.

The main theorem `Erdos768.erdos_768` is deduced from these.
-/

open scoped Classical BigOperators
open Filter

namespace Erdos768

/-- Basic positivity: `1` satisfies the Sylow divisor condition (vacuously). -/
theorem sylowDivisor_one : SylowDivisor 1 := by
  intro p hp hpd
  exact absurd (Nat.le_of_dvd one_pos hpd) (by simpa using! hp.two_le)

/-- For `x ≥ 1` the count `A(x)` is at least `1`, since `1 ∈ [1, ⌊x⌋]` lies in `𝒜`. -/
theorem one_le_Acount {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Acount x := by
  have h1 : (1 : ℕ) ∈ (Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor := by
    refine Finset.mem_filter.2 ⟨?_, sylowDivisor_one⟩
    have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    simpa using! h1
  exact Finset.card_pos.2 ⟨1, h1⟩

/-- `A(x)` is monotone in `x` (larger interval `[1, ⌊x⌋]`). -/
theorem Acount_mono {x y : ℝ} (h : x ≤ y) : Acount x ≤ Acount y := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor h)

/-
`S(x) = √(log x)·log log x` is monotone once `x ≥ e^e` (so `log x ≥ e ≥ 1`
and `log log x ≥ 1 > 0`).
-/
theorem Sscale_le {a b : ℝ} (ha : Real.exp (Real.exp 1) ≤ a) (hab : a ≤ b) :
    Sscale a ≤ Sscale b := by
  apply_rules [ mul_le_mul, Real.sqrt_le_sqrt, Real.log_le_log ];
  · linarith [ Real.exp_pos ( Real.exp 1 ) ];
  · exact Real.log_pos ( lt_of_lt_of_le ( by norm_num [ Real.exp_pos ] ) ha );
  · linarith [ Real.exp_pos ( Real.exp 1 ) ];
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos ( Real.exp 1 ) ] ) ] ; linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] );
  · positivity

/-
**Block bound.**  For all sufficiently large `r`, the constructive lower
bound holds throughout the whole block `[e^{L_r}, e^{L_{r+1}})`.
-/
theorem lower_bound_block (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : ℝ,
      Real.exp (Lr r) ≤ x → x < Real.exp (Lr (r + 1)) →
        x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
  -- By `lower_bound_subsequence (ε/2) (half_pos hε)`, we get `hsub`.
  have h_lower_bound_subsequence : ∀ᶠ r in atTop, Real.exp (Lr r) * Real.exp (-(c₀ + ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r)) ≤ (Acount (Real.exp (Lr r)) : ℝ) := by
    convert! lower_bound_subsequence ( ε / 2 ) ( half_pos hε ) using 1;
  -- By `Lr_gap_negligible`, we get `hgap`.
  have h_Lr_gap_negligible : ∀ᶠ r in atTop, |(Lr (r + 1) - Lr r) / (Real.sqrt (Lr r) * Real.log (Lr r))| < ε / 2 := by
    convert! Metric.tendsto_nhds.mp ( Lr_gap_negligible ) ( ε / 2 ) ( half_pos hε ) using 1 ; norm_num [ abs_div, abs_mul ];
  filter_upwards [ h_lower_bound_subsequence, h_Lr_gap_negligible, Lr_eventually_lt, Lr_tendsto_atTop.eventually_ge_atTop ( Real.exp 1 ) ] with r hr₁ hr₂ hr₃ hr₄;
  intro x hx₁ hx₂
  have h_log_x : Real.log x < Lr (r + 1) := by
    rwa [ Real.log_lt_iff_lt_exp ( lt_of_lt_of_le ( by positivity ) hx₁ ) ]
  have h_Sscale_x : Sscale x ≥ Real.sqrt (Lr r) * Real.log (Lr r) := by
    have h_Sscale_x : Sscale x ≥ Sscale (Real.exp (Lr r)) := by
      apply Sscale_le;
      · exact Real.exp_le_exp.mpr hr₄;
      · linarith;
    convert! h_Sscale_x using 1 ; norm_num [ Sscale ]
  have h_gr : Lr (r + 1) - Lr r ≤ (ε / 2) * Real.sqrt (Lr r) * Real.log (Lr r) := by
    rw [ abs_lt ] at hr₂;
    rw [ div_lt_iff₀ ] at hr₂ <;> nlinarith [ show 0 < Real.sqrt ( Lr r ) * Real.log ( Lr r ) from mul_pos ( Real.sqrt_pos.mpr <| by linarith [ Real.exp_pos 1 ] ) ( Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ] ) ];
  refine le_trans ?_ ( hr₁.trans ?_ );
  · rw [ ← Real.exp_log ( show 0 < x from lt_of_lt_of_le ( by positivity ) hx₁ ) ];
    rw [ ← Real.exp_add, ← Real.exp_add ] ; norm_num [ Sscale ] at * ; nlinarith [ show 0 < c₀ by exact one_div_pos.mpr <| mul_pos zero_lt_two <| Real.sqrt_pos.mpr <| Real.log_pos one_lt_two ] ;
  · exact_mod_cast Acount_mono ( show Real.exp ( Lr r ) ≤ x from hx₁ )

/-
**Theorem 5.3 (constructive lower bound).**  For every `ε > 0`, eventually
`A(x) ≥ x · exp(-(c₀ + ε)·S(x))`.
-/
theorem lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ r ≥ R, ∀ x : ℝ, Real.exp (Lr r) ≤ x → x < Real.exp (Lr (r + 1)) → x * Real.exp (-(c₀ + ε) * Sscale x) ≤ (Acount x : ℝ) := by
    exact Filter.eventually_atTop.mp ( lower_bound_block ε hε ) |> fun ⟨ R, hR ⟩ => ⟨ R, fun r hr x hx₁ hx₂ => hR r hr x hx₁ hx₂ ⟩;
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k ≤ R, Lr k ≤ M := by
    exact ⟨ ∑ k ∈ Finset.range ( R + 1 ), |Lr k|, fun k hk => le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun a _ => abs_nonneg ( Lr a ) ) ( Finset.mem_range_succ_iff.mpr hk ) ) ⟩;
  -- For any $x \geq \exp(M)$, there exists $r \geq R$ such that $\exp(Lr(r)) \leq x < \exp(Lr(r+1))$.
  have h_exists_r : ∀ᶠ x in atTop, ∃ r ≥ R, Real.exp (Lr r) ≤ x ∧ x < Real.exp (Lr (r + 1)) := by
    have h_exists_r : ∀ᶠ x in atTop, ∃ r ≥ R, x < Real.exp (Lr (r + 1)) := by
      have h_exists_r : Filter.Tendsto (fun r : ℕ => Real.exp (Lr (r + 1))) Filter.atTop Filter.atTop := by
        exact Real.tendsto_exp_atTop.comp ( Lr_tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 1 ) );
      exact Filter.eventually_atTop.mpr ⟨ R, fun x hx => by rcases Filter.eventually_atTop.mp ( h_exists_r.eventually_gt_atTop x ) with ⟨ r, hr ⟩ ; exact ⟨ r + R, by linarith, hr _ <| by linarith ⟩ ⟩;
    filter_upwards [ h_exists_r, Filter.eventually_ge_atTop ( Real.exp M ) ] with x hx₁ hx₂;
    contrapose! hx₁;
    intro r hr; induction hr <;> simp_all +decide only [Nat.succ_eq_add_one] ;
    · exact hx₁ R le_rfl ( le_trans ( Real.exp_le_exp.mpr ( hM R le_rfl ) ) hx₂ );
    · exact hx₁ _ ( by linarith ) ( by linarith );
  filter_upwards [ h_exists_r ] with x hx using by obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := hx; exact hR r hr₁ x hr₂ hr₃;

/-
**Theorem 10.4 (sieve upper bound).**  For every `ε > 0`, eventually
`A(x) ≤ x · exp(-(c₀ - ε)·S(x))`.
-/
theorem upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (Acount x : ℝ) ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  have h_irregular_bound := Erdos768.irregular_bound ( ε / 2 ) ( by positivity );
  have h_regular_bound := Erdos768.regular_bound ( ε / 2 ) ( by positivity );
  have h_Sscale_bound : ∀ᶠ x in atTop, Real.log 2 ≤ (ε / 2) * Sscale x := by
    have h_Sscale_bound : Filter.Tendsto Sscale Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_mul_atTop₀ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop;
    exact h_Sscale_bound.eventually_ge_atTop ( Real.log 2 / ( ε / 2 ) ) |> fun h => h.mono fun x hx => by nlinarith [ mul_div_cancel₀ ( Real.log 2 ) ( by positivity : ( ε / 2 ) ≠ 0 ) ] ;
  filter_upwards [ h_irregular_bound, h_regular_bound, h_Sscale_bound, Filter.eventually_ge_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  -- Combine the bounds from `hx₁` and `hx₂`.
  have h_combined : (Acount x : ℝ) ≤ x * Real.exp (-(c₀ - ε / 2) * Sscale x) + x * Real.exp (-(c₀ - ε / 2) * Sscale x) := by
    refine' le_trans _ ( add_le_add hx₁ hx₂ );
    norm_cast;
    refine' le_trans _ ( Finset.card_union_le _ _ );
    refine Finset.card_mono ?_;
    intro n hn; by_cases h : ( n : ℝ ) ≤ x * Real.exp ( -4 * Sscale x ) <;> by_cases h' : Real.exp ( 4 * Sscale x ) < ( n : ℝ ) / ( rad n : ℝ ) <;> aesop;
  rw [ show - ( c₀ - ε ) * Sscale x = - ( c₀ - ε / 2 ) * Sscale x + ( ε / 2 ) * Sscale x by ring, Real.exp_add ];
  nlinarith [ Real.add_one_le_exp ( ε / 2 * Sscale x ), Real.log_le_iff_le_exp ( by positivity ) |>.1 hx₃, show 0 ≤ x * Real.exp ( - ( c₀ - ε / 2 ) * Sscale x ) by positivity ]

/-
Eventually `S(x) = √(log x)·log log x` is positive.
-/
theorem eventually_Sscale_pos : ∀ᶠ x : ℝ in atTop, 0 < Sscale x := by
  filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 1 ] ) ) ) ( Real.log_pos ( by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )

/-
**Main Theorem (Erdős Problem 768).**  One has
`lim_{x→∞} log(x / A(x)) / (√(log x) · log log x) = 1 / (2√(log 2))`.
-/
theorem erdos_768 :
    Tendsto
      (fun x : ℝ =>
        Real.log (x / (Acount x : ℝ)) / (Real.sqrt (Real.log x) * Real.log (Real.log x)))
      atTop (nhds c₀) := by
  refine' Metric.tendsto_nhds.mpr fun ε hε => _;
  filter_upwards [ Filter.eventually_gt_atTop 1, eventually_Sscale_pos, lower_bound ( ε / 2 ) ( half_pos hε ), upper_bound ( ε / 2 ) ( half_pos hε ) ] with x hx₁ hx₂ hx₃ hx₄;
  -- From the bounds, we have $(c₀ - ε/2) * Sscale x ≤ Real.log x - Real.log (Acount x) ≤ (c₀ + ε/2) * Sscale x$.
  have h_bounds : (c₀ - ε / 2) * Sscale x ≤ Real.log x - Real.log (Acount x) ∧ Real.log x - Real.log (Acount x) ≤ (c₀ + ε / 2) * Sscale x := by
    constructor <;> have := Real.log_le_log ( by positivity ) hx₃ <;> have := Real.log_le_log ( by exact Nat.cast_pos.mpr <| one_le_Acount <| by linarith ) hx₄ <;> norm_num at *; all_goals rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] at * ; linarith;
  rw [ Real.log_div ( by positivity ) ( by norm_cast; linarith [ one_le_Acount ( by linarith : ( 1 :ℝ ) ≤ x ) ] ) ];
  exact abs_lt.mpr ⟨ by rw [ show Sscale x = Real.sqrt ( Real.log x ) * Real.log ( Real.log x ) by rfl ] at *; nlinarith [ mul_div_cancel₀ ( Real.log x - Real.log ( Acount x ) ) hx₂.ne' ], by rw [ show Sscale x = Real.sqrt ( Real.log x ) * Real.log ( Real.log x ) by rfl ] at *; nlinarith [ mul_div_cancel₀ ( Real.log x - Real.log ( Acount x ) ) hx₂.ne' ] ⟩

end Erdos768
