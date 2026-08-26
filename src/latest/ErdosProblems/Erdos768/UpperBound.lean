import ErdosProblems.Erdos768.Defs
import ErdosProblems.Erdos768.Elementary
import ErdosProblems.Erdos768.Canonical

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — the sieve upper bound (Sections 6–10)

For each `n ∈ 𝒜` we choose canonical witness divisors, extract a binary
homogeneous subsequence of the prime factors by repeated majority halving, and
build a squarefree factor `Q(n)` and the deterministic compression `n ↦ n/Q(n)`.
The central reconstruction theorem bounds the fibers of this map by growing
divisor moments; combined with the weighted-prefix bound `log Q(n) ≳ W log t / t`
and the optimisation `inf_λ max(λ/2, λ/4 + 1/(4λ log 2)) = c₀`, this yields the
upper bound.

The reconstruction and compression construction are packaged in the single
existence statement `canonical_compression_exists`, whose four clauses are the
paper's Proposition 8.5 (canonical fiber bound), the squarefreeness and
`ω(Q) ≤ H_t` facts, and Proposition 9.2 (weighted-prefix lower bound).  The
theorem `Erdos768.upper_bound` in `ErdosProblems.Erdos768.Main` follows from these by the
range decomposition of `ω(n)` in Lemmas 10.2–10.3 and the optimisation.
-/

open scoped Classical BigOperators
open Finset Filter

namespace Erdos768

/-- **Propositions 8.5 & 9.2 (canonical compression and reconstruction).**  There
is a deterministic squarefree divisor map `Q : ℕ → ℕ` and an absolute constant
`C_fib` such that, for every `n ∈ 𝒜` with `ω(n) ≥ 2`:

* `Q(n)` is squarefree, divides `n`, and `ω(Q(n)) ≤ H_{ω(n)}`;
* (fiber bound) the number of `n ≤ x` in `𝒜` with `ω(n) = t` and `n/Q(n) = m`
  is at most `τ(m)^{H_t} · exp(C_fib((log(t+2))² + log(t+2)·log log(3x)))`;
* (weighted prefix) for every `η > 0` there is `T_η` such that for all
  `n ∈ 𝒜` with `ω(n) = t ≥ T_η`,
  `log Q(n) ≥ (1-η)/(2 log 2) · log(rad n) · log t / t`. -/
theorem canonical_compression_exists :
    ∃ (Cfib : ℝ) (Q : ℕ → ℕ), 0 < Cfib ∧
      (∀ n, Squarefree (Q n)) ∧
      (∀ n, n ∈ Acal → 2 ≤ omegaCount n → Q n ∣ n) ∧
      (∀ n, n ∈ Acal → 2 ≤ omegaCount n → omegaCount (Q n) ≤ Ht (omegaCount n)) ∧
      (∀ x : ℝ, 3 ≤ x → ∀ t : ℕ, 2 ≤ t → ∀ m : ℕ,
        (((Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Q n = m)).card : ℝ)
          ≤ (tauCount m : ℝ) ^ (Ht t) *
              Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
                + Real.log (t + 2) * Real.log (Real.log (3 * x))))) ∧
      (∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ n, n ∈ Acal → T ≤ omegaCount n →
        (1 - η) / (2 * Real.log 2)
            * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n)
          ≤ Real.log (Q n)) := by
  obtain ⟨Cfib, hCfib, hfiber⟩ := Erdos768Comp.canonical_fiber_bound
  exact ⟨Cfib, Erdos768Comp.Qcanon, hCfib, Erdos768Comp.Qcanon_squarefree,
    fun n hn h2 => Erdos768Comp.Qcanon_dvd n hn h2,
    fun n _ h2 => Erdos768Comp.omega_Qcanon_le n h2,
    hfiber, Erdos768Comp.weighted_prefix⟩

/-
**Irregular integers (paper eq. (10.1)).**  An integer `n ≤ x` is *irregular*
if it is far below `x` (`n ≤ x·e^{-4S}`) or has a large radical defect
(`n/rad(n) > e^{4S}`).  The number of irregular `n ≤ x` is negligible against the
target rate: for every `ε > 0`, eventually the count is `≤ x·exp(-(c₀-ε)·S(x))`.

This is the elementary removal step and follows from `radical_defect_tail`
(Lemma 2.5') together with the trivial count of integers below `x·e^{-4S}`.
-/
theorem irregular_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x)
            ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  -- By definition of $S(x)$, we know that $S(x) \to \infty$ as $x \to \infty$.
  have h_S_inf : Filter.Tendsto Sscale Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.atTop_mul_atTop₀ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop;
  -- Using the bounds from `radical_defect_tail` and the trivial count of integers below `x·e^{-4S}`, we get
  have h_bound : ∀ᶠ x in Filter.atTop, (((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x) ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ x * Real.exp (-2 * Sscale x) * (1 + Classical.choose (Erdos768.radical_defect_tail)) := by
      filter_upwards [ Filter.eventually_gt_atTop 1, h_S_inf.eventually_gt_atTop 0 ] with x hx₁ hx₂;
      have h_card_A : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x))).card : ℝ) ≤ x * Real.exp (-4 * Sscale x) := by
        refine' le_trans _ ( Nat.floor_le ( by positivity ) );
        exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun n : ℕ => ( n : ℝ ) ≤ x * Real.exp ( -4 * Sscale x ) ) ( Finset.Icc 1 ⌊x⌋₊ ) ⊆ Finset.Icc 1 ⌊x * Real.exp ( -4 * Sscale x ) ⌋₊ from fun n hn => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1, Nat.le_floor <| Finset.mem_filter.mp hn |>.2 ⟩ ) <| by simp;
      have h_card_B : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ Classical.choose (Erdos768.radical_defect_tail) * x * Real.exp (-2 * Sscale x) := by
        have := Classical.choose_spec Erdos768.radical_defect_tail;
        convert! this.2 x ( Real.exp ( 4 * Sscale x ) ) hx₁.le ( Real.one_le_exp ( by positivity ) ) using 1 ; norm_num [ Real.rpow_def_of_pos ( Real.exp_pos _ ) ] ; ring_nf;
        norm_num;
      have h_card_union : (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x) ∨ Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x * Real.exp (-4 * Sscale x))).card : ℝ) + (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))).card : ℝ) := by
        rw [Finset.filter_or]
        exact_mod_cast Finset.card_union_le _ _
      nlinarith [ Real.exp_pos ( -4 * Sscale x ), Real.exp_le_exp.mpr ( show -4 * Sscale x ≤ -2 * Sscale x by linarith ) ];
  -- Since $2 - (c₀ - ε) > 0$, we have $\exp((2 - (c₀ - ε)) * S(x)) \to \infty$ as $x \to \infty$.
  have h_exp_inf : Filter.Tendsto (fun x => Real.exp ((2 - (c₀ - ε)) * Sscale x)) Filter.atTop Filter.atTop := by
    refine' Real.tendsto_exp_atTop.comp ( Filter.Tendsto.const_mul_atTop _ h_S_inf );
    unfold c₀; nlinarith [ show Real.sqrt ( Real.log 2 ) > 1 / 2 by exact Real.lt_sqrt_of_sq_lt ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith ), Real.sqrt_nonneg ( Real.log 2 ), Real.mul_self_sqrt ( show 0 ≤ Real.log 2 by positivity ), mul_div_cancel₀ 1 ( show ( 2 * Real.sqrt ( Real.log 2 ) ) ≠ 0 by positivity ) ] ;
  filter_upwards [ h_bound, h_exp_inf.eventually_gt_atTop ( 1 + Classical.choose ( Erdos768.radical_defect_tail ) ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
  refine le_trans hx₁ ?_;
  rw [ mul_assoc ];
  exact mul_le_mul_of_nonneg_left ( by convert! mul_le_mul_of_nonneg_left hx₂.le ( Real.exp_nonneg ( -2 * Sscale x ) ) using 1 ; rw [ ← Real.exp_add ] ; ring_nf ) ( by positivity )

/-
Monotonicity of `h(t) = -t·log(t/a) + t` on `(0, a]`: for `0 < t ≤ b ≤ a`,
`h(t) ≤ h(b)`.  (The maximum of `h` is at `t = a`.)
-/
theorem neg_t_log_div_mono (a b t : ℝ) (ht : 0 < t) (htb : t ≤ b) (hba : b ≤ a) :
    -t * Real.log (t / a) + t ≤ -b * Real.log (b / a) + b := by
  by_cases h : a = 0 <;> by_cases h' : b = 0 <;> by_cases h'' : t = 0 <;> simp_all +decide [ Real.log_div ];
  · grind +revert;
  · have := Real.log_le_sub_one_of_pos ( show 0 < b / t by exact div_pos ( by linarith ) ht );
    rw [ Real.log_div ] at this <;> try linarith;
    nlinarith [ mul_div_cancel₀ b ht.ne', Real.log_le_log ( by linarith ) htb, Real.log_le_log ( by linarith ) hba ]

/-
`log log(1+log x) / log log x → 0`: the numerator is `~ log log log x`.
-/
theorem loglog_ratio_tendsto :
    Filter.Tendsto
      (fun x : ℝ => Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x))
      Filter.atTop (nhds 0) := by
  -- Let $y = \log x$, therefore the limit becomes $\lim_{y \to \infty} \frac{\log(\log(1 + y))}{\log y}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log (1 + y)) / Real.log y) Filter.atTop (nhds 0) by
    exact h_log.comp ( Real.tendsto_log_atTop );
  -- We'll use the fact that $\log(\log(1 + y)) = \log(\log y + \log(1 + 1/y))$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y + Real.log (1 + 1 / y)) / Real.log y) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ one_add_div hy.ne', Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf );
  -- We'll use the fact that $\log(\log y + \log(1 + 1/y)) = \log(\log y) + \log(1 + \frac{\log(1 + 1/y)}{\log y})$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => (Real.log (Real.log y) + Real.log (1 + Real.log (1 + 1 / y) / Real.log y)) / Real.log y) Filter.atTop (nhds 0) by
    refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with y hy using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hy ), Real.log_div ( ne_of_gt <| add_pos ( Real.log_pos hy ) <| Real.log_pos <| by norm_num; linarith ) ( ne_of_gt <| Real.log_pos hy ) ] ; ring );
  -- We'll use the fact that $\frac{\log(\log y)}{\log y} \to 0$ as $y \to \infty$.
  have h_log_log : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y) / Real.log y) Filter.atTop (nhds 0) := by
    -- Let $z = \log y$, therefore the expression becomes $\frac{\log z}{z}$.
    suffices h_log_z : Filter.Tendsto (fun z : ℝ => Real.log z / z) Filter.atTop (nhds 0) by
      exact h_log_z.comp ( Real.tendsto_log_atTop );
    -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{\log(1/w)}{1/w} = -w \log(w)$.
    suffices h_log_recip : Filter.Tendsto (fun w : ℝ => -w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
  simpa [ add_div ] using! h_log_log.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( Real.tendsto_log_atTop ) ) ) ( by norm_num ) ) ( Real.tendsto_log_atTop ) )

/-- The exponent inequality behind the ordinary tail rate: for `ℓ = log(1+log x) < t ≤ C√(log x)`,
the `omega_tail` exponent `-t·log(t/ℓ)+t` is at most `-(λ/2-ζ)·S(x)`. -/
theorem ordinary_rate_exp (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      Real.log (1 + Real.log x) < (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      -(t : ℝ) * Real.log ((t : ℝ) / Real.log (1 + Real.log x)) + (t : ℝ)
        ≤ -((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x := by
  have h_eventually : ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 ≤ Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ C ≤ Real.log (1 + Real.log x) ∧ C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) ≤ ζ * Real.log (Real.log x) := by
    have h_log_x_ge_3 : ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 ≤ Real.log x := by
      exact ⟨ Real.exp 3, fun x hx => by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.exp_pos 3 ] ⟩;
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x ≥ x₁, 1 ≤ Real.log (1 + Real.log x) := by
      exact Filter.eventually_atTop.mp ( Real.tendsto_log_atTop.comp ( tendsto_const_nhds.add_atTop ( Real.tendsto_log_atTop ) ) |> Filter.Tendsto.eventually_ge_atTop <| 1 )
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℝ, ∀ x ≥ x₂, C ≤ Real.log (1 + Real.log x) := by
      exact ⟨ Real.exp ( Real.exp C ), fun x hx => by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp C, Real.add_one_le_exp ( Real.exp C ), Real.log_exp C, Real.log_exp ( Real.exp C ), Real.log_le_log ( by positivity ) hx ] ⟩
    obtain ⟨x₃, hx₃⟩ : ∃ x₃ : ℝ, ∀ x ≥ x₃, C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) ≤ ζ * Real.log (Real.log x) := by
      have hLL : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
      have hg : Filter.Tendsto (fun x => C * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
        have h1 := loglog_ratio_tendsto.const_mul C
        have h2 : Filter.Tendsto (fun x : ℝ => C * (Real.log C - 1) / Real.log (Real.log x)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop hLL
        have h3 := h1.sub h2
        simp only [mul_zero, sub_zero] at h3
        refine h3.congr' ?_
        filter_upwards [Real.tendsto_log_atTop.comp Real.tendsto_log_atTop |>.eventually_gt_atTop 0] with x hx
        field_simp [hx.ne']
        ring
      have := hg.eventually (gt_mem_nhds hζ)
      rw [Filter.eventually_atTop] at this; rcases this with ⟨x₃, hx₃⟩
      exact ⟨max x₃ (Real.exp (Real.exp 3)), fun x hx => by
        have hxpos : Real.exp (Real.exp 3) ≤ x := le_trans (le_max_right _ _) hx
        have hLLpos : 0 < Real.log (Real.log x) := by
          have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxpos
          have h1 : Real.exp 3 ≤ Real.log x := by
            rw [Real.le_log_iff_exp_le hx0]; exact hxpos
          have h2 : (0:ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos 3) h1
          have : (3:ℝ) ≤ Real.log (Real.log x) := by
            rw [Real.le_log_iff_exp_le h2]; exact h1
          linarith
        have := hx₃ x (le_trans (le_max_left _ _) hx)
        rw [div_lt_iff₀ hLLpos] at this; linarith⟩;
    use max (max h_log_x_ge_3.choose (max x₁ x₂)) x₃
    intro x hx
    simp [] at *;
    exact ⟨ h_log_x_ge_3.choose_spec x hx.1.1, hx₁ x hx.1.2.1, hx₂ x hx.1.2.2, hx₃ x hx.2 ⟩;
  obtain ⟨ x₀, hx₀ ⟩ := h_eventually; refine Filter.eventually_atTop.mpr ⟨ x₀, fun x hx t ht₁ ht₂ ↦ ?_ ⟩ ; specialize hx₀ x hx; simp_all +decide [ Sscale ] ;
  have h_mono : -t * Real.log (t / (Real.log (1 + Real.log x) * Real.sqrt (Real.log x))) + t ≤ C * Real.sqrt (Real.log x) * (Real.log (Real.log (1 + Real.log x)) - Real.log C + 1) := by
    have := @neg_t_log_div_mono ( Real.log ( 1 + Real.log x ) * Real.sqrt ( Real.log x ) ) ( C * Real.sqrt ( Real.log x ) ) t ?_ ?_ ?_ <;> try nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ];
    convert! this using 1 ; rw [ Real.log_div ( by nlinarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by nlinarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ] ; ring_nf;
    rw [ Real.log_mul ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ), Real.log_mul ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ( by linarith [ Real.sqrt_pos.mpr ( show 0 < Real.log x by linarith ) ] ) ] ; ring;
  rw [ Real.log_div ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ] at h_mono;
  rw [ Real.log_div ( by linarith ) ( by linarith ) ];
  rw [ Real.log_mul ( by linarith ) ( by exact ne_of_gt ( Real.sqrt_pos.mpr ( by linarith ) ) ), Real.log_sqrt ( by linarith ) ] at h_mono ; ring_nf at * ; norm_num at *;
  rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by linarith ) ) ) ];
  nlinarith [ h_mono, mul_le_mul_of_nonneg_right hx₀.2.2.2 ( Real.sqrt_nonneg ( Real.log x ) ), Real.sqrt_nonneg ( Real.log x ) ]

/-
**Ordinary tail rate (paper eq. (10.4)).**  Uniformly for `t ≤ C·√(log x)`,
the number of `n ≤ x` with `ω(n) ≥ t` is at most `x·exp(-(λ/2 - ζ)·S(x))`, where
`λ = t/√(log x)`.  This follows from `omega_tail`.
-/
theorem ordinary_rate (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => (t : ℝ) ≤ (omegaCount n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x) := by
  have h_exp : ∀ᶠ x in Filter.atTop, Real.log (1 + Real.log x) / Real.sqrt (Real.log x) ≤ 2 * ζ := by
    have h_exp : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
      -- Let $y = \log x$, therefore the expression becomes $\frac{\log(1 + y)}{\sqrt{y}}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / Real.sqrt y) Filter.atTop (nhds 0) by
        exact h_log.comp ( Real.tendsto_log_atTop );
      -- We can use the fact that $\log(1 + y) \leq \log(y) + \log(2)$ for $y \geq 1$.
      have h_log_bound : ∀ y : ℝ, 1 ≤ y → Real.log (1 + y) ≤ Real.log y + Real.log 2 := by
        exact fun y hy => by rw [ ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( by linarith ) ;
      -- We can use the fact that $\frac{\log y}{\sqrt{y}}$ tends to $0$ as $y$ tends to infinity.
      have h_log_sqrt : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) := by
        -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log(z^2)}{z} = \frac{2 \log z}{z}$.
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Function.comp_apply, Real.log_sqrt hy.le ] ; ring );
        -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log(1/w)}{1/w} = -2w \log(w)$.
        suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
      refine' squeeze_zero_norm' _ _;
      use fun y => ( Real.log y + Real.log 2 ) / Real.sqrt y;
      · filter_upwards [ Filter.eventually_ge_atTop 1 ] with y hy using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.sqrt_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( h_log_bound y hy ) ( Real.sqrt_nonneg _ ) ;
      · simpa [ add_div ] using! h_log_sqrt.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.sqrt ) );
    exact h_exp.eventually ( ge_mem_nhds <| by positivity );
  filter_upwards [ h_exp, ordinary_rate_exp C ζ hC hζ, Filter.eventually_ge_atTop 3 ] with x hx₁ hx₂ hx₃ t ht;
  by_cases h_case : (t : ℝ) ≤ Real.log (1 + Real.log x);
  · refine' le_trans _ ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_exp _ ) );
    · exact le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by simpa using! Nat.floor_le <| by positivity;
    · refine' mul_nonneg _ _;
      · rw [ div_le_iff₀ ] at hx₁ <;> nlinarith [ Real.sqrt_pos.mpr ( Real.log_pos ( by linarith : 1 < x ) ), Real.mul_self_sqrt ( Real.log_nonneg ( by linarith : 1 ≤ x ) ), mul_div_cancel₀ ( t : ℝ ) ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith : 1 < x ) ) ) ) ];
      · exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) );
  · refine' le_trans ( Erdos768.omega_tail x hx₃ t ( not_le.mp h_case ) ) _;
    exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( hx₂ t ( not_le.mp h_case ) ht ) ) ( by positivity )

/-- Number of *regular* `n ≤ x` in `𝒜` with exactly `t` distinct prime factors. -/
noncomputable def NregT (x : ℝ) (t : ℕ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => SylowDivisor n ∧ omegaCount n = t
      ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
      ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))).card

/-
**Fiber reduction for the compression count.**  Eventually in `x`, for every
`t` with `δ·√(log x) ≤ t ≤ C·√(log x)`, the regular count `NregT x t` is bounded by
`E(x,t)·∑_{m ≤ x·e^{-M}, ω(m) ≥ t-H_t} τ(m)^{H_t}`, where `M = (1-η)²·log x·log t/(2t log 2)`
and `E(x,t) = exp(C_fib((log(t+2))² + log(t+2)·log log(3x)))`.
-/
set_option maxHeartbeats 1600000 in
theorem comp_fiber (C δ η : ℝ) (_hC : 0 < C) (hδ : 0 < δ) (_hδC : δ ≤ C)
    (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤
        Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
            + Real.log (t + 2) * Real.log (Real.log (3 * x))))
        * ∑ m ∈ (Finset.Icc 1 ⌊x * Real.exp
              (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊).filter
            (fun m => (t : ℝ) - Ht t ≤ (omegaCount m : ℝ)),
          (tauCount m : ℝ) ^ (Ht t) := by
  obtain ⟨Cfib, Q, hpos, hsq, hdvd, hom, hfiber, hprefix⟩ := canonical_compression_exists;
  -- Choose X₀ so that for x≥X₀: 3≤x, log x≥1, δ*√(log x) ≥ max (T:ℝ) 3, and 8*Sscale x ≤ η*log x (holds since Sscale x/log x→0).
  obtain ⟨T, hT⟩ := hprefix η hη
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x ≥ X₀, 1 ≤ Real.log x ∧ δ * Real.sqrt (Real.log x) ≥ max (T : ℝ) 3 ∧ 8 * Sscale x ≤ η * Real.log x := by
    -- Choose X₀ such that for x ≥ X₀, 8 * Sscale x ≤ η * Real.log x.
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 8 * Sscale x ≤ η * Real.log x := by
      have h_log_log : Filter.Tendsto (fun x : ℝ => 8 * Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{8 \sqrt{y} \log y}{y}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => 8 * Real.sqrt y * Real.log y / y) Filter.atTop (nhds 0) by
          exact h_log.comp ( Real.tendsto_log_atTop );
        -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{8z \log(z^2)}{z^2} = \frac{16 \log(z)}{z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => 16 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Function.comp_apply, Real.log_sqrt hy.le ] ; rw [ div_eq_div_iff ] <;> ring_nf <;> norm_num [ hy.le, hy.ne' ] );
        -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{16 \log(1/w)}{1/w} = -16w \log(w)$.
        suffices h_w : Filter.Tendsto (fun w : ℝ => -16 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 16 );
      have := h_log_log.eventually ( gt_mem_nhds <| show 0 < η by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₀, hX₀ ⟩ ; exact ⟨ Max.max X₀ 3, fun x hx => by have := hX₀ x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₀ 3 ] ) ] at this; unfold Sscale; linarith ⟩ ;
    obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, ∀ x ≥ X₁, 1 ≤ Real.log x ∧ δ * Real.sqrt (Real.log x) ≥ max (T : ℝ) 3 := by
      have h_log_growth : Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hδ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop );
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop ( Max.max ( T : ℝ ) 3 ) ) |> fun ⟨ X₁, hX₁ ⟩ ↦ ⟨ Max.max X₁ ( Real.exp 1 ), fun x hx ↦ ⟨ by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) ( show x ≥ Real.exp 1 by linarith [ le_max_right X₁ ( Real.exp 1 ) ] ) ], hX₁ x ( le_trans ( le_max_left X₁ ( Real.exp 1 ) ) hx ) ⟩ ⟩;
    exact ⟨ Max.max X₀ ( Max.max X₁ 3 ), by norm_num, fun x hx => ⟨ hX₁ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) |>.1, hX₁ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) |>.2, hX₀ x ( le_trans ( le_max_left _ _ ) hx ) ⟩ ⟩;
  refine' ⟨ Cfib, hpos, Filter.eventually_atTop.mpr ⟨ X₀, fun x hx t ht₁ ht₂ => _ ⟩ ⟩;
  -- For each $n$ in $F$, let $m = n / Q(n)$. Then $m \in TSet$.
  have h_m_in_TSet : ∀ n ∈ Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊), (n / Q n : ℕ) ∈ Finset.filter (fun m => (t : ℝ) - Ht t ≤ omegaCount m) (Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊) := by
    intro n hn
    have h_log_rad : Real.log (rad n) ≥ (1 - η) * Real.log x := by
      have h_log_rad : Real.log (rad n) ≥ Real.log n - Real.log (n / rad n) := by
        rw [ Real.log_div ] <;> norm_num;
        · linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) ];
        · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp;
      have h_log_n : Real.log n ≥ Real.log x - 4 * Sscale x := by
        have h_log_n : (n : ℝ) ≥ x * Real.exp (-4 * Sscale x) := by
          grind;
        have := Real.log_le_log ( by exact mul_pos ( by linarith ) ( Real.exp_pos _ ) ) h_log_n; rw [ Real.log_mul ( by linarith ) ( by positivity ), Real.log_exp ] at this; linarith;
      have h_log_n_div_rad : Real.log (n / rad n) ≤ 4 * Sscale x := by
        simp +zetaDelta at *;
        exact Real.log_le_iff_le_exp ( div_pos ( Nat.cast_pos.mpr hn.1.1 ) ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr ( Nat.pos_of_mem_primeFactors hp ) ) ) |>.2 hn.2.2.2.2;
      linarith [ hX₀.2 x hx ]
    have h_log_Q : Real.log (Q n) ≥ ((1 - η) ^ 2 * Real.log x * Real.log t) / (2 * t * Real.log 2) := by
      have h_log_Q : Real.log (Q n) ≥ (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log t / t := by
        simp +zetaDelta at *;
        convert! hT n hn.2.1 _ using 1;
        · rw [ hn.2.2.1 ];
        · exact hn.2.2.1.symm ▸ Nat.cast_le.mp ( le_trans ( hX₀.2 x hx |>.2.1.1 ) ht₁ );
      refine le_trans ?_ h_log_Q;
      convert! mul_le_mul_of_nonneg_right h_log_rad ( show 0 ≤ ( 1 - η ) * Real.log t / ( 2 * t * Real.log 2 ) by exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| by linarith ) <| Real.log_natCast_nonneg _ ) <| by exact mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num ) using 1 ; ring;
      ring
    have h_m_le : (n / Q n : ℕ) ≤ ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊ := by
      have h_m_le : (n : ℝ) / (Q n : ℝ) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
        have h_m_le : (n : ℝ) / (Q n : ℝ) ≤ x / Real.exp ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)) := by
          gcongr;
          · linarith;
          · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by linarith;
          · rw [ ← Real.log_le_log_iff ( by positivity ) ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
              exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using! hsq n ) ), Real.log_exp ] ; aesop;
        simpa [ Real.exp_neg ] using! h_m_le;
      exact Nat.le_floor <| Nat.cast_div_le .. |> le_trans <| h_m_le
    have h_m_ge : (t : ℝ) - Ht t ≤ omegaCount (n / Q n) := by
      have h_m_ge : omegaCount n ≤ omegaCount (Q n) + omegaCount (n / Q n) := by
        have h_m_ge : n.primeFactors ⊆ (Q n).primeFactors ∪ (n / Q n).primeFactors := by
          intro p hp; by_cases h : p ∣ Q n <;> simp_all +decide ;
          · exact Or.inl <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by specialize hsq n; aesop;
          · refine' ⟨ Nat.dvd_div_of_mul_dvd _, _, _ ⟩;
            · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.Coprime.symm <| hp.1.coprime_iff_not_dvd.mpr h ) ( hdvd n hn.2.1 <| by
                linarith [ show t ≥ 3 by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ) hp.2.1;
            · exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by specialize hsq n; aesop ) );
            · exact Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by
                                                                          linarith [ show t ≥ 3 by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ] ) );
        exact le_trans ( Finset.card_mono h_m_ge ) ( Finset.card_union_le _ _ );
      simp +zetaDelta at *;
      norm_cast at *;
      linarith [ hom n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by linarith [ show 3 ≤ omegaCount n from by linarith [ show 3 ≤ t from by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 3 : ℝ ) ≤ t ) ] ] ] ) |> le_trans <| show Ht ( omegaCount n ) ≤ Ht t from by aesop ]
    exact (by
    simp +zetaDelta at *;
    exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith [ show 2 ≤ omegaCount n from by linarith [ show 2 ≤ t from by exact_mod_cast ( by nlinarith [ hX₀.2 x hx ] : ( 2 :ℝ ) ≤ t ) ] ] ) ) ) ( Nat.pos_of_ne_zero ( by specialize hsq n; aesop ) ), h_m_le ⟩, h_m_ge ⟩);
  have h_card_F : (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊)).card ≤ ∑ m ∈ Finset.filter (fun m => (t : ℝ) - Ht t ≤ omegaCount m) (Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊), (Finset.filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Q n = m) (Finset.Icc 1 ⌊x⌋₊)).card := by
    rw [ ← Finset.card_biUnion ];
    · refine Finset.card_mono ?_;
      intro n hn; specialize h_m_in_TSet n hn; aesop;
    · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun n hn₁ hn₂ => hab <| by aesop;
  refine' le_trans ( Nat.cast_le.mpr h_card_F ) _;
  push_cast [ Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun i hi => by rw [ mul_comm ] ; exact hfiber x ( by linarith ) t ( by exact_mod_cast ( by nlinarith [ hX₀.2 x hx, Real.sqrt_nonneg ( Real.log x ), le_max_right ( T : ℝ ) 3 ] : ( 2 : ℝ ) ≤ t ) ) i;

/-
`H_t ≤ log(t+2)/(2 log 2) + 4` as reals.
-/
theorem Ht_le_real (t : ℕ) : (Ht t : ℝ) ≤ Real.log (t + 2) / (2 * Real.log 2) + 4 := by
  norm_num [ Ht ];
  linarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log ( t + 2 ) / ( 2 * Real.log 2 ) by exact div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) ]

/-
`2^{H_t} ≤ 16·√(t+2)`.
-/
theorem pow_Ht_le (t : ℕ) : (2 : ℝ) ^ (Ht t) ≤ 16 * Real.sqrt (t + 2) := by
  convert! Real.rpow_le_rpow_of_exponent_le one_le_two ( Ht_le_real t ) using 1;
  · norm_cast;
  · rw [ Real.sqrt_eq_rpow, Real.rpow_add, Real.rpow_def_of_pos ] <;> norm_num;
    · rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
      norm_num;
    · positivity

/-
`H_t / t → 0`, hence eventually `H_t < t`.
-/
theorem Ht_div_tendsto : Filter.Tendsto (fun t : ℕ => (Ht t : ℝ) / t) Filter.atTop (nhds 0) := by
  have h_squeeze : Filter.Tendsto (fun t : ℕ => (Real.log (t + 2) / (2 * Real.log 2) + 4) / (t : ℝ)) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\frac{\log(t+2)}{t}$ tends to $0$ as $t$ tends to infinity.
    have h_log : Filter.Tendsto (fun t : ℕ => Real.log (t + 2) / (t : ℝ)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $\frac{\log(t+2)}{t} = \frac{\log(t)}{t} + \frac{\log(1 + \frac{2}{t})}{t}$.
      suffices h_log : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t + (Real.log (1 + 2 / (t : ℝ)) : ℝ) / t) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ show ( t : ℝ ) + 2 = t * ( 1 + 2 / t ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring );
      -- We'll use the fact that $\frac{\log t}{t}$ tends to $0$ as $t$ tends to infinity.
      have h_log_t : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{t}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun t => 1 / (t : ℝ)) Filter.atTop) (nhds 0) by
          exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      simpa using! h_log_t.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) tendsto_inv_atTop_nhds_zero_nat );
    ring_nf at h_log ⊢;
    simpa [ mul_assoc, mul_comm, mul_left_comm ] using! Filter.Tendsto.add ( h_log.const_mul ( Real.log 2 ) ⁻¹ |> Filter.Tendsto.mul_const ( 1 / 2 : ℝ ) ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const 4 );
  refine' squeeze_zero_norm' _ h_squeeze;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( Ht_le_real t ) ( Nat.cast_nonneg _ ) ;

/-
Critical-range hypothesis (a) for `restricted_moment`: `3 ≤ x·e^{-M}`.
-/
theorem crit_hyp_X (η δ C : ℝ) (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (3 : ℝ) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
  -- To show $M \leq \frac{L}{2}$ eventually uniformly, we bound $M$ as follows:
  have h_bound : ∀ᶠ x in atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → (1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2) ≤ Real.log x / 2 := by
    -- We'll use that $\frac{\log t}{t}$ is bounded above by $\frac{\log(C \sqrt{\log x})}{\delta \sqrt{\log x}}$.
    have h_bound : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → Real.log t / t ≤ Real.log (C * Real.sqrt (Real.log x)) / (δ * Real.sqrt (Real.log x)) := by
      refine' Filter.eventually_atTop.mpr ⟨ 2, fun x hx t ht₁ ht₂ => _ ⟩;
      gcongr;
      · refine' Real.log_nonneg _;
        by_cases ht : t = 0;
        · exact absurd ht₁ ( by norm_num [ ht ] ; exact mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) );
        · exact le_trans ( mod_cast Nat.one_le_iff_ne_zero.mpr ht ) ht₂;
      · exact mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) );
      · exact lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) ) ht₁;
    -- We'll use that $\frac{\log(C \sqrt{\log x})}{\delta \sqrt{\log x}}$ tends to $0$ as $x$ tends to infinity.
    have h_lim : Filter.Tendsto (fun x => Real.log (C * Real.sqrt (Real.log x)) / (δ * Real.sqrt (Real.log x)) * (1 - η) ^ 2 / (2 * Real.log 2)) Filter.atTop (nhds 0) := by
      -- We'll use that $\frac{\log(C \sqrt{\log x})}{\sqrt{\log x}}$ tends to $0$ as $x$ tends to infinity.
      have h_lim : Filter.Tendsto (fun x => Real.log (C * Real.sqrt (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\frac{\log y}{y} \to 0$ as $y \to \infty$.
        have h_log_div_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
          -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
          suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
            exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
        have h_log_div_y : Filter.Tendsto (fun x : ℝ => Real.log (C * Real.sqrt (Real.log x)) / (C * Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
          exact h_log_div_y.comp <| Filter.Tendsto.const_mul_atTop ( by linarith ) <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using! Real.log_le_log ( by positivity ) hy ⟩;
        convert! h_log_div_y.const_mul C using 2 <;> ring_nf;
        norm_num [ mul_assoc, mul_comm C, show C ≠ 0 by linarith ];
      convert! h_lim.const_mul ( ( 1 - η ) ^ 2 / ( δ * ( 2 * Real.log 2 ) ) ) using 2 <;> ring;
    filter_upwards [ h_bound, h_lim.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
    intro t ht₁ ht₂; have := hx₁ t ht₁ ht₂; rw [ div_le_iff₀ ] at * <;> norm_num at *;
    · rw [ div_lt_iff₀ ( by positivity ) ] at hx₂;
      nlinarith [ show 0 ≤ Real.log x * t by exact mul_nonneg ( Real.log_nonneg hx₃.le ) ( Nat.cast_nonneg _ ), show 0 ≤ Real.log x * ( 1 - η ) ^ 2 by exact mul_nonneg ( Real.log_nonneg hx₃.le ) ( sq_nonneg _ ) ];
    · exact Nat.cast_pos.mp ( lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ) ) ht₁ );
    · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at ht₁; nlinarith [ Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ] ) ) ) ) ( Real.log_pos one_lt_two );
  filter_upwards [ h_bound, Filter.eventually_gt_atTop 9 ] with x hx₁ hx₂ t ht₁ ht₂ ; refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| neg_le_neg <| hx₁ t ht₁ ht₂ ) <| by positivity ) ; ring_nf ;
  rw [ show Real.log x * ( -1 / 2 ) = - ( Real.log x / 2 ) by ring, Real.exp_neg, Real.exp_half, Real.exp_log ( by positivity ) ] ; ring_nf;
  rw [ ← div_eq_mul_inv, le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ]

/-
Critical-range hypothesis (b) for `restricted_moment`: `0 < t - H_t`.
-/
theorem crit_hyp_u (δ C : ℝ) (hδ : 0 < δ) (_hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      0 < (t : ℝ) - Ht t := by
  -- From `Ht_div_tendsto` (which says `(Ht t)/t → 0`), we get `∀ᶠ t in atTop, (Ht t : ℝ) < t`: indeed `Ht_div_tendsto.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))` gives eventually `(Ht t)/t < 1`, and together with `t > 0` this gives `Ht t < t`.
  have Ht_lt_t : ∀ᶠ t : ℕ in Filter.atTop, (Ht t : ℝ) < t := by
    have h_fiber : ∀ᶠ t : ℕ in Filter.atTop, (Ht t : ℝ) / t < 1 := by
      exact Ht_div_tendsto.eventually ( gt_mem_nhds zero_lt_one );
    filter_upwards [ h_fiber, Filter.eventually_gt_atTop 0 ] with t ht ht' using by rwa [ div_lt_one ( Nat.cast_pos.mpr ht' ) ] at ht;
  -- Since `δ * Real.sqrt (Real.log x) → atTop` as `x → atTop`, there exists `x₀` such that for all `x ≥ x₀`, `δ * Real.sqrt (Real.log x) ≥ t₀`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, δ * Real.sqrt (Real.log x) ≥ Nat.find (Filter.eventually_atTop.mp Ht_lt_t) := by
    have h_sqrt_log_inf : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using! Real.log_le_log ( by positivity ) hy ⟩;
    exact Filter.eventually_atTop.mp ( h_sqrt_log_inf.eventually_ge_atTop ( Nat.find ( Filter.eventually_atTop.mp Ht_lt_t ) / δ ) ) |> fun ⟨ x₀, hx₀ ⟩ ↦ ⟨ x₀, fun x hx ↦ by nlinarith [ hx₀ x hx, mul_div_cancel₀ ( Nat.find ( Filter.eventually_atTop.mp Ht_lt_t ) : ℝ ) hδ.ne' ] ⟩;
  filter_upwards [ Filter.eventually_ge_atTop x₀ ] with x hx t ht₁ ht₂;
  exact sub_pos_of_lt ( Nat.find_spec ( Filter.eventually_atTop.mp Ht_lt_t ) t ( by exact_mod_cast ht₁.trans' ( hx₀ x hx ) ) )

/-
Critical-range hypothesis (c) for `restricted_moment`:
`2^{H_t}·log(1+log(x·e^{-M})) < t - H_t`.
-/
theorem crit_hyp_uB (η δ C : ℝ) (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp
          (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))))
        < (t : ℝ) - Ht t := by
  -- Rewrite the goal using the expressions for LHS and RHS.
  suffices h_suff : ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ t →
    t ≤ C * Real.sqrt (Real.log x) →
    16 * Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) +
    (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) + 4 <
    (δ * Real.sqrt (Real.log x)) by
      filter_upwards [ h_suff, Filter.eventually_gt_atTop 1, crit_hyp_X η δ C hδ hδC, crit_hyp_u δ C hδ hδC ] with x hx₁ hx₂ hx₃ hx₄;
      intro t ht₁ ht₂
      have h_lhs : (2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))) ) ≤ 16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x) := by
        gcongr;
        · exact Real.log_nonneg ( by linarith [ Real.log_nonneg ( show 1 ≤ x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₃ t ht₁ ht₂ ] ) ] );
        · exact_mod_cast pow_Ht_le t;
        · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg ( by linarith [ hx₃ t ht₁ ht₂ ] ) );
        · exact mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) <| Real.log_natCast_nonneg _ ) <| mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num );
      have h_rhs : (t : ℝ) - Ht t ≥ δ * Real.sqrt (Real.log x) - (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) - 4 := by
        have h_rhs : (Ht t : ℝ) ≤ Real.log (t + 2) / (2 * Real.log 2) + 4 := by
          convert! Ht_le_real t using 1;
        linarith [ show Real.log ( t + 2 ) / ( 2 * Real.log 2 ) ≤ Real.log ( C * Real.sqrt ( Real.log x ) + 2 ) / ( 2 * Real.log 2 ) by exact div_le_div_of_nonneg_right ( Real.log_le_log ( by positivity ) ( by linarith ) ) ( by positivity ) ];
      linarith [ hx₁ t ht₁ ht₂, show 16 * Real.sqrt ( t + 2 ) * Real.log ( 1 + Real.log x ) ≤ 16 * Real.sqrt ( C * Real.sqrt ( Real.log x ) + 2 ) * Real.log ( 1 + Real.log x ) by exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by linarith ) <| by positivity ) <| Real.log_nonneg <| by linarith [ Real.log_nonneg hx₂.le ] ];
  -- We'll use the fact that $\frac{\log(C\sqrt{\log x} + 2)}{\sqrt{\log x}}$ tends to $0$ as $x$ tends to infinity.
  have h_log_sqrt : Filter.Tendsto (fun x : ℝ => (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    -- We can factor out $\frac{1}{\sqrt{\log x}}$ and use the fact that $\frac{\log(C\sqrt{\log x} + 2)}{\sqrt{\log x}} \to 0$ as $x \to \infty$.
    have h_log_sqrt : Filter.Tendsto (fun x : ℝ => Real.log (C * Real.sqrt (Real.log x) + 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
      -- Let $y = \sqrt{\log x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(Cy + 2)}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log (C * y + 2) / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop );
      -- We can use the fact that $\log(Cy + 2) = \log y + \log(C + 2/y)$ and apply the properties of logarithms.
      suffices h_log : Filter.Tendsto (fun y : ℝ => (Real.log y + Real.log (C + 2 / y)) / y) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ show C * y + 2 = y * ( C + 2 / y ) by rw [ mul_add, mul_div_cancel₀ _ hy.ne' ] ; ring ] ; rw [ Real.log_mul hy.ne' ( by nlinarith [ div_mul_cancel₀ 2 hy.ne' ] ) ] );
      -- We can use the fact that $\frac{\log y}{y} \to 0$ as $y \to \infty$.
      have h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
        -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
        suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ add_div ] using! h_log_y.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( by linarith ) ) Filter.tendsto_id );
    convert! h_log_sqrt.div_const ( 2 * Real.log 2 ) using 2 <;> ring;
  -- We'll use the fact that $\frac{\sqrt{C\sqrt{\log x} + 2} \cdot \log(1 + \log x)}{\sqrt{\log x}}$ tends to $0$ as $x$ tends to infinity.
  have h_sqrt_log : Filter.Tendsto (fun x : ℝ => Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    -- We can factor out $\sqrt{\log x}$ from the numerator and denominator.
    suffices h_factor : Filter.Tendsto (fun x : ℝ => Real.sqrt (C + 2 / Real.sqrt (Real.log x)) * Real.log (1 + Real.log x) / (Real.log x) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) by
      refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
      rw [ show C * Real.sqrt ( Real.log x ) + 2 = ( C + 2 / Real.sqrt ( Real.log x ) ) * Real.sqrt ( Real.log x ) by rw [ add_mul, div_mul_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ] ; rw [ Real.sqrt_mul <| by exact add_nonneg ( by linarith ) <| div_nonneg zero_le_two <| Real.sqrt_nonneg _ ] ; ring_nf;
      norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( Real.log_nonneg hx.le ), ← Real.rpow_neg ( Real.log_nonneg hx.le ) ] ; ring_nf;
      rw [ show ( -1 / 4 : ℝ ) = -1 / 2 + 1 / 4 by norm_num, Real.rpow_add ( Real.log_pos hx ) ] ; ring;
    -- We can use the fact that $\frac{\log(1 + \log x)}{(\log x)^{1/4}}$ tends to $0$ as $x$ tends to infinity.
    have h_log : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x) / (Real.log x) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \log x$, therefore the expression becomes $\frac{\log(1 + y)}{y^{1/4}}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop );
      -- We can use the fact that $\frac{\log(1 + y)}{y^{1/4}}$ tends to $0$ as $y$ tends to infinity.
      have h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $z = \frac{1}{y^{1/4}}$, therefore the expression becomes $\frac{\log(1/z^{-4})}{z^{-1}} = -4z \log(z)$.
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => -4 * z * Real.log z) (Filter.map (fun y => 1 / y ^ (1 / 4 : ℝ)) Filter.atTop) (nhds 0) by
          refine h_log_z.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by simpa [ Real.log_rpow hy, Real.rpow_neg hy.le ] using! by ring );
        norm_num;
        exact Filter.Tendsto.comp ( by simpa [ mul_assoc ] using! Filter.Tendsto.neg ( tendsto_const_nhds.mul ( Real.continuous_mul_log.tendsto 0 ) ) ) ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) ) );
      -- We can use the fact that $\log(1 + y) = \log y + \log(1 + 1/y)$.
      have h_log_split : Filter.Tendsto (fun y : ℝ => (Real.log y + Real.log (1 + 1 / y)) / y ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using! h_log_y.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_rpow_atTop ( by norm_num ) ) );
      refine h_log_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ one_add_div hy.ne', Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf );
    simpa [ mul_div_assoc ] using! Filter.Tendsto.mul ( Filter.Tendsto.sqrt ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) ) ) ) h_log;
  have h_combined : Filter.Tendsto (fun x : ℝ => (16 * Real.sqrt (C * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) + (Real.log (C * Real.sqrt (Real.log x) + 2)) / (2 * Real.log 2) + 4) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
    simp_all +decide [ add_div, mul_assoc ];
    simpa [ mul_div_assoc ] using! Filter.Tendsto.add ( Filter.Tendsto.add ( h_sqrt_log.const_mul 16 ) h_log_sqrt ) ( tendsto_const_nhds.div_atTop ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) );
  filter_upwards [ h_combined.eventually ( gt_mem_nhds <| show 0 < δ by positivity ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
  exact fun t ht₁ ht₂ => by rwa [ div_lt_iff₀ ( Real.sqrt_pos.mpr ( Real.log_pos hx₂ ) ) ] at hx₁;

/-- The raw exponent obtained by combining `comp_fiber` with `restricted_moment`. -/
noncomputable def compExp (η : ℝ) (x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    - ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))
    - ((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) /
        ((2 : ℝ) ^ (Ht t) * Real.log (1 + Real.log (x * Real.exp
          (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))))))
    + ((t : ℝ) - Ht t)

/-
**Raw compression bound.**  Combining `comp_fiber` with `restricted_moment`
(applied to `X = x·e^{-M}`, `H = H_t`, `u = t - H_t`) gives, eventually in `x`,
`NregT x t ≤ x·exp(compExp η x t Cfib)` for `t` in the critical range.
-/
theorem compression_raw (η δ C : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (compExp η x t Cfib) := by
  obtain ⟨Cfib, hCfib, hcf⟩ := comp_fiber C δ η (lt_of_lt_of_le hδ hδC) hδ hδC hη hη4;
  refine' ⟨ Cfib, hCfib, _ ⟩;
  filter_upwards [ hcf, crit_hyp_X η δ C hδ hδC, crit_hyp_u δ C hδ hδC, crit_hyp_uB η δ C hδ hδC, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ hx₃ hx₄ hx₅;
  intro t ht₁ ht₂; specialize hx₁ t ht₁ ht₂; specialize hx₂ t ht₁ ht₂; specialize hx₃ t ht₁ ht₂; specialize hx₄ t ht₁ ht₂;
  convert! hx₁.trans ( mul_le_mul_of_nonneg_left ( restricted_moment _ hx₂ _ _ hx₃ hx₄ ) ( Real.exp_nonneg _ ) ) using 1;
  unfold compExp; ring_nf;
  norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf;
  norm_num

/-- A simplified upper bound for `compExp`, obtained by bounding the log-ratio
denominator using `2^{H_t} ≤ 16√(t+2)` and `log(1+log(x·e^{-M})) ≤ log(1+log x)`. -/
noncomputable def compExpLo (η : ℝ) (x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    - ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))
    - ((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) /
        (16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x)))
    + ((t : ℝ) - Ht t)

/-
`compExp ≤ compExpLo` eventually in the critical range.
-/
theorem compExp_le_lo (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExp η x t Cfib ≤ compExpLo η x t Cfib := by
  filter_upwards [ crit_hyp_u δ C hδ hδC, crit_hyp_X η δ C hδ hδC, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ t ht₁ ht₂;
  unfold compExp compExpLo;
  gcongr;
  any_goals linarith [ hx₁ t ht₁ ht₂ ];
  any_goals exact pow_Ht_le t;
  · exact div_pos ( hx₁ t ht₁ ht₂ ) ( mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ( Real.log_pos ( by linarith [ Real.log_pos hx₃ ] ) ) );
  · exact mul_pos ( pow_pos ( by norm_num ) _ ) ( Real.log_pos ( by linarith [ Real.log_pos ( show 1 < x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₂ t ht₁ ht₂ ] ) ] ) );
  · exact Real.log_nonneg ( by linarith [ Real.log_nonneg ( show 1 ≤ x * Real.exp ( - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ) by linarith [ hx₂ t ht₁ ht₂ ] ) ] );
  · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg ( by linarith [ hx₂ t ht₁ ht₂ ] ) );
  · exact mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) <| Real.log_natCast_nonneg _ ) <| mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num )

/-
Key elementary inequality: `t·log t − W·log W ≤ H_t·(log t + 1)` for `W = t − H_t`
with `0 < W ≤ t`.  Uses `log y ≤ y − 1`.
-/
theorem WlogW_upper (t : ℕ) (ht : (Ht t : ℝ) < t) (ht1 : 1 ≤ t) :
    (t : ℝ) * Real.log t - ((t : ℝ) - Ht t) * Real.log ((t : ℝ) - Ht t)
      ≤ (Ht t : ℝ) * (Real.log t + 1) := by
  have h_log_div : Real.log ((t : ℝ) / ((t : ℝ) - (Ht t : ℝ))) ≤ (t : ℝ) / ((t : ℝ) - (Ht t : ℝ)) - 1 := by
    exact Real.log_le_sub_one_of_pos ( div_pos ( by positivity ) ( sub_pos.mpr ht ) );
  rw [ Real.log_div ] at h_log_div <;> try linarith;
  rw [ div_sub_one, le_div_iff₀ ] at h_log_div <;> nlinarith

/-- The collected "lower-order" (o(S)) terms of the compressed exponent after the
leading cancellations. -/
noncomputable def critBracket (η x : ℝ) (t : ℕ) (Cfib : ℝ) : ℝ :=
  Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
    + ((t : ℝ) - Ht t)
    + (Ht t : ℝ) * (Real.log t + 1)
    + (t : ℝ) * (Real.log 16 + (1 / 2) * Real.log 2)
    + (t : ℝ) * Real.log (Real.log (1 + Real.log x))
    - (1 / 2) * (t : ℝ) * Real.log ((t : ℝ) / Real.sqrt (Real.log x))
    - (1 - η) ^ 2 * Real.log x * Real.log ((t : ℝ) / Real.sqrt (Real.log x))
        / (2 * (t : ℝ) * Real.log 2)

/-
Algebraic reduction: after the two exact leading cancellations,
`compExpLo` is bounded by the target's leading negatives plus `critBracket`.
-/
theorem compExpLo_le_bracket (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExpLo η x t Cfib ≤
        (-(t : ℝ) * Real.log (Real.log x) / 4
          - (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2))
        + critBracket η x t Cfib := by
  have h_eventually : ∀ᶠ x in Filter.atTop, Real.log x > 0 ∧ Real.log (1 + Real.log x) > 1 := by
    filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ using ⟨ Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ], by rw [ gt_iff_lt ] ; rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.log_exp 1, Real.log_exp ( Real.exp 1 ), Real.log_lt_log ( by positivity ) hx₁, Real.log_lt_log ( by positivity ) hx₂ ] ⟩;
  have h_eventually : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, δ * Real.sqrt (Real.log x) ≤ t → t ≤ C * Real.sqrt (Real.log x) → 2 ≤ t := by
    have h_eventually : ∀ᶠ x in Filter.atTop, δ * Real.sqrt (Real.log x) ≥ 2 := by
      have h_eventually : Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hδ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop );
      exact h_eventually.eventually_ge_atTop 2;
    filter_upwards [ h_eventually ] with x hx using fun t ht₁ ht₂ => Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;
  filter_upwards [ h_eventually, ‹∀ᶠ x in Filter.atTop, Real.log x > 0 ∧ Real.log ( 1 + Real.log x ) > 1›, crit_hyp_u δ C hδ hδC ] with x hx₁ hx₂ hx₃ t ht₁ ht₂;
  have h_step1 : -((t : ℝ) - Ht t) * Real.log (((t : ℝ) - Ht t) / (16 * Real.sqrt (t + 2) * Real.log (1 + Real.log x))) ≤ -t * Real.log t + Ht t * (Real.log t + 1) + (t : ℝ) * (Real.log 16 + (1 / 2) * Real.log (t + 2)) + (t : ℝ) * Real.log (Real.log (1 + Real.log x)) := by
    rw [ Real.log_div, Real.log_mul, Real.log_mul, Real.log_sqrt ] <;> try positivity;
    · have h_step1 : (t : ℝ) * Real.log t - ((t : ℝ) - Ht t) * Real.log ((t : ℝ) - Ht t) ≤ Ht t * (Real.log t + 1) := by
        apply WlogW_upper;
        · linarith [ hx₃ t ht₁ ht₂ ];
        · linarith [ hx₁ t ht₁ ht₂ ];
      nlinarith [ hx₃ t ht₁ ht₂, Real.log_nonneg ( show ( 16 : ℝ ) ≥ 1 by norm_num ), Real.log_nonneg ( show ( t + 2 : ℝ ) ≥ 1 by linarith ), Real.log_nonneg ( show ( Real.log ( 1 + Real.log x ) ) ≥ 1 by linarith ) ];
    · grind +splitImp;
    · linarith [ hx₃ t ht₁ ht₂ ];
    · exact ne_of_gt ( mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ( by linarith ) );
  have h_step2 : Real.log (t + 2) ≤ Real.log 2 + Real.log t := by
    rw [ ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ hx₁ t ht₁ ht₂ ];
  unfold compExpLo critBracket; ring_nf at *; norm_num at *;
  rw [ Real.log_mul, Real.log_mul, Real.log_inv, Real.log_sqrt ] at * <;> try positivity;
  · nlinarith [ show 0 < Real.log 2 by positivity, show 0 < Real.log ( 2 + t ) by exact Real.log_pos <| by linarith, show 0 < Real.log ( Real.log x + Real.log 3 ) by exact Real.log_pos <| by linarith [ show 1 < Real.log x + Real.log 3 by linarith [ show 1 < Real.log 3 by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num ] ], mul_inv_cancel₀ <| show ( t : ℝ ) ≠ 0 by norm_cast; linarith [ hx₁ t ht₁ ht₂ ] ];
  · linarith;
  · exact ne_of_gt ( Nat.cast_pos.mpr ( by linarith [ hx₁ t ht₁ ht₂ ] ) );
  · exact inv_ne_zero <| ne_of_gt <| Real.sqrt_pos.mpr hx₂.1;
  · rintro rfl; norm_num at hx₂

/-- Explicit `t`-independent upper bound for `critBracket` on the critical range. -/
noncomputable def critUpper (η δ C Cfib x : ℝ) : ℝ :=
  Cfib * ((Real.log (Real.log x)) ^ 2
      + Real.log (Real.log x) * Real.log (Real.log (3 * x)))
    + C * Real.sqrt (Real.log x)
    + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1)
    + C * Real.sqrt (Real.log x) * (Real.log 16 + (1 / 2) * Real.log 2)
    + C * Real.sqrt (Real.log x) * Real.log (Real.log (1 + Real.log x))
    + (1 / 2) * C * Real.sqrt (Real.log x) * max |Real.log δ| |Real.log C|
    + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt (Real.log x)
        / (2 * δ * Real.log 2)

/-
`critBracket ≤ critUpper` eventually, uniformly in the critical range.
-/
theorem critBracket_le_upper (η δ C Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (_hδC : δ ≤ C) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      critBracket η x t Cfib ≤ critUpper η δ C Cfib x := by
  -- Let `L := Real.log x`, `L2 := Real.log (Real.log x)`. We work eventually in `x` large enough that: `x > e^e` (so `L > 1`, `L2 > 0`), `Real.log (1 + L) ≥ 1` (so `Real.log (Real.log (1+L)) ≥ 0`), `2 ≤ t` (from `δ√L → ∞`), `C*√L + 2 ≤ L`. `crit_hyp_u` gives `0 < t - Ht t`.
  have h_eventually : ∀ᶠ x in Filter.atTop, 1 < Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ 2 ≤ δ * Real.sqrt (Real.log x) ∧ C * Real.sqrt (Real.log x) + 2 ≤ Real.log x := by
    have h_eventually : ∀ᶠ x in Filter.atTop, 1 < Real.log x ∧ 1 ≤ Real.log (1 + Real.log x) ∧ 2 ≤ δ * Real.sqrt (Real.log x) := by
      have h_eventually : Filter.Tendsto (fun x : ℝ => Real.log x) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.log x)) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun x : ℝ => δ * Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
        exact ⟨ Real.tendsto_log_atTop, Real.tendsto_log_atTop.comp <| tendsto_const_nhds.add_atTop <| Real.tendsto_log_atTop, Filter.Tendsto.const_mul_atTop hδ <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using! Real.log_le_log ( by positivity ) hy ⟩ ⟩;
      exact Filter.eventually_and.mpr ⟨ h_eventually.1.eventually_gt_atTop 1, Filter.eventually_and.mpr ⟨ h_eventually.2.1.eventually_ge_atTop 1, h_eventually.2.2.eventually_ge_atTop 2 ⟩ ⟩;
    have h_eventually : Filter.Tendsto (fun x => (C * Real.sqrt (Real.log x) + 2) / Real.log x) Filter.atTop (nhds 0) := by
      -- We can factor out $\sqrt{\log x}$ and use the fact that $\frac{1}{\sqrt{\log x}} \to 0$ as $x \to \infty$.
      have h_factor : Filter.Tendsto (fun x => (C + 2 / Real.sqrt (Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        exact le_trans ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) <| by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) <| by norm_num;
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ add_div', div_div, Real.mul_self_sqrt ( Real.log_nonneg hx.le ) ] ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos hx ] );
    filter_upwards [ h_eventually.eventually ( gt_mem_nhds zero_lt_one ), ‹∀ᶠ x in atTop, 1 < Real.log x ∧ 1 ≤ Real.log ( 1 + Real.log x ) ∧ 2 ≤ δ * Real.sqrt ( Real.log x ) ›, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using ⟨ hx₂.1, hx₂.2.1, hx₂.2.2, by rw [ div_lt_one ( Real.log_pos hx₃ ) ] at hx₁; linarith ⟩;
  filter_upwards [ h_eventually ] with x hx t ht₁ ht₂;
  refine' add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add _ _ ) _ ) _ ) _ ) _;
  refine' add_le_add _ _;
  refine' mul_le_mul_of_nonneg_left _ hCfib.le;
  any_goals nlinarith [ show 0 ≤ Real.log ( Real.log ( 1 + Real.log x ) ) by exact Real.log_nonneg hx.2.1 ];
  · refine' add_le_add _ _;
    · exact pow_le_pow_left₀ ( Real.log_nonneg ( by linarith ) ) ( Real.log_le_log ( by linarith ) ( by linarith ) ) _;
    · refine' mul_le_mul_of_nonneg_right _ ( Real.log_nonneg _ );
      · exact Real.log_le_log ( by positivity ) ( by linarith );
      · rw [ Real.log_mul ] <;> norm_num;
        · linarith [ Real.log_pos ( by norm_num : ( 3 : ℝ ) > 1 ) ];
        · rintro rfl; norm_num at hx;
  · gcongr;
    · exact add_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) ( by positivity );
    · refine' le_trans ( Ht_le_real t ) _;
      gcongr;
      linarith;
    · nlinarith [hx.2.2.1]
    · linarith;
  · exact mul_le_mul_of_nonneg_right ht₂ ( by positivity );
  · -- Since $δ ≤ t / \sqrt{\log x} ≤ C$, we have $|\log (t / \sqrt{\log x})| ≤ \max |\log δ| |\log C|$.
    have h_log_bound : |Real.log (t / Real.sqrt (Real.log x))| ≤ max |Real.log δ| |Real.log C| := by
      have h_log_bound : Real.log δ ≤ Real.log (t / Real.sqrt (Real.log x)) ∧ Real.log (t / Real.sqrt (Real.log x)) ≤ Real.log C := by
        exact ⟨ Real.log_le_log ( by positivity ) ( by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ), Real.log_le_log ( by exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ) ) ( Real.sqrt_pos.mpr ( by linarith ) ) ) ( by rw [ div_le_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ) ⟩;
      grind;
    nlinarith [ abs_le.mp h_log_bound, show ( 0 : ℝ ) ≤ t by positivity, show ( 0 : ℝ ) ≤ C * Real.sqrt ( Real.log x ) by exact mul_nonneg ( by linarith ) ( Real.sqrt_nonneg _ ) ];
  · -- Since $t / \sqrt{\log x}$ is between $\delta$ and $C$, we have $|\log(t / \sqrt{\log x})| \leq \max(|\log \delta|, |\log C|)$.
    have h_log_bound : |Real.log (t / Real.sqrt (Real.log x))| ≤ max |Real.log δ| |Real.log C| := by
      have h_log_bound : Real.log δ ≤ Real.log (t / Real.sqrt (Real.log x)) ∧ Real.log (t / Real.sqrt (Real.log x)) ≤ Real.log C := by
        exact ⟨ Real.log_le_log ( by positivity ) ( by rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ), Real.log_le_log ( by exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ] ) ) ) ( Real.sqrt_pos.mpr ( by linarith ) ) ) ( by rw [ div_le_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; linarith ) ⟩;
      grind;
    rw [ neg_div', div_le_div_iff₀ ];
    · refine' le_trans ( mul_le_mul_of_nonneg_right ( neg_le_abs _ ) ( by positivity ) ) _;
      rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ ( 1 - η ) ^ 2 ), abs_of_nonneg ( by linarith : 0 ≤ Real.log x ) ];
      refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_log_bound <| by nlinarith [ Real.log_pos one_lt_two ] ) <| by positivity ) _;
      field_simp;
      nlinarith [ show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| by positivity, show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| * δ by positivity, show 0 ≤ ( 1 - η ) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt ( Real.log x ) by positivity, Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by linarith ) ];
    · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith [ Real.sqrt_nonneg ( Real.log x ) ] ) ) ) ) ( Real.log_pos one_lt_two );
    · positivity

/-
`critUpper / S → 0` as `x → ∞`.
-/
theorem critUpper_div_S_tendsto (η δ C Cfib : ℝ) (hδ : 0 < δ) (_hδC : δ ≤ C) :
    Filter.Tendsto (fun x : ℝ => critUpper η δ C Cfib x / Sscale x)
      Filter.atTop (nhds 0) := by
  -- Let's simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun x => (Cfib * ((Real.log (Real.log x)) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) + C * Real.sqrt (Real.log x) + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) + C * Real.sqrt (Real.log x) * (Real.log 16 + (1 / 2) * Real.log 2) + C * Real.sqrt (Real.log x) * Real.log (Real.log (1 + Real.log x)) + (1 / 2) * C * Real.sqrt (Real.log x) * max |Real.log δ| |Real.log C| + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| * Real.sqrt (Real.log x) / (2 * δ * Real.log 2)) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) by
    convert! h_simp using 1;
  -- We'll use the fact that if the denominator grows much faster than the numerator, the limit will be zero. Hence, we can divide both the numerator and the denominator by $\sqrt{\log x}$.
  suffices h_div : Filter.Tendsto (fun x => (Cfib * ((Real.log (Real.log x)) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) / (Real.sqrt (Real.log x) * Real.log (Real.log x)) + C / Real.log (Real.log x) + (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) / (Real.sqrt (Real.log x) * Real.log (Real.log x)) + C * (Real.log 16 + (1 / 2) * Real.log 2) / Real.log (Real.log x) + C * Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x) + (1 / 2) * C * max |Real.log δ| |Real.log C| / Real.log (Real.log x) + (1 - η) ^ 2 * max |Real.log δ| |Real.log C| / (2 * δ * Real.log 2 * Real.log (Real.log x))) ) Filter.atTop (nhds 0) by
    refine h_div.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
    field_simp;
    rw [ ← mul_div_mul_right _ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx₁ ) ) ) ] ; ring_nf;
    grind;
  -- Each term in the sum tends to zero as $x \to \infty$.
  have h_terms : Filter.Tendsto (fun x => Cfib * (Real.log (Real.log x) ^ 2 + Real.log (Real.log x) * Real.log (Real.log (3 * x))) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => C / Real.log (Real.log x)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => (Real.log (Real.log x) / (2 * Real.log 2) + 4) * (Real.log (Real.log x) + 1) / (Real.sqrt (Real.log x) * Real.log (Real.log x))) Filter.atTop (nhds 0) := by
    refine' ⟨ _, _, _ ⟩;
    · -- We can factor out $Cfib$ and simplify the expression.
      suffices h_simp : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log (3 * x))) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        convert! h_simp.const_mul Cfib |> Filter.Tendsto.congr' _ using 2;
        · ring;
        · filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ ← mul_div_mul_right _ _ ( show Real.log ( Real.log x ) ≠ 0 from ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ) ] ; ring;
      -- We can use the fact that $\log(\log(3x)) = \log(\log x + \log 3)$ and apply the properties of logarithms.
      suffices h_log : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log x + Real.log 3)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf );
      -- We can use the fact that $\log(\log x + \log 3) = \log(\log x) + \log(1 + \frac{\log 3}{\log x})$.
      suffices h_log : Filter.Tendsto (fun x => (Real.log (Real.log x) + Real.log (Real.log x) + Real.log (1 + Real.log 3 / Real.log x)) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show Real.log x + Real.log 3 = Real.log x * ( 1 + Real.log 3 / Real.log x ) by rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt <| Real.log_pos hx ) ] ; ring, Real.log_mul ( ne_of_gt <| Real.log_pos hx ) ( ne_of_gt <| add_pos zero_lt_one <| div_pos ( Real.log_pos <| by norm_num ) <| Real.log_pos hx ) ] ; ring );
      -- We can use the fact that $\frac{\log(\log x)}{\sqrt{\log x}} \to 0$ as $x \to \infty$.
      have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{\sqrt{y}}$.
        suffices h_log_y : Filter.Tendsto (fun y => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
        suffices h_log_z : Filter.Tendsto (fun z => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
        -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
        suffices h_log_w : Filter.Tendsto (fun w => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
      simpa [ add_div ] using! Filter.Tendsto.add ( Filter.Tendsto.add h_log_log h_log_log ) ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ) ( by norm_num ) ) ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) );
    · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
    · -- We can factor out $\frac{1}{\sqrt{\log x}}$ and use the fact that $\frac{\log \log x}{\sqrt{\log x}} \to 0$ as $x \to \infty$.
      have h_factor : Filter.Tendsto (fun x => (Real.log (Real.log x) + 4 * 2 * Real.log 2) / (2 * Real.log 2 * Real.sqrt (Real.log x))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => (Real.log (Real.log x) + 1) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
        constructor;
        · -- We can use the fact that $\frac{\log \log x}{\sqrt{\log x}} \to 0$ as $x \to \infty$.
          have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{\sqrt{y}}$.
            suffices h_log_y : Filter.Tendsto (fun y => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
            suffices h_log_z : Filter.Tendsto (fun z => 2 * Real.log z / z) Filter.atTop (nhds 0) by
              have := h_log_z.comp ( show Filter.Tendsto ( fun y => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
            -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
            suffices h_log_w : Filter.Tendsto (fun w => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
              exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
          convert! h_log_log.div_const ( 2 * Real.log 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun x : ℝ => ( 4 * 2 * Real.log 2 ) / ( 2 * Real.log 2 * Real.sqrt ( Real.log x ) ) ) Filter.atTop ( nhds 0 ) from ?_ using 2 <;> ring_nf;
          simpa using! Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) ( tendsto_inv_atTop_zero.sqrt.comp ( Real.tendsto_log_atTop ) ) ) tendsto_const_nhds;
        · ring_nf;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ) ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) ( by norm_num );
      convert! h_factor.1.mul h_factor.2 using 2 <;> ring_nf;
      norm_num ; ring;
  have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
    grind +suggestions;
  have h_log_log : Filter.Tendsto (fun x => C * Real.log (Real.log (1 + Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
    simpa [ mul_div_assoc ] using! h_log_log.const_mul C;
  convert! Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add h_terms.1 h_terms.2.1 ) h_terms.2.2 ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) h_log_log ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) ( tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop ( show 0 < 2 * δ * Real.log 2 by positivity ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) using 2 ; ring

/-- The lower-order terms are `≤ ζ·S` eventually, uniformly in the critical range. -/
theorem critBracket_le (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      critBracket η x t Cfib ≤ ζ * Sscale x := by
  have hStendsto : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hSpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Sscale x := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
      hStendsto.eventually_gt_atTop 0] with x hx hxL
    have hxpos : (1 : ℝ) < x := lt_trans (by nlinarith [Real.exp_pos 1, Real.add_one_le_exp 1]) hx
    have : 0 < Real.log x := Real.log_pos hxpos
    exact mul_pos (Real.sqrt_pos.mpr this) hxL
  filter_upwards [critBracket_le_upper η δ C Cfib hη hη4 hδ hδC hCfib,
    (critUpper_div_S_tendsto η δ C Cfib hδ hδC).eventually (gt_mem_nhds hζ),
    hSpos] with x hub hlim hSp t ht1 ht2
  refine (hub t ht1 ht2).trans ?_
  rw [div_lt_iff₀ hSp] at hlim
  linarith [hlim]

/-- The uniform asymptotic bound on the simplified exponent `compExpLo`. -/
theorem compExpLo_bound (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExpLo η x t Cfib ≤ -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x := by
  have hC : 0 < C := lt_of_lt_of_le hδ hδC
  filter_upwards [compExpLo_le_bracket η δ C Cfib hη hη4 hδ hδC,
    critBracket_le η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib,
    Filter.eventually_gt_atTop (Real.exp 1)] with x h1 h2 hx t ht1 ht2
  have hxpos : (1 : ℝ) < x := lt_trans (by nlinarith [Real.exp_pos 1, Real.add_one_le_exp 1]) hx
  have hLpos : 0 < Real.log x := Real.log_pos hxpos
  have hpos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have htpos : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by positivity) ht1
  have hs : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt hpos
  have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hLpos.le
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  refine (h1 t ht1 ht2).trans ?_
  have e1 : ((t : ℝ) / Real.sqrt (Real.log x)) / 4 * Sscale x
        = (t : ℝ) * Real.log (Real.log x) / 4 := by
    unfold Sscale; field_simp
  have e2 : (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) * Sscale x
        = (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2) := by
    unfold Sscale
    have hstep : (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2)
          * (Real.sqrt (Real.log x) * Real.log (Real.log x))
        = (1 - η) ^ 2 * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) * Real.log (Real.log x)
          / (4 * (t : ℝ) * Real.log 2) := by
      field_simp
    rw [hstep, hsq]
  have hRHS : -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x
        = (-(t : ℝ) * Real.log (Real.log x) / 4
          - (1 - η) ^ 2 * Real.log x * Real.log (Real.log x) / (4 * (t : ℝ) * Real.log 2))
          + ζ * Sscale x := by
    have expand : -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x
        = -(((t : ℝ) / Real.sqrt (Real.log x)) / 4 * Sscale x)
          - ((1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) * Sscale x)
          + ζ * Sscale x := by ring
    rw [expand, e1, e2]; ring
  rw [hRHS]
  have := h2 t ht1 ht2
  linarith [this]

/-- **Compression exponent bound (the uniform asymptotics of paper eq. (10.6)).**
For `Cfib > 0`, eventually in `x`, uniformly for `t` in the critical range,
`compExp η x t Cfib ≤ -(λ/4 + (1-η)²/(4λ log 2) - ζ)·S` where `λ = t/√L`. -/
theorem compression_exp_bound (η δ C ζ Cfib : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) (hCfib : 0 < Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      compExp η x t Cfib ≤ -(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x := by
  filter_upwards [compExp_le_lo η δ C Cfib hη hη4 hδ hδC,
    compExpLo_bound η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib] with x h1 h2 t ht1 ht2
  exact (h1 t ht1 ht2).trans (h2 t ht1 ht2)

theorem compression_rate (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-(((t : ℝ) / Real.sqrt (Real.log x)) / 4
          + (1 - η) ^ 2 / (4 * ((t : ℝ) / Real.sqrt (Real.log x)) * Real.log 2) - ζ)
          * Sscale x) := by
  obtain ⟨Cfib, hCfib, hraw⟩ := compression_raw η δ C hη hη4 hδ hδC
  filter_upwards [hraw, compression_exp_bound η δ C ζ Cfib hη hη4 hδ hδC hζ hCfib,
    Filter.eventually_gt_atTop 0] with x hx hexp hx0 t ht1 ht2
  refine (hx t ht1 ht2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.exp_le_exp.mpr (hexp t ht1 ht2)

/-
Optimisation lower bound with the `(1-η)` factor:
`(1-η)·c₀ ≤ max(λ/2, λ/4 + (1-η)²/(4λ log 2))`.
-/
theorem opt_lower_eta (η lam : ℝ) (hη : η < 1) (hlam : 0 < lam) :
    (1 - η) * c₀ ≤ max (lam / 2) (lam / 4 + (1 - η) ^ 2 / (4 * lam * Real.log 2)) := by
  convert! mul_le_mul_of_nonneg_left ( opt_lower ( lam / ( 1 - η ) ) ( by exact div_pos hlam ( sub_pos.mpr hη ) ) ) ( sub_nonneg.mpr hη.le ) using 1;
  rw [ mul_max_of_nonneg _ _ ( by linarith ) ];
  grind

/-
**Critical range per-`t` bound.**  For `δ√L ≤ t ≤ C√L`, taking the better of the
ordinary tail and the compression bound and optimising gives
`NregT x t ≤ x·exp(-((1-η)c₀ - ζ)S)`.
-/
theorem critical_per_t_bound (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
  -- Use `compression_rate` and `ordinary_rate` to bound `NregT x t`.
  have h₁ : ∀ᶠ x in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
    (NregT x t : ℝ) ≤ x * Real.exp (-((t / Real.sqrt (Real.log x)) / 2 - ζ) * Sscale x) := by
      filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ), ordinary_rate C ζ ( lt_of_lt_of_le hδ hδC ) hζ ] with x hx₁ hx₂ t ht₁ ht₂;
      refine' le_trans _ ( hx₂ t ht₂ );
      refine' Nat.cast_le.mpr ( Finset.card_mono _ );
      intro n hn; aesop;
  generalize_proofs at *; (
  have h₂ : ∀ᶠ x in Filter.atTop, ∀ t : ℕ,
    δ * Real.sqrt (Real.log x) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
    (NregT x t : ℝ) ≤ x * Real.exp (-((t / Real.sqrt (Real.log x)) / 4 + (1 - η) ^ 2 / (4 * (t / Real.sqrt (Real.log x)) * Real.log 2) - ζ) * Sscale x) := by
      exact compression_rate η δ C ζ hη hη4 hδ hδC hζ
  generalize_proofs at *; (
  filter_upwards [ h₁, h₂, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ hx₄ t ht₁ ht₂
  have h₃ : Sscale x ≥ 0 := by
    exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) )
  generalize_proofs at *; (
  have h₄ : (1 - η) * c₀ ≤ max ((t / Real.sqrt (Real.log x)) / 2) ((t / Real.sqrt (Real.log x)) / 4 + (1 - η) ^ 2 / (4 * (t / Real.sqrt (Real.log x)) * Real.log 2)) := by
    apply opt_lower_eta η (t / Real.sqrt (Real.log x)) (by linarith) (by
    exact div_pos ( lt_of_lt_of_le ( mul_pos hδ ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ) ) ht₁ ) ( Real.sqrt_pos.mpr ( Real.log_pos hx₃ ) ))
  generalize_proofs at *; (
  cases max_cases ( ( t : ℝ ) / Real.sqrt ( Real.log x ) / 2 ) ( ( t : ℝ ) / Real.sqrt ( Real.log x ) / 4 + ( 1 - η ) ^ 2 / ( 4 * ( t / Real.sqrt ( Real.log x ) ) * Real.log 2 ) ) <;> simp_all +decide only [mul_assoc];
  · exact le_trans ( hx₁ t ht₁ ht₂ ) ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) <| by linarith );
  · exact le_trans ( hx₂ t ht₁ ht₂ ) ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) <| by linarith )))))

/-
**High-`ω` tail.**  The number of `n ≤ x` with `ω(n) > C√L` is
`≤ x·exp(-(C/2 - ζ)S)`.
-/
theorem high_tail_bound (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ))).card : ℝ)
        ≤ x * Real.exp (-(C / 2 - ζ) * Sscale x) := by
  have h_ordinary_rate : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, (t : ℝ) ≤ (C + 1) * Real.sqrt (Real.log x) → (((Finset.Icc 1 ⌊x⌋₊).filter (fun n => (t : ℝ) ≤ (omegaCount n : ℝ))).card : ℝ) ≤ x * Real.exp (-((t : ℝ) / Real.sqrt (Real.log x) / 2 - ζ) * Sscale x) := by
    exact Erdos768.ordinary_rate ( C + 1 ) ζ ( by linarith ) hζ;
  filter_upwards [ h_ordinary_rate, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
  refine le_trans ?_ ( le_trans ( hx₁ ( Nat.floor ( C * Real.sqrt ( Real.log x ) ) + 1 ) ?_ ) ?_ );
  · norm_num +zetaDelta at *;
    exact Finset.card_mono fun n hn => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hn |>.1, by exact_mod_cast Nat.succ_le_of_lt <| Nat.floor_lt ( by positivity ) |>.2 <| Finset.mem_filter.mp hn |>.2 ⟩;
  · norm_num;
    nlinarith [ Nat.floor_le ( show 0 ≤ C * Real.sqrt ( Real.log x ) by positivity ), Real.sqrt_nonneg ( Real.log x ), Real.mul_self_sqrt ( show 0 ≤ Real.log x by exact Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ), Real.log_exp 1, Real.log_lt_log ( by positivity ) hx₂ ];
  · gcongr;
    · linarith [ Real.exp_pos 1 ];
    · exact mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos 1 ] ) ] ; linarith [ Real.add_one_le_exp 1 ] ) );
    · rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Real.log_pos ( lt_trans ( by norm_num ) hx₂ ) ) ) ] ; push_cast ; linarith [ Nat.lt_floor_add_one ( C * Real.sqrt ( Real.log x ) ) ]

/-
`NregT x 0 ≤ 1` (only `n = 1` has `ω(n) = 0`).
-/
theorem Nreg_zero_le (x : ℝ) : (NregT x 0 : ℝ) ≤ 1 := by
  refine' mod_cast _;
  refine' Finset.card_le_one.mpr _;
  unfold omegaCount; aesop;

/-
`NregT x 1 = 0` (prime powers are not Sylow-divisor numbers).
-/
theorem Nreg_one_eq_zero (x : ℝ) : NregT x 1 = 0 := by
  refine' Finset.card_eq_zero.mpr ( Finset.filter_eq_empty_iff.mpr _ );
  intro n hn; rintro ⟨ h₁, h₂, h₃, h₄ ⟩ ;
  -- Since `omegaCount n = 1`, `n` is a prime power: `n = p^k` for some prime `p` and `k ≥ 1`.
  obtain ⟨p, k, hp, hk⟩ : ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧ n = p^k := by
    obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ n.primeFactors = {p} := by
      exact Exists.elim ( Finset.card_eq_one.mp h₂ ) fun p hp => ⟨ p, Nat.prime_of_mem_primeFactors ( hp.symm ▸ Finset.mem_singleton_self _ ), Nat.dvd_of_mem_primeFactors ( hp.symm ▸ Finset.mem_singleton_self _ ), hp ⟩;
    exact ⟨ p, n.factorization p, hp.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hn ] : n ≠ 0 ) ] ; rw [ Finsupp.prod ] ; aesop ⟩;
  specialize h₁ p hp ; simp_all +decide [ Nat.dvd_prime_pow ];
  exact absurd ( h₁ ( Or.inl ( ne_bot_of_gt hk.1 ) ) ) ( by rintro ⟨ m, hm₁, hm₂, hm₃ ⟩ ; rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.pow_succ' ] )

/-
**One-prime fiber bound (Lemma 6.x).**  For a fixed `m`, the number of
Sylow-divisor `n ≤ x` of the form `n = p·m` with `p` prime the largest prime
factor is `≤ τ(m)·(1 + log₂ x)`.
-/
theorem one_prime_fiber (x : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    (((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => SylowDivisor n ∧ (∃ p : ℕ, p.Prime ∧ n = p * m ∧
          ∀ q ∈ n.primeFactors, q ≤ p))).card : ℝ)
      ≤ (tauCount m : ℝ) * (1 + Real.logb 2 x) := by
  revert m;
  by_contra h_contra;
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, Nat.Prime p ∧ n = p * m ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)).card > (tauCount m : ℝ) * (1 + Real.logb 2 x) := by
    exact by push_neg at h_contra; exact h_contra;
  -- Let F be the filtered set. We build an injection from F into pairs `(D, p)` with `D ∈ m.divisors` and `p ∈ (D-1).primeFactors`, then bound the count.
  set F := Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, Nat.Prime p ∧ n = p * m ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)
  have hF_card : F.card ≤ (Finset.biUnion (Nat.divisors m) (fun D => Nat.primeFactors (D - 1))).card := by
    have hF_card : ∀ n ∈ F, ∃ D ∈ Nat.divisors m, ∃ p ∈ Nat.primeFactors (D - 1), n = p * m := by
      intro n hn
      obtain ⟨hn_sylow, p, hp_prime, hn_eq, hp_max⟩ := (Finset.mem_filter.mp hn).right
      obtain ⟨D, hD_div, hD_gt1, hD_mod⟩ : ∃ D ∈ Nat.divisors n, 1 < D ∧ D % p = 1 := by
        have := hn_sylow p hp_prime ( hn_eq.symm ▸ dvd_mul_right _ _ ) ; aesop;
      -- Since $D \mid n$ and $n = p * m$, we have $D \mid p * m$. Given that $p$ is prime and $D \equiv 1 \pmod{p}$, it follows that $D \mid m$.
      have hD_div_m : D ∣ m := by
        have hD_div_m : D ∣ p * m := by
          grind +splitIndPred;
        refine' Nat.Coprime.dvd_of_dvd_mul_left _ hD_div_m;
        exact Nat.Coprime.symm ( hp_prime.coprime_iff_not_dvd.mpr fun h => by have := Nat.mod_eq_zero_of_dvd h; aesop );
      use D, by
        exact Nat.mem_divisors.mpr ⟨ hD_div_m, by aesop_cat ⟩, p, by
        simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
        exact ⟨ by rw [ ← Nat.mod_add_div D p, hD_mod ] ; norm_num [ hp_prime.ne_one ], Nat.sub_ne_zero_of_lt hD_gt1 ⟩;
    have hF_card : F ⊆ Finset.image (fun p => p * m) (Finset.biUnion (Nat.divisors m) (fun D => Nat.primeFactors (D - 1))) := by
      intro n hn; obtain ⟨ D, hD₁, p, hp₁, rfl ⟩ := hF_card n hn; exact Finset.mem_image.mpr ⟨ p, Finset.mem_biUnion.mpr ⟨ D, hD₁, hp₁ ⟩, rfl ⟩ ;
    exact le_trans ( Finset.card_le_card hF_card ) ( Finset.card_image_le );
  -- Bound each `(D-1).primeFactors.card = ω(D-1) ≤ 1 + Real.logb 2 x`: for `D ∈ m.divisors`, `D ∣ m` so `D ≤ m ≤ n ≤ x`... more directly `D - 1 < D ≤ x`, and `ω(k) ≤ Real.logb 2 k ≤ Real.logb 2 x` for `1 ≤ k` (since `2^{ω(k)} ≤ k`); include `+1` slack.
  have h_bound : ∀ D ∈ Nat.divisors m, (Nat.primeFactors (D - 1)).card ≤ 1 + Real.logb 2 x := by
    intro D hD
    have hD_le_x : D - 1 ≤ x := by
      by_cases hm : m = 0 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      by_cases hF_empty : F = ∅ <;> simp_all +decide [ Finset.ext_iff ];
      · exact False.elim <| absurd ‹ ( tauCount m : ℝ ) * ( 1 + Real.logb 2 x ) < 0 › <| not_lt_of_ge <| mul_nonneg ( Nat.cast_nonneg _ ) <| add_nonneg zero_le_one <| Real.logb_nonneg ( by norm_num ) <| by linarith;
      · obtain ⟨ n, hn ⟩ := hF_empty; simp_all +decide [ F ] ;
        exact le_trans ( Nat.cast_le.mpr ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm ) ( Nat.dvd_of_mod_eq_zero hD ) ) ) ( by nlinarith [ Nat.floor_le ( show 0 ≤ x by positivity ), show ( n : ℝ ) ≤ ⌊x⌋₊ by exact_mod_cast hn.1.2, show ( n : ℝ ) ≥ 1 by exact_mod_cast hn.1.1, show ( m : ℝ ) ≤ n by exact_mod_cast hn.2.2.choose_spec.2.1.symm ▸ Nat.le_mul_of_pos_left _ hn.2.2.choose_spec.1.pos ] );
    rcases D with ( _ | _ | D ) <;> norm_num at *;
    · exact add_nonneg zero_le_one ( Real.logb_nonneg ( by norm_num ) hx );
    · have h_prime_factors_card : (Nat.primeFactors (D + 1)).card ≤ Real.logb 2 (D + 1) := by
        rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast <;> try linarith;
        exact Nat.le_trans ( by simpa using! Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) <| Nat.le_of_dvd ( Nat.succ_pos _ ) <| Nat.prod_primeFactors_dvd _;
      exact le_trans h_prime_factors_card ( by linarith [ show Real.logb 2 ( D + 1 ) ≤ Real.logb 2 x from by gcongr ; linarith ] );
  -- Therefore, `F.card ≤ τ(m) * (1 + Real.logb 2 x)`.
  have h_final_bound : F.card ≤ (Nat.divisors m).card * (1 + Real.logb 2 x) := by
    refine' le_trans ( Nat.cast_le.mpr hF_card ) _;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    simpa using! Finset.sum_le_sum h_bound |> le_trans <| by simp +decide [ mul_add ] ;
  exact (not_le_of_gt hm) h_final_bound

/-
**Small-`ω` bound.**  For fixed `2 ≤ t < T`, `NregT x t ≤ x·exp(-(c₀+1)S)`
eventually (a power saving `x^{1-1/t+o(1)}`).
-/
theorem small_t_bound (t : ℕ) (ht2 : 2 ≤ t) :
    ∀ᶠ x : ℝ in Filter.atTop, (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) := by
  -- For x ≥ 1, X_t(x) ≥ 0, so ⌊X_t(x)⌋₊ ∈ ℕ. Let X_t(x) := x * Real.exp (-(L - 8*S)/t). Then NregT x t ≤ ∑_{mm ∈ Finset.Icc 1 ⌊X_t(x)⌋₊} τ(mm)*(1 + Real.logb 2 x).
  have h_bound : ∀ᶠ x in Filter.atTop, ((NregT x t : ℝ) ≤
      (1 + Real.logb 2 x) * ∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (tauCount mm : ℝ)) := by
        refine' Filter.eventually_atTop.mpr ⟨ 3, fun x hx => _ ⟩;
        -- For each `n` in the `NregT x t` set, let `p := n.primeFactors.max' (nonempty since t = ω n ≥ 2 > 0)` and `mm := n / p`.
        have h_fiber : ∀ n ∈ Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊), ∃ p mm : ℕ, p.Prime ∧ n = p * mm ∧ mm ≤ ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊ ∧ (∀ q ∈ n.primeFactors, q ≤ p) := by
          intro n hn
          obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q ≤ p := by
            have h_prime_factors : n.primeFactors.Nonempty := by
              simp +zetaDelta at *;
              contrapose! hn; interval_cases n <;> simp_all +decide ;
              unfold omegaCount; aesop;
            exact ⟨ Finset.max' _ h_prime_factors, Nat.prime_of_mem_primeFactors <| Finset.max'_mem _ h_prime_factors, Finset.max'_mem _ h_prime_factors, fun q hq => Finset.le_max' _ _ hq ⟩;
          refine' ⟨ p, n / p, hp_prime, Eq.symm ( Nat.mul_div_cancel' <| Nat.dvd_of_mem_primeFactors hp_div.1 ), _, hp_div.2 ⟩;
          -- Since $p \geq (\text{rad } n)^{1/t}$, we have $p \geq (x e^{-8S})^{1/t}$.
          have hp_ge : (p : ℝ) ≥ (x * Real.exp (-8 * Sscale x)) ^ (1 / t : ℝ) := by
            have hp_ge : (p : ℝ) ≥ (rad n) ^ (1 / t : ℝ) := by
              have hp_ge_rad : (rad n : ℝ) ≤ p ^ t := by
                have hp_ge_rad : (rad n : ℝ) ≤ ∏ q ∈ n.primeFactors, p := by
                  exact_mod_cast Finset.prod_le_prod' fun q hq => hp_div.2 q hq;
                simp_all +decide [ omegaCount ];
              exact le_trans ( Real.rpow_le_rpow ( Nat.cast_nonneg _ ) hp_ge_rad ( by positivity ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] );
            refine le_trans ?_ hp_ge;
            gcongr;
            have h_rad_ge : (rad n : ℝ) ≥ n * Real.exp (-4 * Sscale x) := by
              simp +zetaDelta at *;
              rw [ div_le_iff₀ ( Finset.prod_pos fun q hq => Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hq ) ] at hn ; rw [ Real.exp_neg ] at * ; nlinarith [ Real.exp_pos ( 4 * Sscale x ), mul_inv_cancel₀ ( ne_of_gt <| Real.exp_pos ( 4 * Sscale x ) ) ];
            refine le_trans ?_ h_rad_ge;
            refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( n : ℝ ) ≥ x * Real.exp ( -4 * Sscale x ) from _ ) ( Real.exp_nonneg _ ) );
            · rw [ mul_assoc, ← Real.exp_add ] ; ring_nf ; norm_num;
            · grind;
          -- Since $n \leq x$, we have $n / p \leq x / p$.
          have h_div_le : (n : ℝ) / p ≤ x / (x * Real.exp (-8 * Sscale x)) ^ (1 / t : ℝ) := by
            gcongr;
            exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
          refine Nat.le_floor ?_;
          convert! h_div_le.trans _ using 1;
          · rw [ Nat.cast_div ( Nat.dvd_of_mem_primeFactors hp_div.1 ) ( Nat.cast_ne_zero.mpr hp_prime.ne_zero ) ];
          · rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
            rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; ring_nf;
            rw [ ← Real.exp_neg ] ; ring_nf ; norm_num;
        -- By `Finset.card_le_sum_card_fiberwise`, we can bound the cardinality of the set by the sum of the cardinalities of the fibers.
        have h_card_le_sum : (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊)).card ≤ ∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, p.Prime ∧ n = p * mm ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)).card := by
          have h_card_le_sum : Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬(n ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) (Finset.Icc 1 ⌊x⌋₊) ⊆ Finset.biUnion (Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊) (fun mm => Finset.filter (fun n => SylowDivisor n ∧ ∃ p : ℕ, p.Prime ∧ n = p * mm ∧ ∀ q ∈ n.primeFactors, q ≤ p) (Finset.Icc 1 ⌊x⌋₊)) := by
            intro n hn; specialize h_fiber n hn; simp_all +decide ;
            rcases h_fiber with ⟨ p, hp, a, rfl, ha, h ⟩ ; exact ⟨ a, ⟨ Nat.pos_of_ne_zero ( by aesop_cat ), ha ⟩, p, hp, rfl, h ⟩ ;
          exact le_trans ( Finset.card_le_card h_card_le_sum ) ( Finset.card_biUnion_le );
        refine' le_trans ( Nat.cast_le.mpr h_card_le_sum ) _;
        rw [ Nat.cast_sum, Finset.mul_sum _ _ _ ];
        apply Finset.sum_le_sum
        intro m hm
        simpa only [mul_comm] using! one_prime_fiber x (by linarith) m
  -- Now `τ(mm) = dk 2 mm` (divisors = ordered pairs), and by `dk_sum_le X_t (…) 2 (…)`, `∑_{mm ≤ ⌊X_t⌋₊} dk 2 mm ≤ X_t*(1 + Real.log X_t)`.
  have h_sum_bound : ∀ᶠ x in Filter.atTop, ((NregT x t : ℝ) ≤
      (1 + Real.logb 2 x) * (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ) := by
        have h_sum_bound : ∀ᶠ x in Filter.atTop, (∑ mm ∈ Finset.Icc 1 ⌊x * Real.exp (-(Real.log x - 8 * Sscale x) / t)⌋₊, (tauCount mm : ℝ)) ≤
            (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) := by
              have h_sum_bound : ∀ X : ℝ, 1 ≤ X → ∑ mm ∈ Finset.Icc 1 ⌊X⌋₊, (tauCount mm : ℝ) ≤ X * (1 + Real.log X) := by
                intro X hX;
                convert! dk_sum_le X hX 2 ( by norm_num ) using 1;
                · refine' Finset.sum_congr rfl fun n hn => _;
                  refine' congr_arg _ ( Finset.card_bij ( fun x hx => fun i => if i = 0 then x else n / x ) _ _ _ ) <;> simp +decide;
                  · exact fun a ha hn => ⟨ ⟨ ⟨ ha, hn ⟩, Nat.div_dvd_of_dvd ha, hn ⟩, Nat.mul_div_cancel' ha ⟩;
                  · intro a₁ ha₁ hn a₂ ha₂ hn' h; have := congr_fun h 0; have := congr_fun h 1; aesop;
                  · intro b hb₁ hb₂ hb₃ hb₄ hb₅; use b 0; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
                    rw [ Nat.div_eq_of_eq_mul_left ] <;> nlinarith [ Nat.pos_of_dvd_of_pos hb₁ hn.1 ];
                · norm_num;
              have h_exp_bound : Filter.Tendsto (fun x => x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) Filter.atTop Filter.atTop := by
                -- We can simplify the expression inside the exponential further by noting that $Sscale x = \sqrt{\log x} \log \log x$.
                have h_simplify'' : Filter.Tendsto (fun x => Real.exp (-(Real.log x - 8 * Real.sqrt (Real.log x) * Real.log (Real.log x)) / t + Real.log x)) Filter.atTop Filter.atTop := by
                  refine' Real.tendsto_exp_atTop.comp _;
                  have h_simplify'' : Filter.Tendsto (fun x => (8 * Real.sqrt (Real.log x) * Real.log (Real.log x)) / t + (1 - 1 / t) * Real.log x) Filter.atTop Filter.atTop := by
                    have h_simplify'' : Filter.Tendsto (fun x => (1 - 1 / t) * Real.log x) Filter.atTop Filter.atTop := by
                      exact Filter.Tendsto.const_mul_atTop ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) <| Real.tendsto_log_atTop;
                    refine' Filter.tendsto_atTop_mono' _ _ h_simplify'';
                    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using le_add_of_nonneg_left <| div_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) <| Real.sqrt_nonneg _ ) <| Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; linarith [ Real.add_one_le_exp 1 ] ) <| by positivity;
                  convert! h_simplify'' using 2 ; ring;
                refine h_simplify''.congr' ?_;
                filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show Sscale x = Real.sqrt ( Real.log x ) * Real.log ( Real.log x ) by rfl ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ] ; ring_nf;
              filter_upwards [ h_exp_bound.eventually_ge_atTop 1 ] with x hx using h_sum_bound _ hx;
        filter_upwards [ h_bound, h_sum_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using le_trans hx₁ <| by simpa only [ mul_assoc ] using! mul_le_mul_of_nonneg_left hx₂ <| add_nonneg zero_le_one <| Real.logb_nonneg one_lt_two <| by linarith;
  -- It remains to show `4L² * exp(-(L - 8S)/t) ≤ exp(-(c₀+1)*S)` eventually.
  have h_exp_bound : Filter.Tendsto (fun x => Real.log (4 * (Real.log x) ^ 2) + (c₀ + 1) * Sscale x - (Real.log x - 8 * Sscale x) / t) Filter.atTop Filter.atBot := by
    -- We'll use the fact that $Sscale x = \sqrt{\log x} \log \log x$ grows slower than $\log x$.
    have h_Sscale_growth : Filter.Tendsto (fun x => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) by
        exact h_simplify;
      -- Let $y = \log x$, therefore the expression becomes $\frac{\sqrt{y} \log y}{y} = \frac{\log y}{\sqrt{y}}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
        have := h_log_y.comp ( Real.tendsto_log_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Function.comp_apply, div_eq_mul_inv ] ; rw [ ← Real.sqrt_div_self ] ; ring );
      -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
        have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
      -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
      suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
        exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
    -- We can factor out $Real.log x$ from the expression.
    suffices h_factor : Filter.Tendsto (fun x => Real.log x * (Real.log (4 * (Real.log x) ^ 2) / Real.log x + (c₀ + 1) * (Sscale x / Real.log x) - (1 - 8 * (Sscale x / Real.log x)) / t)) Filter.atTop Filter.atBot by
      refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
      field_simp;
      rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hx ) ) ] ; ring_nf;
      simpa [ mul_comm, ne_of_gt ( Real.log_pos hx ) ] using! by ring;
    -- We'll use the fact that $Real.log (4 * (Real.log x) ^ 2) / Real.log x$ tends to $0$ as $x$ tends to infinity.
    have h_log_term : Filter.Tendsto (fun x => Real.log (4 * (Real.log x) ^ 2) / Real.log x) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit further by separating the terms.
      suffices h_simplify'' : Filter.Tendsto (fun x => Real.log 4 / Real.log x + 2 * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) by
        refine h_simplify''.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sq_pos_of_pos ( Real.log_pos hx ) ) ), Real.log_pow ] ; ring );
      -- We'll use the fact that $\frac{\log(\log x)}{\log x}$ tends to $0$ as $x$ tends to infinity.
      have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{y}$.
        suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
        suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ mul_div_assoc ] using! Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ( h_log_log.const_mul 2 );
    apply Filter.Tendsto.atTop_mul_neg;
    exact show ( 0 + ( c₀ + 1 ) * 0 - ( 1 - 8 * 0 ) / t : ℝ ) < 0 from by norm_num; positivity;
    · exact Real.tendsto_log_atTop;
    · exact Filter.Tendsto.sub ( Filter.Tendsto.add h_log_term ( tendsto_const_nhds.mul h_Sscale_growth ) ) ( Filter.Tendsto.div_const ( tendsto_const_nhds.sub ( tendsto_const_nhds.mul h_Sscale_growth ) ) _ );
  -- Conclude via a `Tendsto ... atBot`/eventually argument (e.g. show `(L-8S)/t - Real.log(4L²) - (c₀+1)S → atTop`).
  have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) * (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ≤ 4 * (Real.log x) ^ 2 := by
    have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) ≤ 2 * Real.log x ∧ (1 + Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t))) ≤ 2 * Real.log x := by
      have h_final : ∀ᶠ x in Filter.atTop, (1 + Real.logb 2 x) ≤ 2 * Real.log x := by
        norm_num [ Real.logb ];
        field_simp;
        exact ⟨ Real.exp 2, fun x hx => by nlinarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_le_log ( by positivity ) hx, Real.log_pos one_lt_two, mul_le_mul_of_nonneg_right ( Real.log_two_gt_d9.le ) ( Real.log_nonneg ( show 1 ≤ x by linarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_le_log ( by positivity ) hx ] ) ) ] ⟩;
      have h_final : ∀ᶠ x in Filter.atTop, Real.log (x * Real.exp (-(Real.log x - 8 * Sscale x) / t)) ≤ Real.log x := by
        have h_final : ∀ᶠ x in Filter.atTop, -(Real.log x - 8 * Sscale x) / t ≤ 0 := by
          have h_final : Filter.Tendsto (fun x => (8 * Sscale x) / Real.log x) Filter.atTop (nhds 0) := by
            have h_final : Filter.Tendsto (fun x => Real.sqrt (Real.log x) * Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
              have h_final : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
                have h_final : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
                  -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y}$.
                  suffices h_log_y : Filter.Tendsto (fun y => Real.log (y^2) / y) Filter.atTop (nhds 0) by
                    have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
                    exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.sq_sqrt hx.le ] );
                  -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
                  suffices h_log_z : Filter.Tendsto (fun z => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
                    exact h_log_z.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
                  norm_num +zetaDelta at *;
                  exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
                exact h_final.comp ( Real.tendsto_log_atTop );
              grind +splitImp;
            convert! h_final.const_mul 8 using 2 <;> norm_num [ Sscale ] ; ring;
          filter_upwards [ h_final.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.log_pos hx₂, mul_div_cancel₀ ( 8 * Sscale x ) <| ne_of_gt <| Real.log_pos hx₂ ] ;
        filter_upwards [ h_final, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using Real.log_le_log ( by positivity ) ( by nlinarith [ Real.exp_le_one_iff.mpr hx₁ ] );
      filter_upwards [ ‹∀ᶠ x in atTop, 1 + Real.logb 2 x ≤ 2 * Real.log x›, h_final, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ using ⟨ hx₁, by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) hx₃.le ] ⟩;
    filter_upwards [ h_final, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by nlinarith [ show 0 ≤ 1 + Real.logb 2 x from add_nonneg zero_le_one ( Real.logb_nonneg ( by norm_num ) ( by linarith ) ) ] ;
  filter_upwards [ h_sum_bound, h_final, h_exp_bound.eventually ( Filter.eventually_lt_atBot 0 ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  refine le_trans hx₁ ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| show - ( c₀ + 1 ) * Sscale x ≥ Real.log ( 4 * Real.log x ^ 2 ) - ( Real.log x - 8 * Sscale x ) / t by linarith ) <| by positivity );
  convert! mul_le_mul_of_nonneg_left hx₂ ( show 0 ≤ x * Real.exp ( - ( Real.log x - 8 * Sscale x ) / t ) by positivity ) using 1 ; ring;
  rw [ Real.exp_sub, Real.exp_log ( by exact mul_pos zero_lt_four ( sq_pos_of_pos ( Real.log_pos hx₄ ) ) ) ] ; ring_nf;
  rw [ ← Real.exp_neg ] ; ring_nf

/-
**Low-range fiber reduction.**  Mirroring `comp_fiber` but for the low range
`T ≤ t ≤ δ√L` (with `T` the weighted-prefix threshold) and summing over the
unrestricted range of `m ≤ x·e^{-M_t}` with `M_t = (1-η)²·L·log t/(2t log2)`.
-/
set_option maxHeartbeats 1600000 in
theorem low_fiber (η δ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (_hδ : 0 < δ) :
    ∃ (Cfib : ℝ) (T : ℕ), 0 < Cfib ∧ 3 ≤ T ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (T : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤
        Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
            + Real.log (t + 2) * Real.log (Real.log (3 * x))))
        * ∑ m ∈ (Finset.Icc 1 ⌊x * Real.exp
              (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊),
          (tauCount m : ℝ) ^ (Ht t) := by
  obtain ⟨Cfib, Q, hpos, hsq, hdvd, hom, hfiber, hprefix⟩ := canonical_compression_exists;
  refine' ⟨ Cfib, hprefix η hη |> Classical.choose |> Nat.max 3, hpos, _, _ ⟩;
  · exact le_max_left _ _;
  · obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 3 ≤ x ∧ 1 ≤ Real.log x ∧ 8 * Sscale x ≤ η * Real.log x := by
      have h_Sscale_log : Filter.Tendsto (fun x : ℝ => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
        unfold Sscale;
        -- Let $y = \log x$, therefore the expression becomes $\frac{\sqrt{y} \log y}{y} = \frac{\log y}{\sqrt{y}}$.
        suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
          convert! h_log_y.comp ( Real.tendsto_log_atTop ) using 2 ; norm_num ; ring_nf;
          rw [ ← Real.sqrt_div_self ] ; ring;
        -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
        suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
          have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
        -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
        suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
          exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
      have := h_Sscale_log.eventually ( gt_mem_nhds <| show 0 < η / 8 by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₀, hX₀ ⟩ ; exact ⟨ Max.max X₀ 3, fun x hx => ⟨ by linarith [ le_max_right X₀ 3 ], by rw [ Real.le_log_iff_exp_le ( by linarith [ le_max_right X₀ 3 ] ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ le_max_right X₀ 3 ] ), by have := hX₀ x ( le_trans ( le_max_left X₀ 3 ) hx ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₀ 3 ] ) ] at this; linarith ⟩ ⟩ ;
    filter_upwards [ Filter.eventually_ge_atTop X₀ ] with x hx t ht₁ ht₂;
    -- For each $n$ in the $NregT$ set, we have $log(Q n) \geq M_t$.
    have h_log_Q_ge_Mt : ∀ n ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))), Real.log (Q n) ≥ ((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)) := by
      intro n hn
      have h_log_rad : Real.log (rad n) ≥ (1 - η) * Real.log x := by
        have h_log_rad : (n : ℝ) / (rad n : ℝ) ≤ Real.exp (4 * Sscale x) := by
          grind;
        have h_log_rad : (rad n : ℝ) ≥ (n : ℝ) / Real.exp (4 * Sscale x) := by
          rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num at *;
          · rwa [ ← div_le_iff₀' ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hp ) ];
          · positivity;
        have h_log_rad : Real.log (rad n) ≥ Real.log (n : ℝ) - 4 * Sscale x := by
          have h_log_rad : Real.log (rad n) ≥ Real.log (n / Real.exp (4 * Sscale x)) := by
            exact Real.log_le_log ( div_pos ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ) ) ( Real.exp_pos _ ) ) h_log_rad;
          rwa [ Real.log_div ( by norm_cast; linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) ] ) ( by positivity ), Real.log_exp ] at h_log_rad;
        have h_log_n : Real.log (n : ℝ) ≥ Real.log x - 4 * Sscale x := by
          have h_log_n : (n : ℝ) ≥ x * Real.exp (-4 * Sscale x) := by
            grind;
          have h_log_n : Real.log (n : ℝ) ≥ Real.log (x * Real.exp (-4 * Sscale x)) := by
            exact Real.log_le_log ( mul_pos ( by linarith [ hX₀ x hx ] ) ( Real.exp_pos _ ) ) h_log_n;
          rw [ Real.log_mul ( by linarith [ hX₀ x hx ] ) ( by positivity ), Real.log_exp ] at h_log_n ; linarith;
        linarith [ hX₀ x hx ]
      have h_log_Q : Real.log (Q n) ≥ (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log t / t := by
        have := Classical.choose_spec ( hprefix η hη ) n ( by
          exact Finset.mem_filter.mp hn |>.2.1 ) ( by
          norm_num +zetaDelta at *;
          linarith );
        aesop;
      refine le_trans ?_ h_log_Q;
      convert! mul_le_mul_of_nonneg_right h_log_rad ( show 0 ≤ ( 1 - η ) * Real.log t / ( 2 * t * Real.log 2 ) by exact div_nonneg ( mul_nonneg ( sub_nonneg.2 <| by linarith ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith [ show t ≥ 1 by exact Nat.one_le_iff_ne_zero.2 <| by rintro rfl; norm_num at ht₁ ] ) <| by positivity ) using 1 ; ring;
      ring;
    -- For each $n$ in the $NregT$ set, we have $n / Q n \leq \lfloor x \cdot e^{-M_t} \rfloor$.
    have h_n_div_Q_le_floor : ∀ n ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ ¬((n : ℝ) ≤ x * Real.exp (-4 * Sscale x)) ∧ ¬(Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))), n / Q n ≤ ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊ := by
      intro n hn
      have h_n_div_Q_le_floor : (n : ℝ) / Q n ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
        have h_n_div_Q_le_floor : (n : ℝ) ≤ x := by
          exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) <| Nat.floor_le <| by linarith [ hX₀ x hx ] ;
        have h_n_div_Q_le_floor : (n : ℝ) / Q n ≤ x * Real.exp (-Real.log (Q n)) := by
          rw [ Real.exp_neg, Real.exp_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
            exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using! hsq n ) ) ];
          exact mul_le_mul_of_nonneg_right h_n_div_Q_le_floor <| inv_nonneg.2 <| Nat.cast_nonneg _;
        exact h_n_div_Q_le_floor.trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| neg_le_neg <| h_log_Q_ge_Mt n hn ) <| by linarith [ hX₀ x hx ] );
      exact Nat.le_floor <| by simpa using! h_n_div_Q_le_floor.trans' <| Nat.cast_div_le ..;
    have h_card_le_sum : (NregT x t : ℝ) ≤ ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (Finset.filter (fun n => SylowDivisor n ∧ omegaCount n = t ∧ n / Q n = m) (Finset.Icc 1 ⌊x⌋₊)).card := by
      refine' mod_cast le_trans _ ( Finset.card_biUnion_le );
      refine Finset.card_mono ?_;
      intro n hn; simp_all +decide ;
      refine' Nat.div_pos _ ( Nat.pos_of_dvd_of_pos ( hdvd n hn.2.1 ( by linarith ) ) hn.1.1 );
      exact Nat.le_of_dvd hn.1.1 ( hdvd n hn.2.1 ( by linarith ) );
    refine le_trans h_card_le_sum ?_;
    push_cast [ Finset.mul_sum _ _ _ ];
    apply Finset.sum_le_sum
    intro m hm
    simpa only [Acal, Set.mem_setOf_eq, mul_comm] using! hfiber x (hX₀ x hx |>.1) t
      (by norm_cast at *; linarith [Nat.le_max_left 3 (Classical.choose (hprefix η hη))]) m

/-
Lower bound on the compression exponent `M_t` in the low range: for any
`κ < (1-η)²/(4δ log 2)`, eventually `κ·S ≤ M_t` for `3 ≤ t ≤ δ√L`.
-/
theorem low_Mt_ge (η δ κ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hκ : κ < (1 - η) ^ 2 / (4 * δ * Real.log 2)) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (3 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      κ * Sscale x ≤ (1 - η) ^ 2 * Real.log x * Real.log t / (2 * (t : ℝ) * Real.log 2) := by
  -- Let L := Real.log x and S := Sscale x := Real.sqrt L·log L.
  set Lx := fun x : ℝ => Real.log x
  set Sx := fun x : ℝ => Real.sqrt (Lx x) * Real.log (Lx x);
  -- For x large enough that δ √L ≥ 3 ≥ e, both t and δ √L lie in [e, ∞) with t ≤ δ √L.
  have h_t_bound : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, 3 ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Lx x) →
      Real.log t / t ≥ Real.log (δ * Real.sqrt (Lx x)) / (δ * Real.sqrt (Lx x)) := by
        -- The function $f(s) = \frac{\log s}{s}$ is antitone on $[e, \infty)$.
        have h_antitone : ∀ s t : ℝ, Real.exp 1 ≤ s → s ≤ t → Real.log s / s ≥ Real.log t / t := by
          intros s t hs ht
          have h_deriv_neg : ∀ s : ℝ, Real.exp 1 < s → deriv (fun s => Real.log s / s) s < 0 := by
            intro s hs; norm_num [ show s ≠ 0 by linarith [ Real.exp_pos 1 ] ];
            exact div_neg_of_neg_of_pos ( by linarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) hs ] ) ( sq_pos_of_pos ( by linarith [ Real.exp_pos 1 ] ) );
          by_contra h_contra;
          have := exists_deriv_eq_slope ( f := fun s => Real.log s / s ) ( show s < t from ht.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at *;
          exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => DifferentiableAt.continuousAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hx.1, Real.exp_pos 1 ] ) ) ) ) ( by rintro ⟨ c, ⟨ hsc, hct ⟩, hcd ⟩ ; have := h_deriv_neg c ( by linarith ) ; rw [ hcd, div_lt_iff₀ ] at this <;> linarith );
        -- Choose x large enough so that δ * Real.sqrt (Lx x) ≥ e.
        obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, δ * Real.sqrt (Lx x) ≥ Real.exp 1 := by
          have h_sqrt_log : Filter.Tendsto (fun x => δ * Real.sqrt (Lx x)) Filter.atTop Filter.atTop := by
            exact Filter.Tendsto.const_mul_atTop hδ ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop );
          exact Filter.eventually_atTop.mp ( h_sqrt_log.eventually_ge_atTop ( Real.exp 1 ) );
        filter_upwards [ Filter.eventually_ge_atTop X₀ ] with x hx t ht₁ ht₂ using h_antitone _ _ ( show Real.exp 1 ≤ ( t : ℝ ) by exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith ) ) ht₂;
  -- Hence `M_t ≥ ((1-η)²·L/(2·log2)) · Real.log (δ√L)/(δ√L) =: M_min(x)`.
  have h_M_min : ∀ᶠ x in Filter.atTop, ∀ t : ℕ, 3 ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Lx x) →
      (1 - η) ^ 2 * Lx x * Real.log t / (2 * t * Real.log 2) ≥ (1 - η) ^ 2 * Lx x * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.sqrt (Lx x) * Real.log 2) := by
        filter_upwards [ h_t_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
        intro t ht₁ ht₂; specialize hx₁ t ht₁ ht₂; rw [ ge_iff_le ] at *; rw [ div_le_div_iff₀ ] at * <;> try positivity;
        · convert! mul_le_mul_of_nonneg_left hx₁ ( show 0 ≤ ( 1 - η ) ^ 2 * Lx x * ( 2 * Real.log 2 ) by exact mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.log_nonneg hx₂.le ) ) ( by positivity ) ) using 1 <;> ring;
        · exact lt_of_lt_of_le ( by positivity ) ht₂;
        · exact mul_pos ( mul_pos ( mul_pos two_pos hδ ) ( Real.sqrt_pos.mpr ( Real.log_pos hx₂ ) ) ) ( Real.log_pos one_lt_two );
  -- Now `M_min(x)/S = (1-η)²/(4δ log2)·(1 + 2 Real.log δ / Real.log L)`, which tends to `(1-η)²/(4δ log2) > κ` as `x → ∞`.
  have h_M_min_div_S : Filter.Tendsto (fun x => (1 - η) ^ 2 * Lx x * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.sqrt (Lx x) * Real.log 2) / Sx x) Filter.atTop (nhds ((1 - η) ^ 2 / (4 * δ * Real.log 2))) := by
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun x => (1 - η) ^ 2 * Real.log (δ * Real.sqrt (Lx x)) / (2 * δ * Real.log 2 * Real.log (Lx x))) Filter.atTop (nhds ((1 - η) ^ 2 / (4 * δ * Real.log 2))) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
      rw [ div_div, div_eq_div_iff ] <;> ring_nf!;
      · rw [ Real.sq_sqrt ( Real.log_nonneg hx₁.le ) ] ; ring;
      · exact mul_ne_zero ( mul_ne_zero ( mul_ne_zero hδ.ne' ( by positivity ) ) ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ) two_ne_zero;
      · exact mul_ne_zero ( mul_ne_zero ( mul_ne_zero ( mul_ne_zero hδ.ne' ( pow_ne_zero 2 ( Real.sqrt_ne_zero'.mpr ( Real.log_pos hx₁ ) ) ) ) ( by positivity ) ) ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ) two_ne_zero;
    -- We can simplify the expression inside the limit further.
    suffices h_simplify' : Filter.Tendsto (fun x => (Real.log δ + (1 / 2) * Real.log (Lx x)) / Real.log (Lx x)) Filter.atTop (nhds (1 / 2)) by
      convert! h_simplify'.const_mul ( ( 1 - η ) ^ 2 / ( 2 * δ * Real.log 2 ) ) |> Filter.Tendsto.congr' _ using 2 <;> norm_num;
      · ring;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.sqrt_pos.mpr ( Real.log_pos hx ) ) ), Real.log_sqrt ( Real.log_nonneg hx.le ) ] ; ring;
    ring_nf;
    exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) ( Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ) tendsto_const_nhds ) ) ( by norm_num );
  filter_upwards [ h_M_min_div_S.eventually ( lt_mem_nhds hκ ), h_M_min, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ hx₄;
  intro t ht₁ ht₂; rw [ lt_div_iff₀ ] at hx₁;
  · exact le_trans hx₁.le ( hx₂ t ht₁ ht₂ );
  · exact mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos hx₄ ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )

/-
Upper bound on the lower-order terms `E + (K-1)·log(1+log x)` in the low range:
for any `ρ > 0`, eventually `≤ ρ·S` for `t ≤ δ√L` (here `K = ⌈2^{H_t}⌉`).
-/
theorem low_EP_small (δ ρ Cfib : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) (hCfib : 0 ≤ Cfib) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      Cfib * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))
        + (((⌈(2 : ℝ) ^ (Ht t)⌉₊ - 1 : ℕ) : ℝ)) * Real.log (1 + Real.log x)
        ≤ ρ * Sscale x := by
  -- By combining the bounds on `U(x)` and `Sscale x`, we can conclude the proof.
  have h_U_le_rho_S : ∀ᶠ x in Filter.atTop, Cfib * ((Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 + Real.log (δ * Real.sqrt (Real.log x) + 2) * Real.log (Real.log (3 * x))) + 16 * Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) ≤ ρ * Sscale x := by
    -- Let $L = \log x$ and $L2 = \log (\log x)$. We need to show that $U(x)/Sscale(x) \to 0$ as $x \to \infty$.
    suffices h_lim : Filter.Tendsto (fun x : ℝ => (Cfib * ((Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 + Real.log (δ * Real.sqrt (Real.log x) + 2) * Real.log (Real.log (3 * x))) + 16 * Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x)) / Sscale x) Filter.atTop (nhds 0) by
      filter_upwards [ h_lim.eventually ( gt_mem_nhds <| show 0 < ρ by positivity ), Filter.eventually_gt_atTop 3 ] with x hx₁ hx₂;
      rw [ div_lt_iff₀ ] at hx₁ <;> norm_num [ Sscale ] at *;
      · linarith;
      · exact mul_pos ( Real.sqrt_pos.mpr ( Real.log_pos ( by linarith ) ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) );
    -- We'll use the fact that if the denominator grows faster than the numerator, the limit will be zero.
    have h_lim : Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2)) ^ 2 / Sscale x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2)) * Real.log (Real.log (3 * x)) / Sscale x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => Real.sqrt (δ * Real.sqrt (Real.log x) + 2) * Real.log (1 + Real.log x) / Sscale x) Filter.atTop (nhds 0) := by
      refine' ⟨ _, _, _ ⟩;
      · -- We'll use the fact that $\log(\delta \sqrt{\log x} + 2) \sim \frac{1}{2} \log \log x$ as $x \to \infty$.
        have h_log : Filter.Tendsto (fun x : ℝ => Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) := by
          -- We can use the fact that $\log(\delta \sqrt{\log x} + 2) = \log(\sqrt{\log x}) + \log(\delta + \frac{2}{\sqrt{\log x}})$.
          suffices h_log_split : Filter.Tendsto (fun x : ℝ => (Real.log (Real.sqrt (Real.log x)) + Real.log (δ + 2 / Real.sqrt (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) by
            refine h_log_split.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ) ( by positivity ), mul_add, mul_div_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ; ring_nf;
          rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_sqrt ( Real.log_nonneg hx.le ) ] ) ] ; ring_nf ; norm_num;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) ) <| by norm_num;
        -- We can rewrite the limit expression using the fact that $\log(\delta \sqrt{\log x} + 2) \sim \frac{1}{2} \log \log x$.
        have h_rewrite : Filter.Tendsto (fun x : ℝ => (Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) ^ 2 * (Real.log (Real.log x) / Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
          have h_rewrite : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) / Real.sqrt (Real.log x))) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{\sqrt{y}}$.
            suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
              have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
            -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
            suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
              exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
          simpa using! Filter.Tendsto.mul ( h_log.pow 2 ) h_rewrite;
        convert! h_rewrite using 2 ; norm_num [ Sscale ] ; ring_nf;
        grind;
      · -- We'll use the fact that $\log(\delta \sqrt{\log x} + 2) \sim \frac{1}{2} \log \log x$ and $\log(\log(3x)) \sim \log \log x$ as $x \to \infty$.
        have h_log_approx : Filter.Tendsto (fun x : ℝ => Real.log (δ * Real.sqrt (Real.log x) + 2) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) ∧ Filter.Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
          constructor;
          · -- We can use the fact that $\log(\delta \sqrt{\log x} + 2) = \log(\sqrt{\log x}) + \log(\delta + \frac{2}{\sqrt{\log x}})$.
            suffices h_log_split : Filter.Tendsto (fun x : ℝ => (Real.log (Real.sqrt (Real.log x)) + Real.log (δ + 2 / Real.sqrt (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds (1 / 2)) by
              refine h_log_split.congr' ?_;
              filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ) ( by positivity ), mul_add, mul_div_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos hx ] ; ring_nf;
            rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_sqrt ( Real.log_nonneg hx.le ) ] ) ] ; ring_nf ; norm_num;
            exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) ) <| by norm_num;
          · -- We can use the fact that $\log(3x) = \log 3 + \log x$ to simplify the expression.
            suffices h_log_simplified : Filter.Tendsto (fun x : ℝ => Real.log (Real.log 3 + Real.log x) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
              refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
            -- We can use the fact that $\log(\log 3 + \log x) = \log(\log x) + \log(1 + \frac{\log 3}{\log x})$.
            suffices h_log_simplified : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) + Real.log (1 + Real.log 3 / Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
              refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hx ), Real.log_div ( by linarith [ Real.log_pos hx, Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ] ) ( by linarith [ Real.log_pos hx, Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ] ) ] ; ring_nf );
            ring_nf;
            exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ] ) <| Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add <| tendsto_const_nhds.mul <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop ) <| by positivity ) <| tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) <| by norm_num;
        -- Using the fact that $\log(\log x) / \sqrt{\log x} \to 0$ as $x \to \infty$, we can simplify the expression.
        have h_log_log_sqrt : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) := by
          -- Let $y = \log x$, therefore the expression becomes $\frac{\log y}{\sqrt{y}}$.
          suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
            exact h_log_y.comp ( Real.tendsto_log_atTop );
          -- Let $z = \sqrt{y}$, therefore the expression becomes $\frac{\log z^2}{z} = \frac{2 \log z}{z}$.
          suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
            have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
          -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{2 \log (1/w)}{1/w} = -2w \log w$.
          suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
            exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
        convert! h_log_approx.1.mul ( h_log_approx.2.mul h_log_log_sqrt ) using 2 <;> norm_num [ Sscale ] ; ring_nf;
        grind;
      · -- We can simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (δ * Real.sqrt (Real.log x) + 2) / Real.sqrt (Real.log x)) Filter.atTop (nhds 0) by
          convert! h_simplify.mul ( show Filter.Tendsto ( fun x : ℝ => Real.log ( 1 + Real.log x ) / Real.log ( Real.log x ) ) Filter.atTop ( nhds 1 ) from ?_ ) using 2 <;> norm_num [ Sscale ] ; ring;
          -- We can use the fact that $\log(1 + \log x) = \log(\log x) + \log(1 + 1/\log x)$.
          suffices h_log : Filter.Tendsto (fun x : ℝ => (Real.log (Real.log x) + Real.log (1 + 1 / Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) by
            refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_add_div ( ne_of_gt <| Real.log_pos hx ), Real.log_div ( by linarith [ Real.log_pos hx ] ) ( by linarith [ Real.log_pos hx ] ) ] ; ring_nf );
          ring_nf;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) ) ) ) ( by norm_num );
        -- We can simplify the expression inside the square root.
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (δ / Real.sqrt (Real.log x) + 2 / Real.log x)) Filter.atTop (nhds 0) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
          rw [ ← Real.sqrt_div ( by positivity ) ] ; ring_nf;
          rw [ ← Real.sqrt_div_self ] ; ring_nf;
        exact le_trans ( Filter.Tendsto.sqrt <| Filter.Tendsto.add ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 ), fun y hy => Real.le_sqrt_of_sq_le <| by simpa using! Real.log_le_log ( by positivity ) hy ⟩ ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop ) <| by norm_num;
    convert! Filter.Tendsto.add ( Filter.Tendsto.add ( h_lim.1.const_mul Cfib ) ( h_lim.2.1.const_mul Cfib ) ) ( h_lim.2.2.const_mul 16 ) using 2 <;> ring;
  filter_upwards [ h_U_le_rho_S, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
  intro t ht; refine le_trans ?_ hx₁; gcongr;
  · exact Real.log_nonneg ( by linarith );
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
  · exact Real.log_nonneg ( by linarith [ Real.log_nonneg hx₂.le ] );
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| show ( δ * Real.sqrt ( Real.log x ) + 2 ) ≥ ( t + 2 ) by nlinarith [ Real.sqrt_nonneg ( Real.log x ) ] ) <| by positivity );
    rw [ Nat.cast_sub ] <;> norm_num;
    exact le_trans ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) ( by linarith [ pow_Ht_le t ] )

/-
**Low noncritical range.**  For `δ` small (`(1-η)²/(4δ log 2) > c₀ + 1`), there is
a threshold `T ≥ 3` such that for `T ≤ t ≤ δ√L`, `NregT x t ≤ x·exp(-(c₀+1)S)`.
-/
theorem low_noncritical_bound (η δ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hlow : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (T : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ δ * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) := by
  obtain ⟨Cfib, T, hCfib, hT3, hlf⟩ := low_fiber η δ hη hη4 hδ;
  set κ := ((1 - η)^2 / (4 * δ * Real.log 2) + (c₀ + 1)) / 2;
  set ρ := κ - (c₀ + 1);
  have hκ : c₀ + 1 < κ ∧ κ < (1 - η)^2 / (4 * δ * Real.log 2) := by
    grind;
  have hρ : 0 < ρ := by
    exact sub_pos_of_lt hκ.1;
  refine' ⟨ T, hT3, _ ⟩;
  filter_upwards [ hlf, low_Mt_ge η δ κ hη hη4 hδ ( by linarith ), low_EP_small δ ρ Cfib hδ hρ hCfib.le, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop 16 ] with x hx₁ hx₂ hx₃ hx₄ hx₅;
  intro t ht₁ ht₂
  have hM_t : (1 - η)^2 * Real.log x * Real.log t / (2 * t * Real.log 2) ≤ Real.log x := by
    have hM_t : (1 - η)^2 * Real.log t / (2 * t * Real.log 2) ≤ 1 := by
      have hM_t : Real.log t / t ≤ Real.log 3 / 3 := by
        rw [ div_le_div_iff₀ ] <;> norm_num;
        · norm_num +zetaDelta at *;
          rw [ mul_comm, ← Real.log_rpow, mul_comm, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
          · exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by norm_num [ Nat.pow_succ' ] at * ; nlinarith ) t ( show t ≥ 3 by linarith );
          · exact pow_pos ( by linarith ) _;
          · lia;
        · exact Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) ht₁ );
      have hM_t : (1 - η)^2 * (Real.log 3 / 3) / (2 * Real.log 2) ≤ 1 := by
        rw [ div_le_iff₀ ( by positivity ) ];
        have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_le_sub_one_of_pos zero_lt_three, Real.log_pos one_lt_two, Real.log_lt_log ( by norm_num ) ( by norm_num : ( 3 : ℝ ) > 2 ) ];
      convert! le_trans _ hM_t using 1;
      convert! mul_le_mul_of_nonneg_left ‹Real.log t / t ≤ Real.log 3 / 3› ( show 0 ≤ ( 1 - η ) ^ 2 / ( 2 * Real.log 2 ) by positivity ) using 1 <;> ring;
    convert! mul_le_mul_of_nonneg_left hM_t ( Real.log_nonneg ( show x ≥ 1 by linarith ) ) using 1 <;> ring;
  have hX_ge_one : 1 ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; norm_num ; linarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) hx₄ ];
  have h_sum_bound : ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (tauCount m : ℝ) ^ (Ht t) ≤ x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2))) * Real.exp (((⌈(2 : ℝ) ^ (Ht t)⌉₊ - 1 : ℕ) : ℝ) * Real.log (1 + Real.log x)) := by
    have h_sum_bound : ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (tauCount m : ℝ) ^ (Ht t) ≤ ∑ m ∈ Finset.Icc 1 ⌊x * Real.exp (-((1 - η) ^ 2 * Real.log x * Real.log t / (2 * t * Real.log 2)))⌋₊, (dk ⌈(2 : ℝ) ^ (Ht t)⌉₊ m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      simpa using! local_moment (Ht t) 1 (by norm_num) m (Finset.mem_Icc.mp hm).1
    refine le_trans h_sum_bound ?_;
    refine le_trans ( dk_sum_le _ ?_ _ ?_ ) ?_;
    · linarith;
    · exact Nat.ceil_pos.mpr ( by positivity );
    · gcongr;
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by linarith [ Real.log_nonneg hX_ge_one ] ) ] ; norm_num;
      rw [ mul_comm ] ; gcongr;
      · exact sub_nonneg_of_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.ceil_pos.mpr <| by positivity );
      · exact add_pos_of_pos_of_nonneg zero_lt_one ( Real.log_nonneg hX_ge_one );
      · exact mul_le_of_le_one_right ( by linarith ) ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.log_nonneg ( by linarith ) ) ) ( Real.log_nonneg ( by norm_cast; linarith [ show t ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at ht₁; linarith ) ] ) ) ) ( mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by norm_num ) ) ) ) ) );
  refine le_trans ( hx₁ t ht₁ ht₂ ) ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left h_sum_bound <| Real.exp_nonneg _ ) ?_;
  convert! mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( show Cfib * ( Real.log ( t + 2 ) ^ 2 + Real.log ( t + 2 ) * Real.log ( Real.log ( 3 * x ) ) ) + ( ⌈ ( 2 : ℝ ) ^ Ht t⌉₊ - 1 : ℕ ) * Real.log ( 1 + Real.log x ) - ( ( 1 - η ) ^ 2 * Real.log x * Real.log t / ( 2 * t * Real.log 2 ) ) ≤ - ( c₀ + 1 ) * Sscale x from ?_ ) ) ( show 0 ≤ x by positivity ) using 1;
  · norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg ] ; ring;
  · linarith [ hx₃ t ht₂, hx₂ t ( by linarith [ show ( T : ℝ ) ≥ 3 by norm_cast ] ) ht₂ ]

/-- **Combined per-`t` bound over `2 ≤ t ≤ C√L`.**  Combines the small-`ω`
(one-prime), low-noncritical, and critical-range estimates into a single uniform
bound `NregT x t ≤ x·exp(-((1-η)c₀ - ζ)S)`. -/
theorem Nreg_uniform (η δ C ζ : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4)
    (hδ : 0 < δ) (hδC : δ ≤ C) (hζ : 0 < ζ)
    (hlowineq : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ t : ℕ,
      (2 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ C * Real.sqrt (Real.log x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < c₀ := by
    have : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2
    unfold c₀; positivity
  have hle : (1 - η) * c₀ - ζ ≤ c₀ + 1 := by nlinarith [hc0, hη, hζ]
  obtain ⟨T, hT3, hlow⟩ := low_noncritical_bound η δ hη hη4 hδ hlowineq
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop, ∀ t ∈ Finset.Ico 2 T,
      (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) :=
    (Finset.eventually_all (Finset.Ico 2 T)).2 (fun t ht => small_t_bound t (Finset.mem_Ico.mp ht).1)
  filter_upwards [hsmall, hlow, critical_per_t_bound η δ C ζ hη hη4 hδ hδC hζ,
    Filter.eventually_ge_atTop (Real.exp 1)] with x hs hl hcrit hxe t h2 hC
  have hxpos : (0 : ℝ) ≤ x := le_trans (Real.exp_pos 1).le hxe
  have hLge1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hxe)]; simpa using! hxe
  have hSnonneg : 0 ≤ Sscale x := by
    unfold Sscale
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
  have hdown : ∀ b : ℝ, (NregT x t : ℝ) ≤ x * Real.exp (-(c₀ + 1) * Sscale x) →
      (NregT x t : ℝ) ≤ x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) := by
    intro _ hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hxpos)
    exact Real.exp_le_exp.mpr (by nlinarith [hle, hSnonneg])
  by_cases htT : t < T
  · exact hdown 0 (hs t (Finset.mem_Ico.mpr ⟨by exact_mod_cast h2, htT⟩))
  · push_neg at htT
    by_cases htδ : (t : ℝ) ≤ δ * Real.sqrt (Real.log x)
    · exact hdown 0 (hl t (by exact_mod_cast htT) htδ)
    · push_neg at htδ
      exact hcrit t (le_of_lt htδ) hC

/-- `S(x)/log x → 0`. -/
theorem Sscale_div_log_tendsto :
    Filter.Tendsto (fun x : ℝ => Sscale x / Real.log x) Filter.atTop (nhds 0) := by
  unfold Sscale
  suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) Filter.atTop (nhds 0) by
    have hcomp := h_log_y.comp Real.tendsto_log_atTop
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx)
    have hL : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt (Real.log_pos hx).le
    rw [Function.comp_apply, div_eq_div_iff hs.ne' (Real.log_pos hx).ne']
    linear_combination (-Real.log (Real.log x)) * hL
  suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * Real.log z / z) Filter.atTop (nhds 0) by
    have := h_log_z.comp ( show Filter.Tendsto ( fun y : ℝ => Real.sqrt y ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
  suffices h_log_w : Filter.Tendsto (fun w : ℝ => -2 * w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
    exact h_log_w.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
  norm_num;
  exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );

/-- `log x - d·S(x) → ∞` for any real `d` (since `S = o(log x)`). -/
theorem log_sub_smul_Sscale_atTop (d : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.log x - d * Sscale x) Filter.atTop Filter.atTop := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (1 / 2) * Real.log x ≤ Real.log x - d * Sscale x := by
    have h1 : ∀ᶠ x : ℝ in Filter.atTop, |d| * (Sscale x / Real.log x) < 2⁻¹ :=
      (Sscale_div_log_tendsto.const_mul |d|).eventually
        (by simpa using! gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [h1, Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop (Real.exp 1)]
      with x hx hx1 hxe
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hLge1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by positivity)]; simpa using! hxe
    have hSnn : 0 ≤ Sscale x := by
      unfold Sscale; exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
    have hkey : |d| * Sscale x < (1 / 2) * Real.log x := by
      have h2 := mul_lt_mul_of_pos_right hx hlogpos
      rw [mul_assoc, div_mul_cancel₀ _ hlogpos.ne'] at h2
      linarith [h2]
    have hdd : d * Sscale x ≤ |d| * Sscale x := by
      have := le_abs_self (d * Sscale x)
      rwa [abs_mul, abs_of_nonneg hSnn] at this
    linarith [hkey, hdd]
  exact Filter.tendsto_atTop_mono' atTop hev
    (Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 1/2 by norm_num) Real.tendsto_log_atTop)

/-- `x·exp(-d·S(x)) → ∞` for any real `d`. -/
theorem x_mul_exp_neg_Sscale_atTop (d : ℝ) :
    Filter.Tendsto (fun x : ℝ => x * Real.exp (-d * Sscale x)) Filter.atTop Filter.atTop := by
  have hcomp := Real.tendsto_exp_atTop.comp (log_sub_smul_Sscale_atTop d)
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  rw [Function.comp_apply, Real.exp_sub, Real.exp_log hx, neg_mul, Real.exp_neg]; ring

/-- `y·exp(-b·y) → 0` for `b > 0`. -/
theorem id_mul_exp_neg_atTop (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => y * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hs : Filter.Tendsto (fun y : ℝ => b * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb tendsto_id
  have h2 := (h.comp hs).const_mul (1 / b)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  simp only [Function.comp_apply, pow_one]
  field_simp

/-- `exp(-b·y) → 0` for `b > 0`. -/
theorem exp_neg_mul_atTop (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-b * y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => b * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb tendsto_id
  have hbig : Filter.Tendsto (fun y : ℝ => -b * y) Filter.atTop Filter.atBot := by
    have := Filter.tendsto_neg_atTop_atBot.comp h
    refine this.congr ?_; intro y; simp [Function.comp, neg_mul]
  have := Real.tendsto_exp_atBot.comp hbig
  refine this.congr ?_; intro y; simp [Function.comp]

/-- `(a√(log x) + 2)·exp(-b·S(x)) → 0` for `b > 0`. -/
theorem poly_mul_exp_neg_Sscale_zero (a b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun x : ℝ => (a * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Sscale x))
      Filter.atTop (nhds 0) := by
  have hy : Filter.Tendsto (fun y : ℝ => (|a| * y + 2) * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => |a| * (y * Real.exp (-b * y))) Filter.atTop (nhds 0) := by
      simpa using! (id_mul_exp_neg_atTop b hb).const_mul |a|
    have h2 : Filter.Tendsto (fun y : ℝ => (2 : ℝ) * Real.exp (-b * y)) Filter.atTop (nhds 0) := by
      simpa using! (exp_neg_mul_atTop b hb).const_mul 2
    have hsum : Filter.Tendsto (fun y : ℝ => |a| * (y * Real.exp (-b * y)) + 2 * Real.exp (-b * y))
        Filter.atTop (nhds 0) := by simpa using! h1.add h2
    refine hsum.congr' ?_
    filter_upwards with y using by ring
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop Filter.atTop := by
    simpa only [Real.sqrt_eq_rpow] using!
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  refine squeeze_zero_norm' ?_ (hy.comp hsqrt)
  filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLe : Real.exp 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]; simpa using! hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hLLge1 : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hLpos]; simpa using! hLe
  have hSge : Real.sqrt (Real.log x) ≤ Sscale x := by
    unfold Sscale
    nlinarith [Real.sqrt_nonneg (Real.log x), hLLge1]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), Function.comp_apply]
  have h1 : |a * Real.sqrt (Real.log x) + 2| ≤ |a| * Real.sqrt (Real.log x) + 2 := by
    calc |a * Real.sqrt (Real.log x) + 2|
        ≤ |a * Real.sqrt (Real.log x)| + |(2 : ℝ)| := abs_add_le _ _
      _ = |a| * Real.sqrt (Real.log x) + 2 := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]; norm_num
  have h2 : Real.exp (-b * Sscale x) ≤ Real.exp (-b * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [hSge])
  have hposb : (0 : ℝ) ≤ |a| * Real.sqrt (Real.log x) + 2 := by positivity
  calc |a * Real.sqrt (Real.log x) + 2| * Real.exp (-b * Sscale x)
      ≤ (|a| * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Sscale x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ ≤ (|a| * Real.sqrt (Real.log x) + 2) * Real.exp (-b * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left h2 hposb

set_option maxHeartbeats 1600000 in
/-- **Regular integers (paper Section 10, the critical + noncritical analysis).**
For a regular `n ∈ 𝒜` (i.e. `SylowDivisor n`, `¬(n ≤ x·e^{-4S})` and
`¬(n/rad(n) > e^{4S})`), the count with `n ≤ x` is `≤ x·exp(-(c₀-ε)·S(x))`
eventually, for every `ε > 0`.

This packages the paper's critical-range estimate (Lemma 10.1) via the canonical
compression `canonical_compression_exists` and the divisor moment bounds
`restricted_moment`/`local_moment`/`dk_sum_le`, together with the noncritical -- maxHeartbeats set below
ranges (Lemma 10.2) via `omega_tail` and `valuation_bit`, and the entropy
optimisation `opt_lower`. -/
theorem regular_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => SylowDivisor n
            ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
            ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ)))).card : ℝ)
        ≤ x * Real.exp (-(c₀ - ε) * Sscale x) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < c₀ := by
    have : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2
    unfold c₀; positivity
  set η := min (ε / (4 * c₀)) (1 / 8) with hη_def
  set ζ := ε / 4 with hζ_def
  set C := 2 * c₀ + 2 with hC_def
  set δ := (1 - η) ^ 2 / (4 * (c₀ + 2) * Real.log 2) with hδ_def
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h1mη : 0 < 1 - η := by have := lt_of_le_of_lt (min_le_right (ε / (4 * c₀)) (1/8)) (by norm_num : (1:ℝ)/8 < 1); linarith
  have hηc0 : η * c₀ ≤ ε / 4 := by
    have h : η ≤ ε / (4 * c₀) := min_le_left _ _
    calc η * c₀ ≤ ε / (4 * c₀) * c₀ := by exact mul_le_mul_of_nonneg_right h hc0.le
      _ = ε / 4 := by field_simp
  have hζ0 : 0 < ζ := by rw [hζ_def]; positivity
  have hδ0 : 0 < δ := by rw [hδ_def]; exact div_pos (pow_pos h1mη 2) (by positivity)
  have hC0 : 0 < C := by rw [hC_def]; positivity
  have hnum : (1 - η) ^ 2 ≤ 1 := by nlinarith [hη0, h1mη]
  have hden : (1 : ℝ) ≤ 4 * (c₀ + 2) * Real.log 2 := by
    nlinarith [hc0, Real.log_two_gt_d9]
  have hδC : δ ≤ C := by
    have hδ1 : δ ≤ 1 := by rw [hδ_def, div_le_one (by positivity)]; nlinarith [hnum, hden]
    rw [hC_def]; nlinarith [hδ1, hc0]
  have hlowineq : (1 - η) ^ 2 / (4 * δ * Real.log 2) > c₀ + 1 := by
    have heq : (1 - η) ^ 2 / (4 * δ * Real.log 2) = c₀ + 2 := by
      rw [hδ_def]
      field_simp
    rw [heq]; linarith
  have hcritrate : c₀ - ε / 2 ≤ (1 - η) * c₀ - ζ := by rw [hζ_def]; nlinarith [hηc0]
  have hhighrate : c₀ - ε / 2 ≤ C / 2 - ζ := by rw [hC_def, hζ_def]; linarith
  filter_upwards [Nreg_uniform η δ C ζ hη0 hη4 hδ0 hδC hζ0 hlowineq,
    high_tail_bound C ζ hC0 hζ0,
    (x_mul_exp_neg_Sscale_atTop (c₀ - ε / 2)).eventually_ge_atTop 1,
    (poly_mul_exp_neg_Sscale_zero (2 * C + 1) (ε / 2) (by positivity)).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop 1]
    with x huni hhigh hD1 hMexp hxe hx1
  have hxpos : (0 : ℝ) < x := lt_trans one_pos hx1
  have hLge1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]; simpa using! hxe
  have hSnn : 0 ≤ Sscale x := by
    unfold Sscale; exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hLge1)
  have hsqrtge1 : 1 ≤ Real.sqrt (Real.log x) := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hLge1
  set B := x * Real.exp (-((1 - η) * c₀ - ζ) * Sscale x) with hB_def
  set D := x * Real.exp (-(c₀ - ε / 2) * Sscale x) with hD_def
  set M := ⌊C * Real.sqrt (Real.log x)⌋₊ with hM_def
  have hDnn : 0 ≤ D := by rw [hD_def]; positivity
  have hBnn : 0 ≤ B := by rw [hB_def]; positivity
  have hBle : B ≤ D := by
    rw [hB_def, hD_def]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hcritrate, hSnn])) hxpos.le
  have hMle : (M : ℝ) ≤ C * Real.sqrt (Real.log x) := by
    rw [hM_def]; exact Nat.floor_le (by positivity)
  -- the regular set
  set Rset := (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => SylowDivisor n ∧ ¬ ((n : ℝ) ≤ x * Real.exp (-4 * Sscale x))
        ∧ ¬ (Real.exp (4 * Sscale x) < (n : ℝ) / (rad n : ℝ))) with hRset_def
  -- NregT is the ω-fiber of Rset
  have hNeq : ∀ t : ℕ, (Rset.filter (fun n => omegaCount n = t)).card = NregT x t := by
    intro t
    rw [hRset_def, Finset.filter_filter]
    unfold NregT
    congr 1
    ext n
    simp only [Finset.mem_filter]
    tauto
  -- per-t bound `NregT ≤ 1 + B`
  have hNle : ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (Real.log x) → (NregT x t : ℝ) ≤ 1 + B := by
    intro t ht
    rcases lt_or_ge t 2 with h2 | h2
    · interval_cases t
      · exact le_trans (Nreg_zero_le x) (by linarith [hBnn])
      · rw [Nreg_one_eq_zero]; push_cast; linarith [hBnn]
    · exact le_trans (huni t (by exact_mod_cast h2) ht) (by linarith [hBnn, hBle])
  -- split Rset by ω ≤ M
  have hsplit : (Rset.card : ℝ)
      = ((Rset.filter (fun n => omegaCount n ≤ M)).card : ℝ)
        + ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  -- low part
  have hlowcard : ((Rset.filter (fun n => omegaCount n ≤ M)).card : ℝ) ≤ (↑M + 1) * (1 + B) := by
    have hfib : (Rset.filter (fun n => omegaCount n ≤ M)).card
        = ∑ t ∈ Finset.range (M + 1),
            ((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro n hn
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    rw [hfib]
    push_cast
    calc ∑ t ∈ Finset.range (M + 1),
            (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
        ≤ ∑ _t ∈ Finset.range (M + 1), (1 + B) := by
          apply Finset.sum_le_sum
          intro t ht
          have hsub : (Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)
              ⊆ Rset.filter (fun n => omegaCount n = t) := by
            intro n hn
            rw [Finset.mem_filter] at hn ⊢
            exact ⟨(Finset.mem_filter.mp hn.1).1, hn.2⟩
          have htM : (t : ℝ) ≤ C * Real.sqrt (Real.log x) := by
            have : t ≤ M := by have := Finset.mem_range.mp ht; omega
            exact le_trans (by exact_mod_cast this) hMle
          have hcard : (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
              ≤ (NregT x t : ℝ) := by
            calc (((Rset.filter (fun n => omegaCount n ≤ M)).filter (fun n => omegaCount n = t)).card : ℝ)
                ≤ ((Rset.filter (fun n => omegaCount n = t)).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card hsub
              _ = (NregT x t : ℝ) := by exact_mod_cast hNeq t
          exact le_trans hcard (hNle t htM)
      _ = (↑M + 1) * (1 + B) := by
          rw [Finset.sum_const, Finset.card_range]; ring
  -- high part
  have hHle : ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ) ≤ D := by
    have hsub : Rset.filter (fun n => ¬ omegaCount n ≤ M)
        ⊆ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ)) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      obtain ⟨hnR, hnω⟩ := hn
      refine ⟨(Finset.mem_filter.mp hnR).1, ?_⟩
      have hMω : M < omegaCount n := by omega
      have : (M : ℝ) + 1 ≤ (omegaCount n : ℝ) := by exact_mod_cast hMω
      have hlt : C * Real.sqrt (Real.log x) < (M : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    calc ((Rset.filter (fun n => ¬ omegaCount n ≤ M)).card : ℝ)
        ≤ (((Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => C * Real.sqrt (Real.log x) < (omegaCount n : ℝ))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ x * Real.exp (-(C / 2 - ζ) * Sscale x) := hhigh
      _ ≤ D := by
          rw [hD_def]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hhighrate, hSnn])) hxpos.le
  -- combine
  have hRle : (Rset.card : ℝ) ≤ (↑M + 1) * (1 + B) + D := by
    rw [hsplit]; linarith [hlowcard, hHle]
  -- (M+1)(1+B) + D ≤ (2M+3) D
  have hstep : (↑M + 1) * (1 + B) + D ≤ (2 * ↑M + 3) * D := by
    have h1B : 1 + B ≤ 2 * D := by linarith [hBle, hD1]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1B hMnn, hDnn]
  -- 2M+3 ≤ exp((ε/2) S)
  have hMexp' : (2 * (M : ℝ) + 3) ≤ Real.exp ((ε / 2) * Sscale x) := by
    have hp : ((2 * C + 1) * Real.sqrt (Real.log x) + 2) < Real.exp ((ε / 2) * Sscale x) := by
      have hepos := Real.exp_pos ((ε / 2) * Sscale x)
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_lt_one hepos] at hMexp
      exact hMexp
    have hchain : (2 * (M : ℝ) + 3) ≤ (2 * C + 1) * Real.sqrt (Real.log x) + 2 := by
      nlinarith [hMle, hsqrtge1]
    linarith [hp, hchain]
  -- final
  have hexp_eq : x * Real.exp (-(c₀ - ε) * Sscale x) = D * Real.exp ((ε / 2) * Sscale x) := by
    rw [hD_def, mul_assoc, ← Real.exp_add,
      show -(c₀ - ε) * Sscale x = -(c₀ - ε / 2) * Sscale x + (ε / 2) * Sscale x from by ring]
  calc (Rset.card : ℝ)
      ≤ (↑M + 1) * (1 + B) + D := hRle
    _ ≤ (2 * ↑M + 3) * D := hstep
    _ ≤ Real.exp ((ε / 2) * Sscale x) * D := mul_le_mul_of_nonneg_right hMexp' hDnn
    _ = D * Real.exp ((ε / 2) * Sscale x) := by ring
    _ = x * Real.exp (-(c₀ - ε) * Sscale x) := hexp_eq.symm

end Erdos768
