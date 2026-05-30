/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1100.
https://www.erdosproblems.com/forum/thread/1100

Formalization status:
- Partial
- Conditional on: prime_number_theorem

Informal authors:
- Paul Erdős
- R. R. Hall
- Wouter van Doorn

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/1100#post-1659
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem1100.lean
-/
/-
If $1 = d_1 < \cdots < d_{\tau(n)} = n$ are the divisors of $n$, then define $\tau_\perp(n)$ to be the number of $i$ for which $d_i$ and $d_{i+1}$ are coprime. Erdős and Hall proved that there are infinitely many $n$ with $\tau_\perp(n) > \exp( (\log \log n)^{2 - o(1)} )$.

Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers. J. Austral. Math. Soc. Ser. A (1978), 479--485.

I noticed that the $o(1)$-term in the exponent can be made explicit, which gives $\tau_\perp(n) > \exp( \frac{(1 / 2 - o(1))(\log \log n)^2}{\log \log \log n} )$ infinitely often. Assuming the prime number theorem in the form that the product of all primes in the interval $(x, 2x]$ is $e^{(1 + o(1))x}$, below you can find a formalized proof of this bound, which was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

See https://www.erdosproblems.com/1100 for more information.

-/

import Mathlib

namespace Erdos1100b

set_option linter.style.longLine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Nat

/-
We define $\tau_\perp(n)$ to be the number of consecutive divisors $d_i, d_{i+1}$ of $n$ for which $\gcd(d_i, d_{i+1}) = 1$.
-/
noncomputable def tau_perp (n : ℕ) : ℕ :=
  let l := (divisors n).sort (· ≤ ·)
  (l.zip l.tail).countP (fun (a, b) => Nat.gcd a b = 1)

/-
Definition of n_val_Ioc(x).
-/
noncomputable def n_val_Ioc (x : ℝ) : ℕ :=
  ((Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))).filter Nat.Prime).prod (fun p => p)

/-
The statement of the Prime Number Theorem for the interval (x, 2x].
-/
def PNT_statement : Prop :=
  Filter.Tendsto (fun x => Real.log (n_val_Ioc x) / x) Filter.atTop (nhds 1)

/-
Definition of the lower bound function for tau_perp(n).
-/
noncomputable def bound (n : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ( (1 / 2 - ε) * (Real.log (Real.log n))^2 / Real.log (Real.log (Real.log n)) )

/-
Definition of y_val(x, epsilon).
-/

noncomputable def y_val (x : ℝ) (ε : ℝ) : ℕ :=
  Nat.floor ((1 / 2 - ε) * Real.log x / Real.log (Real.log x))

/-
Definition of the set of divisors of n with exactly y distinct prime factors.
-/
def divisors_with_y_factors (n : ℕ) (y : ℕ) : Finset ℕ :=
  (divisors n).filter (fun d => d.factorization.support.card = y)

/-
Definition of D_set_Ioc(x, epsilon) (divisors of n_val_Ioc with y prime factors).
-/
noncomputable def D_set_Ioc (x : ℝ) (ε : ℝ) : Finset ℕ :=
  divisors_with_y_factors (n_val_Ioc x) (y_val x ε)

/-
Lemma: For sufficiently large x, y_val(x, epsilon) >= 1.
-/
lemma y_val_pos (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, 1 ≤ y_val x ε := by
      -- We'll use that $\frac{\log x}{\log \log x}$ grows faster than any linear function in $x$.
      have h_log_growth : Filter.Tendsto (fun x => (1 / 2 - ε) * Real.log x / Real.log (Real.log x)) Filter.atTop Filter.atTop := by
        -- We can use the change of variables $u = \log x$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u => (1 / 2 - ε) * u / Real.log u) Filter.atTop Filter.atTop by
          exact h_log.comp ( Real.tendsto_log_atTop );
        -- We can use the fact that $\frac{u}{\log u}$ tends to infinity as $u$ tends to infinity.
        have h_log : Filter.Tendsto (fun u => u / Real.log u) Filter.atTop Filter.atTop := by
          -- We can use the change of variables $v = \log u$ to transform the limit expression.
          suffices h_log : Filter.Tendsto (fun v : ℝ => Real.exp v / v) Filter.atTop Filter.atTop by
            have := h_log.comp Real.tendsto_log_atTop;
            exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
          simpa using Real.tendsto_exp_div_pow_atTop 1;
        simpa only [ mul_div_assoc ] using h_log.const_mul_atTop ( by linarith );
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop 1 ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun x hx ↦ Nat.le_floor <| by simpa using hN x hx ⟩

/-
Lemma: For sufficiently large x, and n defined as product of primes in (x, 2x], the divisors with y prime factors are strictly between x^y and (2x)^y.
-/
set_option linter.style.refine false in
set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma D_set_bounds_Ioc (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, ∀ d ∈ D_set_Ioc x ε,
      (x ^ (y_val x ε) : ℝ) < d ∧ (d : ℝ) < ((2 * x) ^ (y_val x ε)) := by
        -- For sufficiently large $x$, $y = y\_val(x, \epsilon) \ge 2$.
        have hy_ge_2 : ∃ N, ∀ x ≥ N, 2 ≤ y_val x ε := by
          -- We'll use that $y_val(x, \epsilon)$ grows without bound as $x$ increases.
          have hy_val_unbounded : Filter.Tendsto (fun x : ℝ => y_val x ε) Filter.atTop Filter.atTop := by
            -- We'll use that $y_val(x, \epsilon)$ grows without bound as $x$ tends to infinity.
            have hy_val_growth : Filter.Tendsto (fun x : ℝ => (1 / 2 - ε) * Real.log x / Real.log (Real.log x)) Filter.atTop Filter.atTop := by
              -- We can use the change of variables $u = \log x$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u : ℝ => (1 / 2 - ε) * u / Real.log u) Filter.atTop Filter.atTop by
                exact h_log.comp ( Real.tendsto_log_atTop );
              -- We can use the change of variables $v = \log u$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun v : ℝ => (1 / 2 - ε) * Real.exp v / v) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with u hu using by rw [ Function.comp_apply, Real.exp_log hu ] );
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop ( by linarith ) ( Real.tendsto_exp_div_pow_atTop 1 );
            exact tendsto_nat_floor_atTop.comp hy_val_growth;
          exact Filter.eventually_atTop.mp ( hy_val_unbounded.eventually_ge_atTop 2 );
        -- By definition of $D_set_Ioc$, for any $d \in D_set_Ioc x ε$, $d$ is a product of $y_val x ε$ distinct primes all in the interval $(x, 2x]$.
        have hd_bounds : ∀ x : ℝ, ∀ d ∈ D_set_Ioc x ε, ∃ s : Finset ℕ, s.card = y_val x ε ∧ (∀ p ∈ s, Nat.Prime p ∧ x < p ∧ p ≤ 2 * x) ∧ d = s.prod (fun p => p) := by
          intros x d hd
          obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s.card = y_val x ε ∧ (∀ p ∈ s, Nat.Prime p ∧ p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))) ∧ d = s.prod (fun p => p) := by
            have h_divisors : ∀ d ∈ Nat.divisors (n_val_Ioc x), d.factorization.support.card = (Nat.primeFactors d).card ∧ (∀ p ∈ Nat.primeFactors d, p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))) → d = (Nat.primeFactors d).prod (fun p => p) := by
              intros d hd h_prime_factors
              have h_square_free : Squarefree d := by
                have h_square_free : Squarefree (n_val_Ioc x) := by
                  have h_square_free : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (S.prod (fun p => p)) := by
                    intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
                    exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
                  exact h_square_free fun p hp => Finset.mem_filter.mp hp |>.2;
                exact h_square_free.squarefree_of_dvd <| Nat.dvd_of_mem_divisors hd;
              rw [ Nat.prod_primeFactors_of_squarefree h_square_free ];
            refine' ⟨ d.primeFactors, _, _, h_divisors d _ _ ⟩ <;> norm_num at *;
            · exact Finset.mem_filter.mp hd |>.2;
            · intro p pp dp _; have := Nat.dvd_trans dp ( show d ∣ n_val_Ioc x from ?_ ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
              · unfold n_val_Ioc at this; simp_all +decide [Nat.coprime_prod_right_iff]
                obtain ⟨ q, hq₁, hq₂, hq₃, hq₄ ⟩ := this; have := Nat.coprime_primes pp hq₃; aesop;
              · exact Finset.mem_filter.mp hd |>.1 |> fun h => Nat.dvd_of_mem_divisors h;
            · exact ⟨ Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hd |>.1, Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ⟩;
            · intro p pp dp hd; have := Nat.dvd_trans dp ( show d ∣ n_val_Ioc x from ?_ ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
              · unfold n_val_Ioc at this; simp_all +decide [ Nat.coprime_prod_right_iff ] ;
                obtain ⟨ q, hq₁, hq₂, hq₃, hq₄ ⟩ := this; have := Nat.coprime_primes pp hq₃; aesop;
              · exact Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp ‹_› |>.1;
          use s;
          field_simp;
          exact ⟨ hs.1, fun p hp => ⟨ hs.2.1 p hp |>.1, by have := hs.2.1 p hp |>.2; rw [ Finset.mem_Ioc ] at this; exact Nat.lt_of_floor_lt this.1, by have := hs.2.1 p hp |>.2; rw [ Finset.mem_Ioc ] at this; exact by rw [ mul_comm ] ; exact Nat.floor_le ( show 0 ≤ 2 * x from le_of_not_gt fun h => by { rw [ Nat.floor_of_nonpos h.le ] at this; linarith } ) |> le_trans ( mod_cast this.2 ) ⟩, hs.2.2 ⟩;
        obtain ⟨ N, hN ⟩ := hy_ge_2; use Max.max N 2; intros x hx d hd; obtain ⟨ s, hs₁, hs₂, rfl ⟩ := hd_bounds x d hd; simp_all +decide ;
        constructor;
        · exact lt_of_le_of_lt ( by norm_num [ ← hs₁ ] ) ( Finset.prod_lt_prod ( fun a _ ↦ by linarith [ hs₂ a ‹_› ] ) ( fun a _ ↦ by linarith [ hs₂ a ‹_› ] ) ( show ∃ a, a ∈ s ∧ ( a : ℝ ) > x from Exists.elim ( Finset.card_pos.mp ( by linarith [ hN x hx.1 ] ) ) fun p hp ↦ ⟨ p, hp, hs₂ p hp |>.2.1 ⟩ ) );
        · -- Since the primes are distinct and $y \ge 2$, the upper bound is strict: $d < (2x)^y$.
          have h_upper_bound : ∏ p ∈ s, (p : ℝ) < ∏ p ∈ s, (2 * x) := by
            apply Finset.prod_lt_prod;
            · exact fun p hp => Nat.cast_pos.mpr ( Nat.Prime.pos ( hs₂ p hp |>.1 ) );
            · exact fun p hp => hs₂ p hp |>.2.2;
            · by_contra h_contra; push Not at h_contra; (
              -- If all primes in $s$ are equal to $2x$, then $s$ can contain at most one prime, contradicting $y_val x ε \ge 2$.
              have h_card : s.card ≤ 1 := by
                exact Finset.card_le_one.mpr fun p hp q hq => Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ hs₂ p hp, hs₂ q hq, h_contra p hp, h_contra q hq ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ hs₂ p hp, hs₂ q hq, h_contra p hp, h_contra q hq ] } );
              linarith [ hN x hx.1 ]);
          aesop

/-
Lemma: Any prime factor of a divisor of n_val_Ioc(x) is in the interval (floor(x), floor(2x)].
-/
lemma prime_factors_of_divisor_of_n_val_Ioc (x : ℝ) (d : ℕ) (hd : d ∣ n_val_Ioc x) :
    ∀ p ∈ d.primeFactors, p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x)) := by
      intro p hp; have := Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) hd; simp_all +decide [ n_val_Ioc ] ;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      obtain ⟨ q, hq₁, hq₂, hq₃, hq₄ ⟩ := this; have := Nat.coprime_primes hp.1 hq₃; aesop;

/-
Gap Lemma Lower: For sufficiently large x, divisors with fewer than y factors are smaller than x^y.
-/
set_option linter.flexible false in
lemma gap_lemma_lower (ε : ℝ) :
    ∃ N, ∀ x ≥ N, ∀ d, d ∣ n_val_Ioc x →
      d.primeFactors.card < y_val x ε → (d : ℝ) < x ^ (y_val x ε) := by
        -- Let $N$ be a number such that for all $x \geq N$, $x > 2$.
        obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ x ≥ N, x > 2 := by
          exact ⟨ 3, fun x hx => by linarith ⟩;
        -- Therefore, $d \leq (2x)^{d.primeFactors.card}$.
        have h_divisor_bound : ∀ x ≥ N, ∀ d, d ∣ n_val_Ioc x → d ≤ (2 * x) ^ (d.primeFactors.card : ℕ) := by
          intros x hx d hd
          have h_prime_factors_bound : ∀ p ∈ d.primeFactors, p ≤ 2 * x := by
            intros p hp
            have h_prime_factor_bound : p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x)) := by
              exact prime_factors_of_divisor_of_n_val_Ioc x d hd p hp;
            exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp h_prime_factor_bound |>.2 ) <| Nat.floor_le <| by linarith [ hN x hx ] ;
          have h_divisor_bound : d ≤ (∏ p ∈ d.primeFactors, p) := by
            rw [ Nat.prod_primeFactors_of_squarefree ];
            have h_squarefree : Squarefree (n_val_Ioc x) := by
              have h_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
                intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
                exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
              exact h_squarefree fun p hp => Finset.mem_filter.mp hp |>.2;
            exact h_squarefree.squarefree_of_dvd hd;
          exact le_trans ( Nat.cast_le.mpr h_divisor_bound ) ( by simpa using Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) h_prime_factors_bound );
        -- Since $y_val x ε \geq 1$ for sufficiently large $x$, we have $(2x)^{y_val x ε - 1} < x^{y_val x ε}$.
        have h_exp_bound : ∃ N' : ℝ, ∀ x ≥ N', y_val x ε ≥ 1 → (2 * x) ^ (y_val x ε - 1) < x ^ (y_val x ε) := by
          -- Since $y_val x ε \geq 1$ for sufficiently large $x$, we have $(2x)^{y_val x ε - 1} < x^{y_val x ε}$ by properties of exponents.
          have h_exp_bound : ∃ N' : ℝ, ∀ x ≥ N', y_val x ε ≥ 1 → (2 : ℝ) ^ (y_val x ε - 1) < x := by
            -- Since $y_val x ε \geq 1$ for sufficiently large $x$, we have $2^{y_val x ε - 1} < x$ by properties of exponents.
            have h_exp_bound : ∃ N' : ℝ, ∀ x ≥ N', y_val x ε ≥ 1 → (y_val x ε - 1) * Real.log 2 < Real.log x := by
              -- Since $y_val x ε \geq 1$ for sufficiently large $x$, we have $y_val x ε \leq \frac{(1 / 2 - ε) \log x}{\log \log x}$.
              have h_y_val_bound : ∃ N' : ℝ, ∀ x ≥ N', y_val x ε ≥ 1 → y_val x ε ≤ (1 / 2 - ε) * Real.log x / Real.log (Real.log x) := by
                use 3;
                intro x hx₁ hx₂; rw [ le_div_iff₀ ] <;> norm_num [ y_val ] at *;
                · exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.floor_le ( by positivity ) ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) ) ( by rw [ div_mul_cancel₀ _ ( ne_of_gt ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ] );
                · exact Real.log_pos <| by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith;
              -- Since $\frac{(1 / 2 - ε) \log x}{\log \log x} \cdot \log 2 < \log x$ for sufficiently large $x$, we can conclude.
              have h_final_bound : ∃ N' : ℝ, ∀ x ≥ N', (1 / 2 - ε) * Real.log x / Real.log (Real.log x) * Real.log 2 < Real.log x := by
                -- We can divide both sides by $\log x$ (which is positive for $x > 1$) to get $(1 / 2 - ε) * \log 2 < \log \log x$.
                suffices h_div : ∃ N' : ℝ, ∀ x ≥ N', (1 / 2 - ε) * Real.log 2 < Real.log (Real.log x) by
                  obtain ⟨ N', hN' ⟩ := h_div; use Max.max N' 3; intro x hx; rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ hN' x ( le_trans ( le_max_left _ _ ) hx ), Real.log_pos ( show 1 < x by linarith [ le_max_right N' 3 ] ), Real.log_pos ( show 1 < Real.log x by rw [ Real.lt_log_iff_exp_lt ( by linarith [ le_max_right N' 3 ] ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ le_max_right N' 3 ] ) ) ] ;
                have h_log_log : Filter.Tendsto (fun x => Real.log (Real.log x)) Filter.atTop Filter.atTop := by
                  exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop;
                exact Filter.eventually_atTop.mp ( h_log_log.eventually_gt_atTop ( ( 1 / 2 - ε ) * Real.log 2 ) ) |> fun ⟨ N', hN' ⟩ => ⟨ N', fun x hx => hN' x hx ⟩;
              exact ⟨ Max.max h_y_val_bound.choose h_final_bound.choose, fun x hx hx' => by nlinarith [ h_y_val_bound.choose_spec x ( le_trans ( le_max_left _ _ ) hx ) hx', h_final_bound.choose_spec x ( le_trans ( le_max_right _ _ ) hx ), Real.log_pos one_lt_two ] ⟩;
            obtain ⟨ N', hN' ⟩ := h_exp_bound; use Max.max N' 2; intro x hx hx'; specialize hN' x ( le_trans ( le_max_left _ _ ) hx ) hx'; rcases n : y_val x ε with ( _ | _ | n ) <;> simp_all +decide ;
            · linarith;
            · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by linarith ), Real.log_pow ] ; aesop;
          obtain ⟨ N', hN' ⟩ := h_exp_bound; use Max.max N' 2; intro x hx hx'; specialize hN' x ( le_trans ( le_max_left _ _ ) hx ) hx'; rcases k : y_val x ε with ( _ | _ | k ) <;> simp_all +decide [mul_pow] ;
          convert mul_lt_mul_of_pos_right hN' ( pow_pos ( by linarith : 0 < x ) ( ‹_› + 1 ) ) using 1 ; ring;
        obtain ⟨ N', hN' ⟩ := h_exp_bound;
        use Max.max N N';
        intros x hx d hd hcard
        have h_exp : (2 * x) ^ (d.primeFactors.card : ℕ) ≤ (2 * x) ^ (y_val x ε - 1) := by
          exact pow_le_pow_right₀ ( by linarith [ hN x ( le_trans ( le_max_left _ _ ) hx ) ] ) ( Nat.le_pred_of_lt hcard );
        exact lt_of_le_of_lt ( h_divisor_bound x ( le_trans ( le_max_left _ _ ) hx ) d hd ) ( lt_of_le_of_lt h_exp ( hN' x ( le_trans ( le_max_right _ _ ) hx ) ( by linarith ) ) )

/-
Gap Lemma Upper: For sufficiently large x, divisors with more than y factors are larger than (2x)^y.
-/
set_option linter.style.refine false in
lemma gap_lemma_upper (ε : ℝ) :
    ∃ N, ∀ x ≥ N, ∀ d, d ∣ n_val_Ioc x →
      d.primeFactors.card > y_val x ε → (d : ℝ) > (2 * x) ^ (y_val x ε) := by
        -- Let's choose any $x \geq N$.
        by_contra h_contra;
        obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, ∀ x ≥ N₁, y_val x ε ≥ 1 := by
          apply y_val_pos;
          contrapose! h_contra;
          -- Since ε ≥ 1 / 2, we have y_val x ε ≤ 0 for sufficiently large x.
          have hy_val_nonpos : ∃ N : ℝ, ∀ x ≥ N, y_val x ε ≤ 0 := by
            use 3; intro x hx; unfold y_val; norm_num [ Nat.floor_le ] ;
            exact lt_of_le_of_lt ( div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( by linarith ) ( Real.log_nonneg ( by linarith ) ) ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) ) ( by norm_num );
          obtain ⟨ N, hN ⟩ := hy_val_nonpos; use Max.max N 2; intros x hx d hd hd'; specialize hN x ( le_trans ( le_max_left _ _ ) hx ) ; aesop;
        obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℝ, ∀ x ≥ N₂, ∀ p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x)), Nat.Prime p → (p : ℝ) ≥ x := by
          exact ⟨ 0, fun x hx p hp hp' => le_of_lt <| Nat.lt_of_floor_lt <| Finset.mem_Ioc.mp hp |>.1 ⟩
        obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℝ, ∀ x ≥ N₃, ∀ d, d ∣ n_val_Ioc x → d.primeFactors.card > y_val x ε → (d : ℝ) ≥ (x : ℝ) ^ (d.primeFactors.card) := by
          -- By combining the results from hN₂ and the fact that the product of primes in (x, 2x] is at least x^k for any k, we can conclude that there exists an N₃ such that for x ≥ N₃, the product of the primes in the prime factors of d is at least x^k.
          use max N₂ 1;
          intros x hx d hd hd_card
          have h_prod_ge_x_k : (∏ p ∈ d.primeFactors, p : ℝ) ≥ x ^ (d.primeFactors.card) := by
            have h_prod_ge_x_k : ∀ p ∈ d.primeFactors, (p : ℝ) ≥ x := by
              intros p hp
              have hp_interval : p ∈ Finset.Ioc (Nat.floor x) (Nat.floor (2 * x)) := by
                apply prime_factors_of_divisor_of_n_val_Ioc x d hd p hp |> fun h => by simpa using h;
              generalize_proofs at *;
              exact hN₂ x (le_trans (le_max_left _ _) hx) p hp_interval (Nat.prime_of_mem_primeFactors hp) |> le_trans <| by norm_num;
            exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by linarith [ le_max_right N₂ 1 ] ) h_prod_ge_x_k );
          refine le_trans h_prod_ge_x_k ?_;
          rw [ ← Nat.cast_prod ] ; exact mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.prod_primeFactors_dvd _ ) ;
        obtain ⟨N₄, hN₄⟩ : ∃ N₄ : ℝ, ∀ x ≥ N₄, (x : ℝ) ^ (y_val x ε + 1) > (2 * x) ^ (y_val x ε) := by
          -- We can choose $N₄$ such that for all $x ≥ N₄$, we have $x > 2^{y_val x ε}$.
          obtain ⟨N₄, hN₄⟩ : ∃ N₄ : ℝ, ∀ x ≥ N₄, x > 2 ^ (y_val x ε) := by
            -- We can choose $N₄$ such that for all $x ≥ N₄$, we have $x > 2^{y_val x ε}$ by using the fact that $y_val x ε$ grows slower than $x$.
            have h_y_val_growth : Filter.Tendsto (fun x : ℝ => (y_val x ε : ℝ) / Real.log x) Filter.atTop (nhds 0) := by
              -- We'll use the fact that $y_val x ε$ is approximately $(1 / 2 - ε) * \log x / \log \log x$.
              have h_y_val_approx : Filter.Tendsto (fun x : ℝ => ((1 / 2 - ε) * Real.log x / Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
                -- We can simplify the expression inside the limit.
                suffices h_simplify : Filter.Tendsto (fun x : ℝ => (1 / 2 - ε) / Real.log (Real.log x)) Filter.atTop (nhds 0) by
                  refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ eq_div_iff ( ne_of_gt <| Real.log_pos hx ) ] ; ring );
                exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
              have h_y_val_approx : ∀ x ≥ 3, ((y_val x ε : ℝ) / Real.log x) ≤ ((1 / 2 - ε) * Real.log x / Real.log (Real.log x)) / Real.log x + 1 / Real.log x := by
                intro x hx; rw [ ← add_div, div_le_div_iff_of_pos_right ( Real.log_pos <| by linarith ) ] ; norm_num [ y_val ] ;
                exact le_add_of_le_of_nonneg ( Nat.floor_le ( show 0 ≤ ( 1 / 2 - ε ) * Real.log x / Real.log ( Real.log x ) from div_nonneg ( mul_nonneg ( sub_nonneg.2 <| by
                                                                by_cases hε_half : ε > 1 / 2;
                                                                · have h_contra : ∃ N, ∀ x ≥ N, y_val x ε ≤ 0 := by
                                                                    exact ⟨ 3, fun x hx => Nat.le_of_lt_succ <| by rw [ y_val ] ; exact Nat.floor_lt' ( by positivity ) |>.2 <| by norm_num; nlinarith [ Real.log_pos <| show 1 < x by linarith, Real.log_le_log ( by linarith ) hx, Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith, mul_div_cancel₀ ( ( 1 / 2 - ε ) * Real.log x ) <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith ] ⟩;
                                                                  exact absurd ( h_contra.choose_spec ( Max.max N₁ ( Max.max N₂ ( Max.max N₃ h_contra.choose ) ) ) ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) ) ( not_le_of_gt ( hN₁ _ ( le_max_left _ _ ) ) );
                                                                · linarith ) <| Real.log_nonneg <| by linarith ) <| Real.log_nonneg <| show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le <| by linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) ) zero_le_one;
              have h_y_val_approx : Filter.Tendsto (fun x : ℝ => ((1 / 2 - ε) * Real.log x / Real.log (Real.log x)) / Real.log x + 1 / Real.log x) Filter.atTop (nhds 0) := by
                simpa using Filter.Tendsto.add ‹Filter.Tendsto ( fun x : ℝ => ( 1 / 2 - ε ) * Real.log x / Real.log ( Real.log x ) / Real.log x ) Filter.atTop ( _ ) › ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) );
              refine' squeeze_zero_norm' _ h_y_val_approx;
              filter_upwards [ Filter.eventually_ge_atTop 3 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by linarith ) ) ) ] ; exact ‹∀ x ≥ 3, ( y_val x ε : ℝ ) / Real.log x ≤ ( 1 / 2 - ε ) * Real.log x / Real.log ( Real.log x ) / Real.log x + 1 / Real.log x› x hx;
            -- Since $(y_val x ε) / \log x$ tends to $0$, there exists some $N₄$ such that for all $x ≥ N₄$, $(y_val x ε) / \log x < 1 / \log 2$.
            obtain ⟨N₄, hN₄⟩ : ∃ N₄ : ℝ, ∀ x ≥ N₄, (y_val x ε : ℝ) / Real.log x < 1 / Real.log 2 := by
              simpa using h_y_val_growth.eventually ( gt_mem_nhds <| by positivity );
            use Max.max N₄ 2; intro x hx; specialize hN₄ x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ div_lt_div_iff₀ ] at hN₄ <;> norm_num at *;
            · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by linarith ), Real.log_pow ] ; linarith;
            · exact Real.log_pos <| by linarith;
            · positivity;
          use Max.max N₄ 2; intro x hx; specialize hN₄ x ( le_trans ( le_max_left _ _ ) hx ) ; norm_num [ mul_pow, pow_add ] at *; (
          nlinarith [ pow_pos ( by linarith : 0 < x ) ( y_val x ε ) ]);
        use False.elim (h_contra ⟨Max.max N₁ (Max.max N₂ (Max.max N₃ N₄)), by
          intros x hx d hd hd_card
          have h_exp : (d : ℝ) ≥ x ^ (d.primeFactors.card) := by
            exact hN₃ x ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hx ) d hd hd_card
          have h_exp_gt : x ^ (d.primeFactors.card) > (2 * x) ^ (y_val x ε) := by
            exact lt_of_lt_of_le ( hN₄ x ( by aesop ) ) ( pow_le_pow_right₀ ( by linarith [ show 1 ≤ x from le_trans ( show 1 ≤ N₁ from le_of_not_gt fun h => by have := hN₁ 1 ( by linarith ) ; norm_num [ y_val ] at this ) ( le_trans ( le_max_left _ _ ) hx ) ] ) ( by linarith ) )
          exact lt_of_lt_of_le h_exp_gt h_exp.le⟩)

/-
Definition of count_primes_Ioc(x) and lemma stating that the size of D_set_Ioc is the binomial coefficient (count_primes_Ioc choose y_val).
-/
noncomputable def count_primes_Ioc (x : ℝ) : ℕ :=
  ((Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))).filter Nat.Prime).card

set_option linter.style.refine false in
set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma card_D_set_Ioc_eq_choose (x : ℝ) (ε : ℝ) :
    (D_set_Ioc x ε).card = Nat.choose (count_primes_Ioc x) (y_val x ε) := by
      -- By definition of $D_set_Ioc$, we know that every element in $D_set_Ioc x ε$ is a divisor of $n_val_Ioc x$ with exactly $y_val x ε$ prime factors.
      have h_divisors : D_set_Ioc x ε = Finset.image (fun s => ∏ p ∈ s, p) (Finset.powersetCard (y_val x ε) (Finset.filter Nat.Prime (Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))))) := by
        ext; simp [D_set_Ioc];
        constructor;
        · intro h_div
          obtain ⟨h_div_n, h_card⟩ : ‹_› ∣ n_val_Ioc x ∧ (Nat.primeFactors ‹_›).card = y_val x ε := by
            unfold divisors_with_y_factors at h_div; aesop;
          refine' ⟨ _, ⟨ _, h_card ⟩, _ ⟩;
          · intro p hp; have := prime_factors_of_divisor_of_n_val_Ioc x _ h_div_n p hp; aesop;
          · rw [ Nat.prod_primeFactors_of_squarefree ];
            -- Since $n_val_Ioc x$ is squarefree, any divisor of $n_val_Ioc x$ is also squarefree.
            have h_squarefree : Squarefree (n_val_Ioc x) := by
              have h_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
                intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
                exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
              exact h_squarefree fun p hp => Finset.mem_filter.mp hp |>.2;
            exact h_squarefree.squarefree_of_dvd h_div_n;
        · rintro ⟨ s, ⟨ hs₁, hs₂ ⟩, rfl ⟩ ; simp_all +decide [ divisors_with_y_factors ] ;
          refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
          · apply_rules [ Finset.prod_dvd_prod_of_subset ];
          · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2;
          · rw [ Nat.primeFactors_prod ] ; aesop;
            exact fun p hp => Finset.mem_filter.mp ( hs₁ hp ) |>.2;
      unfold count_primes_Ioc; rw [ h_divisors, Finset.card_image_of_injOn ] ; aesop;
      intro s hs t ht h_eq; apply_fun fun s => Nat.primeFactors s at h_eq; simp_all +decide [ Finset.subset_iff, Nat.primeFactors_prod ] ;

/-
Lemma: The divisors in D_set are consecutive in the set of all divisors.
-/
lemma D_set_consecutive (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, ∀ d₁ ∈ D_set_Ioc x ε, ∀ d₂ ∈ D_set_Ioc x ε, d₁ < d₂ →
      ∀ k, k ∣ n_val_Ioc x → d₁ < k → k < d₂ → k ∈ D_set_Ioc x ε := by
        -- By the gap lemma, for large x, the divisors with fewer than y factors are smaller than x^y and those with more than y factors are larger than (2x)^y.
        obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ x ≥ N₁, ∀ d, d ∣ n_val_Ioc x → d.primeFactors.card < y_val x ε → (d : ℝ) < x ^ (y_val x ε) := by
          exact gap_lemma_lower ε
        obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ x ≥ N₂, ∀ d, d ∣ n_val_Ioc x → d.primeFactors.card > y_val x ε → (d : ℝ) > (2 * x) ^ (y_val x ε) := by
          exact gap_lemma_upper ε;
        obtain ⟨N₃, hN₃⟩ : ∃ N₃, ∀ x ≥ N₃, ∀ d₁ ∈ D_set_Ioc x ε, ∀ d₂ ∈ D_set_Ioc x ε, d₁ < d₂ → (d₂ : ℝ) < (2 * x) ^ (y_val x ε) ∧ (d₁ : ℝ) > x ^ (y_val x ε) := by
          obtain ⟨N₃, hN₃⟩ : ∃ N₃, ∀ x ≥ N₃, ∀ d ∈ D_set_Ioc x ε, (x ^ (y_val x ε) : ℝ) < d ∧ (d : ℝ) < ((2 * x) ^ (y_val x ε)) := by
            have := D_set_bounds_Ioc ε hε hε2; aesop;
          exact ⟨ N₃, fun x hx d₁ hd₁ d₂ hd₂ h => ⟨ hN₃ x hx d₂ hd₂ |>.2, hN₃ x hx d₁ hd₁ |>.1 ⟩ ⟩;
        use Max.max N₁ ( Max.max N₂ N₃ );
        intros x hx d₁ hd₁ d₂ hd₂ hlt k hk hk₁ hk₂
        by_contra h_contra
        have h_card : k.primeFactors.card ≠ y_val x ε := by
          exact fun h => h_contra <| Finset.mem_filter.mpr ⟨ Nat.mem_divisors.mpr ⟨ hk, by
            exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ⟩, h ⟩;
        cases lt_or_gt_of_ne h_card <;> simp_all +decide [ D_set_Ioc ];
        · linarith [ hN₁ x hx.1 k hk ‹_›, hN₃ x hx.2.2 d₁ hd₁ d₂ hd₂ hlt, show ( k : ℝ ) ≥ d₁ + 1 by exact_mod_cast hk₁ ];
        · have := hN₂ x hx.2.1 k hk ‹_›;
          linarith [ hN₃ x hx.2.2 d₁ hd₁ d₂ hd₂ hlt, show ( k : ℝ ) < d₂ from mod_cast hk₂ ]

/-
Lemma: If two distinct divisors of n_val_Ioc(x) share a common factor, their difference is greater than x.
-/
set_option linter.style.refine false in
set_option linter.flexible false in
lemma gcd_gt_one_implies_diff_gt_x (x : ℝ) (d₁ d₂ : ℕ) (h₁ : d₁ ∣ n_val_Ioc x) (h₂ : d₂ ∣ n_val_Ioc x) (h_neq : d₁ ≠ d₂) (h_gcd : Nat.gcd d₁ d₂ > 1) :
    |(d₁ : ℤ) - (d₂ : ℤ)| > x := by
      -- Since $g$ divides both $d₁$ and $d₂$, it follows that $g$ is a product of distinct primes in the interval $(x, 2x]$.
      have h_prime_factors : ∀ p ∈ Nat.primeFactors (Nat.gcd d₁ d₂), x < p := by
        intros p hp; have := Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) ( Nat.gcd_dvd_left d₁ d₂ ) ; have := Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) ( Nat.gcd_dvd_right d₁ d₂ ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
        have := prime_factors_of_divisor_of_n_val_Ioc x d₁ h₁ p; have := prime_factors_of_divisor_of_n_val_Ioc x d₂ h₂ p; simp_all +decide [ Nat.dvd_gcd_iff ] ;
        exact Nat.lt_of_floor_lt ( by cases d₁ <;> cases d₂ <;> aesop );
      -- Since $g$ is a product of distinct primes in the interval $(x, 2x]$, we have $g \geq p$ for some prime $p$ in that interval.
      obtain ⟨p, hp_prime, hp_interval⟩ : ∃ p ∈ Nat.primeFactors (Nat.gcd d₁ d₂), x < p := by
        exact ⟨ Nat.minFac _, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime h_gcd.ne', Nat.minFac_dvd _, by aesop ⟩, h_prime_factors _ <| Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime h_gcd.ne', Nat.minFac_dvd _, by aesop ⟩ ⟩;
      have h_div_p : p ∣ Int.natAbs (d₁ - d₂) := by
        exact Int.natAbs_dvd_natAbs.mpr ( dvd_sub ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp_prime ) ( Nat.gcd_dvd_left _ _ ) ) ) ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp_prime ) ( Nat.gcd_dvd_right _ _ ) ) ) );
      refine' lt_of_lt_of_le hp_interval _;
      norm_cast;
      rw [ Int.subNatNat_eq_coe ] ; exact Int.le_of_dvd ( abs_pos.mpr <| sub_ne_zero.mpr <| mod_cast h_neq ) <| by simpa [ ← Int.natCast_dvd_natCast ] using h_div_p;

/-
Lemma: The number of consecutive pairs in D_set that are not coprime is bounded by (2x)^y / x.
-/
set_option linter.style.refine false in
lemma non_coprime_pairs_bound (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N,
      let D := (D_set_Ioc x ε).sort (· ≤ ·)
      let r := D.length
      let non_coprime_count := (List.range (r - 1)).countP (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1)
      (non_coprime_count : ℝ) ≤ (2 * x) ^ (y_val x ε) / x := by
        obtain ⟨N₀, hN₀⟩ := D_set_bounds_Ioc ε hε hε2
        refine' ⟨max N₀ 1, fun x hx => _⟩
        let D := (D_set_Ioc x ε).sort (· ≤ ·)
        let r := D.length
        let B : ℝ := (2 * x) ^ (y_val x ε)
        let bad : Finset ℕ :=
          (Finset.range (r - 1)).filter
            (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1)
        change (((List.range (r - 1)).countP
            (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1) : ℕ) : ℝ) ≤ B / x
        have hxpos : 0 < x := by linarith [le_trans (le_max_right N₀ 1) hx]
        have hB_nonneg : 0 ≤ B := by
          dsimp [B]
          exact pow_nonneg (mul_nonneg zero_le_two hxpos.le) _
        have hD_bounds : ∀ d ∈ D_set_Ioc x ε, (x ^ (y_val x ε) : ℝ) < d ∧ (d : ℝ) < B := by
          intro d hd
          simpa [B] using hN₀ x (le_trans (le_max_left N₀ 1) hx) d hd
        have hsorted : List.Pairwise (· ≤ ·) D := by
          exact Finset.pairwise_sort (D_set_Ioc x ε) (· ≤ ·)
        have hnodup : D.Nodup := by
          simp [D]
        have mem_of_index : ∀ {i : ℕ} (hiD : i < D.length), D[i]'hiD ∈ D_set_Ioc x ε := by
          intro i hiD
          have hmem_list : D[i]'hiD ∈ D := List.getElem_mem hiD
          have hmem_sort : D[i]'hiD ∈ (D_set_Ioc x ε).sort (· ≤ ·) := by
            simpa only [D] using hmem_list
          exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := D[i]'hiD)).mp hmem_sort
        have dvd_of_mem_D : ∀ {d : ℕ}, d ∈ D_set_Ioc x ε → d ∣ n_val_Ioc x := by
          intro d hd
          unfold D_set_Ioc divisors_with_y_factors at hd
          exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
        have abs_int_sub_of_nat_le :
            ∀ a b : ℕ, a ≤ b → ((↑|(a : ℤ) - (b : ℤ)| : ℝ) = (b : ℝ) - a) := by
          intro a b hle
          rw [Int.cast_abs, abs_of_nonpos]
          · push_cast
            ring
          · norm_num
            exact hle
        have gap_nonneg : ∀ i ∈ Finset.range (r - 1), 0 ≤ (D[i + 1]! : ℝ) - D[i]! := by
          intro i hi
          have hi_range : i < r - 1 := Finset.mem_range.mp hi
          have hi0 : i < r := by omega
          have hi1 : i + 1 < r := by omega
          have hi0D : i < D.length := by simpa [r] using hi0
          have hi1D : i + 1 < D.length := by simpa [r] using hi1
          have hle_get : D[i] ≤ D[i + 1] := by
            have hlt_fin : (⟨i, hi0D⟩ : Fin D.length) < ⟨i + 1, hi1D⟩ := by
              exact Nat.lt_succ_self i
            have := hsorted.rel_get_of_lt hlt_fin
            simpa [List.get_eq_getElem] using this
          have hD_i : D[i]! = D[i] := getElem!_pos D i hi0D
          have hD_i1 : D[i + 1]! = D[i + 1] := getElem!_pos D (i + 1) hi1D
          rw [hD_i, hD_i1]
          exact sub_nonneg.mpr (Nat.cast_le.mpr hle_get)
        have bad_gap_ge_x : ∀ i ∈ bad, x ≤ (D[i + 1]! : ℝ) - D[i]! := by
          intro i hi_bad
          have hi_range : i < r - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hi_bad).1
          have hi0 : i < r := by omega
          have hi1 : i + 1 < r := by omega
          have hi0D : i < D.length := by simpa [r] using hi0
          have hi1D : i + 1 < D.length := by simpa [r] using hi1
          have hD_i : D[i]! = D[i] := getElem!_pos D i hi0D
          have hD_i1 : D[i + 1]! = D[i + 1] := getElem!_pos D (i + 1) hi1D
          have hle_get : D[i] ≤ D[i + 1] := by
            have hlt_fin : (⟨i, hi0D⟩ : Fin D.length) < ⟨i + 1, hi1D⟩ := by
              exact Nat.lt_succ_self i
            have := hsorted.rel_get_of_lt hlt_fin
            simpa [List.get_eq_getElem] using this
          have hneq_get : D[i] ≠ D[i + 1] := by
            intro heq
            have hidx : i = i + 1 := (hnodup.getElem_inj_iff (i := i) (j := i + 1)).mp heq
            omega
          have hd₁ : D[i]! ∣ n_val_Ioc x := by
            simpa [hD_i] using dvd_of_mem_D (mem_of_index hi0D)
          have hd₂ : D[i + 1]! ∣ n_val_Ioc x := by
            simpa [hD_i1] using dvd_of_mem_D (mem_of_index hi1D)
          have hneq : D[i]! ≠ D[i + 1]! := by
            simpa [hD_i, hD_i1] using hneq_get
          have hgcd : Nat.gcd (D[i]!) (D[i + 1]!) > 1 := (Finset.mem_filter.mp hi_bad).2
          have hdiff := gcd_gt_one_implies_diff_gt_x x (D[i]!) (D[i + 1]!) hd₁ hd₂ hneq hgcd
          have hle : D[i]! ≤ D[i + 1]! := by
            simpa [hD_i, hD_i1] using hle_get
          have habs : ((↑|(D[i]! : ℤ) - (D[i + 1]! : ℤ)| : ℝ) =
              (D[i + 1]! : ℝ) - D[i]!) := by
            exact abs_int_sub_of_nat_le (D[i]!) (D[i + 1]!) hle
          exact le_of_lt (by rwa [gt_iff_lt, habs] at hdiff)
        have hcount :
            (((List.range (r - 1)).countP
              (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1) : ℕ) : ℝ) = (bad.card : ℝ) := by
          change (Nat.count (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1) (r - 1) : ℝ) = _
          rw [Nat.count_eq_card_filter_range]
        rw [hcount]
        have hbad_sum :
            (bad.card : ℝ) * x ≤ ∑ i ∈ bad, ((D[i + 1]! : ℝ) - D[i]!) := by
          calc
            (bad.card : ℝ) * x = ∑ _i ∈ bad, x := by
              rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ i ∈ bad, ((D[i + 1]! : ℝ) - D[i]!) := by
              exact Finset.sum_le_sum bad_gap_ge_x
        have hbad_subset : bad ⊆ Finset.range (r - 1) := by
          intro i hi
          exact (Finset.mem_filter.mp hi).1
        have hbad_sum_le_all :
            (∑ i ∈ bad, ((D[i + 1]! : ℝ) - D[i]!)) ≤
              ∑ i ∈ Finset.range (r - 1), ((D[i + 1]! : ℝ) - D[i]!) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hbad_subset
            (fun i hi_range _hi_not_bad => gap_nonneg i hi_range)
        have hsum_all :
            (∑ i ∈ Finset.range (r - 1), ((D[i + 1]! : ℝ) - D[i]!)) =
              (D[r - 1]! : ℝ) - D[0]! := by
          simpa using Finset.sum_range_sub (fun i => (D[i]! : ℝ)) (r - 1)
        have hsum_all_le_B :
            (∑ i ∈ Finset.range (r - 1), ((D[i + 1]! : ℝ) - D[i]!)) ≤ B := by
          rw [hsum_all]
          by_cases hr : r = 0
          · simp [hr, hB_nonneg]
          · have hlast : r - 1 < r := Nat.sub_one_lt hr
            have hlastD : r - 1 < D.length := by simpa [r] using hlast
            have hlast_get : D[r - 1]! = D[r - 1] := getElem!_pos D (r - 1) hlastD
            have hlast_mem : D[r - 1] ∈ D_set_Ioc x ε := by
              simpa using mem_of_index hlastD
            have hlast_lt : (D[r - 1]! : ℝ) < B := by
              simpa [hlast_get] using (hD_bounds (D[r - 1]) hlast_mem).2
            calc
              (D[r - 1]! : ℝ) - D[0]! ≤ (D[r - 1]! : ℝ) := by
                exact sub_le_self _ (Nat.cast_nonneg _)
              _ ≤ B := le_of_lt hlast_lt
        have hmul_le : (bad.card : ℝ) * x ≤ B :=
          le_trans hbad_sum (le_trans hbad_sum_le_all hsum_all_le_B)
        rw [le_div_iff₀ hxpos]
        exact hmul_le

/-
For $1 \le k \le n$, $\binom{n}{k} \ge (n/k)^k$.
-/
lemma choose_ge_pow (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) : (n.choose k : ℝ) ≥ ((n : ℝ) / k) ^ k := by
  field_simp;
  -- We'll use the fact that $\binom{n}{k} = \frac{n(n-1)\cdots(n-k+1)}{k!}$ and show that each term in the numerator is at least $n/k$.
  have h_prod : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥ (n / k : ℝ) ^ k * (Nat.factorial k) := by
    have h_prod : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥ (∏ i ∈ Finset.range k, (n / k : ℝ)) * (∏ i ∈ Finset.range k, (k - i : ℝ)) := by
      rw [ ← Finset.prod_mul_distrib ];
      exact Finset.prod_le_prod ( fun _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith [ Finset.mem_range.mp ‹_› ] ) ) ) ) fun i hi => by nlinarith [ show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( n : ℝ ) ≥ k by norm_cast, div_mul_cancel₀ ( n : ℝ ) ( show ( k : ℝ ) ≠ 0 by positivity ) ] ;
    convert h_prod using 1 ; norm_num [ Finset.prod_range_succ' ];
    exact congrArg₂ _ ( by ring ) ( Nat.recOn k ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.prod_range_succ' ] ; ring );
  -- Recall that $\binom{n}{k} = \frac{n(n-1)\cdots(n-k+1)}{k!}$.
  have h_binom : (Nat.choose n k : ℝ) = (∏ i ∈ Finset.range k, (n - i : ℝ)) / (Nat.factorial k) := by
    field_simp;
    rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ Nat.descFactorial_eq_prod_range ];
    rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
  rw [ h_binom, le_div_iff₀ ] <;> first | positivity | linarith;

/-
The number of primes in (x, 2x] is at least log(product of primes) / log(2x).
-/
lemma count_primes_ge_log_n_val_div_log_2x (x : ℝ) (hx : x > 1) :
    (count_primes_Ioc x : ℝ) ≥ Real.log (n_val_Ioc x) / Real.log (2 * x) := by
      -- By definition, $\log (n\_val\_Ioc x) = \sum_{p \in (x, 2x]} \log p$.
      have h_log_sum : Real.log (n_val_Ioc x) = ∑ p ∈ (Finset.filter Nat.Prime (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊)), Real.log p := by
        unfold n_val_Ioc; erw [ Nat.cast_prod ] ; rw [ Real.log_prod ] ; aesop;
      -- Each term in this sum is at most $\log (2x)$, so the sum is at most $count\_primes\_Ioc(x) \cdot \log(2x)$.
      have h_sum_le : ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊), Real.log p ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊), Real.log (2 * x) := by
        gcongr;
        · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp ‹_› |>.2 ) );
        · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp ‹_› |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
      rw [ ge_iff_le, div_le_iff₀ ( Real.log_pos <| by linarith ) ] ; aesop

/-
Assuming PNT, for sufficiently large x, the number of primes in (x, 2x] is greater than x / (2 log x).
-/
set_option linter.style.refine false in
lemma count_primes_lower_bound_of_PNT (hPNT : PNT_statement) :
    ∃ N, ∀ x ≥ N, (count_primes_Ioc x : ℝ) > x / (2 * Real.log x) := by
      -- From PNT, we know that for sufficiently large x, log(n_val_Ioc x) > 0.9 * x.
      have h_log_bound : ∃ N, ∀ x ≥ N, Real.log (n_val_Ioc x) > 0.9 * x := by
        have := hPNT.eventually ( lt_mem_nhds <| show 1 > 0.9 by norm_num );
        rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ Max.max N 1, fun x hx => by have := hN x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ lt_div_iff₀ ] at this <;> linarith [ le_max_right N 1 ] ⟩ ;
      -- From PNT, we know that for sufficiently large x, log(n_val_Ioc x) > 0.9 * x. Therefore, count_primes_Ioc x > 0.9 * x / log(2x).
      obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ x ≥ N₁, (count_primes_Ioc x : ℝ) > 0.9 * x / Real.log (2 * x) := by
        have h_count_bound : ∀ x : ℝ, x > 1 → (count_primes_Ioc x : ℝ) ≥ (Real.log (n_val_Ioc x)) / (Real.log (2 * x)) := by
          exact fun x a => count_primes_ge_log_n_val_div_log_2x x a;
        exact ⟨ Max.max 2 h_log_bound.choose, fun x hx => lt_of_lt_of_le ( div_lt_div_iff_of_pos_right ( Real.log_pos <| by linarith [ le_max_left 2 h_log_bound.choose, le_max_right 2 h_log_bound.choose ] ) |>.2 <| h_log_bound.choose_spec x <| le_trans ( le_max_right _ _ ) hx ) <| h_count_bound x <| by linarith [ le_max_left 2 h_log_bound.choose, le_max_right 2 h_log_bound.choose ] ⟩;
      -- For sufficiently large x, log(2x) < 1.8 * log(x).
      have h_log_ineq : ∃ N₂, ∀ x ≥ N₂, Real.log (2 * x) < 1.8 * Real.log x := by
        -- We can choose $N₂$ such that for all $x \geq N₂$, $\log(2) < 0.8 \log(x)$.
        use Real.exp (Real.log 2 / 0.8) + 1;
        intro x hx; rw [ Real.log_mul ( by positivity ) ( by linarith [ Real.exp_pos ( Real.log 2 / 0.8 ) ] ) ] ; norm_num at *;
        linarith [ Real.log_exp ( Real.log 2 / ( 4 / 5 ) ), Real.log_lt_log ( by positivity ) ( show x > Real.exp ( Real.log 2 / ( 4 / 5 ) ) by linarith ) ];
      obtain ⟨ N₂, hN₂ ⟩ := h_log_ineq; refine' ⟨ Max.max N₁ ( Max.max N₂ 2 ), fun x hx₁ => _ ⟩ ; specialize hN₁ x ( le_trans ( le_max_left _ _ ) hx₁ ) ; specialize hN₂ x ( le_trans ( le_max_of_le_right <| le_max_left _ _ ) hx₁ ) ; rw [ gt_iff_lt ] at *; rw [ div_lt_iff₀ ] at * <;> ring_nf at * <;> norm_num at *;
      · nlinarith [ Real.log_pos ( by linarith : 1 < x ), Real.log_pos ( by linarith : 1 < x * 2 ) ];
      · exact Real.log_pos ( by linarith );
      · exact Real.log_pos <| by linarith;

/-
Assuming PNT, for sufficiently large x, the number of divisors r is bounded below by (x / (2y log x))^y.
-/
set_option linter.style.refine false in
lemma r_lower_bound (hPNT : PNT_statement) (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, ((D_set_Ioc x ε).card : ℝ) > (x / (2 * (y_val x ε) * Real.log x)) ^ (y_val x ε) := by
      -- Applying the bounds from `card_D_set_Ioc_eq_choose` and `choose_ge_pow`, we get the desired inequality.
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ, ∀ x ≥ N₀, y_val x ε ≥ 1 := by
        exact y_val_pos ε hε2;
      -- Applying the bounds from `card_D_set_Ioc_eq_choose` and `choose_ge_pow`, we get the desired inequality for sufficiently large x.
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, ∀ x ≥ N₁, (count_primes_Ioc x : ℝ) > x / (2 * Real.log x) := by
        exact count_primes_lower_bound_of_PNT hPNT;
      -- Combining the bounds from `card_D_set_Ioc_eq_choose` and `choose_ge_pow`, we get the desired inequality for sufficiently large x.
      obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℝ, ∀ x ≥ N₂, y_val x ε ≤ count_primes_Ioc x := by
        -- Since $count\_primes\_Ioc x$ is the number of primes in $(x, 2x]$, and $y\_val x ε$ is defined as the floor of $((1 / 2 - ε) * log x / log (log x))$, we can use the fact that the number of primes in $(x, 2x]$ is greater than $x / (2 log x)$ for sufficiently large $x$.
        have h_count_primes : ∃ N₂ : ℝ, ∀ x ≥ N₂, count_primes_Ioc x > ((1 / 2 - ε) * Real.log x / Real.log (Real.log x)) := by
          -- We'll use that $x / (2 \log x)$ grows faster than $(1 / 2 - \epsilon) \log x / \log \log x$ for sufficiently large $x$.
          have h_growth : Filter.Tendsto (fun x : ℝ => ((1 / 2 - ε) * Real.log x / Real.log (Real.log x)) / (x / (2 * Real.log x))) Filter.atTop (nhds 0) := by
            -- We can simplify the expression inside the limit.
            suffices h_simplify : Filter.Tendsto (fun x : ℝ => (1 / 2 - ε) * 2 * (Real.log x)^2 / (x * Real.log (Real.log x))) Filter.atTop (nhds 0) by
              convert h_simplify using 2 ; group;
            -- We can use the fact that $\frac{(\log x)^2}{x}$ tends to $0$ as $x$ tends to infinity.
            have h_log_sq_over_x : Filter.Tendsto (fun x : ℝ => (Real.log x)^2 / x) Filter.atTop (nhds 0) := by
              -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
              suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
            convert h_log_sq_over_x.const_mul ( ( 1 / 2 - ε ) * 2 ) |> Filter.Tendsto.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop using 2 ; ring_nf;
            rfl;
          have := h_growth.eventually ( gt_mem_nhds zero_lt_one );
          obtain ⟨ N₂, hN₂ ⟩ := Filter.eventually_atTop.mp this;
          exact ⟨ Max.max N₁ ( Max.max N₂ 2 ), fun x hx => by have := hN₁ x ( le_trans ( le_max_left _ _ ) hx ) ; have := hN₂ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) ; rw [ div_lt_one ( div_pos ( by linarith [ le_max_right N₁ ( Max.max N₂ 2 ), le_max_right N₂ 2 ] ) ( mul_pos zero_lt_two ( Real.log_pos ( by linarith [ le_max_right N₁ ( Max.max N₂ 2 ), le_max_right N₂ 2 ] ) ) ) ) ] at this; linarith ⟩;
        exact ⟨ h_count_primes.choose, fun x hx => Nat.floor_le_of_le <| le_of_lt <| h_count_primes.choose_spec x hx ⟩;
      -- Using the bounds from `card_D_set_Ioc_eq_choose` and `choose_ge_pow`, we get the desired inequality for sufficiently large x.
      have h_bound : ∀ x ≥ max N₀ (max N₁ N₂), (D_set_Ioc x ε).card ≥ ((count_primes_Ioc x : ℝ) / y_val x ε) ^ y_val x ε := by
        intros x hx
        have h_card : (D_set_Ioc x ε).card = Nat.choose (count_primes_Ioc x) (y_val x ε) := by
          exact card_D_set_Ioc_eq_choose x ε;
        convert choose_ge_pow ( count_primes_Ioc x ) ( y_val x ε ) _ _ using 1 <;> aesop;
      refine' ⟨ Max.max N₀ ( Max.max N₁ N₂ ), fun x hx => lt_of_lt_of_le _ ( h_bound x hx ) ⟩ ; refine' pow_lt_pow_left₀ _ _ _ <;> norm_num;
      · convert div_lt_div_iff_of_pos_right ( show ( y_val x ε : ℝ ) > 0 from Nat.cast_pos.mpr ( hN₀ x ( le_trans ( le_max_left _ _ ) hx ) ) ) |>.2 ( hN₁ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ) ) using 1 ; ring;
      · refine' div_nonneg _ _ <;> norm_num at *;
        · contrapose! hN₁;
          exact absurd ( hN₀ 0 ( by linarith ) ) ( by norm_num [ y_val ] );
        · exact mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by linarith [ show 1 ≤ x from le_of_not_gt fun h => by have := hN₀ 1 ( by linarith ) ; norm_num [ y_val ] at this ] ) );
      · linarith [ hN₀ x ( le_trans ( le_max_left _ _ ) hx ) ]


/-
Assuming PNT, log(log(n_val_Ioc x)) / log x tends to 1 as x -> infinity.
-/
lemma log_log_n_sim_log_x (hPNT : PNT_statement) :
    Filter.Tendsto (fun x => Real.log (Real.log (n_val_Ioc x)) / Real.log x) Filter.atTop (nhds 1) := by
      -- From PNT, $\log n \sim x$.
      have h_log_n : Filter.Tendsto (fun x => Real.log (n_val_Ioc x) / x) Filter.atTop (nhds 1) := by
        convert hPNT using 1;
      -- So $\log \log n \sim \log x$.
      have h_log_log_n : Filter.Tendsto (fun x => Real.log (Real.log (n_val_Ioc x)) - Real.log x) Filter.atTop (nhds 0) := by
        have := h_log_n.log;
        simpa using this one_ne_zero |> Filter.Tendsto.congr' ( by filter_upwards [ h_log_n.eventually ( lt_mem_nhds one_pos ) ] with x hx using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] );
      have := h_log_log_n.div_atTop ( Real.tendsto_log_atTop );
      simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ sub_div, div_self <| ne_of_gt <| Real.log_pos hx ] ; ring )

/-
The number of pairs satisfying P in a contiguous sublist s is at most the number of pairs in the full list.
-/
set_option linter.flexible false in
lemma countP_zip_tail_sublist {α : Type*} (l s r : List α) (P : α × α → Bool) :
    (s.zip s.tail).countP P ≤ ((l ++ s ++ r).zip (l ++ s ++ r).tail).countP P := by
      -- The zipped list of l ++ s ++ r is a sublist of the zipped list of l ++ s ++ r ++ [], so the countP of P over s.zip s.tail is less than or equal to the countP of P over the zipped list of l ++ s ++ r.
      have h_sublist : List.Sublist (s.zip s.tail) ((l ++ s ++ r).zip ((l ++ s ++ r).tail)) := by
        induction l generalizing s r with
        | nil =>
          simp_all +decide;
          induction s <;> simp_all +decide [ List.zip ];
          cases ‹List α› <;> simp_all +decide [ List.zipWith ];
        | cons l hl ih =>
          simp_all +decide;
          specialize ih s r; cases s <;> simp_all +decide [ List.zip ] ;
          cases hl <;> aesop;
      exact List.Sublist.countP_le h_sublist

lemma prefix_of_head_mem_of_convex {α : Type*} [LinearOrder α] :
    ∀ (L S : List α),
      List.Pairwise (· ≤ ·) L → L.Nodup →
      List.Pairwise (· ≤ ·) S → S.Nodup →
      (∀ x ∈ S, x ∈ L) →
      (∀ a ∈ S, ∀ b ∈ S, a < b → ∀ x ∈ L, a < x → x < b → x ∈ S) →
      ∀ {a : α} {L' : List α}, L = a :: L' → a ∈ S → S <+: L := by
  classical
  intro L
  induction L with
  | nil =>
      intro S hL_sorted hL_nodup hS_sorted hS_nodup hsub hconv a L' hL_eq haS
      cases hL_eq
  | cons a L ih =>
      intro S hL_sorted hL_nodup hS_sorted hS_nodup hsub hconv a₀ L₀ hL_eq haS
      cases hL_eq
      cases S with
      | nil => cases haS
      | cons b S' =>
          have hb_mem_L : b ∈ a :: L := hsub b (by simp)
          have hle_ab : a ≤ b := by
            rcases (by simpa using hb_mem_L : b = a ∨ b ∈ L) with hba | hb_tail
            · simp [hba]
            · exact List.rel_of_pairwise_cons hL_sorted hb_tail
          have hle_ba : b ≤ a := by
            rcases (by simpa using haS : a = b ∨ a ∈ S') with hab | ha_tail
            · simp [hab]
            · exact List.rel_of_pairwise_cons hS_sorted ha_tail
          have hba : b = a := le_antisymm hle_ba hle_ab
          subst b
          have hL_tail_sorted : List.Pairwise (· ≤ ·) L := List.Pairwise.tail hL_sorted
          have hL_tail_nodup : L.Nodup := (List.nodup_cons.mp hL_nodup).2
          have ha_not_S' : a ∉ S' := (List.nodup_cons.mp hS_nodup).1
          have hS'_sorted : List.Pairwise (· ≤ ·) S' := List.Pairwise.tail hS_sorted
          have hS'_nodup : S'.Nodup := (List.nodup_cons.mp hS_nodup).2
          have hsub' : ∀ x ∈ S', x ∈ L := by
            intro x hxS'
            have hxL : x ∈ a :: L := hsub x (by simp [hxS'])
            rcases (by simpa using hxL : x = a ∨ x ∈ L) with hxa | hx_tail
            · exact False.elim (ha_not_S' (by simpa [hxa] using hxS'))
            · exact hx_tail
          have hconv' : ∀ u ∈ S', ∀ v ∈ S', u < v → ∀ x ∈ L, u < x → x < v → x ∈ S' := by
            intro u hu v hv huv x hxL hux hxv
            have hxS : x ∈ a :: S' := hconv u (by simp [hu]) v (by simp [hv]) huv x (by simp [hxL]) hux hxv
            rcases (by simpa using hxS : x = a ∨ x ∈ S') with hxa | hx_tail
            · have hau : a ≤ u := List.rel_of_pairwise_cons hS_sorted (by simp [hu])
              exact False.elim ((not_lt_of_ge hau) (by simpa [hxa] using hux))
            · exact hx_tail
          have hprefix_tail : S' <+: L := by
            cases L with
            | nil =>
                cases S' with
                | nil => exact ⟨[], rfl⟩
                | cons s S'' =>
                    have hsL : s ∈ ([] : List α) := hsub' s (by simp)
                    cases hsL
            | cons c L'' =>
                cases S' with
                | nil => exact ⟨c :: L'', rfl⟩
                | cons s S'' =>
                    have hL_tail_sorted_cons : List.Pairwise (· ≤ ·) (c :: L'') := hL_tail_sorted
                    have hL_tail_nodup_cons : (c :: L'').Nodup := hL_tail_nodup
                    have hS_tail_sorted_cons : List.Pairwise (· ≤ ·) (s :: S'') := hS'_sorted
                    have hS_tail_nodup_cons : (s :: S'').Nodup := hS'_nodup
                    have hsub_tail_cons : ∀ x ∈ s :: S'', x ∈ c :: L'' := hsub'
                    have hconv_tail_cons : ∀ u ∈ s :: S'', ∀ v ∈ s :: S'', u < v → ∀ x ∈ c :: L'', u < x → x < v → x ∈ s :: S'' := hconv'
                    have hcS' : c ∈ s :: S'' := by
                      have hs_in_tail : s ∈ c :: L'' := hsub_tail_cons s (by simp)
                      have hcle : c ≤ s := by
                        rcases (by simpa using hs_in_tail : s = c ∨ s ∈ L'') with hsc | hs_tail
                        · simp [hsc]
                        · exact List.rel_of_pairwise_cons hL_tail_sorted_cons hs_tail
                      by_cases hcs : c = s
                      · simp [hcs]
                      · have hcslt : c < s := lt_of_le_of_ne hcle hcs
                        have haclt : a < c := by
                          have hle_ac : a ≤ c := List.rel_of_pairwise_cons hL_sorted (by simp)
                          have hne_ac : a ≠ c := by
                            intro hac
                            have ha_not_tail : a ∉ c :: L'' := (List.nodup_cons.mp hL_nodup).1
                            exact ha_not_tail (by simp [hac])
                          exact lt_of_le_of_ne hle_ac hne_ac
                        have haslt : a < s := by
                          have hle_as : a ≤ s := List.rel_of_pairwise_cons hS_sorted (by simp)
                          have hne_as : a ≠ s := by
                            intro has
                            exact ha_not_S' (by simp [has])
                          exact lt_of_le_of_ne hle_as hne_as
                        have hcS : c ∈ a :: s :: S'' := hconv a (by simp) s (by simp) haslt c (by simp) haclt hcslt
                        rcases (by simpa using hcS : c = a ∨ c ∈ s :: S'') with hca | hc_tail
                        · exact False.elim ((ne_of_gt haclt) hca)
                        · exact hc_tail
                    exact ih (s :: S'') hL_tail_sorted_cons hL_tail_nodup_cons hS_tail_sorted_cons
                      hS_tail_nodup_cons hsub_tail_cons hconv_tail_cons rfl hcS'
          rcases hprefix_tail with ⟨t, ht⟩
          exact ⟨t, by simp [ht]⟩

/-
If S is a sorted sublist of a sorted list L, and S is convex in L (contains all intermediate elements), then S is a contiguous sublist of L.
-/
lemma contiguous_sublist_of_convex {α : Type*} [LinearOrder α] (L S : List α)
    (hL_sorted : List.Pairwise (· ≤ ·) L) (hL_nodup : L.Nodup)
    (hS_sorted : List.Pairwise (· ≤ ·) S) (hS_nodup : S.Nodup)
    (hsub : ∀ x ∈ S, x ∈ L)
    (hconv : ∀ a ∈ S, ∀ b ∈ S, a < b → ∀ x ∈ L, a < x → x < b → x ∈ S) :
    ∃ l r, L = l ++ S ++ r := by
  classical
  suffices hInfix : S <:+: L by
    rcases hInfix with ⟨l, r, h⟩
    exact ⟨l, r, h.symm⟩
  revert S
  induction L with
  | nil =>
      intro S hS_sorted hS_nodup hsub hconv
      cases S with
      | nil => exact ⟨[], [], rfl⟩
      | cons s S' =>
          have hs : s ∈ ([] : List α) := hsub s (by simp)
          cases hs
  | cons a L ih =>
      intro S hS_sorted hS_nodup hsub hconv
      by_cases haS : a ∈ S
      · exact (prefix_of_head_mem_of_convex (a :: L) S hL_sorted hL_nodup hS_sorted hS_nodup hsub hconv rfl haS).isInfix
      · have hL_tail_sorted : List.Pairwise (· ≤ ·) L := List.Pairwise.tail hL_sorted
        have hL_tail_nodup : L.Nodup := (List.nodup_cons.mp hL_nodup).2
        have hsub' : ∀ x ∈ S, x ∈ L := by
          intro x hxS
          have hxL : x ∈ a :: L := hsub x hxS
          rcases (by simpa using hxL : x = a ∨ x ∈ L) with hxa | hx_tail
          · exact False.elim (haS (by simpa [hxa] using hxS))
          · exact hx_tail
        have hconv' : ∀ u ∈ S, ∀ v ∈ S, u < v → ∀ x ∈ L, u < x → x < v → x ∈ S := by
          intro u hu v hv huv x hxL hux hxv
          exact hconv u hu v hv huv x (by simp [hxL]) hux hxv
        rcases ih hL_tail_sorted hL_tail_nodup S hS_sorted hS_nodup hsub' hconv' with ⟨l, r, h⟩
        exact ⟨a :: l, r, by simp [h]⟩

/-
For sufficiently large x, tau_perp(n) is at least the number of coprime consecutive pairs in D_set.
-/
lemma tau_perp_ge_D_set_pairs (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, (tau_perp (n_val_Ioc x) : ℝ) ≥
      ((((D_set_Ioc x ε).sort (· ≤ ·)).zip (((D_set_Ioc x ε).sort (· ≤ ·)).tail)).countP (fun (a, b) => Nat.gcd a b = 1) : ℝ) := by
  obtain ⟨N, hN⟩ := D_set_consecutive ε hε hε2
  refine ⟨N, fun x hx => ?_⟩
  let L := (n_val_Ioc x).divisors.sort (· ≤ ·)
  let S := (D_set_Ioc x ε).sort (· ≤ ·)
  let P : ℕ × ℕ → Bool := fun (a, b) => Nat.gcd a b = 1
  have hL_sorted : List.Pairwise (· ≤ ·) L := by
    exact Finset.pairwise_sort (n_val_Ioc x).divisors (· ≤ ·)
  have hL_nodup : L.Nodup := by
    simp [L]
  have hS_sorted : List.Pairwise (· ≤ ·) S := by
    exact Finset.pairwise_sort (D_set_Ioc x ε) (· ≤ ·)
  have hS_nodup : S.Nodup := by
    simp [S]
  have hsub : ∀ d ∈ S, d ∈ L := by
    intro d hdS
    have hdD : d ∈ D_set_Ioc x ε := by
      exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := d)).mp (by simpa [S] using hdS)
    have hdDiv : d ∈ (n_val_Ioc x).divisors := by
      unfold D_set_Ioc divisors_with_y_factors at hdD
      exact (Finset.mem_filter.mp hdD).1
    exact (Finset.mem_sort (s := (n_val_Ioc x).divisors) (r := (· ≤ ·)) (a := d)).mpr (by simpa [L] using hdDiv)
  have hconv : ∀ a ∈ S, ∀ b ∈ S, a < b → ∀ k ∈ L, a < k → k < b → k ∈ S := by
    intro a haS b hbS hab k hkL hak hkb
    have haD : a ∈ D_set_Ioc x ε := by
      exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := a)).mp (by simpa [S] using haS)
    have hbD : b ∈ D_set_Ioc x ε := by
      exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := b)).mp (by simpa [S] using hbS)
    have hkDiv : k ∈ (n_val_Ioc x).divisors := by
      exact (Finset.mem_sort (s := (n_val_Ioc x).divisors) (r := (· ≤ ·)) (a := k)).mp (by simpa [L] using hkL)
    have hkDvd : k ∣ n_val_Ioc x := Nat.dvd_of_mem_divisors hkDiv
    have hkD : k ∈ D_set_Ioc x ε := hN x hx a haD b hbD hab k hkDvd hak hkb
    exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := k)).mpr (by simpa [S] using hkD)
  obtain ⟨l, r, hLR⟩ := contiguous_sublist_of_convex L S hL_sorted hL_nodup hS_sorted hS_nodup hsub hconv
  have hnat : (S.zip S.tail).countP P ≤ (L.zip L.tail).countP P := by
    rw [hLR]
    exact countP_zip_tail_sublist l S r P
  dsimp [tau_perp, P]
  change ((L.zip L.tail).countP (fun x : ℕ × ℕ => x.1.gcd x.2 = 1) : ℝ) ≥
    ((S.zip S.tail).countP (fun x : ℕ × ℕ => x.1.gcd x.2 = 1) : ℝ)
  exact_mod_cast hnat

/-
The number of pairs in (L zip L.tail) satisfying P is equal to the number of indices i such that P(L[i], L[i+1]) holds.
-/
set_option linter.flexible false in
lemma countP_zip_eq_countP_range {α : Type*} [Inhabited α] (L : List α) (P : α × α → Bool) :
    (L.zip L.tail).countP P = (List.range (L.length - 1)).countP (fun i => P (L[i]!, L[i+1]!)) := by
      induction L generalizing P with
      | nil =>
        rfl
      | cons x L ih =>
        cases L <;> simp_all +decide [ List.range_succ_eq_map ];
        rw [ List.countP_cons, List.countP_cons ] ; aesop

/-
The number of pairs in (L zip L.tail) satisfying P is equal to the number of indices i such that P(L[i], L[i+1]) holds.
-/
lemma countP_zip_eq_countP_range_nat (L : List ℕ) (P : ℕ × ℕ → Bool) :
    (L.zip L.tail).countP P = (List.range (L.length - 1)).countP (fun i => P (L[i]!, L[i+1]!)) := by
      convert countP_zip_eq_countP_range L P using 1

/-
For sufficiently large x, tau_perp(n) is at least |D_set| - 1 - (2x)^y/x.
-/
lemma tau_perp_lower_bound_explicit (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, (tau_perp (n_val_Ioc x) : ℝ) ≥ (D_set_Ioc x ε).card - 1 - (2 * x) ^ (y_val x ε) / x := by
  obtain ⟨N₁, hN₁⟩ := tau_perp_ge_D_set_pairs ε hε hε2
  obtain ⟨N₂, hN₂⟩ := non_coprime_pairs_bound ε hε hε2
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  let D := (D_set_Ioc x ε).sort (· ≤ ·)
  let r := D.length
  let good : ℕ := (List.range (r - 1)).countP (fun i => Nat.gcd (D[i]!) (D[i + 1]!) = 1)
  let bad : ℕ := (List.range (r - 1)).countP (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1)
  let E : ℝ := (2 * x) ^ (y_val x ε) / x
  have hTau := hN₁ x (le_trans (le_max_left N₁ N₂) hx)
  have hBad : (bad : ℝ) ≤ E := by
    have h := hN₂ x (le_trans (le_max_right N₁ N₂) hx)
    change (((List.range (r - 1)).countP (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1) : ℕ) : ℝ) ≤ E at h
    simpa [bad] using h
  have hr_card : r = (D_set_Ioc x ε).card := by
    simp [D, r]
  have hpos_index : ∀ {i : ℕ}, i < r → 0 < D[i]! := by
    intro i hi
    have hiD : i < D.length := by simpa [r] using hi
    have hget : D[i]! = D[i] := getElem!_pos D i hiD
    have hmem_list : D[i] ∈ D := List.getElem_mem hiD
    have hmem_D : D[i] ∈ D_set_Ioc x ε := by
      exact (Finset.mem_sort (s := D_set_Ioc x ε) (r := (· ≤ ·)) (a := D[i])).mp (by simpa only [D] using hmem_list)
    have hmem_div : D[i] ∈ (n_val_Ioc x).divisors := by
      unfold D_set_Ioc divisors_with_y_factors at hmem_D
      exact (Finset.mem_filter.mp hmem_D).1
    rw [hget]
    exact Nat.pos_of_mem_divisors hmem_div
  have hnot_good_iff_bad : ∀ i ∈ Finset.range (r - 1),
      (¬Nat.gcd (D[i]!) (D[i + 1]!) = 1) ↔ Nat.gcd (D[i]!) (D[i + 1]!) > 1 := by
    intro i hi
    have hi_range : i < r - 1 := Finset.mem_range.mp hi
    have hi0 : i < r := by omega
    have hgpos : 0 < Nat.gcd (D[i]!) (D[i + 1]!) := Nat.gcd_pos_of_pos_left (D[i + 1]!) (hpos_index hi0)
    constructor
    · intro hne
      omega
    · intro hgt heq
      omega
  have hfilter_eq : {i ∈ Finset.range (r - 1) | ¬Nat.gcd (D[i]!) (D[i + 1]!) = 1} =
      {i ∈ Finset.range (r - 1) | Nat.gcd (D[i]!) (D[i + 1]!) > 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hnot⟩
      exact ⟨hi, (hnot_good_iff_bad i (Finset.mem_range.mpr hi)).mp hnot⟩
    · rintro ⟨hi, hgt⟩
      exact ⟨hi, (hnot_good_iff_bad i (Finset.mem_range.mpr hi)).mpr hgt⟩
  have hgood_count : good = {i ∈ Finset.range (r - 1) | Nat.gcd (D[i]!) (D[i + 1]!) = 1}.card := by
    change Nat.count (fun i => Nat.gcd (D[i]!) (D[i + 1]!) = 1) (r - 1) = _
    rw [Nat.count_eq_card_filter_range]
  have hbad_count : bad = {i ∈ Finset.range (r - 1) | Nat.gcd (D[i]!) (D[i + 1]!) > 1}.card := by
    change Nat.count (fun i => Nat.gcd (D[i]!) (D[i + 1]!) > 1) (r - 1) = _
    rw [Nat.count_eq_card_filter_range]
  have hgood_bad : good + bad = r - 1 := by
    have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range (r - 1))
      (p := fun i => Nat.gcd (D[i]!) (D[i + 1]!) = 1)
    rw [hfilter_eq] at hpart
    rw [hgood_count, hbad_count]
    simpa using hpart
  have hbad_le : bad ≤ r - 1 := by omega
  have hgood_eq : (good : ℝ) = (((r - 1 : ℕ) : ℝ) - (bad : ℝ)) := by
    have hgood_nat : good = (r - 1) - bad := by omega
    rw [hgood_nat, Nat.cast_sub hbad_le]
  have hpred_ge : ((r - 1 : ℕ) : ℝ) ≥ (r : ℝ) - 1 := by
    cases r <;> norm_num
  have hgood_lower : (good : ℝ) ≥ (D_set_Ioc x ε).card - 1 - E := by
    have hr_real : (r : ℝ) = ((D_set_Ioc x ε).card : ℝ) := by exact_mod_cast hr_card
    linarith
  have hzip_good : (((D.zip D.tail).countP (fun (a, b) => Nat.gcd a b = 1) : ℕ) : ℝ) = (good : ℝ) := by
    have hzip := countP_zip_eq_countP_range D (fun (a, b) => Nat.gcd a b = 1)
    change (((D.zip D.tail).countP (fun x : ℕ × ℕ => x.1.gcd x.2 = 1) : ℕ) : ℝ) = (good : ℝ)
    rw [hzip]
  have hTau' : (tau_perp (n_val_Ioc x) : ℝ) ≥ (good : ℝ) := by
    calc
      (tau_perp (n_val_Ioc x) : ℝ) ≥ (((D.zip D.tail).countP (fun (a, b) => Nat.gcd a b = 1) : ℕ) : ℝ) := by
        simpa [D] using hTau
      _ = (good : ℝ) := hzip_good
  exact le_trans hgood_lower hTau'


/-
For sufficiently large x, bound(n, epsilon) < exp((1 / 2 - epsilon + delta) * (log x)^2 / log log x).
-/
set_option linter.style.refine false in
set_option linter.style.multiGoal false in
lemma bound_asymptotic (hPNT : PNT_statement) (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) (δ : ℝ) (hδ : δ > 0) :
    ∃ N, ∀ x ≥ N, bound (n_val_Ioc x) ε < Real.exp ((1 / 2 - ε + δ) * (Real.log x)^2 / Real.log (Real.log x)) := by
      -- By definition of $bound$, we know that for sufficiently large $x$, $(1 / 2 - ε) * (log (log n))^2 / log (log (log n)) < (1 / 2 - ε + δ) * (log x)^2 / log (log x)$.
      have h_bound_lt : Filter.Tendsto (fun x => ((1 / 2 - ε) * (Real.log (Real.log (n_val_Ioc x)))^2 / Real.log (Real.log (Real.log (n_val_Ioc x)))) / ((Real.log x)^2 / Real.log (Real.log x))) Filter.atTop (nhds ((1 / 2 - ε))) := by
        -- We'll use the fact that $\log \log n \sim \log x$ and $\log \log \log n \sim \log \log x$ as $x \to \infty$.
        have h_log_log_n : Filter.Tendsto (fun x => Real.log (Real.log (n_val_Ioc x)) / Real.log x) Filter.atTop (nhds 1) := by
          exact log_log_n_sim_log_x hPNT
        have h_log_log_log_n : Filter.Tendsto (fun x => Real.log (Real.log (Real.log (n_val_Ioc x))) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
          have h_log_log_log_n : Filter.Tendsto (fun x => Real.log (Real.log (Real.log (n_val_Ioc x)) / Real.log x) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
            convert Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_log_log_n _ ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) using 2 ; norm_num;
          have h_log_log_log_n : Filter.Tendsto (fun x => (Real.log (Real.log (Real.log (n_val_Ioc x))) - Real.log (Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
            refine h_log_log_log_n.congr' ( by filter_upwards [ h_log_log_n.eventually ( lt_mem_nhds one_pos ) ] with x hx using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] );
          have := h_log_log_log_n.const_add 1;
          simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ add_div' ] ; ring ; exact ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] );
        convert h_log_log_n.pow 2 |> Filter.Tendsto.mul <| h_log_log_log_n.inv₀ one_ne_zero |> Filter.Tendsto.const_mul ( 1 / 2 - ε ) using 2 <;> ring;
      -- By the definition of limit, there exists an N such that for all x ≥ N, the ratio is within δ of (1 / 2 - ε).
      obtain ⟨N, hN⟩ : ∃ N, ∀ x ≥ N, ((1 / 2 - ε) * (Real.log (Real.log (n_val_Ioc x)))^2 / Real.log (Real.log (Real.log (n_val_Ioc x)))) / ((Real.log x)^2 / Real.log (Real.log x)) < (1 / 2 - ε) + δ := by
        exact Filter.eventually_atTop.mp ( h_bound_lt.eventually ( gt_mem_nhds <| by linarith ) );
      refine' ⟨ Max.max N 4, fun x hx => Real.exp_lt_exp.mpr _ ⟩ ; specialize hN x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ div_lt_iff₀ ] at hN <;> ring_nf at * <;> norm_num at *;
      · linarith;
      · exact mul_pos ( sq_pos_of_pos ( Real.log_pos ( by linarith ) ) ) ( inv_pos.mpr ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) )

/-
The ratio of the error term to the lower bound of r tends to 0.
-/
set_option linter.style.refine false in
set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma error_term_ratio_tendsto_zero (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    Filter.Tendsto (fun x => ((2 * x) ^ (y_val x ε) / x) / ((x / (2 * (y_val x ε) * Real.log x)) ^ (y_val x ε))) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun x => ( 4 * ( y_val x ε : ℝ ) * Real.log x ) ^ ( y_val x ε : ℝ ) / x;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
        by_cases h : y_val x ε = 0 <;> simp_all +decide [mul_comm, mul_assoc, div_eq_mul_inv];
        · rw [ abs_of_pos ( zero_lt_one.trans hx ) ];
        · rw [ abs_of_pos ( by positivity ) ] ; ring_nf ; norm_num [ h ] ;
          rw [ abs_of_nonneg ( Real.log_nonneg hx.le ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_pow ] ; ring_nf ; norm_num [ h ] ;
          norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans hx ) ];
          rw [ mul_left_comm ] ; norm_num [ h, ne_of_gt ( zero_lt_one.trans hx ) ];
      · -- We'll use that $y_val x ε \approx (1 / 2 - ε) \log x / \log \log x$ to simplify the expression.
        have h_y_val_approx : ∀ᶠ x in Filter.atTop, (y_val x ε : ℝ) ≤ (1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1 := by
          refine' Filter.eventually_atTop.mpr ⟨ 3, fun x hx => _ ⟩ ; norm_num [ y_val ];
          exact le_add_of_le_of_nonneg ( Nat.floor_le ( div_nonneg ( mul_nonneg ( by linarith ) ( Real.log_nonneg ( by linarith ) ) ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) ) ) zero_le_one;
        -- Using the approximation $y_val x ε \approx (1 / 2 - ε) \log x / \log \log x$, we can bound the expression.
        have h_bound : ∀ᶠ x in Filter.atTop, (4 * (y_val x ε : ℝ) * Real.log x) ^ (y_val x ε : ℝ) ≤ (Real.log x) ^ (2 * (y_val x ε : ℝ)) := by
          have h_bound : ∀ᶠ x in Filter.atTop, (4 * (y_val x ε : ℝ) * Real.log x) ≤ (Real.log x) ^ 2 := by
            -- By multiplying both sides of the inequality $y_val x ε ≤ (1 / 2 - ε) * log x / log (log x) + 1$ by $4 * log x$, we get $4 * y_val x ε * log x ≤ 4 * [(1 / 2 - ε) * log x / log (log x) + 1] * log x$.
            have h_mul : ∀ᶠ x in Filter.atTop, 4 * (y_val x ε : ℝ) * Real.log x ≤ 4 * ((1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1) * Real.log x := by
              filter_upwards [ h_y_val_approx, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hx₁ <| by norm_num ) <| Real.log_nonneg hx₂.le;
            -- We'll use that $4 * ((1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1) * Real.log x \leq Real.log x ^ 2$ for sufficiently large $x$.
            have h_bound : ∀ᶠ x in Filter.atTop, 4 * ((1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1) ≤ Real.log x := by
              -- We'll use that $4 * ((1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1) \leq Real.log x$ for sufficiently large $x$.
              have h_bound : Filter.Tendsto (fun x => 4 * ((1 / 2 - ε) * Real.log x / Real.log (Real.log x) + 1) / Real.log x) Filter.atTop (nhds 0) := by
                -- We can factor out $4$ and use the fact that $\frac{\log x}{\log \log x}$ tends to $0$ as $x$ tends to infinity.
                have h_factor : Filter.Tendsto (fun x => (Real.log x / Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
                  -- We can simplify the expression inside the limit.
                  suffices h_simplify : Filter.Tendsto (fun x => 1 / Real.log (Real.log x)) Filter.atTop (nhds 0) by
                    refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_right_comm, div_self <| ne_of_gt <| Real.log_pos hx ] );
                  exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
                simp_all +decide [ mul_div_assoc, add_div ];
                simpa using Filter.Tendsto.const_mul 4 ( Filter.Tendsto.add ( h_factor.const_mul ( 2⁻¹ - ε ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) );
              filter_upwards [ h_bound.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ div_lt_iff₀ ( Real.log_pos hx₂ ) ] at hx₁; linarith;
            filter_upwards [ h_mul, h_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using le_trans hx₁ ( by nlinarith [ Real.log_pos hx₃ ] );
          filter_upwards [ h_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using le_trans ( Real.rpow_le_rpow ( by exact mul_nonneg ( mul_nonneg zero_le_four <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by linarith ) hx₁ <| by exact Nat.cast_nonneg _ ) <| by rw [ Real.rpow_mul ( Real.log_nonneg <| by linarith ) ] ; norm_num;
        -- Using the approximation $y_val x ε \approx (1 / 2 - ε) \log x / \log \log x$, we can bound the expression further.
        have h_bound_further : ∀ᶠ x in Filter.atTop, (Real.log x) ^ (2 * (y_val x ε : ℝ)) ≤ x ^ (1 - 2 * ε) * (Real.log x) ^ 2 := by
          -- Using the approximation $y_val x ε \approx (1 / 2 - ε) \log x / \log \log x$, we can bound the expression further by taking the logarithm.
          have h_log_bound : ∀ᶠ x in Filter.atTop, 2 * (y_val x ε : ℝ) * Real.log (Real.log x) ≤ (1 - 2 * ε) * Real.log x + 2 * Real.log (Real.log x) := by
            filter_upwards [ h_y_val_approx, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃;
            rw [ div_add_one, le_div_iff₀ ] at hx₁ <;> nlinarith [ Real.log_pos hx₂, Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ];
          filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
          rw [ Real.rpow_def_of_pos ( Real.log_pos hx₂ ), Real.rpow_def_of_pos ( by positivity ) ];
          rw [ ← Real.log_le_log_iff ( by positivity ) ( by exact mul_pos ( Real.exp_pos _ ) ( sq_pos_of_pos ( Real.log_pos hx₂ ) ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sq_pos_of_pos ( Real.log_pos hx₂ ) ) ), Real.log_exp ] ; norm_num ; linarith;
        -- Using the bounds, we can show that the expression tends to 0.
        have h_tendsto_zero : Filter.Tendsto (fun x => x ^ (1 - 2 * ε) * (Real.log x) ^ 2 / x) Filter.atTop (nhds 0) := by
          -- We can simplify the expression $x^{1 - 2\epsilon} * (\log x)^2 / x$ to $x^{-2\epsilon} * (\log x)^2$.
          suffices h_simplified : Filter.Tendsto (fun x => x ^ (-2 * ε) * (Real.log x) ^ 2) Filter.atTop (nhds 0) by
            refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ show x ^ ( 1 - 2 * ε ) = x ^ ( -2 * ε ) * x by rw [ ← Real.rpow_add_one hx.ne' ] ; ring_nf ] ; rw [ mul_div_right_comm, mul_div_cancel_right₀ _ hx.ne' ] );
          -- Let $y = \log x$, therefore the expression becomes $y^2 e^{-2\epsilon y}$.
          suffices h_log : Filter.Tendsto (fun y => y^2 * Real.exp (-2 * ε * y)) Filter.atTop (nhds 0) by
            have := h_log.comp Real.tendsto_log_atTop;
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring_nf );
          -- Let $z = 2\epsilon y$, therefore the expression becomes $\frac{z^2}{(2\epsilon)^2} e^{-z}$.
          suffices h_z : Filter.Tendsto (fun z => z^2 * Real.exp (-z) / (2 * ε)^2) Filter.atTop (nhds 0) by
            convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < 2 * ε by positivity ) ) using 2 ; norm_num ; ring_nf;
            norm_num [ mul_right_comm, hε.ne' ];
          simpa using Filter.Tendsto.div_const ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 ) _;
        refine' squeeze_zero_norm' _ h_tendsto_zero;
        filter_upwards [ h_bound, h_bound_further, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃ using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.rpow_nonneg ( mul_nonneg ( mul_nonneg zero_le_four ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg hx₃.le ) ) _ ) ( by positivity ) ) ] ; exact div_le_div_of_nonneg_right ( le_trans hx₁ hx₂ ) ( by positivity ) ;

/-
The log of the lower bound of r is asymptotically (1 / 2 - epsilon) * (log x)^2 / log log x.
-/
set_option linter.style.refine false in
lemma log_r_lower_bound_asymptotic (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    Filter.Tendsto (fun x => Real.log ((x / (2 * (y_val x ε) * Real.log x)) ^ (y_val x ε)) / ((Real.log x)^2 / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) := by
      -- Let's simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun x => (y_val x ε : ℝ) * (Real.log x - Real.log (2 * (y_val x ε) * Real.log x)) / (Real.log x ^ 2 / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1, y_val_pos ε hε2 |> Classical.choose_spec |> fun h => Filter.eventually_ge_atTop ( Classical.choose ( y_val_pos ε hε2 ) ) ] with x hx₁ hx₂ ; rw [ Real.log_pow ] ; rw [ Real.log_div ] <;> norm_num <;> try positivity;
        exact ⟨ Nat.ne_of_gt ( Classical.choose_spec ( y_val_pos ε hε2 ) x hx₂ ), by linarith, by linarith, by linarith ⟩;
      -- We'll use the fact that $y_val x ε \sim (1 / 2 - ε) \log x / \log \log x$.
      have h_y_val : Filter.Tendsto (fun x => (y_val x ε : ℝ) / (Real.log x / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) := by
        -- By definition of $y_val$, we know that $y_val x ε \approx (1 / 2 - ε) \cdot \frac{\log x}{\log \log x}$.
        have hy_val_approx : Filter.Tendsto (fun x => (Nat.floor ((1 / 2 - ε) * Real.log x / Real.log (Real.log x))) / ((1 / 2 - ε) * Real.log x / Real.log (Real.log x))) Filter.atTop (nhds 1) := by
          have hy_val_approx : Filter.Tendsto (fun x => (Nat.floor x : ℝ) / x) Filter.atTop (nhds 1) := by
            rw [ Metric.tendsto_nhds ];
            intro ε hε; filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( ε⁻¹ ) ] with x hx₁ hx₂ using abs_lt.mpr ⟨ by nlinarith [ Nat.floor_le hx₁.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₁.ne' ], by nlinarith [ Nat.floor_le hx₁.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₁.ne' ] ⟩ ;
          refine hy_val_approx.comp ?_;
          -- We can use the fact that $\frac{\log x}{\log \log x}$ tends to infinity as $x$ tends to infinity.
          have h_log_log : Filter.Tendsto (fun x => Real.log x / Real.log (Real.log x)) Filter.atTop Filter.atTop := by
            -- We can use the change of variables $u = \log x$ to transform the limit expression.
            suffices h_log : Filter.Tendsto (fun u => u / Real.log u) Filter.atTop Filter.atTop by
              exact h_log.comp ( Real.tendsto_log_atTop );
            -- We can use the change of variables $v = \log u$ to transform the limit expression.
            suffices h_log : Filter.Tendsto (fun v => Real.exp v / v) Filter.atTop Filter.atTop by
              have := h_log.comp Real.tendsto_log_atTop;
              exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
            simpa using Real.tendsto_exp_div_pow_atTop 1;
          simpa only [ mul_div_assoc ] using h_log_log.const_mul_atTop ( by linarith );
        convert hy_val_approx.const_mul ( 1 / 2 - ε ) using 2 <;> ring_nf!;
        unfold y_val; ring_nf;
        grind;
      -- We'll use the fact that $\log(2y \log x) = \log 2 + \log y + \log \log x$.
      suffices h_log : Filter.Tendsto (fun x => (y_val x ε : ℝ) * (Real.log x - (Real.log 2 + Real.log (y_val x ε) + Real.log (Real.log x))) / (Real.log x ^ 2 / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) by
        refine h_log.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1, h_y_val.eventually ( lt_mem_nhds <| show 1 / 2 - ε > 0 by linarith ) ] with x hx₁ hx₂ ; rw [ Real.log_mul, Real.log_mul ] <;> norm_num <;> aesop;
      -- We'll use the fact that $\log(y_val x ε) = \log((1 / 2 - ε) \log x / \log \log x) \sim \log \log x$.
      have h_log_y_val : Filter.Tendsto (fun x => Real.log (y_val x ε) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
        have h_log_y_val : Filter.Tendsto (fun x => Real.log ((y_val x ε : ℝ) / (Real.log x / Real.log (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_y_val <| by linarith ) ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop );
        have h_log_y_val : Filter.Tendsto (fun x => (Real.log (y_val x ε) - Real.log (Real.log x) + Real.log (Real.log (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
          refine h_log_y_val.congr' ?_;
          filter_upwards [ h_y_val.eventually ( lt_mem_nhds <| show 1 / 2 - ε > 0 by linarith ) ] with x hx using by rw [ Real.log_div ( by aesop ) ( by aesop ), Real.log_div ( by aesop ) ( by aesop ) ] ; ring;
        have h_log_y_val : Filter.Tendsto (fun x => (Real.log (Real.log x) - Real.log (Real.log (Real.log x))) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
          have h_log_y_val : Filter.Tendsto (fun x => 1 - Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
            have h_log_y_val : Filter.Tendsto (fun x => Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
              have h_log_y_val : Filter.Tendsto (fun x => Real.log x / x) Filter.atTop (nhds 0) := by
                -- Let $z = \frac{1}{x}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
                suffices h_log_recip : Filter.Tendsto (fun z => z * Real.log (1 / z)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
              exact h_log_y_val.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
            simpa only [ sub_zero ] using tendsto_const_nhds.sub h_log_y_val;
          refine h_log_y_val.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ sub_div, div_self <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ] );
        convert h_log_y_val.add ‹Filter.Tendsto ( fun x => ( Real.log ( y_val x ε ) - Real.log ( Real.log x ) + Real.log ( Real.log ( Real.log x ) ) ) / Real.log ( Real.log x ) ) Filter.atTop ( nhds 0 ) › using 2 <;> ring;
      -- We'll use the fact that $\log(2) + \log(y_val x ε) + \log(\log x) \sim \log(\log x)$.
      have h_log_sum : Filter.Tendsto (fun x => (Real.log 2 + Real.log (y_val x ε) + Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\log(2) + \log(y_val x ε) + \log(\log x) \sim \log(\log x)$ to simplify the expression.
        have h_log_sum_simplified : Filter.Tendsto (fun x => (Real.log (y_val x ε) + Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
          have h_log_sum_simplified : Filter.Tendsto (fun x => (Real.log (y_val x ε) / Real.log (Real.log x)) * (Real.log (Real.log x) / Real.log x) + (Real.log (Real.log x) / Real.log x)) Filter.atTop (nhds 0) := by
            have h_log_log_x : Filter.Tendsto (fun x => Real.log (Real.log x) / Real.log x) Filter.atTop (nhds 0) := by
              -- Let $z = \log x$, therefore the expression becomes $\frac{\log z}{z}$.
              suffices h_log_z : Filter.Tendsto (fun z => Real.log z / z) Filter.atTop (nhds 0) by
                exact h_log_z.comp ( Real.tendsto_log_atTop );
              -- Let $w = \frac{1}{z}$, therefore the expression becomes $\frac{\log (1/w)}{1/w} = -w \log w$.
              suffices h_log_w : Filter.Tendsto (fun w => -w * Real.log w) (Filter.map (fun z => 1 / z) Filter.atTop) (nhds 0) by
                exact h_log_w.congr ( by simp +contextual [ div_eq_inv_mul ] );
              norm_num +zetaDelta at *;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
            simpa using Filter.Tendsto.add ( h_log_y_val.mul h_log_log_x ) h_log_log_x;
          refine h_log_sum_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ div_mul_div_cancel₀ ( ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ] ; ring );
        simpa [ add_div, add_assoc ] using Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) h_log_sum_simplified;
      convert h_y_val.mul ( h_log_sum.const_sub 1 ) using 2 <;> ring_nf;
      by_cases h : Real.log ‹_› = 0 <;> simp +decide [ sq, mul_assoc, h ] ; ring

/-
Definition of the lower bound for r_val.
-/
noncomputable def r_lower_bound_val (x : ℝ) (ε : ℝ) : ℝ :=
  (x / (2 * (y_val x ε) * Real.log x)) ^ (y_val x ε)

/-
The lower bound for r_val tends to infinity.
-/
lemma r_lower_bound_val_tendsto_atTop (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    Filter.Tendsto (fun x => r_lower_bound_val x ε) Filter.atTop Filter.atTop := by
      -- The logarithm of the lower bound is asymptotically $(1 / 2 - \epsilon) (\log x)^2 / \log \log x$.
      have h_log_lower_bound : Filter.Tendsto (fun x => Real.log (r_lower_bound_val x ε) / ((Real.log x)^2 / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) := by
        convert log_r_lower_bound_asymptotic ε hε hε2 using 1;
      -- Since $\frac{(\log x)^2}{\log \log x} \to \infty$, it follows that $\log(LB) \to \infty$.
      have h_log_tendsto_infty : Filter.Tendsto (fun x => Real.log x ^ 2 / Real.log (Real.log x)) Filter.atTop Filter.atTop := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{\log y}$.
        suffices h_log_y : Filter.Tendsto (fun y => y^2 / Real.log y) Filter.atTop Filter.atTop by
          exact h_log_y.comp ( Real.tendsto_log_atTop );
        -- We can use the change of variables $u = \log y$ to transform the limit expression.
        suffices h_log_y' : Filter.Tendsto (fun u => Real.exp (2 * u) / u) Filter.atTop Filter.atTop by
          have := h_log_y'.comp Real.tendsto_log_atTop;
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, mul_comm, Real.exp_mul, Real.exp_log hx ] ; norm_cast );
        have := Real.tendsto_exp_div_pow_atTop 1;
        have := this.comp ( Filter.tendsto_id.const_mul_atTop zero_lt_two );
        convert this.const_mul_atTop ( show ( 0 : ℝ ) < 2 by norm_num ) using 2 ; norm_num ; ring;
      have h_log_tendsto_infty : Filter.Tendsto (fun x => Real.log (r_lower_bound_val x ε)) Filter.atTop Filter.atTop := by
        have h_log_tendsto_infty : Filter.Tendsto (fun x => (Real.log x ^ 2 / Real.log (Real.log x)) * (Real.log (r_lower_bound_val x ε) / (Real.log x ^ 2 / Real.log (Real.log x)))) Filter.atTop Filter.atTop := by
          apply Filter.Tendsto.atTop_mul_pos;
          exacts [ show 0 < 1 / 2 - ε by linarith, h_log_tendsto_infty, h_log_lower_bound ];
        refine h_log_tendsto_infty.congr' ( by filter_upwards [ ‹Filter.Tendsto ( fun x : ℝ => Real.log x ^ 2 / Real.log ( Real.log x ) ) Filter.atTop Filter.atTop›.eventually_ne_atTop 0 ] with x hx using by rw [ mul_div_cancel₀ _ hx ] );
      have h_exp_log_tendsto_infty : Filter.Tendsto (fun x => Real.exp (Real.log (r_lower_bound_val x ε))) Filter.atTop Filter.atTop := by
        exact Real.tendsto_exp_atTop.comp h_log_tendsto_infty;
      refine h_exp_log_tendsto_infty.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; rw [ Real.exp_log ] ; norm_num [ r_lower_bound_val ] ; ring_nf ; (
      by_cases hy : y_val x ε = 0 <;> simp_all +decide [Real.log_pos hx] ; ring_nf ; norm_num [ hx, Real.log_pos hx ] ; positivity;);

/-
The error term is eventually less than 1/4 of the lower bound.
-/
lemma error_term_lt_quarter_lower_bound (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, (2 * x) ^ (y_val x ε) / x < (r_lower_bound_val x ε) / 4 := by
      -- We'll use the fact that the ratio of the error term to the lower bound of r tends to 0.
      have h_ratio_zero : Filter.Tendsto (fun x => ((2 * x) ^ (y_val x ε) / x) / (r_lower_bound_val x ε)) Filter.atTop (nhds 0) := by
        convert error_term_ratio_tendsto_zero ε hε hε2 using 1;
      have := h_ratio_zero.eventually ( gt_mem_nhds <| show 0 < 1 / 4 by norm_num );
      have h_pos : Filter.Tendsto (fun x => r_lower_bound_val x ε) Filter.atTop Filter.atTop := by
        exact r_lower_bound_val_tendsto_atTop ε hε hε2;
      exact Filter.eventually_atTop.mp ( this.and ( h_pos.eventually_gt_atTop 0 ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun x hx => by have := hN x hx; rw [ div_lt_iff₀ ] at this <;> linarith ⟩

/-
The lower bound is eventually greater than 4.
-/
lemma lower_bound_gt_four (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, r_lower_bound_val x ε > 4 := by
      have := r_lower_bound_val_tendsto_atTop ε hε hε2;
      simpa using this.eventually_gt_atTop 4

/-
For sufficiently large x, tau_perp(n) > |D_set| / 2.
-/
set_option linter.flexible false in
lemma tau_perp_gt_half_card_D_set (hPNT : PNT_statement) (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, (tau_perp (n_val_Ioc x) : ℝ) > ((D_set_Ioc x ε).card : ℝ) / 2 := by
      -- By combining the results from the lemmas, we can find such an N.
      obtain ⟨N1, hN1⟩ := r_lower_bound hPNT ε hε hε2
      obtain ⟨N2, hN2⟩ := error_term_lt_quarter_lower_bound ε hε hε2
      obtain ⟨N3, hN3⟩ := lower_bound_gt_four ε hε hε2
      obtain ⟨N4, hN4⟩ := tau_perp_lower_bound_explicit ε hε hε2
      use max N1 (max N2 (max N3 N4));
      simp +zetaDelta at *;
      intro x hx1 hx2 hx3 hx4; linarith [ hN1 x hx1, hN2 x hx2, hN3 x hx3, hN4 x hx4, show ( r_lower_bound_val x ε : ℝ ) = ( x / ( 2 * y_val x ε * Real.log x ) ) ^ y_val x ε by rfl ] ;

/-
For sufficiently large x, |D_set| > exp((1 / 2 - epsilon - delta) * (log x)^2 / log log x).
-/
set_option linter.style.refine false in
set_option linter.style.multiGoal false in
lemma card_D_set_lower_bound_explicit (hPNT : PNT_statement) (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) (δ : ℝ) (hδ : δ > 0) :
    ∃ N, ∀ x ≥ N, ((D_set_Ioc x ε).card : ℝ) > Real.exp ((1 / 2 - ε - δ) * (Real.log x)^2 / Real.log (Real.log x)) := by
      -- By the properties of logarithms and exponentials, if $\log(LB(x))$ tends to infinity, then $LB(x)$ itself tends to infinity.
      have h_exp_gt_one : Filter.Tendsto (fun x => (D_set_Ioc x ε).card / Real.exp ((1 / 2 - ε - δ) * (Real.log x)^2 / Real.log (Real.log x))) Filter.atTop Filter.atTop := by
        have h_exp_gt_one : Filter.Tendsto (fun x => (r_lower_bound_val x ε) / Real.exp ((1 / 2 - ε - δ) * (Real.log x)^2 / Real.log (Real.log x))) Filter.atTop Filter.atTop := by
          have h_exp_gt_one : Filter.Tendsto (fun x => Real.log (r_lower_bound_val x ε) - ((1 / 2 - ε - δ) * (Real.log x)^2 / Real.log (Real.log x))) Filter.atTop Filter.atTop := by
            have h_exp_gt_one : Filter.Tendsto (fun x => Real.log (r_lower_bound_val x ε) / ((Real.log x)^2 / Real.log (Real.log x))) Filter.atTop (nhds (1 / 2 - ε)) := by
              convert log_r_lower_bound_asymptotic ε hε hε2 using 1;
            have h_exp_gt_one : Filter.Tendsto (fun x => ((Real.log (r_lower_bound_val x ε)) / ((Real.log x)^2 / Real.log (Real.log x)) - (1 / 2 - ε - δ)) * ((Real.log x)^2 / Real.log (Real.log x))) Filter.atTop Filter.atTop := by
              apply Filter.Tendsto.pos_mul_atTop;
              exact show 0 < δ by linarith;
              · convert h_exp_gt_one.sub_const ( 1 / 2 - ε - δ ) using 2 ; ring;
              · -- We can use the change of variables $u = \log x$ to transform the limit expression.
                suffices h_log : Filter.Tendsto (fun u => u^2 / Real.log u) Filter.atTop Filter.atTop by
                  exact h_log.comp ( Real.tendsto_log_atTop );
                rw [ Filter.tendsto_atTop_atTop ] at *;
                exact fun b => ⟨ Max.max b 2, fun x hx => by rw [ le_div_iff₀ ( Real.log_pos <| by linarith [ le_max_left b 2, le_max_right b 2 ] ) ] ; nlinarith [ le_max_left b 2, le_max_right b 2, Real.log_le_sub_one_of_pos ( by linarith [ le_max_left b 2, le_max_right b 2 ] : 0 < x ), Real.log_pos ( by linarith [ le_max_left b 2, le_max_right b 2 ] : 1 < x ) ] ⟩;
            refine h_exp_gt_one.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂;
            rw [ sub_mul, div_mul_cancel₀ _ ( ne_of_gt <| div_pos ( sq_pos_of_pos <| Real.log_pos hx₁ ) <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ] ; ring;
          have h_exp_gt_one : Filter.Tendsto (fun x => Real.exp (Real.log (r_lower_bound_val x ε) - ((1 / 2 - ε - δ) * (Real.log x)^2 / Real.log (Real.log x)))) Filter.atTop Filter.atTop := by
            exact Real.tendsto_exp_atTop.comp h_exp_gt_one;
          refine h_exp_gt_one.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1, r_lower_bound_val_tendsto_atTop ε hε hε2 |> Filter.Tendsto.eventually_gt_atTop <| 0 ] with x hx₁ hx₂ using by rw [ Real.exp_sub, Real.exp_log <| by positivity ] ;
        refine' Filter.tendsto_atTop_mono' _ _ h_exp_gt_one;
        filter_upwards [ Filter.eventually_ge_atTop ( Classical.choose ( r_lower_bound hPNT ε hε hε2 ) ) ] with x hx using div_le_div_of_nonneg_right ( mod_cast Classical.choose_spec ( r_lower_bound hPNT ε hε hε2 ) x hx |> le_of_lt ) ( Real.exp_nonneg _ );
      exact Filter.eventually_atTop.mp ( h_exp_gt_one.eventually_gt_atTop 1 ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun x hx => by have := hN x hx; rw [ gt_iff_lt ] at *; rw [ lt_div_iff₀ ( Real.exp_pos _ ) ] at *; linarith ⟩

/-
For sufficiently large x, tau_perp(n) > bound(n, epsilon).
-/
set_option linter.style.refine false in
set_option linter.style.multiGoal false in
lemma tau_perp_gt_bound (hPNT : PNT_statement) (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1 / 2) :
    ∃ N, ∀ x ≥ N, (tau_perp (n_val_Ioc x) : ℝ) > bound (n_val_Ioc x) ε := by
      -- Let $\epsilon' = \epsilon / 2$. Let $\delta = \epsilon / 8$.
      set ε' : ℝ := ε / 2
      set δ : ℝ := ε / 8;
      obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ x ≥ N₁, (tau_perp (n_val_Ioc x) : ℝ) > ((D_set_Ioc x ε').card : ℝ) / 2 := by
        apply_rules [ tau_perp_gt_half_card_D_set ];
        · positivity;
        · exact div_lt_iff₀' ( by norm_num ) |>.2 ( by linarith );
      -- By combining the results from hN₁, h_lower_bound, and h_bound, we can conclude that for sufficiently large x, tau_perp is greater than the bound.
      obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ x ≥ N₂, ((D_set_Ioc x ε').card : ℝ) > 2 * Real.exp ((1 / 2 - ε + δ) * (Real.log x)^2 / Real.log (Real.log x)) := by
        obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ x ≥ N₂, ((D_set_Ioc x ε').card : ℝ) > Real.exp ((1 / 2 - ε' - δ) * (Real.log x)^2 / Real.log (Real.log x)) := by
          apply_rules [ card_D_set_lower_bound_explicit ] ; aesop;
          · exact lt_of_le_of_lt ( div_le_self hε.le ( by norm_num ) ) hε2;
          · positivity;
        -- We'll use that exponential functions grow faster than polynomial functions to find such an $N₂$.
        have h_exp_growth : Filter.Tendsto (fun x => Real.exp ((1 / 2 - ε' - δ) * (Real.log x)^2 / Real.log (Real.log x)) / Real.exp ((1 / 2 - ε + δ) * (Real.log x)^2 / Real.log (Real.log x))) Filter.atTop Filter.atTop := by
          norm_num +zetaDelta at *;
          norm_num [ ← Real.exp_sub ];
          -- We can factor out $(Real.log x)^2 / Real.log (Real.log x)$ from the expression.
          suffices h_factor : Filter.Tendsto (fun x => (Real.log x)^2 / Real.log (Real.log x)) Filter.atTop Filter.atTop by
            convert h_factor.const_mul_atTop ( show 0 < ( 1 / 2 - ε / 2 - ε / 8 ) - ( 1 / 2 - ε + ε / 8 ) by linarith ) using 2 ; ring;
          -- We can use the change of variables $u = \log x$ to transform the limit expression.
          suffices h_log : Filter.Tendsto (fun u => u^2 / Real.log u) Filter.atTop Filter.atTop by
            exact h_log.comp ( Real.tendsto_log_atTop );
          refine' Filter.tendsto_atTop_atTop.mpr fun x => _;
          exact ⟨ Max.max x 3, fun a ha => by rw [ le_div_iff₀ ( Real.log_pos <| by linarith [ le_max_left x 3, le_max_right x 3 ] ) ] ; nlinarith [ le_max_left x 3, le_max_right x 3, Real.log_le_sub_one_of_pos ( by linarith [ le_max_left x 3, le_max_right x 3 ] : 0 < a ), Real.log_pos <| show 1 < a by linarith [ le_max_left x 3, le_max_right x 3 ] ] ⟩;
        have := h_exp_growth.eventually_gt_atTop 2;
        rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N₃, hN₃ ⟩ ; exact ⟨ Max.max N₂ N₃, fun x hx => by have := hN₃ x ( le_trans ( le_max_right _ _ ) hx ) ; rw [ lt_div_iff₀ ( Real.exp_pos _ ) ] at this; linarith [ hN₂ x ( le_trans ( le_max_left _ _ ) hx ) ] ⟩ ;
      obtain ⟨N₃, hN₃⟩ : ∃ N₃, ∀ x ≥ N₃, bound (n_val_Ioc x) ε < Real.exp ((1 / 2 - ε + δ) * (Real.log x)^2 / Real.log (Real.log x)) := by
        convert bound_asymptotic hPNT ε hε hε2 δ ( by positivity ) using 1;
      exact ⟨ Max.max N₁ ( Max.max N₂ N₃ ), fun x hx => by linarith [ hN₁ x ( le_trans ( le_max_left _ _ ) hx ), hN₂ x ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hx ), hN₃ x ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hx ) ] ⟩

/-
There are infinitely many n for which tau_perp(n) > bound(n, epsilon).
-/
theorem main_theorem (hPNT : PNT_statement) :
    ∀ ε ∈ Set.Ioo 0 (1 / 2), ∀ N, ∃ n ≥ N, (tau_perp n : ℝ) > bound n ε := by
      intro ε hε N
      obtain ⟨N0, hN0⟩ := tau_perp_gt_bound hPNT ε hε.left hε.right
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ≥ N0 ∧ (Nat.floor x ≥ N) ∧ (n_val_Ioc x ≥ N) := by
        -- Since there are infinitely many primes, we can choose $x$ such that $x \geq N0$ and $n_val_Ioc x \geq N$.
        have h_inf_primes : Filter.Tendsto (fun x : ℝ => n_val_Ioc x) Filter.atTop Filter.atTop := by
          have h_inf_primes : Filter.Tendsto (fun x : ℝ => Real.log (n_val_Ioc x)) Filter.atTop Filter.atTop := by
            have h_inf_primes : Filter.Tendsto (fun x : ℝ => Real.log (n_val_Ioc x) / x) Filter.atTop (nhds 1) := by
              convert hPNT using 1
            generalize_proofs at *; (
            have h_inf_primes : Filter.Tendsto (fun x : ℝ => Real.log (n_val_Ioc x) / x * x) Filter.atTop Filter.atTop := by
              apply Filter.Tendsto.pos_mul_atTop;
              exacts [ zero_lt_one, h_inf_primes, Filter.tendsto_id ]
            generalize_proofs at *; (
            exact h_inf_primes.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_mul_cancel₀ _ hx.ne' ] )))
          generalize_proofs at *; (
          rw [ Filter.tendsto_atTop_atTop ] at *;
          exact fun b => by rcases h_inf_primes ( Real.log b ) with ⟨ i, hi ⟩ ; exact ⟨ i, fun x hx => Nat.le_of_not_lt fun h => by have := hi x hx; rw [ Real.log_le_log_iff ] at this <;> norm_cast at * <;> linarith [ show 0 < n_val_Ioc x from Nat.pos_of_ne_zero <| by unfold n_val_Ioc; exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| by aesop ] ⟩ ;)
        generalize_proofs at *; (
        rcases Filter.eventually_atTop.mp ( h_inf_primes.eventually_ge_atTop N ) with ⟨ x, hx ⟩ ; exact ⟨ Max.max N0 ( Max.max x N ), le_max_left _ _, Nat.le_floor <| le_max_of_le_right <| le_max_right _ _, hx _ <| le_max_of_le_right <| le_max_left _ _ ⟩ ;)
      generalize_proofs at *;
      exact ⟨ _, hx.2.2, hN0 x hx.1 ⟩

#print axioms main_theorem
-- 'Erdos1100b.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1100b
