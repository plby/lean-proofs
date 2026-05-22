/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 457.
https://www.erdosproblems.com/forum/thread/457

Informal authors:
- GPT-5.2 Pro
- Kevin Barreto

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/457#post-4668
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/457.lean
-/
/-
Prompted by Kevin Barreto, GPT-5.2 Pro managed to solve Erdős Problem #457 (https://www.erdosproblems.com/457) by exhibiting infinitely many $n$ such that $\prod_{1 \le i \le \log n} n+i$ is divisible by all primes smaller than $2.1 \log n$.

Aristotle from Harmonic (https://aristotle.harmonic.fun) already formalized the solution, but the proof had not yet been connected to the statement from Google DeepMind's Formal Conjectures Project. 

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/457.lean

I gave the already existing formalization to Aristotle and asked it to fill in the sorry from the above statement. It managed it mere minutes!

-/

import Mathlib

namespace Erdos457

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.refine false
set_option linter.style.multiGoal false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of A(n,k) as the product of (n+i) for 1 <= i <= k, and F(n) as A(n, floor(log n)).
-/
noncomputable def A_func (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)

noncomputable def F (n : ℕ) : ℕ := A_func n ⌊Real.log n⌋₊

/-
The number of primes in (2m, 3m] is at most 3m log 2 / log(2m).
-/
lemma lemma_prime_count (m : ℕ) (hm : m ≥ 1) :
  (Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m))).card ≤ (3 * m * Real.log 2) / Real.log (2 * m) := by
    -- Let $q_1, \dots, q_t$ be the primes in $(2m, 3m]$. Each $q_j$ divides $\binom{3m}{m}$. Thus $\prod q_j \le \binom{3m}{m} \le 2^{3m}$.
    have h_prod_le : (∏ q ∈ Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)), q) ≤ Nat.choose (3 * m) m := by
      refine' Nat.le_of_dvd ( Nat.choose_pos ( by linarith ) ) _;
      refine' Nat.dvd_trans _ ( Nat.prod_primeFactors_dvd _ );
      apply_rules [ Finset.prod_dvd_prod_of_subset ];
      intro q hq;
      simp +zetaDelta at *;
      refine' ⟨ hq.2, _, _ ⟩;
      · apply_mod_cast hq.2.dvd_choose;
        · grind +ring;
        · omega;
        · grind;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
    have h_binom_le : Nat.choose (3 * m) m ≤ 2 ^ (3 * m) := by
      rw [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr ( by linarith ) ) ;
    have h_log_prod_le : (∑ q ∈ Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)), Real.log q) ≤ 3 * m * Real.log 2 := by
      have h_log_prod_le : Real.log (∏ q ∈ Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)), q) ≤ Real.log (2 ^ (3 * m)) := by
        exact Real.log_le_log ( Finset.prod_pos fun x hx => Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) <| by rw [ ← Nat.cast_prod ] ; exact_mod_cast h_prod_le.trans h_binom_le;
      rw [ Real.log_prod fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop ] at h_log_prod_le ; aesop;
    have h_log_le : (∑ q ∈ Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)), Real.log q) ≥ (Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m))).card * Real.log (2 * m) := by
      exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x hx => Real.log_le_log ( by positivity ) ( show ( x : ℝ ) ≥ 2 * m by norm_cast; linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ) ) ;
    have h_card_le : (Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m))).card ≤ (3 * m * Real.log 2) / Real.log (2 * m) := by
      exact le_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) |>.2 <| by linarith;
    exact_mod_cast h_card_le.trans (by norm_num) ;

/-
4^m / (2m+1) <= choose(2m, m) <= 4^m.
-/
lemma lemma_binom_bounds (m : ℕ) (hm : m ≥ 1) :
  (4 ^ m : ℝ) / (2 * m + 1) ≤ Nat.choose (2 * m) m ∧ Nat.choose (2 * m) m ≤ 4 ^ m := by
    rw [ div_le_iff₀ ( by positivity ) ];
    have h_sum : ∑ r ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) r = 4 ^ m := by
      rw [ show 4 ^ m = 2 ^ ( 2 * m ) by norm_num [ pow_mul ], ← Nat.sum_range_choose ];
    rw_mod_cast [ ← h_sum ];
    exact ⟨ le_trans ( Finset.sum_le_sum fun _ _ => Nat.choose_le_middle _ _ ) ( by simp +decide [ mul_comm ] ), Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr ( by linarith ) ) ⟩

/-
Given an integer A and a finite set of positive integers Q, there exists k in [1, 6^|Q|] such that for all q in Q, the distance from kA/q to the nearest integer is less than 1/6.
-/
lemma lemma_simultaneous_approximation (A : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q > 0) :
  ∃ k : ℕ, k ∈ Finset.Icc 1 (6 ^ Q.card) ∧ ∀ q ∈ Q, ∃ ℓ : ℤ, |(k * A : ℝ) - ℓ * q| < (q : ℝ) / 6 := by
    -- Let $t = |Q|$. Consider the $6^t+1$ points $x_r = (\{rA/q\})_{q \in Q} \in [0,1)^t$ for $r \in \{0, \dots, 6^t\}$.
    let t := Q.card
    let points := fun r : ℕ => fun q : Q => (r * A : ℝ) / q.val - ⌊(r * A : ℝ) / q.val⌋
    -- Partition $[0,1)^t$ into $6^t$ subcubes of side length $1/6$. By PHP, two points $x_r, x_s$ with $r > s$ fall in the same subcube.
    obtain ⟨r, s, hrs⟩ : ∃ r s : ℕ, r ∈ Finset.Icc 0 (6 ^ t) ∧ s ∈ Finset.Icc 0 (6 ^ t) ∧ r > s ∧ ∀ q : Q, abs ((points r q) - (points s q)) < 1 / 6 := by
      have h_pigeonhole : Finset.card (Finset.image (fun r : ℕ => fun q : Q => ⌊(points r q) * 6⌋) (Finset.Icc 0 (6 ^ t))) ≤ 6 ^ t := by
        refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.Icc ( fun _ => 0 ) ( fun _ => 5 );
        · simp +zetaDelta at *;
          exact fun x hx => ⟨ fun q => Int.floor_nonneg.2 <| mul_nonneg ( Int.fract_nonneg _ ) <| by norm_num, fun q => Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith [ Int.fract_lt_one ( ( x : ℝ ) * A / q ) ] ⟩;
        · erw [ Finset.card_map, Finset.card_pi ] ; aesop;
      -- Since there are $6^t + 1$ points and only $6^t$ subcubes, by the pigeonhole principle, at least two of these points must fall into the same subcube.
      obtain ⟨r, s, hrs⟩ : ∃ r s : ℕ, r ∈ Finset.Icc 0 (6 ^ t) ∧ s ∈ Finset.Icc 0 (6 ^ t) ∧ r ≠ s ∧ (fun q : Q => ⌊(points r q) * 6⌋) = (fun q : Q => ⌊(points s q) * 6⌋) := by
        contrapose! h_pigeonhole;
        rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by contrapose! hxy; exact h_pigeonhole x y hx hy hxy ] ; norm_num;
      cases lt_or_gt_of_ne hrs.2.2.1 <;> [ refine ⟨ s, r, hrs.2.1, hrs.1, ‹_›, fun q ↦ ?_ ⟩ ; refine ⟨ r, s, hrs.1, hrs.2.1, ‹_›, fun q ↦ ?_ ⟩ ] <;> simp_all +decide [ funext_iff ];
      · have := hrs.2.2.2 q q.2; rw [ Int.floor_eq_iff ] at this; norm_num at * ; exact abs_sub_lt_iff.mpr ⟨ by linarith [ Int.floor_le ( points r q * 6 ), Int.lt_floor_add_one ( points r q * 6 ), Int.floor_le ( points s q * 6 ), Int.lt_floor_add_one ( points s q * 6 ) ], by linarith [ Int.floor_le ( points r q * 6 ), Int.lt_floor_add_one ( points r q * 6 ), Int.floor_le ( points s q * 6 ), Int.lt_floor_add_one ( points s q * 6 ) ] ⟩ ;
      · have := hrs.2.2.2 q q.2; rw [ Int.floor_eq_iff ] at this; norm_num at *; exact abs_sub_lt_iff.mpr ⟨ by linarith [ Int.floor_le ( points r q * 6 ), Int.lt_floor_add_one ( points r q * 6 ), Int.floor_le ( points s q * 6 ), Int.lt_floor_add_one ( points s q * 6 ) ], by linarith [ Int.floor_le ( points r q * 6 ), Int.lt_floor_add_one ( points r q * 6 ), Int.floor_le ( points s q * 6 ), Int.lt_floor_add_one ( points s q * 6 ) ] ⟩ ;
    norm_num +zetaDelta at *;
    refine' ⟨ r - s, ⟨ Nat.sub_pos_of_lt hrs.2.2.1, Nat.sub_le_of_le_add <| by linarith ⟩, fun q hq => _ ⟩;
    use ⌊(r * A : ℝ) / q⌋ - ⌊(s * A : ℝ) / q⌋;
    rw [ Nat.cast_sub hrs.2.2.1.le ] ; have := hrs.2.2.2 q hq ; rw [ abs_lt ] at * ; constructor <;> push_cast at * <;> nlinarith [ Int.fract_add_floor ( ( r : ℝ ) * A / q ), Int.fract_add_floor ( ( s : ℝ ) * A / q ), show ( q : ℝ ) > 0 from Nat.cast_pos.mpr ( hQ q hq ), mul_div_cancel₀ ( ( r : ℝ ) * A ) ( show ( q : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr ( ne_of_gt ( hQ q hq ) ) ), mul_div_cancel₀ ( ( s : ℝ ) * A ) ( show ( q : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr ( ne_of_gt ( hQ q hq ) ) ) ] ;

/-
For sufficiently large m, 2.1 * (log 4 + (3 log 2 log 6) / log(2m)) < 3.
-/
lemma lemma_asymptotic_inequality : ∃ M : ℕ, ∀ m ≥ M,
  2.1 * (Real.log 4 + (3 * Real.log 2 * Real.log 6) / Real.log (2 * m)) < 3 := by
    -- We'll use that $\frac{3 \log 2 \log 6}{\log(2m)}$ tends to $0$ as $m \to \infty$.
    have h_log_term : Filter.Tendsto (fun m : ℕ => (3 * Real.log 2 * Real.log 6) / Real.log (2 * (m : ℝ))) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two );
    have := h_log_term.const_add ( Real.log 4 ) ; ( have := this.const_mul 2.1; ( ( have := this.eventually ( gt_mem_nhds ( show ( 2.1 * ( Real.log 4 + 0 ) ) < 3 by rw [ show ( 4 : ℝ ) = ( 2 ^ 2 ) by norm_num, Real.log_pow ] ; norm_num ; have := Real.log_two_lt_d9 ; norm_num1 at * ; linarith ) ) ) ; aesop ) ) ;

/-
If n = k*A - c satisfies log n >= 1.2m, and k provides a good approximation for primes in (2m, 3m], then every prime p <= 3m divides F(n).
-/
lemma lemma_divisibility (m : ℕ) (hm : m ≥ 100) (k : ℕ) (hk_pos : k ≥ 1)
  (hk_approx : ∀ q ∈ Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)), ∃ ℓ : ℤ, |(k * Nat.choose (2 * m) m : ℝ) - ℓ * q| < (q : ℝ) / 6) :
  let A := Nat.choose (2 * m) m
  let c := Nat.floor (3 * m / 5)
  let n := k * A - c
  Real.log n ≥ 1.2 * m →
  ∀ p, p.Prime → p ≤ 3 * m → p ∣ F n := by
    intro A c n hn p hp hp';
    -- Case 1: $p \le m$. Then $p \le 1.2m \le \log n$, so $p \le \lfloor \log n \rfloor$. The product $F(n)$ contains $n+1, \dots, n+\lfloor \log n \rfloor$. This range has length $\ge p$, so it contains a multiple of $p$.
    by_cases hp_case1 : p ≤ m;
    · -- Since $p \leq 1.2m \leq \log n$, we have $p \leq \lfloor \log n \rfloor$.
      have hp_floor : p ≤ Nat.floor (Real.log n) := by
        exact Nat.le_floor <| by norm_num at *; linarith [ ( by norm_cast : ( p :ℝ ) ≤ m ) ] ;
      -- The product $F(n)$ contains $n+1, \dots, n+\lfloor \log n \rfloor$. This range has length $\ge p$, so it contains a multiple of $p$.
      have h_prod_range : ∃ i ∈ Finset.Icc 1 (Nat.floor (Real.log n)), (n + i) % p = 0 := by
        use p - n % p;
        exact ⟨ Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt <| Nat.mod_lt _ hp.pos, Nat.le_trans ( Nat.sub_le _ _ ) hp_floor ⟩, Nat.mod_eq_zero_of_dvd <| by use ( n / p ) + 1; linarith [ Nat.div_add_mod n p, Nat.sub_add_cancel <| Nat.mod_lt n hp.pos |> Nat.le_of_lt ] ⟩;
      obtain ⟨ i, hi₁, hi₂ ⟩ := h_prod_range; exact dvd_trans ( Nat.dvd_of_mod_eq_zero hi₂ ) ( Finset.dvd_prod_of_mem _ hi₁ ) ;
    · -- Case 2: $m < p \le 2m$. Then $p \mid A$. Since $n+c = kA$, $p \mid n+c$. We need to check $1 \le c \le \lfloor \log n \rfloor$.
      by_cases hp_case2 : p ≤ 2 * m;
      · -- Since $p \mid A$, we have $p \mid n + c$. Also, $1 \le c \le \lfloor \log n \rfloor$.
        have hp_div_nc : p ∣ n + c := by
          rw [ Nat.sub_add_cancel ];
          · refine' dvd_mul_of_dvd_right _ _;
            apply_mod_cast hp.dvd_choose;
            · linarith;
            · omega;
            · linarith;
          · have hA_ge_4m : A ≥ 4 ^ m / (2 * m + 1) := by
              have hA_ge_4m : (Nat.choose (2 * m) m : ℝ) ≥ 4 ^ m / (2 * m + 1) := by
                have := lemma_binom_bounds m ( by linarith ) ; aesop;
              exact Nat.div_le_of_le_mul <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast; rw [ ge_iff_le, div_le_iff₀ ] at * <;> first | positivity | linarith;
            -- Since $4^m / (2m + 1) > 3m / 5$ for $m \geq 100$, we have $A > 3m / 5$.
            have hA_gt_3m5 : 4 ^ m / (2 * m + 1) > 3 * m / 5 := by
              refine' Nat.le_div_iff_mul_le ( by positivity ) |>.2 _;
              refine' Nat.le_induction _ _ m hm <;> norm_num [ Nat.pow_succ' ] at *;
              intro n hn hn'; rw [ Nat.mul_succ ] ; nlinarith [ Nat.div_mul_le_self ( 3 * n ) 5, Nat.div_mul_le_self ( 3 * ( n + 1 ) ) 5, Nat.div_add_mod ( 3 * n ) 5, Nat.mod_lt ( 3 * n ) ( by decide : 5 > 0 ), Nat.div_add_mod ( 3 * ( n + 1 ) ) 5, Nat.mod_lt ( 3 * ( n + 1 ) ) ( by decide : 5 > 0 ) ] ;
            exact le_trans ( Nat.div_le_div_right <| by linarith ) ( le_trans hA_gt_3m5.le <| le_trans hA_ge_4m <| le_mul_of_one_le_left' hk_pos )
        have hc_bound : 1 ≤ c ∧ c ≤ Nat.floor (Real.log n) := by
          refine' ⟨ Nat.floor_pos.mpr _, Nat.le_floor <| le_trans _ hn ⟩ <;> norm_num at *;
          · omega;
          · field_simp;
            exact_mod_cast ( by linarith [ Nat.floor_le ( show 0 ≤ 3 * m / 5 by positivity ), Nat.div_mul_le_self ( 3 * m ) 5 ] : ( c : ℕ ) * 5 ≤ 6 * m );
        exact dvd_trans hp_div_nc ( Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hc_bound.1, hc_bound.2 ⟩ ) );
      · -- Case 3: $2m < p \le 3m$. Then $p \in Q$. By hypothesis, $\exists \ell, |kA - \ell p| < p/6$.
        obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℤ, |(k * A : ℝ) - ℓ * p| < p / 6 := hk_approx p (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by linarith, by linarith⟩, hp⟩);
        -- Let $r = kA - \ell p$. Then $|r| < p/6 \le 3m/6 = m/2$.
        set r := k * A - ℓ * p
        have hr_bounds : |(r : ℝ)| < m / 2 := by
          simp +zetaDelta at *;
          linarith [ show ( p : ℝ ) ≤ 3 * m by norm_cast ];
        -- We want to find $i$ such that $n+i$ is a multiple of $p$.
        -- $n+i = kA - c + i$.
        -- Set $kA - c + i = \ell p \implies r - c + i = 0 \implies i = c - r$.
        have hi_exists : ∃ i : ℕ, 1 ≤ i ∧ i ≤ Nat.floor (Real.log n) ∧ n + i ≡ 0 [ZMOD p] := by
          refine' ⟨ Int.toNat ( c - r ), _, _, _ ⟩ <;> norm_num;
          · simp +zetaDelta at *;
            rw [ abs_lt ] at hr_bounds ; rw [ lt_div_iff₀ ] at * <;> norm_cast at * ; omega;
          · -- Since $c = \lfloor 0.6m \rfloor$, we have $c \leq 0.6m$.
            have hc_le : (c : ℝ) ≤ 0.6 * m := by
              norm_num +zetaDelta at *;
              rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 3 * m ) 5 ];
            norm_num [ abs_lt ] at *;
            exact Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Nat.lt_floor_add_one <| Real.log n ] ;
          · rw [ Nat.cast_sub ] <;> norm_num [ Int.modEq_iff_dvd ];
            · rw [ max_eq_left ] <;> norm_num ; ring_nf at * ; aesop;
              norm_num +zetaDelta at *;
              rw [ abs_lt ] at hr_bounds ; rw [ lt_div_iff₀ ] at * <;> norm_cast at * ; omega;
            · refine' Nat.div_le_of_le_mul _;
              have h_binom : Nat.choose (2 * m) m ≥ 2 ^ m := by
                rw [ two_mul, Nat.add_choose_eq ];
                rw [ ← Nat.sum_range_choose ];
                rw [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => Nat.choose m i * Nat.choose m j ];
                exact Finset.sum_le_sum fun i hi => by nlinarith only [ Nat.choose_pos ( show i ≤ m from Finset.mem_range_succ_iff.mp hi ), Nat.choose_pos ( show m - i ≤ m from Nat.sub_le m i ) ] ;
              nlinarith [ show 2 ^ m > m by exact Nat.recOn m ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn, Nat.one_le_pow n 2 zero_lt_two ] ];
        obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := hi_exists;
        exact dvd_trans ( Int.natCast_dvd_natCast.mp ( Int.dvd_of_emod_eq_zero hi₃ ) ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hi₁, hi₂ ⟩ ) )

set_option maxHeartbeats 1000000 in
-- The asymptotic construction proof exceeds the default heartbeat limit.
theorem thm_main : Set.Infinite { n : ℕ | ∀ p : ℕ, p.Prime → p ≤ 2.1 * Real.log n → p ∣ F n } := by
  -- To prove the infiniteness, we show that for any natural number $a$, there exists an $n$ in the set such that $n > a$.
  have h_infinite : ∀ a : ℕ, ∃ n > a, ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ 2.1 * Real.log n → p ∣ F n := by
    intro a
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≥ 100 ∧ a < (4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5 ∧ 2.1 * (Real.log 4 + (3 * Real.log 2 * Real.log 6) / Real.log (2 * m)) < 3 ∧ 1.2 * m ≤ Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5) := by
      -- We'll use that $Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5)$ grows faster than $1.2 * m$.
      have h_log_growth : Filter.Tendsto (fun m : ℕ => Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5) / m) Filter.atTop (nhds (Real.log 4)) := by
        -- We'll use the fact that $\log((4^m / (2m + 1) - 3m / 5)) = m \log 4 + \log((1 - (2m + 1) * 3m / (5 * 4^m))) - \log(2m + 1)$.
        suffices h_log_simplified : Filter.Tendsto (fun m : ℕ => (m * Real.log 4 + Real.log ((1 - (2 * m + 1) * 3 * m / (5 * 4 ^ m))) - Real.log (2 * m + 1)) / (m : ℝ)) Filter.atTop (nhds (Real.log 4)) by
          refine h_log_simplified.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm ; rw [ show ( 4 ^ m / ( 2 * m + 1 ) - 3 * m / 5 : ℝ ) = ( 4 ^ m ) / ( 2 * m + 1 ) * ( 1 - ( 2 * m + 1 ) * 3 * m / ( 5 * 4 ^ m ) ) by
                                                                                                                field_simp ] ; rw [ Real.log_mul ( by positivity ) ( by
                                                                                                                rw [ Ne.eq_def, sub_eq_zero, eq_div_iff ] <;> norm_cast <;> induction hm <;> norm_num [ Nat.pow_succ ] at *;
                                                                                                                rename_i k hk ih; exact ne_of_gt <| by { exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; nlinarith } ; ) ] ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; norm_num ; ring;
        -- We'll use the fact that $\frac{\log(1 - \frac{(2m+1) \cdot 3m}{5 \cdot 4^m})}{m}$ and $\frac{\log(2m+1)}{m}$ tend to $0$ as $m \to \infty$.
        have h_log_zero : Filter.Tendsto (fun m : ℕ => Real.log (1 - (2 * m + 1) * 3 * m / (5 * 4 ^ m)) / (m : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun m : ℕ => Real.log (2 * m + 1) / (m : ℝ)) Filter.atTop (nhds 0) := by
          constructor;
          · -- We'll use the fact that $\frac{(2m+1) \cdot 3m}{5 \cdot 4^m}$ tends to $0$ as $m \to \infty$.
            have h_frac_zero : Filter.Tendsto (fun m : ℕ => (2 * m + 1) * 3 * m / (5 * 4 ^ m : ℝ)) Filter.atTop (nhds 0) := by
              refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
              norm_num;
              exact ⟨ 20, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith [ pow_pos ( show 0 < 4 by norm_num ) ‹_› ] ⟩;
            simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( h_frac_zero.const_sub 1 ) ( by norm_num ) ) tendsto_natCast_atTop_atTop;
          · -- We can use the fact that $\log(2m + 1) = \log(m) + \log(2 + \frac{1}{m})$.
            suffices h_log : Filter.Tendsto (fun m : ℕ => (Real.log m + Real.log (2 + 1 / (m : ℝ))) / (m : ℝ)) Filter.atTop (nhds 0) by
              refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ show ( 2 * m + 1 : ℝ ) = m * ( 2 + 1 / m ) by nlinarith [ one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ] ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
            -- We'll use the fact that $\frac{\log m}{m}$ tends to $0$ as $m$ tends to infinity.
            have h_log_m : Filter.Tendsto (fun m : ℕ => Real.log m / (m : ℝ)) Filter.atTop (nhds 0) := by
              -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
              suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
              norm_num;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
            simpa [ add_div ] using h_log_m.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
        simp_all +decide [ add_div, sub_div ];
        simpa using Filter.Tendsto.sub ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with m hm; rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr hm ) ] ) ) h_log_zero.1 ) h_log_zero.2;
      have h_log_growth : ∃ M : ℕ, ∀ m ≥ M, Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5) ≥ 1.2 * m := by
        have h_log_growth : ∃ M : ℕ, ∀ m ≥ M, Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5) / m ≥ 1.2 := by
          have h_log_growth : Real.log 4 > 1.2 := by
            rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; norm_num ; have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
          exact Filter.eventually_atTop.mp ( ‹Filter.Tendsto ( fun m : ℕ => Real.log ( 4 ^ m / ( 2 * ( m : ℝ ) + 1 ) - 3 * ( m : ℝ ) / 5 ) / ( m : ℝ ) ) Filter.atTop ( nhds ( Real.log 4 ) ) ›.eventually ( le_mem_nhds h_log_growth ) ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun m hm => hM m hm ⟩;
        exact ⟨ h_log_growth.choose + 1, fun m hm => by have := h_log_growth.choose_spec m ( by linarith ) ; rw [ ge_iff_le ] at *; rw [ le_div_iff₀ ( by norm_cast; linarith ) ] at *; linarith ⟩;
      obtain ⟨ M, hM ⟩ := h_log_growth; obtain ⟨ M', hM' ⟩ := lemma_asymptotic_inequality; refine' ⟨ M + M' + 100 + a + 1, _, _, _, _ ⟩ <;> norm_num at * <;> try linarith;
      · rw [ lt_sub_iff_add_lt, lt_div_iff₀ ] <;> norm_cast <;> norm_num [ Nat.pow_succ' ] at *;
        ring_nf at *;
        refine' Nat.recOn a _ _ <;> norm_num [ pow_succ' ] at *;
        · refine' Nat.recOn M _ _ <;> norm_num [ pow_succ' ] at *;
          · exact Nat.recOn M' ( by norm_num ) fun n ihn => by norm_num [ pow_succ' ] ; nlinarith;
          · intro n hn; nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show n ≥ 0 by norm_num ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show M' ≥ 0 by norm_num ) ] ;
        · intro n hn; nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show M ≥ 0 by norm_num ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show M' ≥ 0 by norm_num ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show n ≥ 0 by norm_num ) ] ;
      · exact_mod_cast hM' ( M + M' + 100 + a + 1 ) ( by linarith );
      · exact_mod_cast hM _ ( by linarith );
    -- Let $Q$ be the set of primes in $(2m, 3m]$.
    set Q := Finset.filter Nat.Prime (Finset.Ioc (2 * m) (3 * m)) with hQ_def
    have hQ_card : Q.card ≤ (3 * m * Real.log 2) / Real.log (2 * m) := by
      have := lemma_prime_count m ( by linarith ) ; aesop;
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k ∈ Finset.Icc 1 (6 ^ Q.card) ∧ ∀ q ∈ Q, ∃ ℓ : ℤ, |(k * Nat.choose (2 * m) m : ℝ) - ℓ * q| < (q : ℝ) / 6 := by
      apply lemma_simultaneous_approximation (Nat.choose (2 * m) m) Q (by
      exact fun q hq => Nat.Prime.pos <| Finset.mem_filter.mp hq |>.2;)
    set A := Nat.choose (2 * m) m with hA_def
    set c := Nat.floor (3 * m / 5) with hc_def
    set n := k * A - c with hn_def
    have hn_gt_a : n > a := by
      have hn_gt_a : (k * A : ℝ) - c > a := by
        have hn_gt_a : (A : ℝ) ≥ (4 ^ m : ℝ) / (2 * m + 1) := by
          have := lemma_binom_bounds m ( by linarith ) ; aesop;
        have hn_gt_a' : (c : ℝ) ≤ 3 * m / 5 := by
          rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 3 * m ) 5, Nat.floor_le ( show 0 ≤ 3 * m / 5 by positivity ) ] ;
        have hn_gt_a'' : (k : ℝ) ≥ 1 := by
          exact_mod_cast Finset.mem_Icc.mp hk.1 |>.1
        have hn_gt_a''' : (k * A : ℝ) - c ≥ (4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5 := by
          exact sub_le_sub ( le_trans hn_gt_a ( le_mul_of_one_le_left ( Nat.cast_nonneg _ ) hn_gt_a'' ) ) hn_gt_a' |> le_trans ( by ring_nf; norm_num ) ;
        linarith [hm.2.1];
      norm_cast at *;
      rw [ Int.subNatNat_eq_coe ] at hn_gt_a ; omega;
    have hn_log : Real.log n ≥ 1.2 * m := by
      have hn_log : Real.log n ≥ Real.log ((4 ^ m : ℝ) / (2 * m + 1) - 3 * m / 5) := by
        have hA_ge : (A : ℝ) ≥ (4 ^ m : ℝ) / (2 * m + 1) := by
          have := lemma_binom_bounds m ( by linarith ) ; aesop;
        have hc_le : (c : ℝ) ≤ 3 * m / 5 := by
          rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 3 * m ) 5, Nat.floor_le ( show 0 ≤ ( 3 * m / 5 : ℕ ) by positivity ) ] ;
        gcongr;
        · linarith [ show ( a : ℝ ) ≥ 0 by positivity ];
        · rw [ Nat.cast_sub ] <;> norm_num at *;
          · nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith ];
          · grind;
      linarith [ hm.2.2.2 ] ;
    have hn_log_bound : 2.1 * Real.log n < 3 * m := by
      -- Using the bounds on $A$ and $k$, we have $\log n \leq \log(kA) \leq \log(6^{|Q|} A) = |Q| \log 6 + \log A$.
      have hn_log_bound : Real.log n ≤ Q.card * Real.log 6 + Real.log A := by
        have hn_log_bound : Real.log n ≤ Real.log (k * A) := by
          exact Real.log_le_log ( Nat.cast_pos.mpr <| pos_of_gt hn_gt_a ) <| mod_cast Nat.sub_le _ _ |> le_trans <| by norm_num;
        have hn_log_bound' : Real.log (k * A) ≤ Real.log (6 ^ Q.card * A) := by
          exact Real.log_le_log ( mul_pos ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk.1 |>.1 ) <| Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) <| mul_le_mul_of_nonneg_right ( mod_cast Finset.mem_Icc.mp hk.1 |>.2 ) <| Nat.cast_nonneg _;
        have hn_log_bound'' : Real.log (6 ^ Q.card * A) = Q.card * Real.log 6 + Real.log A := by
          rw [ Real.log_mul ( by positivity ) ( by norm_cast; exact Nat.ne_of_gt ( Nat.choose_pos ( by linarith ) ) ), Real.log_pow ]
        linarith [hn_log_bound, hn_log_bound', hn_log_bound'']
      have hn_log_bound' : Real.log A ≤ m * Real.log 4 := by
        have hn_log_bound' : A ≤ 4 ^ m := by
          rw [ show ( 4 : ℕ ) ^ m = ( 2 ^ m ) ^ 2 by rw [ pow_right_comm ] ; norm_num ] ; nlinarith [ show Nat.choose ( 2 * m ) m ≤ 2 ^ ( 2 * m ) by rw [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr ( by linarith ) ), pow_mul' 2 2 m ] ;
        have hn_log_bound'' : Real.log A ≤ Real.log (4 ^ m) := by
          exact Real.log_le_log ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) <| mod_cast hn_log_bound'
        rw [Real.log_pow] at hn_log_bound''; norm_num at *; exact hn_log_bound'';
      have hn_log_bound'' : Real.log n ≤ (3 * m * Real.log 2) / Real.log (2 * m) * Real.log 6 + m * Real.log 4 := by
        exact hn_log_bound.trans ( add_le_add ( mul_le_mul_of_nonneg_right hQ_card <| Real.log_nonneg <| by norm_num ) hn_log_bound' ) |> le_trans <| by ring_nf; norm_num;
      have hn_log_bound''' : 2.1 * Real.log n < 3 * m := by
        ring_nf at *; nlinarith [ ( by norm_cast; linarith : ( 100 :ℝ ) ≤ m ) ] ;
      exact hn_log_bound'''
    have hn_div : ∀ p : ℕ, Nat.Prime p → p ≤ 3 * m → p ∣ F n := by
      apply lemma_divisibility m (by linarith) k (by
      grind) (by
      aesop) hn_log
    use n
    constructor
    exact_mod_cast hn_gt_a
    intro p hp hpn
    by_cases hp_le : p ≤ 3 * m
    exact hn_div p hp hp_le
    have h_contra : 2.1 * Real.log n < p := by
      exact lt_of_lt_of_le hn_log_bound ( mod_cast by linarith )
    exact absurd hpn (by linarith);
  exact Set.infinite_of_forall_exists_gt fun a => by obtain ⟨ n, hn₁, hn₂ ⟩ := h_infinite a; exact ⟨ n, hn₂, hn₁ ⟩ ;

/-
Statement from the Formal Conjectures Project.
-/
theorem erdos_457 : ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  -- Let's choose ε = 0.1.
  use 0.1; norm_num;
  -- Apply the theorem thm_main to conclude that the set is infinite.
  apply thm_main.mono; intro n hn; exact (by
  -- By definition of $F(n)$, we know that $F(n) = \prod_{i=1}^{\lfloor \log n \rfloor} (n + i)$.
  have hF_def : F n = ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) := by
    -- By definition of $F(n)$, we know that $F(n) = \prod_{i=1}^{\lfloor \log n \rfloor} (n + i)$ follows directly from the definition of $F$.
    simp [F, A_func]
  generalize_proofs at *; (
  -- By combining the results from hn and hF_def, we can conclude that for any prime p ≤ 2.1 * log n, p divides the product of (n + i) for i in the specified range.
  intros p hp hprime; exact hF_def ▸ hn p hprime (by linarith)))

end

end Erdos457

#print axioms Erdos457.thm_main
-- 'Erdos457.thm_main' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos457.erdos_457
-- 'Erdos457.erdos_457' depends on axioms: [propext, Classical.choice, Quot.sound]
