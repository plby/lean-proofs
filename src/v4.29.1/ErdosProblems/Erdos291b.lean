/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 291.
https://www.erdosproblems.com/forum/thread/291

Formalization status:
- Partial
- Conditional on: prime_number_theorem

Informal authors:
- Wouter van Doorn

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/291#post-4219
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem291.lean
- https://github.com/Woett/Miscellaneous/blob/main/Generalized%20harmonic%20sums%20have%20arbitrarily%20large%20prime%20factors.pdf
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
-/
/-
Let $r_1, r_2, \ldots$ be a bounded sequence of non-zero integers, let $L_n$ be the least common multiple of $1, 2, \ldots, n$ and let $X_n$ be such that $\frac{X_n}{L_n} = \sum_{i=1}^n \frac{r_i}{i}$. Below you can find a conditional Lean proof that $X_n$ has arbitrarily large prime divisors. From this fact one can conclude that, if the $r_i$ are periodic, then $\limsup \gcd(X_n, L_n) = \infty$. In particular, there are infinitely many $n$ for which $\gcd(X_n, L_n) > 1$, settling a generalization of the second part of Erdős Problem #291 (https://www.erdosproblems.com/291). The Lean proof was formalized by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) based on the following note:

https://github.com/Woett/Miscellaneous/blob/main/Generalized%20harmonic%20sums%20have%20arbitrarily%20large%20prime%20factors.pdf

This note itself is based on my paper

W. van Doorn, On the non-monotonicity of the denominator of generalized harmonic sums. arXiv:2411.03073 (2024)

in which a generalized version of Erdős Problem #290 (https://www.erdosproblems.com/290) is solved.

The Lean proof uses two prime number theorem type results as axioms, which is the reason the Lean proof is conditional. Both results will eventually follow from the PNT+ Project which can be found here:

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd

The exact statements of these two axioms are recorded as h_priemteller and h_bla0 below, and can be found as Lemma 2 and Lemma 3 in the GitHub note I linked above.

-/

import Mathlib

namespace Erdos291b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

-- The proof of `exists_good_p` times out at Lean's default heartbeat limit.
set_option maxHeartbeats 300000

/-
Definitions of L_n and X_n as in the problem description.
-/
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

def X (r : ℕ → ℤ) (n : ℕ) : ℚ := (L n : ℚ) * ∑ i ∈ Finset.Icc 1 n, (r i : ℚ) / i

/-
z is the number of primes smaller than m.
-/
def z (m : ℕ) : ℕ := ((Finset.range m).filter Nat.Prime).card

/-
Redefining Parameters to include the admitted lemmas as assumptions, and J1, J2.
-/
structure ProblemParameters where
  r : ℕ → ℤ
  m : ℕ
  tilde_m : ℕ
  q0 : ℕ
  hm4 : 4 ≤ m
  h_r_nz : ∀ i, r i ≠ 0
  h_r_bdd : ∀ i, |r i| < m
  htilde_m : 20 * m^(2 * z m) < tilde_m
  hq0_prime : q0.Prime
  hq0_dvd : q0 ∣ tilde_m
  hq0_large : m^(2 * z m - 1) < q0
  h_priemteller : (m : ℝ)^(2 * z m) < Real.exp (2.52 * m)
  h_bla0 : ∀ w ∈ Finset.Ico (tilde_m - m^(2 * z m - 1)) tilde_m, ∀ k, L (w + k) > 2^(w + k)

def J1' (p : ProblemParameters) : Finset ℕ := Finset.Ico (p.tilde_m - p.m^(2 * z p.m - 1)) p.tilde_m
def J2' (p : ProblemParameters) : Finset ℕ := Finset.Ico p.tilde_m (p.tilde_m + p.m^(2 * z p.m - 1))

/-
For m >= 4, z(m) >= 2.
-/
theorem z_ge_two (m : ℕ) (hm : 4 ≤ m) : 2 ≤ z m := by
  exact Finset.one_lt_card.2 ⟨ 2, by norm_num; linarith, 3, by norm_num; linarith ⟩

/-
Helper lemma to construct ProblemParameters from global hypotheses.
-/
lemma exists_good_p (r : ℕ → ℤ) (m : ℕ) (hm : 4 ≤ m) (h_r_nz : ∀ i, r i ≠ 0) (h_r_bdd : ∀ i, |r i| < m)
    (h_priemteller : (m : ℝ) ^ (2 * z m) < Real.exp (2.52 * m))
    (h_bla0_global : ∀ n ≥ 100, L n > 2 ^ n) :
    ∃ p : ProblemParameters, p.r = r ∧ p.m = m := by
      obtain ⟨q0, hq0_prime, hq0_large⟩ : ∃ q0, Nat.Prime q0 ∧ q0 > m ^ (2 * z m - 1) := by
        exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( m ^ ( 2 * z m - 1 ) + 1 ) )
      generalize_proofs at *;
      obtain ⟨tilde_m, htilde_m_gt, htilde_m_div⟩ : ∃ tilde_m, tilde_m > 20 * m^(2 * z m) ∧ q0 ∣ tilde_m := by
        exact ⟨ q0 * ( 20 * m ^ ( 2 * z m ) + 1 ), by nlinarith [ pow_pos ( zero_lt_four.trans_le hm ) ( 2 * z m ), hq0_prime.two_le ], by norm_num ⟩
      generalize_proofs at *; (
      constructor;
      swap;
      constructor;
      any_goals tauto;
      intro w hw k
      have h_wk_ge_100 : w + k ≥ 100 := by
        -- Since $m \geq 4$, we have $m^{2z-1} \geq 4^3 = 64$.
        have h_m_pow : m^(2 * z m - 1) ≥ 64 := by
          have h_m_pow : 2 * z m - 1 ≥ 3 := by
            exact Nat.le_sub_one_of_lt ( by linarith [ show z m ≥ 2 from z_ge_two m hm ] )
          generalize_proofs at *; (
          exact le_trans ( by decide ) ( Nat.pow_le_pow_left hm _ ) |> le_trans <| Nat.pow_le_pow_right ( by linarith ) h_m_pow)
        generalize_proofs at *; (
        linarith [ Finset.mem_Ico.mp hw, Nat.sub_add_cancel ( show m ^ ( 2 * z m - 1 ) ≤ tilde_m from by linarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ m ) ( show 2 * z m - 1 ≤ 2 * z m from Nat.sub_le _ _ ) ] ), pow_le_pow_right₀ ( by linarith : 1 ≤ m ) ( show 2 * z m ≥ 2 * z m - 1 from Nat.sub_le _ _ ) ])
      generalize_proofs at *; exact h_bla0_global (w + k) h_wk_ge_100;)

/-
The sum $\sum_{i=w+1}^{w+k} \frac{r_i}{i}$ is non-zero.
-/
theorem bla_nonzero (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p) (k : ℕ) (hk : w + k ∈ J2' p) :
    ∑ i ∈ Finset.Ioc w (w + k), (p.r i : ℚ) / i ≠ 0 := by
      -- Let's first establish that $\tilde{m}$ is the unique multiple of $q_0$ in the interval $S = \{w+1, \dots, w+k\}$.
      have h_unique : ∀ i ∈ Finset.Icc (w + 1) (w + k), i ≠ p.tilde_m → ¬(p.q0 ∣ i) := by
        intro i hi hne hdvd
        have h_bounds : w + 1 ≤ i ∧ i ≤ w + k := by
          aesop
        have h_tilde_bounds : p.tilde_m - p.m^(2 * z p.m - 1) ≤ w ∧ w + k < p.tilde_m + p.m^(2 * z p.m - 1) := by
          exact ⟨ Finset.mem_Ico.mp hw |>.1, Finset.mem_Ico.mp hk |>.2 ⟩
        have h_q0_bounds : p.q0 > p.m^(2 * z p.m - 1) := by
          exact p.hq0_large
        have h_unique : ∀ i ∈ Finset.Icc (w + 1) (w + k), i ≠ p.tilde_m → ¬(p.q0 ∣ i) := by
          intros i hi hne hdvd
          have h_bounds : p.tilde_m - p.m^(2 * z p.m - 1) < i ∧ i < p.tilde_m + p.m^(2 * z p.m - 1) := by
            constructor <;> linarith [ Finset.mem_Icc.mp hi ];
          have h_unique : p.q0 ∣ p.tilde_m := by
            exact p.hq0_dvd;
          have h_unique : p.q0 ∣ Int.natAbs (i - p.tilde_m) := by
            exact Int.natAbs_dvd_natAbs.mpr ( dvd_sub ( Int.natCast_dvd_natCast.mpr hdvd ) ( Int.natCast_dvd_natCast.mpr h_unique ) );
          have h_unique : Int.natAbs (i - p.tilde_m) < p.q0 := by
            grind;
          exact h_unique.not_ge ( Nat.le_of_dvd ( Int.natAbs_pos.mpr ( sub_ne_zero_of_ne <| mod_cast hne ) ) ‹_› )
        aesop;
      -- Let $L_{local} = \text{lcm}(S)$.
      set L_local := Finset.lcm (Finset.Icc (w + 1) (w + k)) id with hL_local;
      -- Consider the sum $N = \sum_{i \in S} r_i \frac{L_{local}}{i}$.
      set N := ∑ i ∈ Finset.Icc (w + 1) (w + k), (p.r i : ℤ) * (L_local / i) with hN;
      -- We show that $N$ is not divisible by $q_0$.
      have hN_not_div : ¬(p.q0 ∣ Int.natAbs N) := by
        -- For $i = \tilde{m}$, term is $r_{\tilde{m}} \frac{L_{local}}{\tilde{m}}$.
        -- $v_{q_0}(r_{\tilde{m}}) = 0$ since $0 < |r_{\tilde{m}}| < m < q_0$.
        -- $v_{q_0}(\frac{L_{local}}{\tilde{m}}) = 0$.
        -- So $v_{q_0}(\text{term } \tilde{m}) = 0$.
        have h_term_tilde_m : ¬(p.q0 ∣ Int.natAbs ((p.r p.tilde_m : ℤ) * (L_local / p.tilde_m))) := by
          -- Since $p.q0$ is prime and $p.r p.tilde_m$ is not divisible by $p.q0$, it follows that $p.q0$ does not divide $p.r p.tilde_m * (L_local / p.tilde_m)$.
          have h_not_div : ¬(p.q0 ∣ Int.natAbs (p.r p.tilde_m)) ∧ ¬(p.q0 ∣ Int.natAbs (L_local / p.tilde_m)) := by
            constructor;
            · have h_not_div_r : |p.r p.tilde_m| < p.q0 := by
                exact lt_of_lt_of_le ( p.h_r_bdd _ ) ( mod_cast p.hq0_large.le.trans' ( Nat.le_self_pow ( Nat.sub_ne_zero_of_lt ( by linarith [ show z p.m > 0 from Finset.card_pos.mpr ⟨ 2, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ p.hm4 ] ), by norm_num ⟩ ⟩ ] ) ) _ ) );
              exact fun h => h_not_div_r.not_ge ( Int.le_of_dvd ( abs_pos.mpr ( p.h_r_nz _ ) ) ( by simpa [ ← Int.natCast_dvd_natCast ] using h ) );
            · -- Since $p.q0$ is prime and $p.tilde_m$ is the unique multiple of $p.q0$ in $S$, it follows that $v_{q0}(L_{local}) = v_{q0}(p.tilde_m)$.
              have h_val : Nat.factorization L_local p.q0 = Nat.factorization p.tilde_m p.q0 := by
                have h_val_L_local : Nat.factorization L_local p.q0 = Finset.sup (Finset.Icc (w + 1) (w + k)) (fun i => Nat.factorization i p.q0) := by
                  have h_val_L_local : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) → Nat.factorization (Finset.lcm S id) p.q0 = Finset.sup S (fun i => Nat.factorization i p.q0) := by
                    intros S hS_nonzero
                    induction S using Finset.induction with
                    | empty => simp +decide [ Finset.lcm ]
                    | @insert i S hiS ih =>
                      simp_all +decide [ Finset.lcm_insert ];
                      erw [ Nat.factorization_lcm ] <;> simp_all +decide;
                  exact h_val_L_local fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
                rw [ h_val_L_local ];
                refine le_antisymm ?_ ?_;
                · simp +zetaDelta at *;
                  intro i hi₁ hi₂; by_cases hi₃ : i = p.tilde_m <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
                · refine Finset.le_sup ( f := fun i => Nat.factorization i p.q0 ) ?_;
                  unfold J1' J2' at * ; aesop;
              rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_cast;
              · rw [ Nat.factorization_div ];
                · intro H; have := H p.q0; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
                  exact absurd ( this.resolve_right ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by rintro h; have := p.hq0_prime; aesop ) ) ) ) ( by exact fun h => absurd h ( by exact fun h' => absurd ( p.hq0_prime ) ( by aesop ) ) );
                · refine Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩ );
                  · linarith [ Finset.mem_Ico.mp hw ];
                  · unfold J2' at hk; aesop;
              · exact Nat.Prime.ne_zero p.hq0_prime;
              · refine Nat.ne_of_gt ( Nat.div_pos ?_ ?_ );
                · refine Nat.le_of_dvd ( Nat.pos_of_ne_zero ?_ ) ?_;
                  · norm_num +zetaDelta at *;
                  · refine Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩ );
                    · linarith [ Finset.mem_Ico.mp hw ];
                    · exact Finset.mem_Ico.mp hk |>.1;
                · linarith [ p.htilde_m, pow_pos ( by linarith [ p.hm4 ] : 0 < p.m ) ( 2 * z p.m ) ];
          simp_all +decide [Int.natAbs_mul];
          exact Nat.Prime.not_dvd_mul ( p.hq0_prime ) h_not_div.1 h_not_div.2;
        -- For $i \ne \tilde{m}$, $i$ is not a multiple of $q_0$, so $v_{q_0}(i) = 0$.
        -- $v_{q_0}(\frac{L_{local}}{i}) = v_{q_0}(L_{local}) \ge 1$.
        -- So $v_{q_0}(\text{term } i) \ge 1$.
        have h_term_other : ∀ i ∈ Finset.Icc (w + 1) (w + k), i ≠ p.tilde_m → p.q0 ∣ Int.natAbs ((p.r i : ℤ) * (L_local / i)) := by
          intros i hi hi_ne_tilde_m
          have h_div_L_local : p.q0 ∣ L_local := by
            have h_div_L_local : p.tilde_m ∈ Finset.Icc (w + 1) (w + k) := by
              unfold J1' J2' at * ; aesop;
            exact dvd_trans ( p.hq0_dvd ) ( Finset.dvd_lcm h_div_L_local );
          rw [ Int.natAbs_mul ];
          refine dvd_mul_of_dvd_right ?_ (Int.natAbs (p.r i));
          refine Nat.dvd_div_of_mul_dvd ?_;
          refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ h_div_L_local;
          · exact Nat.Coprime.symm ( p.hq0_prime.coprime_iff_not_dvd.mpr ( h_unique i hi hi_ne_tilde_m ) );
          · exact Finset.dvd_lcm hi;
        -- Therefore, $N \equiv r_{\tilde{m}} \frac{L_{local}}{\tilde{m}} \not\equiv 0 \pmod{q_0}$.
        have hN_mod : N ≡ (p.r p.tilde_m : ℤ) * (L_local / p.tilde_m) [ZMOD p.q0] := by
          have hN_mod : ∑ i ∈ Finset.Icc (w + 1) (w + k) \ {p.tilde_m}, (p.r i : ℤ) * (L_local / i) ≡ 0 [ZMOD p.q0] := by
            exact Int.modEq_zero_iff_dvd.mpr <| Finset.dvd_sum fun i hi => Int.natCast_dvd.mpr <| h_term_other i ( Finset.mem_sdiff.mp hi |>.1 ) <| by aesop;
          by_cases h : p.tilde_m ∈ Finset.Icc ( w + 1 ) ( w + k ) <;> simp_all +decide [ Int.modEq_iff_dvd ];
          contrapose! h;
          constructor <;> linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, pow_pos ( by linarith [ p.hm4 ] : 0 < p.m ) ( 2 * z p.m - 1 ) ];
        rw [ ← Int.natCast_dvd ] at *;
        exact fun h => h_term_tilde_m <| Int.dvd_of_emod_eq_zero <| hN_mod.symm.trans <| Int.modEq_zero_iff_dvd.mpr h;
      -- Since $N$ is not divisible by $q_0$, the sum $\sum_{i=w+1}^{w+k} \frac{r_i}{i}$ cannot be zero.
      have h_sum_nonzero : (∑ i ∈ Finset.Icc (w + 1) (w + k), (p.r i : ℚ) / i) = N / L_local := by
        simp +decide [ hN, Finset.sum_div _ _ _ ];
        refine Finset.sum_congr rfl fun i hi => ?_;
        rw [ Int.cast_div ] <;> norm_num;
        · rw [ eq_div_iff ( Nat.cast_ne_zero.mpr <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) ] ; ring;
        · exact_mod_cast Finset.dvd_lcm hi;
        · linarith [ Finset.mem_Icc.mp hi ];
      simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)];
      norm_cast at * ; aesop

/-
Lemma 3: For all k with w+k in J2, the absolute value of the sum of r_i/i from w+1 to w+k is at least 1/(w+k)^k.
-/
theorem bla (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p) (k : ℕ) (hk : w + k ∈ J2' p) :
    |∑ i ∈ Finset.Ioc w (w + k), (p.r i : ℚ) / i| ≥ 1 / (w + k : ℚ) ^ k := by
      -- We have already shown that the sum $S = \sum_{i=w+1}^{w+k} \frac{r_i}{i}$ is non-zero (Lemma `bla_nonzero`).
      have h_nonzero : ∑ i ∈ Finset.Ioc w (w + k), (p.r i : ℚ) / i ≠ 0 := by
        exact bla_nonzero p w hw k hk;
      -- Let $L_{local} = \text{lcm}(w+1, \dots, w+k)$.
      set Llocal := Finset.lcm (Finset.Ioc w (w + k)) (fun i => i) with hLlocal;
      -- We can write $S = \frac{N}{L_{local}}$ for some integer $N$.
      obtain ⟨N, hN⟩ : ∃ N : ℤ, (∑ i ∈ Finset.Ioc w (w + k), (p.r i : ℚ) / i) = N / Llocal := by
        use ∑ i ∈ Finset.Ioc w (w + k), p.r i * (Llocal / i);
        push_cast [ Finset.sum_div _ _ _ ];
        refine Finset.sum_congr rfl fun i hi => ?_;
        rw [ Int.cast_div ] <;> norm_num;
        · rw [ eq_div_iff ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) ] ; ring;
        · exact_mod_cast Finset.dvd_lcm hi;
        · linarith [ Finset.mem_Ioc.mp hi ];
      -- Since $S \ne 0$, $N \ne 0$, so $|N| \ge 1$.
      have hN_abs : |N| ≥ 1 := by
        contrapose! h_nonzero; aesop;
      -- Thus $|S| = \frac{|N|}{L_{local}} \ge \frac{1}{L_{local}}$.
      have hS_abs : |∑ i ∈ Finset.Ioc w (w + k), (p.r i : ℚ) / i| ≥ 1 / Llocal := by
        rw [ hN, abs_div ];
        gcongr
        focus
          norm_cast
        · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) );
        · norm_cast;
        · norm_num [ abs_of_nonneg ];
      -- We know $L_{local}$ divides $\prod_{i=w+1}^{w+k} i$.
      have hLlocal_div : Llocal ∣ ∏ i ∈ Finset.Ioc w (w + k), i := by
        exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
      -- Each term in the product is $\le w+k$. There are $k$ terms.
      have h_prod_le : ∏ i ∈ Finset.Ioc w (w + k), i ≤ (w + k)^k := by
        exact le_trans ( Finset.prod_le_prod' fun _ _ => show _ ≤ w + k from by linarith [ Finset.mem_Ioc.mp ‹_› ] ) ( by norm_num );
      refine le_trans ?_ hS_abs;
      gcongr
      focus
        norm_cast
      · exact Nat.pos_of_dvd_of_pos hLlocal_div ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Ioc.mp hi ] );
      · exact_mod_cast Nat.le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Ioc.mp hi ] ) hLlocal_div ) h_prod_le

/-
The function x / log x is monotonically increasing for x >= 3.
-/
theorem x_div_log_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) : x / Real.log x ≤ y / Real.log y := by
  -- The derivative of $f(x) = x / \log x$ is $f'(x) = \frac{\log x - 1}{(\log x)^2}$.
  have h_deriv : ∀ x > 1, deriv (fun x => x / Real.log x) x = (Real.log x - 1) / (Real.log x)^2 := by
    intro x hx; norm_num [ show x ≠ 0 by linarith, show Real.log x ≠ 0 by exact ne_of_gt <| Real.log_pos hx ] ;
  -- Since $x \geq 3$, we have $\log x \geq \log 3 > 1$.
  have h_log_x_gt_1 : 1 < Real.log x := by
    exact Real.lt_log_iff_exp_lt ( by linarith ) |>.2 ( by exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) );
  by_cases hy : y > x;
  · have := exists_deriv_eq_slope ( f := fun x => x / Real.log x ) hy;
    contrapose! this;
    exact ⟨ continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by linarith [ hz.1 ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hz.1 ] ) ) ), fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( differentiableAt_id ) ( Real.differentiableAt_log ( by linarith [ hz.1 ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hz.1 ] ) ) ) ), fun z hz => by rw [ h_deriv z ( by linarith [ hz.1 ] ) ] ; rw [ Ne, div_eq_div_iff ] <;> nlinarith [ hz.1, hz.2, Real.log_pos ( by linarith [ hz.1 ] : 1 < z ), Real.log_le_log ( by linarith [ hz.1 ] ) hz.1.le, Real.log_le_log ( by linarith [ hz.1 ] ) hz.2.le ] ⟩;
  · grind

/-
The lcm of numbers from w+1 to w+k is at most (w+k)^k.
-/
theorem lcm_le_pow (w k : ℕ) : Finset.lcm (Finset.Ioc w (w + k)) id ≤ (w + k)^k := by
  -- The length of the interval $[w+1, w+k]$ is $k$, so the product of the elements is at most $(w+k)^k$.
  have prod_le : ∏ x ∈ Finset.Ioc w (w + k), x ≤ (w + k) ^ k := by
    exact le_trans ( Finset.prod_le_prod' fun x hx => show x ≤ w + k by linarith [ Finset.mem_Ioc.mp hx ] ) ( by norm_num );
  refine le_trans ?_ prod_le;
  exact Nat.le_of_dvd ( Finset.prod_pos fun x hx => by linarith [ Finset.mem_Ioc.mp hx ] ) ( Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx )

/-
Numerical bound step 1: 20 m^(2z) / (log 20 + 2.52 m) > 6 m^(2z-1).
-/
theorem bound_step1 (m : ℕ) (hm : 4 ≤ m) (z : ℕ) (hz : 2 ≤ z) :
    20 * (m : ℝ)^(2*z) / (Real.log 20 + 2.52 * m) > 6 * (m : ℝ)^(2*z-1) := by
      -- We want to show $\frac{20 m^{2z}}{\log 20 + 2.52 m} > 6 m^{2z-1}$.
      suffices h_div : 20 * (m : ℝ) > 6 * (Real.log 20 + 2.52 * m) by
        rcases z with ( _ | _ | z ) <;> norm_num [ Nat.mul_succ, pow_succ ] at *;
        field_simp;
        linarith;
      -- We know that $\log 20 \approx 2.9957$.
      have h_log_20 : Real.log 20 < 3 := by
        rw [ Real.log_lt_iff_lt_exp ] <;> norm_num;
        have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ;
      nlinarith [ ( by norm_cast : ( 4 : ℝ ) ≤ m ) ]

/-
Numerical bound step 2: 6 m^(2z-1) > 2m + 5.8 m^(2z-1).
-/
theorem bound_step2 (m : ℕ) (hm : 4 ≤ m) (z : ℕ) (hz : 2 ≤ z) :
    6 * (m : ℝ)^(2*z-1) > 2 * m + 5.8 * (m : ℝ)^(2*z-1) := by
      -- Since $m \geq 4$ and $z \geq 2$, we have $2z - 2 \geq 2$. Therefore, $m^{2z - 2} \geq m^2 \geq 16 > 10$.
      have h_exp : (m : ℝ) ^ (2 * z - 2) > 10 := by
        exact_mod_cast lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_left hm _ ) |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( by linarith ) <| show 2 * z - 2 ≥ 2 by exact Nat.le_sub_of_add_le <| by linarith;
      rcases z with ( _ | _ | z ) <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
      nlinarith [ ( by norm_cast : ( 4 : ℝ ) ≤ m ) ]

/-
Numerical bound step 3: 2m + 5.8 m^(2z-1) > 2z + 4 m^(2z-1) / log 2.
-/
theorem bound_step3 (m : ℕ) (hm : 4 ≤ m) (z : ℕ) (hzm : z ≤ m) :
    2 * m + 5.8 * (m : ℝ)^(2*z-1) > 2 * z + 4 * (m : ℝ)^(2*z-1) / Real.log 2 := by
      -- We'll use that $m \ge z$ to show that $2m \ge 2z$.
      have h2m_ge_2z : (2 * m : ℝ) ≥ 2 * z := by
        exact_mod_cast Nat.mul_le_mul_left 2 hzm;
      -- We'll use that $5.8 > \frac{4}{\log 2}$ to conclude the proof.
      have h5_8_gt_4_div_log2 : (5.8 : ℝ) > 4 / Real.log 2 := by
        rw [ gt_iff_lt, div_lt_iff₀ ] <;> have := Real.log_two_gt_d9 <;> norm_num at * <;> linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
      field_simp;
      rw [ gt_iff_lt, div_lt_iff₀ ] at h5_8_gt_4_div_log2 <;> nlinarith [ Real.log_pos one_lt_two, pow_pos ( by positivity : 0 < ( m : ℝ ) ) ( 2 * z - 1 ) ]

/-
Numerical bound step 4: 2z + 4 m^(2z-1) / log 2 > 1 + z / log 2 + 2k / log 2.
-/
theorem bound_step4 (m : ℕ) (_hm : 4 ≤ m) (z : ℕ) (hz : 2 ≤ z) (k : ℕ) (hk : k < 2 * m ^ (2 * z - 1)) :
    2 * z + 4 * (m : ℝ) ^ (2 * z - 1) / Real.log 2 > 1 + (z : ℝ) / Real.log 2 + 2 * k / Real.log 2 := by
      -- Since $k < 2 m^{2z-1}$, it follows that $\frac{2k}{\log 2} < \frac{4 m^{2z-1}}{\log 2}$, so it suffices to show that $2z > 1 + \frac{z}{\log 2}$.
      have h_step4 : 2 * (z : ℝ) > 1 + (z : ℝ) / Real.log 2 := by
        rw [ add_div', gt_iff_lt, div_lt_iff₀ ] <;> norm_num;
        · have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ show ( z : ℝ ) ≥ 2 by norm_cast ] ;
        · positivity;
      nlinarith [ show ( k :ℝ ) < 2 * m ^ ( 2 * z - 1 ) by exact_mod_cast hk, show ( 0 :ℝ ) < m ^ ( 2 * z - 1 ) by positivity, show ( 0 :ℝ ) < Real.log 2 by positivity, mul_div_cancel₀ ( 4 * m ^ ( 2 * z - 1 ) :ℝ ) ( ne_of_gt <| Real.log_pos one_lt_two ), mul_div_cancel₀ ( 2 * k :ℝ ) ( ne_of_gt <| Real.log_pos one_lt_two ), mul_div_cancel₀ ( z :ℝ ) ( ne_of_gt <| Real.log_pos one_lt_two ) ]

/-
Lemma 4a: The logarithmic inequality holds.
-/
theorem boring_log_ineq (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p) (k : ℕ) (hk : w + k ∈ J2' p) :
    (w + k : ℝ) / Real.log (w + k) > 1 / Real.log (w + k) + (z p.m) / Real.log 2 + 2 * k / Real.log 2 := by
      -- By transitivity of inequalities, we can chain the steps together.
      have h_chain : (w + k : ℝ) / (Real.log (w + k)) > 6 * (p.m : ℝ)^(2 * (z p.m) - 1) ∧ 6 * (p.m : ℝ)^(2 * (z p.m) - 1) > 2 * p.m + 5.8 * (p.m : ℝ)^(2 * (z p.m) - 1) ∧ 2 * p.m + 5.8 * (p.m : ℝ)^(2 * (z p.m) - 1) > 2 * (z p.m) + 4 * (p.m : ℝ)^(2 * (z p.m) - 1) / (Real.log 2) ∧ 2 * (z p.m) + 4 * (p.m : ℝ)^(2 * (z p.m) - 1) / (Real.log 2) > 1 + (z p.m : ℝ) / (Real.log 2) + 2 * k / (Real.log 2) ∧ 1 + (z p.m : ℝ) / (Real.log 2) + 2 * k / (Real.log 2) > 1 / (Real.log (w + k)) + (z p.m : ℝ) / (Real.log 2) + 2 * k / (Real.log 2) := by
        refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
        · -- Apply the lemma `bound_step1` to get the inequality.
          have h_bound_step1 : (20 * (p.m : ℝ) ^ (2 * (z p.m)) : ℝ) / (Real.log 20 + 2.52 * p.m) > 6 * (p.m : ℝ) ^ (2 * (z p.m) - 1) := by
            apply bound_step1 p.m p.hm4 ( z p.m ) ( z_ge_two p.m p.hm4 );
          -- Apply the lemma `x_div_log_mono` to get the inequality.
          have h_x_div_log_mono : (w + k : ℝ) / Real.log (w + k) ≥ (20 * (p.m : ℝ) ^ (2 * (z p.m))) / Real.log (20 * (p.m : ℝ) ^ (2 * (z p.m))) := by
            apply x_div_log_mono;
            · exact_mod_cast le_trans ( by norm_num ) ( Nat.mul_le_mul_left _ ( Nat.one_le_pow _ _ ( by linarith [ p.hm4 ] ) ) );
            · norm_cast;
              linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, show p.tilde_m > 20 * p.m ^ ( 2 * z p.m ) from p.htilde_m ];
          refine lt_of_lt_of_le h_bound_step1 ( le_trans ?_ h_x_div_log_mono );
          gcongr;
          · exact Real.log_pos ( one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( mod_cast p.hm4.trans' ( by norm_num ) ) ) );
          · rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( pow_pos ( Nat.cast_pos.mpr ( by linarith [ p.hm4 ] ) ) _ ) ), Real.log_pow ] ; norm_num;
            have := p.h_priemteller;
            have := Real.log_lt_log ( by exact pow_pos ( Nat.cast_pos.mpr ( by linarith [ p.hm4 ] ) ) _ ) this ; norm_num at * ; linarith;
        · convert bound_step2 p.m p.hm4 ( z p.m ) ( z_ge_two p.m p.hm4 ) using 1;
        · convert bound_step3 p.m p.hm4 ( z p.m ) _ using 1;
          exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range p.m ) ⊆ Finset.Ico 2 p.m from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide );
        · refine bound_step4 p.m p.hm4 ( z p.m ) ( z_ge_two p.m p.hm4 ) k ?_ |> lt_of_le_of_lt ?_;
          · bound;
          · unfold J1' J2' at * ; norm_num at * ; linarith;
        · norm_num +zetaDelta at *;
          refine inv_lt_one_of_one_lt₀ ?_;
          rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk ] ) ];
          -- Since $w + k \geq \tilde{m} - m^{2z-1}$ and $\tilde{m} > 20m^{2z}$, we have $w + k > 20m^{2z} - m^{2z-1}$.
          have h_wk_lower_bound : (w + k : ℝ) > 20 * (p.m : ℝ)^(2 * (z p.m)) - (p.m : ℝ)^(2 * (z p.m) - 1) := by
            norm_cast;
            rw [ Int.subNatNat_eq_coe ] ; push_cast ; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, p.htilde_m ];
          refine lt_of_le_of_lt ?_ h_wk_lower_bound;
          refine le_trans ?_ ( sub_le_sub_left ( pow_le_pow_right₀ ( mod_cast by linarith [ p.hm4 ] ) ( show 2 * z p.m - 1 ≤ 2 * z p.m from Nat.sub_le _ _ ) )
            (20 * (p.m : ℝ) ^ (2 * z p.m)) );
          exact le_tsub_of_add_le_left ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; nlinarith [ show ( p.m : ℝ ) ^ ( 2 * z p.m ) ≥ 4 ^ ( 2 * z p.m ) by gcongr ; norm_cast ; linarith [ p.hm4 ], show ( 4 : ℝ ) ^ ( 2 * z p.m ) ≥ 16 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( Nat.mul_le_mul_left 2 ( show z p.m ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr <| by exact ne_of_gt <| z_ge_two p.m p.hm4 |> lt_of_lt_of_le ( by norm_num ) ) ) ) ] );
      linarith

/-
Lemma 4b: 2^(w+k) > 2 * (w+k)^(2k+z).
-/
theorem boring_exp_ineq (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p) (k : ℕ) (hk : w + k ∈ J2' p) :
    (2 : ℝ)^(w + k) > 2 * (w + k : ℝ)^(2 * k + z p.m) := by
      -- Apply the boring_log_ineq theorem to get the inequality.
      have h_log_ineq : (w + k : ℝ) / Real.log (w + k) > 1 / Real.log (w + k) + (z p.m) / Real.log 2 + 2 * k / Real.log 2 := by
        exact boring_log_ineq p w hw k hk;
      -- Multiply both sides of the inequality by `Real.log (w + k)` (which is positive since `w + k >= 20m^2z >= 3`).
      have h_mul : (w + k : ℝ) > 1 + (z p.m) * Real.log (w + k) / Real.log 2 + 2 * k * Real.log (w + k) / Real.log 2 := by
        contrapose! h_log_ineq;
        rw [ div_le_iff₀ ];
        · convert h_log_ineq using 1 ; ring_nf;
          rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, show w + k > 1 from by linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, show p.tilde_m > 20 * p.m ^ ( 2 * z p.m ) by exact p.htilde_m, show p.m ^ ( 2 * z p.m ) > 0 by exact pow_pos ( by linarith [ p.hm4 ] ) _ ] ] ) ) ) ] ; ring;
        · exact Real.log_pos <| mod_cast by linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, show w + k ≥ 3 by linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk, show p.m ≥ 4 by exact p.hm4, show p.tilde_m ≥ 20 * p.m ^ ( 2 * z p.m ) by exact p.htilde_m.le, show p.m ^ ( 2 * z p.m ) ≥ p.m by exact Nat.le_self_pow ( by linarith [ show z p.m ≥ 2 by exact z_ge_two p.m p.hm4 ] ) _ ] ] ;
      -- Exponentiate both sides of the inequality to eliminate the logarithms.
      have h_exp : Real.exp ((w + k) * Real.log 2) > Real.exp (Real.log 2 + (z p.m) * Real.log (w + k) + 2 * k * Real.log (w + k)) := by
        exact Real.exp_lt_exp.mpr ( by nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( ( z p.m : ℝ ) * Real.log ( w + k ) ) ( ne_of_gt ( Real.log_pos one_lt_two ) ), mul_div_cancel₀ ( 2 * k * Real.log ( w + k ) ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] );
      convert h_exp using 1 <;> norm_num [ Real.exp_add, Real.exp_nat_mul, Real.exp_log ]
      focus
        ring_nf
      · rw [ Real.exp_add, ← Real.rpow_natCast, ← Real.rpow_natCast, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num ; ring_nf;
      · rw [ Real.exp_log ( by norm_cast; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk ] ) ] ; ring_nf;
        rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk ] ) ] ; norm_num ; ring_nf;
        exact Or.symm (Or.inr trivial)

/-
Lemma 4: For all k with w+k in J2, 2^(w+k)/(w+k)^k - (w+k)^k * w^z > (w+k)^z.
-/
theorem boring (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p) (k : ℕ) (hk : w + k ∈ J2' p) :
    (2 : ℝ)^(w + k) / (w + k : ℝ)^k - (w + k : ℝ)^k * (w : ℝ)^(z p.m) > (w + k : ℝ)^(z p.m) := by
      -- From `boring_exp_ineq`, we have `2^(w+k) > 2 * (w+k)^(2k+z)`.
      have h_exp : (2 : ℝ)^(w + k) > 2 * (w + k : ℝ)^(2 * k + z p.m) := by
        convert boring_exp_ineq p w hw k hk using 1;
      field_simp;
      rw [ lt_div_iff₀ ];
      · ring_nf at *;
        rw [ pow_mul ] at *;
        nlinarith [ show 0 ≤ ( ( w : ℝ ) + k ) ^ k * ( ( w : ℝ ) + k ) ^ z p.m by positivity, show ( w : ℝ ) ^ z p.m ≤ ( ( w : ℝ ) + k ) ^ z p.m by gcongr ; linarith, show ( ( w : ℝ ) + k ) ^ k ≥ 1 by exact one_le_pow₀ ( by norm_cast; linarith [ Finset.mem_Ico.mp hw, Finset.mem_Ico.mp hk ] ) ];
      · cases k <;> cases w <;> norm_num at *
        focus
          positivity
        positivity

/-
The ratio L(w+k)/L(w) is bounded by (w+k)^k.
-/
theorem L_ratio_le (w k : ℕ) : L (w + k) / L w ≤ (w + k)^k := by
  -- By definition of $L$, we know that $L(w+k) = \text{lcm}(1, \ldots, w+k)$ and $L(w) = \text{lcm}(1, \ldots, w)$.
  have h_lcm_def : L (w + k) = Finset.lcm (Finset.Icc 1 (w + k)) id ∧ L w = Finset.lcm (Finset.Icc 1 w) id := by
    exact ⟨ rfl, rfl ⟩;
  -- By definition of $L$, we know that $L(w+k) = \text{lcm}(1, \ldots, w+k)$ and $L(w) = \text{lcm}(1, \ldots, w)$. Thus, $L(w+k) \mid L(w) \cdot \text{lcm}(w+1, \ldots, w+k)$.
  have h_div : L (w + k) ∣ L w * Finset.lcm (Finset.Ioc w (w + k)) id := by
    have h_div : Finset.lcm (Finset.Icc 1 (w + k)) id ∣ Finset.lcm (Finset.Icc 1 w ∪ Finset.Ioc w (w + k)) id := by
      convert Finset.lcm_dvd fun x hx => Finset.dvd_lcm ( show x ∈ Finset.Icc 1 w ∪ Finset.Ioc w ( w + k ) from ?_ ) using 1;
      exact if h : x ≤ w then Finset.mem_union_left _ ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩ ) else Finset.mem_union_right _ ( Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩ );
    refine dvd_trans h_div ?_;
    rw [ Finset.lcm_union ] ; aesop;
  refine Nat.div_le_of_le_mul ?_;
  refine Nat.le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( Nat.pos_of_ne_zero ?_ ) ( Nat.pos_of_ne_zero ?_ ) ) h_div ) ?_;
  · aesop;
  · norm_num [ Finset.lcm_eq_zero_iff ];
  · exact Nat.mul_le_mul_left _ ( lcm_le_pow _ _ )

lemma L_pos (n : ℕ) : 0 < L n := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [L, Finset.lcm_eq_zero_iff] at h
  simp at h

lemma sum_Icc_one_add_Ioc {G : Type*} [AddCommMonoid G] (f : ℕ → G)
    {w n : ℕ} (hwn : w ≤ n) :
    (∑ i ∈ Finset.Icc 1 w, f i) + ∑ i ∈ Finset.Ioc w n, f i =
      ∑ i ∈ Finset.Icc 1 n, f i := by
  have hsub : Finset.Icc 1 w ⊆ Finset.Icc 1 n := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, le_trans (Finset.mem_Icc.mp hx).2 hwn⟩
  have hsum := Finset.sum_sdiff hsub (f := f)
  have hsdiff : Finset.Icc 1 n \ Finset.Icc 1 w = Finset.Ioc w n := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hsdiff] at hsum
  simpa [add_comm] using hsum

lemma X_div_L_sub_X_div_L (r : ℕ → ℤ) {w n : ℕ} (hwn : w ≤ n) :
    X r n / (L n : ℚ) - X r w / (L w : ℚ) =
      ∑ i ∈ Finset.Ioc w n, (r i : ℚ) / i := by
  have hLn : (L n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (L_pos n))
  have hLw : (L w : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (L_pos w))
  have hsum := sum_Icc_one_add_Ioc (fun i => (r i : ℚ) / i) hwn
  unfold X
  rw [← hsum]
  field_simp [hLn, hLw]
  ring

lemma L_dvd_of_le {w n : ℕ} (hwn : w ≤ n) : L w ∣ L n := by
  unfold L
  exact Finset.lcm_dvd fun x hx =>
    Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
      le_trans (Finset.mem_Icc.mp hx).2 hwn⟩)

lemma xpo_pair_contradiction (p : ProblemParameters) (w : ℕ) (hw : w ∈ J1' p)
    (k : ℕ) (hk : w + k ∈ J2' p)
    (hw_small : |X p.r w| ≤ (w : ℚ) ^ (z p.m))
    (hn_small : |X p.r (w + k)| ≤ (w + k : ℚ) ^ (z p.m)) :
    False := by
  let n := w + k
  have hwn : w ≤ n := by
    dsimp [n]
    omega
  have hLn_pos_nat : 0 < L n := L_pos n
  have hLw_pos_nat : 0 < L w := L_pos w
  have hLn_pos : 0 < (L n : ℝ) := by exact_mod_cast hLn_pos_nat
  have hLw_pos : 0 < (L w : ℝ) := by exact_mod_cast hLw_pos_nat
  have hn_pos_nat : 0 < n := by
    have hmem := Finset.mem_Ico.mp hk
    have htilde_pos : 0 < p.tilde_m := by
      have htilde := p.htilde_m
      omega
    omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_pow_pos : 0 < (n : ℝ) ^ k := pow_pos hn_pos k
  have hdiff_lower_Q :
      1 / (n : ℚ) ^ k ≤ |X p.r n / (L n : ℚ) - X p.r w / (L w : ℚ)| := by
    have hsum := X_div_L_sub_X_div_L p.r hwn
    have hb := bla p w hw k hk
    dsimp [n]
    rw [hsum]
    simpa [n] using hb
  have hdiff_lower :
      1 / (n : ℝ) ^ k ≤ |(X p.r n : ℝ) / (L n : ℝ) - (X p.r w : ℝ) / (L w : ℝ)| := by
    have hcast :
        ((1 / (n : ℚ) ^ k : ℚ) : ℝ) ≤
          ((|X p.r n / (L n : ℚ) - X p.r w / (L w : ℚ)| : ℚ) : ℝ) := by
      exact_mod_cast hdiff_lower_Q
    simpa [Rat.cast_abs] using hcast
  have hw_small_R : |(X p.r w : ℝ)| ≤ (w : ℝ) ^ (z p.m) := by
    exact_mod_cast hw_small
  have hn_small_R : |(X p.r n : ℝ)| ≤ (n : ℝ) ^ (z p.m) := by
    exact_mod_cast hn_small
  have hdiff_upper :
      |(X p.r n : ℝ) / (L n : ℝ) - (X p.r w : ℝ) / (L w : ℝ)|
        ≤ (n : ℝ) ^ (z p.m) / (L n : ℝ) + (w : ℝ) ^ (z p.m) / (L w : ℝ) := by
    calc
      |(X p.r n : ℝ) / (L n : ℝ) - (X p.r w : ℝ) / (L w : ℝ)|
          ≤ |(X p.r n : ℝ) / (L n : ℝ)| + |(X p.r w : ℝ) / (L w : ℝ)| := abs_sub _ _
      _ = |(X p.r n : ℝ)| / (L n : ℝ) + |(X p.r w : ℝ)| / (L w : ℝ) := by
        rw [abs_div, abs_div, abs_of_pos hLn_pos, abs_of_pos hLw_pos]
      _ ≤ (n : ℝ) ^ (z p.m) / (L n : ℝ) + (w : ℝ) ^ (z p.m) / (L w : ℝ) := by
        exact add_le_add
          (div_le_div_of_nonneg_right hn_small_R hLn_pos.le)
          (div_le_div_of_nonneg_right hw_small_R hLw_pos.le)
  have hmain_div :
      1 / (n : ℝ) ^ k
        ≤ (n : ℝ) ^ (z p.m) / (L n : ℝ) + (w : ℝ) ^ (z p.m) / (L w : ℝ) :=
    le_trans hdiff_lower hdiff_upper
  have hmain :
      (L n : ℝ) / (n : ℝ) ^ k
        ≤ (n : ℝ) ^ (z p.m) + ((L n : ℝ) / (L w : ℝ)) * (w : ℝ) ^ (z p.m) := by
    have hmul := mul_le_mul_of_nonneg_left hmain_div hLn_pos.le
    field_simp [hLn_pos.ne', hLw_pos.ne', hn_pow_pos.ne'] at hmul ⊢
    linarith
  have hratio :
      (L n : ℝ) / (L w : ℝ) ≤ (n : ℝ) ^ k := by
    have hratio_nat : L n / L w ≤ n ^ k := by
      simpa [n] using L_ratio_le w k
    have hdvd : L w ∣ L n := L_dvd_of_le hwn
    rw [← Nat.cast_div hdvd (by exact_mod_cast hLw_pos_nat.ne')]
    exact_mod_cast hratio_nat
  have hmain' :
      (L n : ℝ) / (n : ℝ) ^ k
        ≤ (n : ℝ) ^ (z p.m) + (n : ℝ) ^ k * (w : ℝ) ^ (z p.m) := by
    have hw_pow_nonneg : 0 ≤ (w : ℝ) ^ (z p.m) := pow_nonneg (by positivity) _
    have hmul := mul_le_mul_of_nonneg_right hratio hw_pow_nonneg
    nlinarith
  have hLlarge : (2 : ℝ) ^ n < (L n : ℝ) := by
    have h := p.h_bla0 w hw k
    dsimp [n]
    exact_mod_cast h
  have htwo_div :
      (2 : ℝ) ^ n / (n : ℝ) ^ k < (L n : ℝ) / (n : ℝ) ^ k :=
    div_lt_div_of_pos_right hLlarge hn_pow_pos
  have hupper :
      (2 : ℝ) ^ n / (n : ℝ) ^ k
        < (n : ℝ) ^ (z p.m) + (n : ℝ) ^ k * (w : ℝ) ^ (z p.m) :=
    lt_of_lt_of_le htwo_div hmain'
  have hboring :
      (2 : ℝ) ^ n / (n : ℝ) ^ k - (n : ℝ) ^ k * (w : ℝ) ^ (z p.m)
        > (n : ℝ) ^ (z p.m) := by
    simpa [n] using boring p w hw k hk
  nlinarith

/-
Theorem: Either |X_n| > n^z for all n in J1 or |X_n| > n^z for all n in J2.
-/
theorem xpo (p : ProblemParameters) :
    (∀ n ∈ J1' p, |X p.r n| > (n : ℚ)^(z p.m)) ∨ (∀ n ∈ J2' p, |X p.r n| > (n : ℚ)^(z p.m)) := by
  by_cases hJ1 : ∀ n ∈ J1' p, |X p.r n| > (n : ℚ) ^ (z p.m)
  · exact Or.inl hJ1
  · right
    push Not at hJ1
    rcases hJ1 with ⟨w, hw, hw_small⟩
    intro n hn
    by_contra hn_not
    have hn_small : |X p.r n| ≤ (n : ℚ) ^ (z p.m) := le_of_not_gt hn_not
    have hwn : w ≤ n := by
      have hw_mem := Finset.mem_Ico.mp hw
      have hn_mem := Finset.mem_Ico.mp hn
      omega
    let k := n - w
    have hnk : w + k = n := by
      dsimp [k]
      exact Nat.add_sub_of_le hwn
    have hk : w + k ∈ J2' p := by
      simpa [hnk] using hn
    have hn_small' : |X p.r (w + k)| ≤ (w + k : ℚ) ^ (z p.m) := by
      have hnkQ : (w + k : ℚ) = (n : ℚ) := by exact_mod_cast hnk
      simpa [hnk, hnkQ] using hn_small
    exact xpo_pair_contradiction p w hw k hk hw_small hn_small'

/-
X_n is an integer.
-/
def X_int (r : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, r i * ((L n) / i : ℕ)

theorem X_eq_X_int (r : ℕ → ℤ) (n : ℕ) : X r n = (X_int r n : ℚ) := by
  unfold X X_int;
  push_cast [ Finset.mul_sum _ _ _ ];
  refine Finset.sum_congr rfl fun i hi => ?_;
  rw [ Int.cast_div ] <;> norm_num;
  · ring;
  · exact_mod_cast Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ );
  · linarith [ Finset.mem_Icc.mp hi ]

/-
Definition of I0 and its property.
-/
noncomputable def I0 (p : ProblemParameters) : Finset ℕ :=
  if ∀ n ∈ J1' p, |X p.r n| > (n : ℚ)^(z p.m) then J1' p else J2' p

theorem I0_prop (p : ProblemParameters) : ∀ n ∈ I0 p, |X p.r n| > (n : ℚ)^(z p.m) := by
  rcases xpo p with h | h <;> unfold I0 <;> aesop

/-
Definitions of primes_lt_m, p_i, e, and d.
-/
def primes_lt_m (p : ProblemParameters) : List ℕ :=
  ((Finset.range p.m).filter Nat.Prime).sort (· ≤ ·)

def p_i (p : ProblemParameters) (i : ℕ) : ℕ :=
  (primes_lt_m p)[i - 1]? |>.getD 0

def e (p : ProblemParameters) (i : ℕ) (x : ℤ) : ℕ :=
  padicValNat (p_i p i) (Int.natAbs x)

def d (p : ProblemParameters) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n))

/-
Definition of sigma.
-/
noncomputable def sigma (p : ProblemParameters) (n : ℕ) : ℕ :=
  if h : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n then
    Nat.find h
  else
    1

/-
Definitions of k_exp, n_seq, and I_j.
-/
def k_exp (p : ProblemParameters) (s : ℕ) (j : ℕ) : ℕ :=
  Nat.log (p_i p s) (p.m ^ (2 * z p.m - 2 * j))

noncomputable def n_seq (p : ProblemParameters) : ℕ → ℕ
| 0 => 0 -- unused
| 1 => if h : (I0 p).Nonempty then (I0 p).min' h else 0
| (j + 1) =>
  let n := n_seq p j
  let s := sigma p n
  let k := k_exp p s j
  if h : ∃ x > n, e p s x - e p s (p.r x) ≥ k then
    Nat.find h
  else
    n + 1 -- fallback

/-
p_i returns a prime.
-/
theorem p_i_prime (p : ProblemParameters) (i : ℕ) (hi : i ∈ Finset.Icc 1 (z p.m)) :
    Nat.Prime (p_i p i) := by
      have h_prime : ∀ i ∈ Finset.Icc 1 (z p.m), Nat.Prime (p_i p i) := by
        intro i hi
        have h_prime_list : ∀ x ∈ primes_lt_m p, Nat.Prime x := by
          unfold primes_lt_m; aesop;
        have h_index : (primes_lt_m p).length ≥ z p.m := by
          unfold primes_lt_m; aesop;
        generalize_proofs at *; (
        have h_index : (primes_lt_m p)[i - 1]? ≠ none := by
          simp +zetaDelta at *;
          omega
        generalize_proofs at *; (
        unfold p_i; aesop;));
      exact h_prime i hi

/-
p_i returns a prime less than m.
-/
theorem p_i_lt_m (p : ProblemParameters) (i : ℕ) (hi : i ∈ Finset.Icc 1 (z p.m)) :
    p_i p i < p.m := by
      -- By definition of $p_i$, we know that $p_i p i$ is a prime number less than $m$.
      have h_prime : p_i p i ∈ Finset.filter Nat.Prime (Finset.range p.m) := by
        convert Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 _;
        convert List.getElem_mem _;
        rotate_left;
        focus
          exact i - 1;
        all_goals norm_num [ p_i ];
        focus
          exact Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.mem_Icc.mp hi |>.1 ) ) ) ( Finset.mem_Icc.mp hi |>.2 );
        rw [ List.getElem?_eq_getElem ] ; aesop;
      exact Finset.mem_range.mp ( Finset.mem_filter.mp h_prime |>.1 )

/-
Upper bound on p^{k_j}.
-/
theorem k_exp_upper_bound (p : ProblemParameters) (j : ℕ) (n : ℕ) :
    let s := sigma p n
    let k := k_exp p s j
    (p_i p s) ^ k ≤ p.m ^ (2 * z p.m - 2 * j) := by
      -- By definition of logarithm, we know that $p_i p s ^ k \leq p.m ^ (2 * z p.m - 2 * j)$.
      apply Nat.pow_log_le_self; (
      exact pow_ne_zero _ ( by linarith [ p.hm4 ] ))

/-
Helper lemma for log lower bound.
-/
theorem pow_log_gt_div (b x : ℕ) (hb : 1 < b) (hx : 0 < x) :
    b ^ (Nat.log b x) > (x - 1) / b := by
      rcases x with ( _ | _ | x ) <;> simp_all +decide;
      rw [ Nat.div_lt_iff_lt_mul hb.le ];
      rw [ ← pow_succ ] ; exact Nat.lt_pow_succ_log_self hb _ |> lt_of_le_of_lt ( by linarith )

/-
Lower bound on p^{k_j} for j < z.
-/
theorem k_exp_lower_bound (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m - 1)) (n : ℕ) :
    let s := sigma p n
    let k := k_exp p s j
    (p_i p s) ^ k > p.m ^ (2 * z p.m - 2 * j - 1) := by
      -- By definition of $k_exp$, we have $p_i p s ^ k > (p.m ^ (2 * z p.m - 2 * j) - 1) / p_i p s$.
      have h_k_exp_gt_div : (p_i p (sigma p n) : ℕ) ^ k_exp p (sigma p n) j > (p.m ^ (2 * z p.m - 2 * j) - 1) / p_i p (sigma p n) := by
        convert pow_log_gt_div _ _ _ _ using 1;
        · have h_prime : Nat.Prime (p_i p (sigma p n)) := by
            apply p_i_prime;
            unfold sigma;
            split_ifs <;> simp_all +decide;
            · exact ⟨ _, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ) |>.2, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ), Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.2 ⟩;
            · exact le_trans ( by decide ) ( z_ge_two p.m p.hm4 );
          exact h_prime.one_lt;
        · exact pow_pos ( by linarith [ p.hm4 ] ) _;
      -- Since $p_i p (sigma p n) < p.m$, we have $(p.m ^ (2 * z p.m - 2 * j) - 1) / p_i p (sigma p n) \geq p.m ^ (2 * z p.m - 2 * j - 1)$.
      have h_div_ge : (p.m ^ (2 * z p.m - 2 * j) - 1) / p_i p (sigma p n) ≥ p.m ^ (2 * z p.m - 2 * j - 1) := by
        have h_div_ge : (p.m ^ (2 * z p.m - 2 * j) - 1) ≥ p_i p (sigma p n) * p.m ^ (2 * z p.m - 2 * j - 1) := by
          have h_div_ge : p_i p (sigma p n) < p.m := by
            apply p_i_lt_m;
            unfold sigma;
            split_ifs <;> simp_all +decide;
            · exact ⟨ _, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ) |>.2, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ), Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.2 ⟩;
            · grind;
          rcases k : 2 * z p.m - 2 * j with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
          · omega;
          · exact Nat.le_sub_one_of_lt ( mul_lt_mul_of_pos_right h_div_ge ( pow_pos ( by linarith ) _ ) );
        exact Nat.le_div_iff_mul_le ( Nat.Prime.pos ( show Nat.Prime ( p_i p ( sigma p n ) ) from by
                                                        have h_sigma_range : sigma p n ∈ Finset.Icc 1 (z p.m) := by
                                                          have h_sigma_def : sigma p n = if h : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n then Nat.find h else 1 := by
                                                            exact rfl
                                                          split_ifs at h_sigma_def <;> simp_all +decide;
                                                          · exact ⟨ _, Finset.mem_Icc.mp ( Nat.find_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ) |>.2, Finset.mem_Icc.mp ( Nat.find_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ), Nat.find_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.2 ⟩;
                                                          · exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ z p.m from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] );
                                                        exact p_i_prime p _ h_sigma_range ) ) |>.2 ( by linarith );
      exact lt_of_le_of_lt h_div_ge h_k_exp_gt_div

/-
Existence of a multiple of P in (n, n+P].
-/
theorem exists_multiple_in_interval (n P : ℕ) (hP : P > 0) : ∃ x ∈ Finset.Ioc n (n + P), P ∣ x := by
  exact ⟨ P * ( n / P + 1 ), Finset.mem_Ioc.mpr ⟨ by linarith [ Nat.div_add_mod n P, Nat.mod_lt n hP ], by linarith [ Nat.div_mul_le_self n P ] ⟩, by norm_num ⟩

/-
Bound on the valuation of r_x.
-/
theorem valuation_r_bound (p : ProblemParameters) (s : ℕ) (hs : s ∈ Finset.Icc 1 (z p.m)) (x : ℕ) :
    e p s (p.r x) ≤ Nat.log (p_i p s) (p.m - 1) := by
      refine Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( p_i_prime p s hs ) ) ?_;
      have h_r_lt_m : Int.natAbs (p.r x) < p.m := by
        simpa [ ← Int.ofNat_lt ] using p.h_r_bdd x;
      have h_e_le_log : (p_i p s) ^ e p s (p.r x) ≤ Int.natAbs (p.r x) := by
        convert Nat.le_of_dvd ( Int.natAbs_pos.mpr ( show p.r x ≠ 0 from p.h_r_nz x ) ) ( Nat.ordProj_dvd _ _ ) using 1;
        focus
          unfold e
          rw [ Nat.factorization_def ]
          exact p_i_prime p s hs;
      exact Nat.le_sub_one_of_lt ( lt_of_le_of_lt h_e_le_log h_r_lt_m )

/-
Bound on the step size power.
-/
theorem step_size_bound (p : ProblemParameters) (s : ℕ) (_hs : s ∈ Finset.Icc 1 (z p.m)) (k : ℕ) :
    (p_i p s) ^ (k + Nat.log (p_i p s) (p.m - 1)) ≤ (p.m - 1) * (p_i p s) ^ k := by
      rw [ pow_add, mul_comm ];
      exact Nat.mul_le_mul_right _ ( Nat.pow_log_le_self _ ( Nat.sub_ne_zero_of_lt ( by linarith [ p.hm4 ] ) ) )

/-
The interval I0 is nonempty.
-/
theorem I0_nonempty (p : ProblemParameters) : (I0 p).Nonempty := by
  unfold I0;
  unfold J1' J2';
  split_ifs <;> simp_all +decide [ Finset.nonempty_Ico ];
  · exact ⟨ by linarith [ p.htilde_m, pow_pos ( by linarith [ p.hm4 ] : 0 < p.m ) ( 2 * z p.m ) ], pow_pos ( by linarith [ p.hm4 ] ) _ ⟩;
  · exact pow_pos ( by linarith [ p.hm4 ] ) _

/-
The sequence n_j is strictly increasing for j >= 1.
-/
theorem n_seq_increasing (p : ProblemParameters) (j : ℕ) (hj : j ≥ 1) :
    n_seq p j < n_seq p (j + 1) := by
      -- By definition of $n_{j+1}$, we know that it is either $n_j + 1$ or the smallest $x > n_j$ satisfying some condition.
      have h_def : n_seq p (j + 1) = if h : ∃ x > n_seq p j, e p (sigma p (n_seq p j)) x - e p (sigma p (n_seq p j)) (p.r x) ≥ k_exp p (sigma p (n_seq p j)) j then Nat.find h else n_seq p j + 1 := by
        rcases j <;> tauto;
      split_ifs at h_def <;> simp_all +decide

/-
I0 is the interval starting at n_seq p 1 with length m^(2z-1).
-/
theorem I0_eq_Ico (p : ProblemParameters) :
    I0 p = Finset.Ico (n_seq p 1) (n_seq p 1 + p.m^(2 * z p.m - 1)) := by
      have h_interval_def : I0 p = if ∀ n ∈ J1' p, |X p.r n| > n ^ (z p.m) then Finset.Ico (p.tilde_m - p.m ^ (2 * z p.m - 1)) p.tilde_m else Finset.Ico p.tilde_m (p.tilde_m + p.m ^ (2 * z p.m - 1)) := by
        exact rfl;
      have h_n_seq_p1 : n_seq p 1 = if ∀ n ∈ J1' p, |X p.r n| > n ^ (z p.m) then p.tilde_m - p.m ^ (2 * z p.m - 1) else p.tilde_m := by
        split_ifs <;> simp_all +decide [ n_seq ];
        · split_ifs <;> simp_all +decide [ Finset.min' ];
          · refine le_antisymm ?_ ?_ <;> norm_num;
            · refine ⟨ p.tilde_m - p.m ^ ( 2 * z p.m - 1 ), ?_, ?_ ⟩ <;> norm_num;
              exact ⟨ by rw [ tsub_add_cancel_of_le ( show p.m ^ ( 2 * z p.m - 1 ) ≤ p.tilde_m from by linarith [ show p.m ^ ( 2 * z p.m - 1 ) ≤ p.tilde_m from by linarith [ show p.tilde_m > 20 * p.m ^ ( 2 * z p.m ) from p.htilde_m, show p.m ^ ( 2 * z p.m ) ≥ p.m ^ ( 2 * z p.m - 1 ) from pow_le_pow_right₀ ( by linarith [ p.hm4 ] ) ( Nat.sub_le _ _ ) ] ] ) ], by linarith, by linarith ⟩;
            · exact fun b a a_1 => a;
          · rename_i h₁ h₂;
            exact absurd ( h₂ ( by linarith [ p.htilde_m, pow_pos ( by linarith [ p.hm4 ] : 0 < p.m ) ( 2 * z p.m ) ] ) ) ( by rintro ⟨ h₃, h₄ ⟩ ; linarith [ p.hm4 ] );
        · split_ifs <;> simp_all +decide [ Finset.min' ];
          · exact le_antisymm ( Finset.inf'_le _ <| Finset.left_mem_Ico.mpr <| by linarith ) ( Finset.le_inf' _ _ fun x hx => Finset.mem_Ico.mp hx |>.1 );
          · linarith [ p.hm4 ];
      split_ifs at * <;> simp_all +decide;
      rw [ Nat.sub_add_cancel ( show p.m ^ ( 2 * z p.m - 1 ) ≤ p.tilde_m from _ ) ];
      exact le_trans ( Nat.pow_le_pow_right ( by linarith [ p.hm4 ] ) ( Nat.sub_le _ _ ) ) ( by linarith [ p.htilde_m ] )

/-
The prime power p^{v_p(L n)} is less than or equal to n.
-/
theorem valuation_lcm_le (n : ℕ) (hn : n ≥ 1) (p : ℕ) (hp : p.Prime) :
    p ^ (padicValNat p (L n)) ≤ n := by
      -- Let $k$ be such that $v_p(L(n)) = k$.
      obtain ⟨k, hk⟩ : ∃ k, padicValNat p (L n) = k ∧ ∃ i ∈ Finset.Icc 1 n, padicValNat p i = k := by
        -- By definition of $L(n)$, there exists some $i \in \{1, 2, \ldots, n\}$ such that $v_p(i) = v_p(L(n))$.
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, padicValNat p j ≤ padicValNat p i := by
          exact Finset.exists_max_image _ _ ⟨ 1, Finset.mem_Icc.mpr ⟨ by norm_num, hn ⟩ ⟩;
        refine ⟨ _, rfl, i, hi.1, ?_ ⟩;
        -- By definition of $L(n)$, we know that $v_p(L(n))$ is the maximum of $v_p(j)$ for $j \in \{1, ..., n\}$.
        have h_lcm_val : padicValNat p (Finset.lcm (Finset.Icc 1 n) id) = Finset.sup (Finset.Icc 1 n) (fun j => padicValNat p j) := by
          have h_lcm_val : ∀ {S : Finset ℕ}, (∀ x ∈ S, x ≠ 0) → padicValNat p (Finset.lcm S id) = Finset.sup S (fun x => padicValNat p x) := by
            intros S hS_nonzero
            induction S using Finset.induction with
            | empty => aesop
            | @insert x S hxS ih =>
            generalize_proofs at *; (
            have h_lcm_val : padicValNat p (Nat.lcm x (Finset.lcm S id)) = max (padicValNat p x) (padicValNat p (Finset.lcm S id)) := by
              have h_lcm_val : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → padicValNat p (Nat.lcm a b) = max (padicValNat p a) (padicValNat p b) := by
                intros a b ha hb; haveI := Fact.mk hp; rw [ ← Nat.factorization_def, ← Nat.factorization_def, ← Nat.factorization_def ] ;
                · rw [ Nat.factorization_lcm ] <;> aesop;
                · exact hp;
                · exact hp;
                · exact hp
              generalize_proofs at *; (
              exact h_lcm_val ( hS_nonzero x ( Finset.mem_insert_self _ _ ) ) ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by intros h; obtain ⟨ y, hy ⟩ := h; specialize hS_nonzero y ( Finset.mem_insert_of_mem hy.1 ) ; aesop ) ) ) ))
            generalize_proofs at *; (
            convert h_lcm_val using 1
            focus
              aesop
            rw [ Finset.sup_insert, ih fun y hy => hS_nonzero y <| Finset.mem_insert_of_mem hy ]));
          exact h_lcm_val fun x hx => by linarith [ Finset.mem_Icc.mp hx ] ;
        exact h_lcm_val.symm ▸ le_antisymm ( Finset.le_sup ( f := fun j => padicValNat p j ) hi.1 ) ( Finset.sup_le fun j hj => hi.2 j hj );
      -- Since $p$ is a prime, the exponent of $p$ in $i$'s factorization cannot exceed the exponent in $n$'s factorization. Therefore, $k \leq \text{padicValNat } p n$.
      obtain ⟨i, hi₁, hi₂⟩ := hk.right
      have h_exp : padicValNat p i ≤ Nat.log p n := by
        have h_exp : p ^ padicValNat p i ∣ i := by
          exact pow_padicValNat_dvd;
        exact Nat.le_log_of_pow_le hp.one_lt ( Nat.le_trans ( Nat.le_of_dvd ( Finset.mem_Icc.mp hi₁ |>.1 ) h_exp ) ( Finset.mem_Icc.mp hi₁ |>.2 ) );
      exact hk.1.symm ▸ hi₂.symm ▸ Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp hi₁ ] ) h_exp |> le_trans <| by linarith [ Finset.mem_Icc.mp hi₁ ] ;

/-
If the condition for sigma holds, then sigma satisfies the inequality.
-/
theorem sigma_prop (p : ProblemParameters) (n : ℕ) (h : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n) :
    (p_i p (sigma p n)) ^ (e p (sigma p n) (X_int p.r n)) > n := by
      -- By definition of sigma, there exists some i in the interval [1, z p.m] such that p_i p i ^ e p i (X_int p.r n) > n.
      obtain ⟨i, hi₁, hi₂⟩ := h;
      -- By definition of `Nat.find`, we know that `sigma p n` is the smallest index `i` such that `p_i p i ^ e p i (X_int p.r n) > n`.
      have h_sigma_def : sigma p n = Nat.find (show ∃ i ∈ Finset.Icc 1 (z p.m), p_i p i ^ e p i (X_int p.r n) > n from ⟨i, hi₁, hi₂⟩) := by
                                                unfold sigma;
                                                grind;
      exact h_sigma_def.symm ▸ Nat.find_spec ( ⟨ i, hi₁, hi₂ ⟩ : ∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n ) |>.2

/-
The valuation of X_{n_j} is strictly greater than the valuation of L_{n_j} (given the hypothesis).
-/
theorem part1_valuation (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m))
    (h_sigma : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r (n_seq p j))) > n_seq p j) :
    let n_j := n_seq p j
    let s := sigma p n_j
    e p s (X_int p.r n_j) ≥ e p s (L n_j) + 1 := by
      -- By `sigma_prop`, we have $(p_i\ p\ s)^{e\ p\ s\ (X\_int\ p.r\ n_j)} > n_j$.
      have h_sigma_gt : (p_i p (sigma p (n_seq p j))) ^ (e p (sigma p (n_seq p j)) (X_int p.r (n_seq p j))) > n_seq p j := by
        apply_rules [ sigma_prop ];
      -- By `valuation_lcm_le`, we have $(p_i\ p\ s)^{e\ p\ s\ (L\ n_j)} \le n_j$.
      have h_val_lcm_le : (p_i p (sigma p (n_seq p j))) ^ (e p (sigma p (n_seq p j)) (L (n_seq p j))) ≤ n_seq p j := by
        convert valuation_lcm_le _ _ _ _;
        · rcases j with ( _ | _ | j ) <;> norm_num at *;
          · -- By definition of $n_seq$, we know that $n_seq p 1$ is the minimum element of $I0 p$.
            have h_n_seq_1_min : n_seq p 1 = (I0 p).min' (I0_nonempty p) := by
              exact dif_pos ( I0_nonempty p );
            rw [ h_n_seq_1_min ];
            refine Nat.pos_of_ne_zero ?_;
            intro h; have := Finset.min'_mem ( I0 p ) ( I0_nonempty p ) ; simp_all +decide [ I0 ] ;
            split_ifs at this <;> simp_all +decide [ J1', J2' ];
            exact absurd this.1 ( Nat.sub_ne_zero_of_lt ( by linarith [ show p.m ^ ( 2 * z p.m - 1 ) < p.tilde_m from by linarith [ show p.tilde_m > 20 * p.m ^ ( 2 * z p.m ) from by linarith [ p.htilde_m ], show p.m ^ ( 2 * z p.m - 1 ) ≤ p.m ^ ( 2 * z p.m ) from pow_le_pow_right₀ ( by linarith [ p.hm4 ] ) ( Nat.sub_le _ _ ) ] ] ) );
          · exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ n_seq_increasing p ( j + 1 ) ( by linarith ) ] );
        · apply p_i_prime;
          unfold sigma; aesop;
      exact Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => h_sigma_gt.not_ge <| le_trans ( Nat.pow_le_pow_right ( Nat.pos_of_ne_zero <| by { have := p_i_prime p ( sigma p ( n_seq p j ) ) ( by
                                                                                                                                              unfold sigma; aesop; ) ; aesop } ) h ) h_val_lcm_le )

/-
The valuation of the term r_i * (L_n / i) is equal to e(L_n) + e(r_i) - e(i).
-/
theorem valuation_term_eq (p : ProblemParameters) (n : ℕ) (i : ℕ) (hi : i ∈ Finset.Icc 1 n) (s : ℕ) (hs : s ∈ Finset.Icc 1 (z p.m)) :
    e p s (p.r i * ((L n) / i : ℕ)) = e p s (L n) + e p s (p.r i) - e p s i := by
      unfold e;
      rw [ Int.natAbs_mul, Int.natAbs_natCast ];
      by_cases h : p.r i = 0 <;> by_cases h' : L n / i = 0 <;> simp_all +decide;
      · exact absurd h ( p.h_r_nz i );
      · exact absurd h ( p.h_r_nz i );
      · exact absurd ( h'.resolve_left ( by linarith ) ) ( not_lt_of_ge ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr hi ) ) ) );
      · have h_val : padicValNat (p_i p s) (L n) = padicValNat (p_i p s) i + padicValNat (p_i p s) (L n / i) := by
          have h_val : i ∣ L n := by
            exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hi.1, hi.2 ⟩ );
          convert padicValNat.mul _ _ using 1;
          · rw [ Nat.mul_div_cancel' h_val ];
          · exact ⟨ p_i_prime p s ( Finset.mem_Icc.mpr hs ) ⟩;
          · aesop;
          · exact Nat.ne_of_gt ( Nat.div_pos h'.2 ( Nat.pos_of_dvd_of_pos h_val ( Nat.pos_of_ne_zero ( by aesop ) ) ) );
        have h_val : padicValNat (p_i p s) ((p.r i).natAbs * (L n / i)) = padicValNat (p_i p s) (p.r i).natAbs + padicValNat (p_i p s) (L n / i) := by
          convert padicValNat.mul _ _ using 1;
          · exact ⟨ p_i_prime p s ( Finset.mem_Icc.mpr hs ) ⟩;
          · positivity;
          · exact ne_of_gt ( Nat.div_pos ( by linarith ) ( by linarith ) );
        grind

/-
k_exp is at least 1 for j < z.
-/
theorem k_ge_one (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m - 1)) (n : ℕ) :
    let s := sigma p n
    k_exp p s j ≥ 1 := by
      -- For k_exp to be zero, m^(2z-2j) must be less than p_s. Since p_s is a prime less than m, p_s ≤ m.
      have h_m_pow_gt_p (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m - 1)) (n : ℕ) (s : ℕ) (hs : s ∈ Finset.Icc 1 (z p.m)) :
        (p.m ^ (2 * z p.m - 2 * j) : ℕ) ≥ (p_i p s : ℕ) := by
          refine le_trans ?_ ( Nat.pow_le_pow_right ( by linarith [ p.hm4 ] ) ( show 2 * z p.m - 2 * j ≥ 2 by exact Nat.le_sub_of_add_le <| by linarith [ Finset.mem_Icc.mp hj, Nat.sub_add_cancel <| show 1 ≤ z p.m from Finset.card_pos.mpr ⟨ 2, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith [ p.hm4 ], by decide ⟩ ⟩ ] ) );
          exact le_trans ( Nat.le_of_lt ( p_i_lt_m p s hs ) ) ( Nat.le_self_pow ( by norm_num ) _ );
      refine Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( p_i_prime p ( sigma p n ) ?_ ) ) ?_;
      · unfold sigma;
        split_ifs <;> simp_all +decide;
        · exact ⟨ _, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ) |>.2, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.1 ), Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r n ) > n› |>.2 ⟩;
        · grind;
      · by_cases h_sigma : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n <;> simp_all +decide [ sigma ];
        · grind;
        · grind

/-
The first part of the sum can be factored as $(L_n / L_{n_j}) * X_{n_j}$.
-/
theorem part1_sum_eq (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ≥ n_seq p j) :
    ∑ i ∈ Finset.Icc 1 (n_seq p j), p.r i * ((L n) / i : ℕ) = (L n / L (n_seq p j)) * X_int p.r (n_seq p j) := by
      -- By definition of $L$, we know that $L_n$ is divisible by $L_{n_j}$.
      have h_div : L (n_seq p j) ∣ L n := by
        exact Finset.lcm_dvd fun i hi => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hi |>.1, by linarith [ Finset.mem_Icc.mp hi |>.2 ] ⟩ )
      generalize_proofs at *; (
      have h_sum_rewrite : ∑ i ∈ Finset.Icc 1 (n_seq p j), (p.r i : ℚ) * (L n / i : ℕ) = (L n / L (n_seq p j) : ℚ) * ∑ i ∈ Finset.Icc 1 (n_seq p j), (p.r i : ℚ) * (L (n_seq p j) / i : ℕ) := by
        rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_congr rfl fun i hi => ?_ ; rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num
        focus
          ring_nf
        · by_cases h : L ( n_seq p j ) = 0 <;> aesop;
        · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ ) |> dvd_trans ( by aesop ) ;
        · linarith [ Finset.mem_Icc.mp hi ];
        · exact dvd_trans ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ ) ) h_div;
        · linarith [ Finset.mem_Icc.mp hi ]
      generalize_proofs at *; (
      norm_num [ ← @Int.cast_inj ℚ, X_int, h_sum_rewrite ];
      convert h_sum_rewrite using 1 ; norm_cast ; aesop;))

/-
The valuation of the first part of the sum is equal to $e(L_n) - e(L_{n_j}) + e(X_{n_j})$.
-/
theorem part1_valuation_eq (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ≥ n_seq p j)
    (h_nonzero : X_int p.r (n_seq p j) ≠ 0) :
    let n_j := n_seq p j
    let s := sigma p n_j
    e p s (∑ i ∈ Finset.Icc 1 n_j, p.r i * ((L n) / i : ℕ)) = e p s (L n) - e p s (L n_j) + e p s (X_int p.r n_j) := by
      have h_val : let n_j := n_seq p j;
        let s := sigma p n_j;
        let k := k_exp p s j;
        e p s (∑ i ∈ Finset.Icc 1 (n_seq p j), p.r i * (↑(L n / i))) = e p s (L n / L (n_seq p j)) + e p s (X_int p.r (n_seq p j)) := by
          have h_val : let n_j := n_seq p j;
            let s := sigma p n_j;
            let k := k_exp p s j;
            e p s (∑ i ∈ Finset.Icc 1 (n_seq p j), p.r i * (↑(L n / i))) = e p s ((L n / L (n_seq p j)) * X_int p.r (n_seq p j)) := by
              convert congr_arg _ ( part1_sum_eq p j hj n hn ) using 1;
          convert padicValNat.mul _ _ using 1;
          · convert h_val using 1;
            unfold e; norm_cast;
            rw [ Int.natAbs_mul, Int.natAbs_natCast ];
          · refine ⟨ ?_ ⟩;
            apply p_i_prime;
            unfold sigma;
            split_ifs <;> simp_all +decide;
            · exact ⟨ _, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq p j ) ) > n_seq p j› |>.1 ) |>.2, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq p j ) ) > n_seq p j› |>.1 ), Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq p j ) ) > n_seq p j› |>.2 ⟩;
            · linarith;
          · exact ne_of_gt ( mod_cast Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.lcm_dvd_iff.mpr fun i hi => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ ) ) ) ( Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) );
          · exact Int.natAbs_ne_zero.mpr h_nonzero;
      have h_val : let n_j := n_seq p j;
        let s := sigma p n_j;
        (padicValNat (p_i p s) (L n)) = (padicValNat (p_i p s) (L n / L (n_seq p j))) + (padicValNat (p_i p s) (L (n_seq p j))) := by
          have h_val : let n_j := n_seq p j;
            let s := sigma p n_j;
            (L n) = (L n / L (n_seq p j)) * (L (n_seq p j)) := by
              rw [ Nat.div_mul_cancel ];
              apply_rules [ Finset.lcm_dvd_iff.mpr ];
              exact fun x hx => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hx |>.1, hn.trans' ( Finset.mem_Icc.mp hx |>.2 ) ⟩ );
          convert padicValNat.mul _ _ using 1;
          · congr! 1;
          · exact ⟨ p_i_prime p ( sigma p ( n_seq p j ) ) ( by
              unfold sigma; norm_num;
              split_ifs <;> norm_num;
              · grind;
              · exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ Finset.mem_Icc.mp hj ] ) ) ⟩;
          · intro h; simp_all +singlePass ;
            exact absurd h_val <| ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
          · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by simp +decide [ Finset.mem_Icc ] ;
      unfold e; aesop;

/-
If the condition for `sigma` is met, then `sigma` returns an index in the range $[1, z]$.
-/
theorem sigma_mem (p : ProblemParameters) (n : ℕ) (h : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n) :
    sigma p n ∈ Finset.Icc 1 (z p.m) := by
      unfold sigma; aesop;

/-
The valuation of $X_{n_j}$ is strictly greater than the valuation of $L_{n_j}$.
-/

theorem part1_valuation_v2 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m))
    (h_sigma : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r (n_seq p j))) > n_seq p j) :
    let n_j := n_seq p j
    let s := sigma p n_j
    e p s (X_int p.r n_j) ≥ e p s (L n_j) + 1 := by
      convert part1_valuation p j hj h_sigma using 1

/-
Redefinition of the sequence $n_j$ and intervals $I_j$ to ensure the valuation condition $e(n) \ge e(r) + k$ holds.
-/
noncomputable def n_seq_v2 (p : ProblemParameters) : ℕ → ℕ
| 0 => 0
| 1 => if h : (I0 p).Nonempty then (I0 p).min' h else 0
| (j + 1) =>
  let n := n_seq_v2 p j
  let s := sigma p n
  let k := k_exp p s j
  if h : ∃ x > n, e p s x ≥ e p s (p.r x) + k then
    Nat.find h
  else
    n + 1

/-
Existence of a valid x for n_seq_v2.
-/
theorem exists_valid_x_v2 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) :
    let s := sigma p n
    let k := k_exp p s j
    ∃ x ∈ Finset.Ioc n (n + (p.m - 1) * (p_i p s) ^ k), e p s x ≥ e p s (p.r x) + k := by
      obtain ⟨ x, hx₁, hx₂ ⟩ := exists_multiple_in_interval n ( p_i p ( sigma p n ) ^ ( k_exp p ( sigma p n ) j + Nat.log ( p_i p ( sigma p n ) ) ( p.m - 1 ) ) ) ( pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p n ) ( by
        by_cases h : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n <;> simp_all +decide [ sigma ];
        · exact ⟨ h.choose, h.choose_spec.1.2, h.choose_spec.1, h.choose_spec.2 ⟩;
        · grind ) ) ) _ );
      -- Since $p_i p (sigma p n)^{k + \log_p(m-1)} \mid x$, we have $e p (sigma p n) x \ge k + \log_p(m-1)$.
      have h_val_x : e p (sigma p n) x ≥ k_exp p (sigma p n) j + Nat.log (p_i p (sigma p n)) (p.m - 1) := by
        haveI := Fact.mk ( p_i_prime p ( sigma p n ) ( by
          by_cases h : ∃ i ∈ Finset.Icc 1 ( z p.m ), ( p_i p i ) ^ ( e p i ( X_int p.r n ) ) > n <;> simp_all +decide [ sigma ];
          · exact ⟨ _, h.choose_spec.1.2, h.choose_spec.1, h.choose_spec.2 ⟩;
          · grind ) ) ; rw [ padicValNat_dvd_iff ] at hx₂ ; aesop;
      -- Since $p_i p (sigma p n)^{k + \log_p(m-1)} \mid x$, we have $e p (sigma p n) (p.r x) \le \log_p(m-1)$.
      have h_val_r_x : e p (sigma p n) (p.r x) ≤ Nat.log (p_i p (sigma p n)) (p.m - 1) := by
        apply valuation_r_bound;
        by_cases h : ∃ i ∈ Finset.Icc 1 ( z p.m ), ( p_i p i ) ^ ( e p i ( X_int p.r n ) ) > n <;> simp_all +decide [ sigma ];
        · exact ⟨ _, h.choose_spec.1.2, h.choose_spec.1, h.choose_spec.2 ⟩;
        · grind;
      have h_interval : p_i p (sigma p n) ^ (k_exp p (sigma p n) j + Nat.log (p_i p (sigma p n)) (p.m - 1)) ≤ (p.m - 1) * p_i p (sigma p n) ^ k_exp p (sigma p n) j := by
        convert step_size_bound p ( sigma p n ) ( by
          by_cases h : ∃ i ∈ Finset.Icc 1 ( z p.m ), ( p_i p i ) ^ ( e p i ( X_int p.r n ) ) > n <;> simp_all +decide [ sigma ];
          · exact ⟨ _, h.choose_spec.1.2, h.choose_spec.1, h.choose_spec.2 ⟩;
          · grind ) ( k_exp p ( sigma p n ) j ) using 1;
      exact ⟨ x, Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp hx₁ ], by linarith [ Finset.mem_Ioc.mp hx₁ ] ⟩, by linarith ⟩

/-
Bound on the step size of n_seq_v2.
-/
theorem n_seq_v2_step_bound (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n := n_seq_v2 p j
    let s := sigma p n
    let k := k_exp p s j
    n_seq_v2 p (j + 1) ≤ n + (p.m - 1) * (p_i p s) ^ k := by
      -- By definition of $n_seq_v2$, we know that $n_{j+1} \leq n + (p.m - 1) * p_i p s ^ k$ follows directly from the definition of $n_seq_v2$.
      set n := n_seq_v2 p j
      set s := sigma p n
      set k := k_exp p s j
      have h_witness : ∃ x ∈ Finset.Ioc n (n + (p.m - 1) * p_i p s ^ k), e p s x ≥ e p s (p.r x) + k := by
        convert exists_valid_x_v2 p j hj n using 1;
      -- By definition of $n_seq_v2$, we know that $n_{j+1}$ is the smallest $x > n$ such that $e(x) \geq e(r(x)) + k$.
      have h_def : n_seq_v2 p (j + 1) = if h : ∃ x > n, e p s x ≥ e p s (p.r x) + k then Nat.find h else n + 1 := by
        cases j <;> aesop;
      split_ifs at h_def <;> simp_all +decide;
      · exact ⟨ h_witness.choose, h_witness.choose_spec.1.2, h_witness.choose_spec.1.1, h_witness.choose_spec.2 ⟩;
      · exact absurd h_witness ( by rintro ⟨ x, hx₁, hx₂ ⟩ ; linarith [ ‹∀ x : ℕ, n < x → e p s ↑x < e p s ( p.r x ) + k› x hx₁.1 ] )

/-
The defining property of n_seq_v2 holds: e(n_{j+1}) >= e(r_{n_{j+1}}) + k_j.
-/
theorem n_seq_v2_prop (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n_next := n_seq_v2 p (j + 1)
    let s := sigma p (n_seq_v2 p j)
    let k := k_exp p s j
    e p s n_next ≥ e p s (p.r n_next) + k := by
      have h_exists_x : ∃ x ∈ Finset.Ioc (n_seq_v2 p j) (n_seq_v2 p j + (p.m - 1) * (p_i p (sigma p (n_seq_v2 p j)) ^ k_exp p (sigma p (n_seq_v2 p j)) j)), e p (sigma p (n_seq_v2 p j)) x ≥ e p (sigma p (n_seq_v2 p j)) (p.r x) + k_exp p (sigma p (n_seq_v2 p j)) j := by
        have := exists_valid_x_v2 p j hj ( n_seq_v2 p j ) ; aesop;
      convert Nat.find_spec ( _ : ∃ x, x > n_seq_v2 p j ∧ e p ( sigma p ( n_seq_v2 p j ) ) x ≥ e p ( sigma p ( n_seq_v2 p j ) ) ( p.r x ) + k_exp p ( sigma p ( n_seq_v2 p j ) ) j ) |> fun x => x.2 using 1;
      focus
        rw [ n_seq_v2 ];
      focus
        grind;
      focus
        exact fun h => by linarith [ Finset.mem_Icc.mp hj ] ;
      focus
        rw [ n_seq_v2 ];
      focus
        grind;
      · exact fun h => by linarith [ Finset.mem_Icc.mp hj ] ;
      · exact ⟨ h_exists_x.choose, Finset.mem_Ioc.mp h_exists_x.choose_spec.1 |>.1, h_exists_x.choose_spec.2 ⟩

/-
Redefinition of n_seq and I_j using the stronger condition e(x) >= e(r(x)) + k, which avoids issues when k=0.
-/
noncomputable def n_seq_v4 (p : ProblemParameters) : ℕ → ℕ
| 0 => 0
| 1 => if h : (I0 p).Nonempty then (I0 p).min' h else 0
| (j + 1) =>
  let n := n_seq_v4 p j
  let s := sigma p n
  let k := k_exp p s j
  if h : ∃ x > n, e p s x ≥ e p s (p.r x) + k then
    Nat.find h
  else
    n + 1

noncomputable def I_j_v4 (p : ProblemParameters) (j : ℕ) : Finset ℕ :=
  let n_next := n_seq_v4 p (j + 1)
  let s := sigma p (n_seq_v4 p j)
  let k := k_exp p s j
  Finset.Ico n_next (n_next + (p_i p s) ^ k)

noncomputable def I_set_v4 (p : ProblemParameters) (j : ℕ) : Finset ℕ :=
  if j = 0 then I0 p
  else I_j_v4 p j

/-
The sequence n_seq_v4 is strictly increasing.
-/
theorem n_seq_v4_increasing (p : ProblemParameters) (j : ℕ) (hj : j ≥ 1) :
    n_seq_v4 p j < n_seq_v4 p (j + 1) := by
      -- By definition of $n_seq_v4$, we know that $n_seq_v4 p j < n_seq_v4 p (j + 1)$ for $j \geq 1$.
      induction j with
      | zero => contradiction
      | succ j ih =>
        by_cases hj : j ≥ 1 <;> simp_all +decide [ n_seq_v4 ];
        · split_ifs <;> simp_all +decide;
        · split_ifs <;> simp_all +decide

/-
The step size of the sequence $n_j$ is bounded by $(m-1)p_{\sigma(j)}^{k_j}$.
-/
theorem n_seq_v4_step_bound (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n := n_seq_v4 p j
    let s := sigma p n
    let k := k_exp p s j
    n_seq_v4 p (j + 1) ≤ n + (p.m - 1) * (p_i p s) ^ k := by
      convert n_seq_v2_step_bound p j hj using 1;
      convert Iff.rfl using 3 ; ring_nf;
      rw [ add_comm, add_comm ( ( p.m - 1 ) * p_i p ( sigma p ( n_seq_v4 p j ) ) ^ k_exp p ( sigma p ( n_seq_v4 p j ) ) j ) ];
      congr! 1;
      · congr! 1;
        funext p j; induction j using Nat.strong_induction_on with | h j ih => rcases j with ( _ | _ | j ) <;> simp +arith +decide [ *, n_seq_v2, n_seq_v4 ] ;
      · congr! 1;
        · induction j using Nat.strong_induction_on with | h j ih =>
          rcases j with ( _ | _ | j ) <;> simp_all +decide [ n_seq_v2, n_seq_v4 ];
          rw [ ih _ ( Nat.lt_succ_self _ ) ( Nat.succ_pos _ ) ( by linarith ) ];
        · congr! 2;
          · congr! 2;
            induction j using Nat.strong_induction_on with | h j ih =>
            rcases j with ( _ | _ | j ) <;> simp_all +decide [ n_seq_v2, n_seq_v4 ];
            rw [ ih _ ( Nat.lt_succ_self _ ) ( by linarith ) ( by linarith ) ];
          · congr! 2;
            induction j using Nat.strong_induction_on with | h j ih =>
            rcases j with ( _ | _ | j ) <;> simp_all +decide [ n_seq_v2, n_seq_v4 ];
            rw [ ih _ ( Nat.lt_succ_self _ ) ( Nat.succ_pos _ ) ( by linarith ) ]

/-
The inequality $m \cdot p_{\sigma(j)}^{k_j} < p_{\sigma(j-1)}^{k_{j-1}}$ holds for $j \ge 2$.
-/
theorem power_inequality_step_v4 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 2 (z p.m)) :
    (p.m : ℕ) * (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) <
    (p_i p (sigma p (n_seq_v4 p (j - 1)))) ^ (k_exp p (sigma p (n_seq_v4 p (j - 1))) (j - 1)) := by
  have hj_pred : j - 1 ∈ Finset.Icc 1 (z p.m - 1) := by
    rw [Finset.mem_Icc] at hj ⊢
    omega
  have h_upper :
      (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) ≤
        p.m ^ (2 * z p.m - 2 * j) := by
    simpa using k_exp_upper_bound p j (n_seq_v4 p j)
  have h_lower :
      p.m ^ (2 * z p.m - 2 * (j - 1) - 1) <
        (p_i p (sigma p (n_seq_v4 p (j - 1)))) ^
          (k_exp p (sigma p (n_seq_v4 p (j - 1))) (j - 1)) := by
    simpa using k_exp_lower_bound p (j - 1) hj_pred (n_seq_v4 p (j - 1))
  have h_exp :
      2 * z p.m - 2 * (j - 1) - 1 = 2 * z p.m - 2 * j + 1 := by
    rw [Finset.mem_Icc] at hj
    omega
  have h_left :
      p.m * (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) ≤
        p.m ^ (2 * z p.m - 2 * j + 1) := by
    calc
      p.m * (p_i p (sigma p (n_seq_v4 p j))) ^
          (k_exp p (sigma p (n_seq_v4 p j)) j)
          ≤ p.m * p.m ^ (2 * z p.m - 2 * j) := by
            exact Nat.mul_le_mul_left p.m h_upper
      _ = p.m ^ (2 * z p.m - 2 * j + 1) := by
            rw [pow_succ]
            exact Nat.mul_comm _ _
  exact lt_of_le_of_lt h_left (by simpa [h_exp] using h_lower)

/-
Abstract algebraic inequality for the interval bound.
-/
theorem interval_bound_abstract (n1 n2 m z p_val k : ℕ) (hm : m ≥ 1) (hz : z ≥ 1)
    (h_step : n2 ≤ n1 + (m - 1) * p_val ^ k)
    (h_pow : p_val ^ k ≤ m ^ (2 * z - 2)) :
    n2 + p_val ^ k ≤ n1 + m ^ (2 * z - 1) := by
  calc
    n2 + p_val ^ k ≤ n1 + (m - 1) * p_val ^ k + p_val ^ k := by
      exact Nat.add_le_add_right h_step (p_val ^ k)
    _ = n1 + m * p_val ^ k := by
      rw [add_assoc]
      have hadd : (m - 1) * p_val ^ k + p_val ^ k = m * p_val ^ k := by
        nth_rewrite 2 [← one_mul (p_val ^ k)]
        rw [← Nat.add_mul, Nat.sub_add_cancel hm]
      rw [hadd]
    _ ≤ n1 + m * m ^ (2 * z - 2) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left m h_pow) n1
    _ = n1 + m ^ (2 * z - 1) := by
      rw [mul_comm, ← pow_succ]
      congr
      omega

/-
The upper bound of the interval $I_1$ is less than or equal to the upper bound of $I_0$.
-/
theorem interval_upper_bound_base_v4 (p : ProblemParameters) :
    n_seq_v4 p 2 + (p_i p (sigma p (n_seq_v4 p 1))) ^ (k_exp p (sigma p (n_seq_v4 p 1)) 1) ≤
    n_seq_v4 p 1 + p.m ^ (2 * z p.m - 1) := by
  have hz2 : 2 ≤ z p.m := z_ge_two p.m p.hm4
  have hz1 : 1 ≤ z p.m := by omega
  have hj : 1 ∈ Finset.Icc 1 (z p.m) := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, hz1⟩
  have hstep :
      n_seq_v4 p 2 ≤
        n_seq_v4 p 1 +
          (p.m - 1) *
            (p_i p (sigma p (n_seq_v4 p 1))) ^
              (k_exp p (sigma p (n_seq_v4 p 1)) 1) := by
    simpa using n_seq_v4_step_bound p 1 hj
  have hpow :
      (p_i p (sigma p (n_seq_v4 p 1))) ^
          (k_exp p (sigma p (n_seq_v4 p 1)) 1) ≤
        p.m ^ (2 * z p.m - 2) := by
    simpa using k_exp_upper_bound p 1 (n_seq_v4 p 1)
  have hm1 : p.m ≥ 1 := le_trans (by norm_num : 1 ≤ 4) p.hm4
  exact
    interval_bound_abstract
      (n_seq_v4 p 1)
      (n_seq_v4 p 2)
      p.m
      (z p.m)
      (p_i p (sigma p (n_seq_v4 p 1)))
      (k_exp p (sigma p (n_seq_v4 p 1)) 1)
      hm1
      hz1
      hstep
      hpow

/-
`I0` is the interval starting at `n_1` with length `m^{2z-1}`.
-/
theorem I0_eq_Ico_v4 (p : ProblemParameters) :
    I0 p = Finset.Ico (n_seq_v4 p 1) (n_seq_v4 p 1 + p.m^(2 * z p.m - 1)) := by
      convert I0_eq_Ico p using 1

/-
The sequence $n_j$ is strictly increasing.
-/
theorem n_seq_v4_increasing' (p : ProblemParameters) (j : ℕ) (hj : j ≥ 1) :
    n_seq_v4 p j < n_seq_v4 p (j + 1) := by
      convert n_seq_v4_increasing p j hj using 1

/-
The intervals $I_j$ form a decreasing sequence $I_0 \supseteq I_1 \supseteq \dots \supseteq I_z$.
-/
theorem decreasing_intervals_v4 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    I_set_v4 p j ⊆ I_set_v4 p (j - 1) := by
  by_cases h1 : j = 1
  · subst j
    simpa [I_set_v4, I_j_v4, I0_eq_Ico_v4 p] using
      (Finset.Ico_subset_Ico
        (Nat.le_of_lt (n_seq_v4_increasing' p 1 (by norm_num)))
        (interval_upper_bound_base_v4 p))
  · have hj_ge1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_le_z : j ≤ z p.m := (Finset.mem_Icc.mp hj).2
    have hj_ge2 : 2 ≤ j := by omega
    have hj_Icc2 : j ∈ Finset.Icc 2 (z p.m) := Finset.mem_Icc.mpr ⟨hj_ge2, hj_le_z⟩
    have hj_ne_zero : j ≠ 0 := by omega
    have hj_sub_ne_zero : j - 1 ≠ 0 := by omega
    let pow_j :=
      (p_i p (sigma p (n_seq_v4 p j))) ^
        (k_exp p (sigma p (n_seq_v4 p j)) j)
    let pow_prev :=
      (p_i p (sigma p (n_seq_v4 p (j - 1)))) ^
        (k_exp p (sigma p (n_seq_v4 p (j - 1))) (j - 1))
    have hleft : n_seq_v4 p j ≤ n_seq_v4 p (j + 1) :=
      Nat.le_of_lt (n_seq_v4_increasing' p j hj_ge1)
    have hstep :
        n_seq_v4 p (j + 1) ≤ n_seq_v4 p j + (p.m - 1) * pow_j := by
      simpa [pow_j] using n_seq_v4_step_bound p j hj
    have hpow : p.m * pow_j ≤ pow_prev := by
      exact Nat.le_of_lt (by simpa [pow_j, pow_prev] using power_inequality_step_v4 p j hj_Icc2)
    have hm_ge1 : 1 ≤ p.m := le_trans (by norm_num) p.hm4
    have hmul : (p.m - 1) * pow_j + pow_j = p.m * pow_j := by
      calc
        (p.m - 1) * pow_j + pow_j = (p.m - 1) * pow_j + 1 * pow_j := by
          rw [one_mul]
        _ = ((p.m - 1) + 1) * pow_j := by
          rw [Nat.add_mul]
        _ = p.m * pow_j := by
          rw [Nat.sub_add_cancel hm_ge1]
    have hright : n_seq_v4 p (j + 1) + pow_j ≤ n_seq_v4 p j + pow_prev := by
      calc
        n_seq_v4 p (j + 1) + pow_j
            ≤ (n_seq_v4 p j + (p.m - 1) * pow_j) + pow_j :=
              Nat.add_le_add_right hstep pow_j
        _ = n_seq_v4 p j + ((p.m - 1) * pow_j + pow_j) := by
              rw [Nat.add_assoc]
        _ = n_seq_v4 p j + p.m * pow_j := by
              rw [hmul]
        _ ≤ n_seq_v4 p j + pow_prev :=
              Nat.add_le_add_left hpow (n_seq_v4 p j)
    simpa [I_set_v4, I_j_v4, hj_ne_zero, hj_sub_ne_zero, Nat.sub_add_cancel hj_ge1,
      pow_j, pow_prev] using
      (Finset.Ico_subset_Ico hleft hright)

/-
The integer $n_{j+1}$ satisfies the valuation condition.
-/
theorem n_seq_v4_prop (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n_next := n_seq_v4 p (j + 1)
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s n_next ≥ e p s (p.r n_next) + k := by
      convert n_seq_v2_prop p j hj using 1;
      -- By definition of `n_seq_v2` and `n_seq_v4`, they are equal for all `j`.
      have h_eq : ∀ j, n_seq_v2 p j = n_seq_v4 p j := by
        intro j; induction j using Nat.strong_induction_on with | h j ih => rcases j with ( _ | _ | j ) <;> simp_all +decide [ n_seq_v2, n_seq_v4 ] ;
      simp +decide only [h_eq]

/-
For any $x$ strictly between $n_j$ and $n_{j+1}$, the valuation condition fails.
-/
theorem n_seq_v4_min_prop (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n := n_seq_v4 p j
    let n_next := n_seq_v4 p (j + 1)
    let s := sigma p n
    let k := k_exp p s j
    ∀ x ∈ Finset.Ioc n (n_next - 1), e p s x < e p s (p.r x) + k := by
      field_simp;
      intro x hx;
      have h_val : n_seq_v4 p (j + 1) = if h : ∃ x > n_seq_v4 p j, e p (sigma p (n_seq_v4 p j)) x ≥ e p (sigma p (n_seq_v4 p j)) (p.r x) + k_exp p (sigma p (n_seq_v4 p j)) j then Nat.find h else n_seq_v4 p j + 1 := by
        cases j <;> aesop;
      split_ifs at h_val <;> simp_all +decide;
      exact lt_of_not_ge fun h => hx.2.not_gt <| Nat.lt_of_lt_of_le ( Nat.sub_lt ( Nat.pos_of_ne_zero <| by aesop ) zero_lt_one ) <| Nat.find_min' _ ⟨ hx.1, h ⟩

/-
$n_{j+1}$ divides $L_n$.
-/
theorem n_next_dvd_L_n_v4 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let n_next := n_seq_v4 p (j + 1)
    n_next ∣ L n := by
      apply Nat.dvd_of_mod_eq_zero;
      have h_div : n_seq_v4 p (j + 1) ∈ Finset.Icc 1 n := by
        induction j generalizing n with
        | zero => simp_all +decide
        | succ j ih =>
        simp_all +decide [ I_set_v4 ];
        -- Since $n$ is in $I_j_v4 p (j + 1)$, we have $n_seq_v4 p (j + 2) \leq n$.
        have h_le : n_seq_v4 p (j + 2) ≤ n := by
          exact Finset.mem_Ico.mp hn |>.1;
        refine ⟨ ?_, h_le ⟩;
        exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ n_seq_v4_increasing' p ( j + 1 ) ( by linarith ) ] );
      exact Nat.mod_eq_zero_of_dvd <| Finset.dvd_lcm h_div

/-
The first term of the sequence $n_j$ is positive.
-/
theorem n_seq_v4_1_pos (p : ProblemParameters) : n_seq_v4 p 1 > 0 := by
  -- Since $p.tilde_m$ is much larger than $p.m^{2*z p.m - 1}$, the lower bound $p.tilde_m - p.m^{2*z p.m - 1}$ is positive.
  have h_lower_bound_pos : p.tilde_m - p.m ^ (2 * z p.m - 1) > 0 := by
    refine Nat.sub_pos_of_lt ?_;
    -- Since $p.m \geq 4$, we have $p.tilde_m = p.m^{2*z+1}! > 20 * p.m^{2*z}$.
    have h_tilde_m_gt : p.tilde_m > 20 * p.m ^ (2 * z p.m) := by
      exact p.htilde_m;
    refine lt_of_le_of_lt ?_ h_tilde_m_gt ; induction p.m with
    | zero => norm_num [ Nat.mul_succ, Nat.pow_succ' ] at *; norm_num [ z ]
    | succ p_m ih =>
      norm_num [ Nat.mul_succ, Nat.pow_succ' ] at *;
      exact le_trans ( pow_le_pow_right₀ ( by linarith ) ( Nat.sub_le _ _ ) ) ( le_mul_of_one_le_left ( by positivity ) ( by linarith ) );
  -- Since $n_seq_v4 p 1$ is the minimum of $I0 p$, and $I0 p$ is nonempty, $n_seq_v4 p 1$ must be positive.
  have h_min_pos : ∀ x ∈ I0 p, x ≥ p.tilde_m - p.m ^ (2 * z p.m - 1) := by
    unfold I0 at *; simp_all +decide ;
    unfold J1' J2' at *; split_ifs at * <;> simp_all +decide [ Finset.mem_Ico ] ;
    exact fun x hx₁ hx₂ => by linarith;
  by_cases h : ( I0 p ).Nonempty <;> simp_all +decide [ n_seq_v4 ];
  · grind;
  · exact absurd h ( Finset.Nonempty.ne_empty ( I0_nonempty p ) )

/-
The sequences $n_j$ and $n_j'$ are equal up to index $z$.
-/
theorem n_seq_eq_n_seq_v4 (p : ProblemParameters) (j : ℕ) (hj : j ≤ z p.m) :
    n_seq p j = n_seq_v4 p j := by
  induction j using Nat.strong_induction_on with | h j ih =>
  rcases j with _ | _ | j
  · rfl
  · simp [n_seq, n_seq_v4]
  · have hprev : n_seq p (j + 1) = n_seq_v4 p (j + 1) := by
      exact ih (j + 1) (by omega) (by omega)
    have hj' : j + 1 ∈ Finset.Icc 1 (z p.m - 1) := by
      simp [Finset.mem_Icc]
      omega
    have hk : k_exp p (sigma p (n_seq_v4 p (j + 1))) (j + 1) ≥ 1 := by
      simpa [← hprev] using k_ge_one p (j + 1) hj' (n_seq p (j + 1))
    simp [n_seq, n_seq_v4, hprev]
    set n := n_seq_v4 p (j + 1)
    set s := sigma p n
    set k := k_exp p s (j + 1)
    have hk' : k ≥ 1 := by
      simpa [n, s, k] using hk
    have hiff : ∀ x : ℕ,
        (n < x ∧ k ≤ e p s (x : ℤ) - e p s (p.r x)) ↔
        (n < x ∧ e p s (p.r x) + k ≤ e p s (x : ℤ)) := by
      intro x
      constructor
      · intro hx
        exact ⟨hx.1, by omega⟩
      · intro hx
        exact ⟨hx.1, by omega⟩
    by_cases hP : ∃ x, n < x ∧ k ≤ e p s (x : ℤ) - e p s (p.r x)
    · have hQ : ∃ x, n < x ∧ e p s (p.r x) + k ≤ e p s (x : ℤ) := by
        rcases hP with ⟨x, hx⟩
        exact ⟨x, (hiff x).1 hx⟩
      simp [hP, hQ, n, s, k]
      simpa [n, s, k] using Nat.find_congr (Nat.find_spec hP) (fun x hx => hiff x)
    · have hQ : ¬ ∃ x, n < x ∧ e p s (p.r x) + k ≤ e p s (x : ℤ) := by
        intro h
        rcases h with ⟨x, hx⟩
        exact hP ⟨x, (hiff x).2 hx⟩
      simp [hP, hQ, n, s, k]

/-
The sequence $n_j$ consists of positive integers.
-/
theorem n_seq_v4_pos (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    n_seq_v4 p j > 0 := by
      induction j with
      | zero => norm_num at hj
      | succ j ih =>
        rcases j with ( _ | j ) <;> simp_all +decide;
        · exact n_seq_v4_1_pos p;
        · exact lt_of_le_of_lt ( Nat.zero_le _ ) ( n_seq_v4_increasing' p ( j + 1 ) ( by linarith ) )

/-
The function $p_i$ is injective on the domain $1 \dots z$.
-/
theorem p_i_injective (p : ProblemParameters) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 (z p.m)) (hj : j ∈ Finset.Icc 1 (z p.m)) (hij : i ≠ j) :
    p_i p i ≠ p_i p j := by
      intro h_eq
      have hi_bounds := Finset.mem_Icc.mp hi
      have hj_bounds := Finset.mem_Icc.mp hj
      have hlen : (primes_lt_m p).length = z p.m := by
        simp [primes_lt_m, z]
      have hi_lt : i - 1 < (primes_lt_m p).length := by
        rw [hlen]
        exact lt_of_lt_of_le (Nat.sub_lt hi_bounds.1 zero_lt_one) hi_bounds.2
      have hj_lt : j - 1 < (primes_lt_m p).length := by
        rw [hlen]
        exact lt_of_lt_of_le (Nat.sub_lt hj_bounds.1 zero_lt_one) hj_bounds.2
      have h_eq' : (primes_lt_m p)[i - 1] = (primes_lt_m p)[j - 1] := by
        unfold p_i at h_eq
        simp [hi_lt, hj_lt] at h_eq
        exact h_eq
      have hnodup : (primes_lt_m p).Nodup := by
        unfold primes_lt_m
        exact Finset.sort_nodup ((Finset.range p.m).filter Nat.Prime) (· ≤ ·)
      have hfin : (⟨i - 1, hi_lt⟩ : Fin (primes_lt_m p).length) = ⟨j - 1, hj_lt⟩ := by
        exact (List.Nodup.get_inj_iff hnodup).mp h_eq'
      have hij_sub : i - 1 = j - 1 := by
        exact congrArg Fin.val hfin
      exact hij (by linarith [Nat.sub_add_cancel hi_bounds.1, Nat.sub_add_cancel hj_bounds.1, hij_sub])

/-
The prime power factors in $d(n)$ are pairwise coprime.
-/
theorem d_terms_coprime (p : ProblemParameters) (n : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 (z p.m)) (hj : j ∈ Finset.Icc 1 (z p.m)) (hij : i ≠ j) :
    Nat.Coprime ((p_i p i) ^ (e p i (X_int p.r n))) ((p_i p j) ^ (e p j (X_int p.r n))) := by
      -- Since $p_i$ and $p_j$ are distinct primes, their powers are coprime.
      have h_distinct_primes : Nat.Prime (p_i p i) ∧ Nat.Prime (p_i p j) ∧ p_i p i ≠ p_i p j := by
        exact ⟨ p_i_prime p i hi, p_i_prime p j hj, p_i_injective p i j hi hj hij ⟩
      generalize_proofs at *;
      exact Nat.coprime_pow_primes _ _ h_distinct_primes.1 h_distinct_primes.2.1 h_distinct_primes.2.2

/-
Each prime power factor in $d(n)$ divides $|X_n|$.
-/
theorem d_term_dvd_X_int (p : ProblemParameters) (n : ℕ) (i : ℕ) (_hi : i ∈ Finset.Icc 1 (z p.m)) :
    (p_i p i) ^ (e p i (X_int p.r n)) ∣ Int.natAbs (X_int p.r n) := by
      have h_div : (p_i p i) ^ (padicValNat (p_i p i) (Int.natAbs (X_int p.r n))) ∣ Int.natAbs (X_int p.r n) := by
        exact pow_padicValNat_dvd;
      convert h_div using 1

/-
$d(n)$ divides $|X_n|$.
-/
theorem d_dvd_X_int (p : ProblemParameters) (n : ℕ) :
    d p n ∣ Int.natAbs (X_int p.r n) := by
      -- Apply the theorem that allows us to combine the coprime divisibilities.
      have h_prod_dvd : ∀ {S : Finset ℕ} {a : ℕ}, (∀ i ∈ S, (p_i p i) ^ (e p i (X_int p.r n)) ∣ a) → (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime ((p_i p i) ^ (e p i (X_int p.r n))) ((p_i p j) ^ (e p j (X_int p.r n)))) → (∏ i ∈ S, (p_i p i) ^ (e p i (X_int p.r n))) ∣ a := by
        intros S a h_div h_coprime
        induction S using Finset.induction with
        | empty => aesop
        | @insert i S hi ih =>
        rw [ Finset.prod_insert hi ];
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by exact Nat.Coprime.prod_right fun j hj => h_coprime i ( Finset.mem_insert_self _ _ ) j ( Finset.mem_insert_of_mem hj ) ( by aesop ) ) ( h_div i ( Finset.mem_insert_self _ _ ) ) ( ih ( fun j hj => h_div j ( Finset.mem_insert_of_mem hj ) ) ( fun j hj k hk => h_coprime j ( Finset.mem_insert_of_mem hj ) k ( Finset.mem_insert_of_mem hk ) ) );
      convert h_prod_dvd _ _ using 1;
      · exact fun i a => d_term_dvd_X_int p n i a;
      · exact fun i a j a_1 a_2 => d_terms_coprime p n i j a a_1 a_2

/-
The valuation of any prime $q < m$ in $d(n)$ is equal to its valuation in $|X_n|$.
-/
theorem valuation_d_eq_valuation_X_int (p : ProblemParameters) (n : ℕ) (q : ℕ) (hq : q < p.m) (hq_prime : Nat.Prime q) :
    padicValNat q (d p n) = padicValNat q (Int.natAbs (X_int p.r n)) := by
      -- Since $q$ is a prime less than $m$, it must appear in the list `primes_lt_m` at some index $k$.
      obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc 1 (z p.m), p_i p k = q := by
        -- Since $q$ is a prime less than $m$, it must appear in the list `primes_lt_m`.
        have hq_in_list : q ∈ (Finset.range p.m).filter Nat.Prime := by
          exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hq, hq_prime ⟩;
        -- Since $q$ is in the list `primes_lt_m`, there exists an index $k$ such that $p_i p k = q$.
        obtain ⟨k, hk⟩ : ∃ k < (primes_lt_m p).length, (primes_lt_m p)[k]! = q := by
          have hq_in_list : q ∈ primes_lt_m p := by
            exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 hq_in_list;
          obtain ⟨ k, hk ⟩ := List.mem_iff_get.1 hq_in_list; use k; aesop;
        refine ⟨ k + 1, ?_, ?_ ⟩;
        · unfold z primes_lt_m at *; aesop;
        · unfold p_i; aesop;
      -- By definition of $d(n)$, we have $d(n) = q^{e_k} \cdot \prod_{j \ne k} p_j^{e_j}$.
      have hd : d p n = q ^ (e p k (X_int p.r n)) * (∏ j ∈ Finset.Icc 1 (z p.m) \ {k}, (p_i p j) ^ (e p j (X_int p.r n))) := by
        unfold d; rw [ Finset.prod_eq_mul_prod_diff_singleton k (fun j => (p_i p j) ^ (e p j (X_int p.r n))) (by intro h; exact False.elim (h hk.1)) ] ; aesop;
      by_cases h : X_int p.r n = 0 <;> simp_all +decide [Finset.prod_eq_zero_iff];
      · unfold e at *; aesop;
      · haveI := Fact.mk hq_prime; rw [ padicValNat.mul ] <;> simp_all +decide [ Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ] ;
        · -- Since $p_i j$ are distinct primes for $j \ne k$, their product is coprime with $q$.
          have h_coprime : ∀ j ∈ Finset.Icc 1 (z p.m) \ {k}, Nat.Coprime q (p_i p j) := by
            intros j hj
            have h_distinct : p_i p j ≠ p_i p k := by
              exact p_i_injective p j k ( Finset.mem_sdiff.mp hj |>.1 ) ( Finset.mem_Icc.mpr hk.1 ) ( by aesop );
            exact hq_prime.coprime_iff_not_dvd.mpr fun h => h_distinct <| by have := Nat.prime_dvd_prime_iff_eq hq_prime ( p_i_prime p j <| Finset.mem_sdiff.mp hj |>.1 ) ; aesop;
          have h_coprime_prod : Nat.Coprime q (∏ j ∈ Finset.Icc 1 (z p.m) \ {k}, (p_i p j) ^ (e p j (X_int p.r n))) := by
            exact Nat.Coprime.prod_right fun j hj => Nat.Coprime.pow_right _ <| h_coprime j hj;
          haveI := Fact.mk hq_prime; rw [ padicValNat.eq_zero_of_not_dvd ] <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          unfold e; aesop;
        · unfold e; aesop;

/-
The valuation of the term $T$ is at most $e(L_n) - k$.
-/
theorem valuation_T_le (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let n_next := n_seq_v4 p (j + 1)
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s (p.r n_next * ((L n) / n_next : ℕ)) ≤ e p s (L n) - k := by
      have h_div : n_seq_v4 p (j + 1) ∣ L n := by
        exact n_next_dvd_L_n_v4 p j hj n hn
      have h_k_le_val : k_exp p (sigma p (n_seq_v4 p j)) j ≤ e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) := by
        have := n_seq_v4_prop p j hj
        generalize_proofs at *; (
        linarith [ Nat.zero_le ( e p ( sigma p ( n_seq_v4 p j ) ) ( p.r ( n_seq_v4 p ( j + 1 ) ) ) ) ])
      generalize_proofs at *; (
      field_simp;
      have h_val_T : (e p (sigma p (n_seq_v4 p j)) (p.r (n_seq_v4 p (j + 1)) * ((L n) / (n_seq_v4 p (j + 1)) : ℕ))) = (e p (sigma p (n_seq_v4 p j)) (p.r (n_seq_v4 p (j + 1)))) + (e p (sigma p (n_seq_v4 p j)) (L n)) - (e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1))) := by
        convert valuation_term_eq p n ( n_seq_v4 p ( j + 1 ) ) ?_ ( sigma p ( n_seq_v4 p j ) ) ?_ using 1
        focus
          generalize_proofs at *
          rw [ add_comm ];
        · -- Since $n \in I_set_v4 p j$, we have $n \geq n_seq_v4 p (j + 1)$.
          have h_n_ge_n_next : n ≥ n_seq_v4 p (j + 1) := by
            -- By definition of $I_set_v4$, we know that $n \geq n_seq_v4 p (j + 1)$.
            have h_n_ge_n_next : n ∈ Finset.Ico (n_seq_v4 p (j + 1)) (n_seq_v4 p (j + 1) + (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j)) := by
              convert hn using 1
              generalize_proofs at *; (
              unfold I_set_v4; aesop;)
            generalize_proofs at *; (
            exact Finset.mem_Ico.mp h_n_ge_n_next |>.1)
          generalize_proofs at *; (
          exact Finset.mem_Icc.mpr ⟨ Nat.pos_of_dvd_of_pos h_div ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ), h_n_ge_n_next ⟩);
        · by_cases h : ∃ i ∈ Finset.Icc 1 ( z p.m ), ( p_i p i ) ^ ( e p i ( X_int p.r ( n_seq_v4 p j ) ) ) > n_seq_v4 p j <;> simp_all +decide [ sigma ];
          · exact ⟨ _, Finset.mem_Icc.mp ( Nat.find_spec ( show ∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j from by aesop ) |>.1 ) |>.2, Finset.mem_Icc.mp ( Nat.find_spec ( show ∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j from by aesop ) |>.1 ), Nat.find_spec ( show ∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j from by aesop ) |>.2 ⟩;
          · grind
      generalize_proofs at *; (
      have h_val_T_le : e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) ≥ e p (sigma p (n_seq_v4 p j)) (p.r (n_seq_v4 p (j + 1))) + k_exp p (sigma p (n_seq_v4 p j)) j := by
        exact n_seq_v4_prop p j hj |> fun h => by linarith;
      generalize_proofs at *; (
      exact h_val_T.symm ▸ by omega;)))

/-
Decomposition of X_int into four parts.
-/
noncomputable def S1 (p : ProblemParameters) (j : ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 (n_seq_v4 p j), p.r i * ((L n) / i : ℕ)

noncomputable def S2 (p : ProblemParameters) (j : ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1), p.r i * ((L n) / i : ℕ)

noncomputable def T3 (p : ProblemParameters) (j : ℕ) (n : ℕ) : ℤ :=
  p.r (n_seq_v4 p (j + 1)) * ((L n) / n_seq_v4 p (j + 1) : ℕ)

noncomputable def S4 (p : ProblemParameters) (j : ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ioc (n_seq_v4 p (j + 1)) n, p.r i * ((L n) / i : ℕ)

theorem X_int_decomp (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    X_int p.r n = S1 p j n + S2 p j n + T3 p j n + S4 p j n := by
      have h_decomp : Finset.Icc 1 n = Finset.Icc 1 (n_seq_v4 p j) ∪ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1) ∪ {n_seq_v4 p (j + 1)} ∪ Finset.Ioc (n_seq_v4 p (j + 1)) n := by
        ext x;
        constructor <;> intro hx <;> simp_all +decide [ Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc ];
        · grind +ring;
        · rcases hx with ( rfl | hx | hx | hx ) <;> simp_all +decide [ I_set_v4 ];
          · split_ifs at hn <;> simp_all +decide [ I_j_v4 ];
            exact Nat.pos_of_ne_zero ( by linarith [ n_seq_v4_increasing p j hj.1 ] );
          · split_ifs at hn <;> simp_all +decide [ I_j_v4 ];
            linarith [ n_seq_v4_increasing' p j hj.1 ];
          · split_ifs at hn <;> simp_all +decide [ I_j_v4 ];
            omega;
          · grind;
      unfold X_int S1 S2 T3 S4; rw [ h_decomp ] ; rw [ Finset.sum_union, Finset.sum_union, Finset.sum_union ] <;> norm_num;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Ioc.mp hx₂ ] ;
      · exact ⟨ fun _ => n_seq_v4_increasing' p j ( by linarith [ Finset.mem_Icc.mp hj ] ), fun _ => by linarith [ n_seq_v4_increasing' p j ( by linarith [ Finset.mem_Icc.mp hj ] ) ] ⟩;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Ioc.mp hx₂, n_seq_v4_increasing p j ( Finset.mem_Icc.mp hj |>.1 ) ] ;

/-
The valuation of the term T3 is at most e(L_n) - k.
-/
theorem T3_valuation_le (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s (T3 p j n) ≤ e p s (L n) - k := by
      convert valuation_T_le p j hj n hn using 1

/-
The valuation of L_n is at least k.
-/
theorem e_L_n_ge_k (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s (L n) ≥ k := by
      -- We know that $n_{j+1}$ divides $L_n$ (by $n_next_dvd_L_n_v4$).
      have h_div : n_seq_v4 p (j + 1) ∣ L n := by
        exact n_next_dvd_L_n_v4 p j hj n hn;
      -- From n_seq_v4_prop, e(n_{j+1}) >= e(r_{n_{j+1}}) + k.
      have h_e_n_j1 : e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) ≥ e p (sigma p (n_seq_v4 p j)) (p.r (n_seq_v4 p (j + 1))) + k_exp p (sigma p (n_seq_v4 p j)) j := by
        convert n_seq_v4_prop p j hj using 1;
      have h_e_L_n : e p (sigma p (n_seq_v4 p j)) (L n) ≥ e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) := by
        have h_e_L_n : padicValNat (p_i p (sigma p (n_seq_v4 p j))) (L n) ≥ padicValNat (p_i p (sigma p (n_seq_v4 p j))) (n_seq_v4 p (j + 1)) := by
          haveI := Fact.mk ( p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( by
            by_cases h : ∃ i ∈ Finset.Icc 1 ( z p.m ), ( p_i p i ) ^ ( e p i ( X_int p.r ( n_seq_v4 p j ) ) ) > n_seq_v4 p j <;> simp_all +decide [ sigma ];
            · exact ⟨ h.choose, h.choose_spec.1.2, h.choose_spec.1, h.choose_spec.2 ⟩;
            · grind ) ) ; rw [ ← Nat.factorization_def, ← Nat.factorization_def ]
          focus
            exact Nat.factorization_le_iff_dvd ( by
              exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos h_div ( Nat.pos_of_ne_zero ( by unfold L; aesop ) ) ) ) ( by
              exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop; ) |>.2 h_div _;
          · exact this.1;
          · exact this.1;
        convert h_e_L_n using 1;
      grind

/-
The valuation of the term r_i * (L_n / i) is e(r_i) + e(L_n) - e(i).
-/
theorem valuation_term_eq_v4 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (i : ℕ) (hi : i ∈ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1)) :
    let s := sigma p (n_seq_v4 p j)
    e p s (p.r i * ((L n) / i : ℕ)) = e p s (p.r i) + e p s (L n) - e p s i := by
      have h_i_in_Ln : i ∈ Finset.Icc 1 n := by
        -- Since $i$ is in the interval $(n_{j+1}, n]$, we have $i \leq n$.
        have h_i_le_n : i ≤ n := by
          rcases j with ( _ | j ) <;> simp_all +decide [ I_set_v4 ];
          exact le_trans hi.2 ( Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Ico.mp hn ] );
        exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_pos p j hj ], h_i_le_n ⟩;
      convert valuation_term_eq p n i h_i_in_Ln _ _ using 1;
      · ring_nf;
      · unfold sigma;
        split_ifs <;> simp_all +decide;
        · exact ⟨ _, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j› |>.1 ) |>.2, Finset.mem_Icc.mp ( Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j› |>.1 ), Classical.choose_spec ‹∃ i ∈ Finset.Icc 1 ( z p.m ), p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) > n_seq_v4 p j› |>.2 ⟩;
        · linarith

/-
The valuation of each term in S2 is at least e(L_n) - k + 1.
-/
theorem S2_term_valuation_ge (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (i : ℕ) (hi : i ∈ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1)) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s (p.r i * ((L n) / i : ℕ)) ≥ e p s (L n) - k + 1 := by
      -- Using `valuation_term_eq_v4`, the valuation of the term is `e(r_i) + e(L n) - e(i)`.
      have h_val : e p (sigma p (n_seq_v4 p j)) (p.r i * ((L n) / i : ℕ)) = e p (sigma p (n_seq_v4 p j)) (p.r i) + e p (sigma p (n_seq_v4 p j)) (L n) - e p (sigma p (n_seq_v4 p j)) i := by
        convert valuation_term_eq_v4 p j hj n hn i hi using 1;
      have h_ineq : e p (sigma p (n_seq_v4 p j)) i < e p (sigma p (n_seq_v4 p j)) (p.r i) + k_exp p (sigma p (n_seq_v4 p j)) j := by
        convert n_seq_v4_min_prop p j hj i _; aesop;
      have h_ineq : e p (sigma p (n_seq_v4 p j)) (L n) ≥ k_exp p (sigma p (n_seq_v4 p j)) j := by
        apply e_L_n_ge_k p j hj n hn;
      omega

/-
Each term in S2 is divisible by p^(e(L_n) - k + 1).
-/
theorem term_divisible (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (i : ℕ) (hi : i ∈ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1)) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    (p_i p s) ^ (e p s (L n) - k + 1) ∣ Int.natAbs (p.r i * ((L n) / i : ℕ)) := by
      have h_term_div_p : let s := sigma p (n_seq_v4 p j)
        let k := k_exp p s j
        e p s (p.r i * ((L n) / i : ℕ)) ≥ e p s (L n) - k + 1 := by
          convert S2_term_valuation_ge p j hj n hn i hi using 1;
      have h_term_div_p : ∀ {x : ℕ}, x ≠ 0 → ∀ {V : ℕ}, padicValNat (p_i p (sigma p (n_seq_v4 p j))) x ≥ V → (p_i p (sigma p (n_seq_v4 p j))) ^ V ∣ x := by
        intros x hx V hV; exact (by
        have h_term_div_p : padicValNat (p_i p (sigma p (n_seq_v4 p j))) x ≥ V → (p_i p (sigma p (n_seq_v4 p j))) ^ V ∣ x := by
          intro hV
          have h_prime : Nat.Prime (p_i p (sigma p (n_seq_v4 p j))) := by
            have h_prime : ∀ i ∈ Finset.Icc 1 (z p.m), Nat.Prime (p_i p i) := by
              exact fun i a => p_i_prime p i a;
            apply h_prime; exact (by
            apply Classical.byContradiction
            intro h_contra;
            simp_all +decide [ sigma ];
            split_ifs at h_contra <;> norm_num at h_contra;
            · exact absurd ( h_contra _ ( Classical.choose_spec ‹∃ i, ( 1 ≤ i ∧ i ≤ z p.m ) ∧ n_seq_v4 p j < p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) › |>.1 |>.2 ) ( Classical.choose_spec ‹∃ i, ( 1 ≤ i ∧ i ≤ z p.m ) ∧ n_seq_v4 p j < p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) › |>.1 |>.1 ) ( Classical.choose_spec ‹∃ i, ( 1 ≤ i ∧ i ≤ z p.m ) ∧ n_seq_v4 p j < p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) › |>.1 |>.2 ) ) ( not_le_of_gt ( Classical.choose_spec ‹∃ i, ( 1 ≤ i ∧ i ≤ z p.m ) ∧ n_seq_v4 p j < p_i p i ^ e p i ( X_int p.r ( n_seq_v4 p j ) ) › |>.2 ) );
            · grind)
          have h_term_div_p : padicValNat (p_i p (sigma p (n_seq_v4 p j))) x ≥ V → (p_i p (sigma p (n_seq_v4 p j))) ^ V ∣ x := by
            intro hV
            have h_factorization : (Nat.factorization x) (p_i p (sigma p (n_seq_v4 p j))) ≥ V := by
              rw [ Nat.factorization_def ]
              focus
                aesop
              exact h_prime
            exact Nat.dvd_trans ( pow_dvd_pow _ h_factorization ) ( Nat.ordProj_dvd _ _ );
          exact h_term_div_p hV;
        exact h_term_div_p hV);
      by_cases h : p.r i * ↑ ( L n / i ) = 0 <;> aesop

/-
If the valuation of x is at least k, then p^k divides |x|.
-/
theorem pow_dvd_of_le_valuation (p : ProblemParameters) (s : ℕ) (_hs : s ∈ Finset.Icc 1 (z p.m)) (x : ℤ) (k : ℕ) (h : e p s x ≥ k) :
    (p_i p s) ^ k ∣ Int.natAbs x := by
      have h_div : (p_i p s) ^ (padicValNat (p_i p s) x.natAbs) ∣ x.natAbs := by
        exact pow_padicValNat_dvd;
      exact dvd_trans ( pow_dvd_pow _ h ) h_div

/-
sigma returns an index in the range [1, z].
-/
theorem sigma_in_range (p : ProblemParameters) (n : ℕ) : sigma p n ∈ Finset.Icc 1 (z p.m) := by
  by_contra h_contra;
  unfold sigma at h_contra; simp_all +decide [ Finset.mem_Icc ] ;
  unfold z at *; split_ifs at *
  focus
    simp_all +decide
  · obtain ⟨ i, hi₁, hi₂ ⟩ := ‹∃ i, ( 1 ≤ i ∧ i ≤ _ ) ∧ n < p_i p i ^ e p i ( X_int p.r n ) › ; linarith [ h_contra i hi₁.2 hi₁.1 ] ;
  · have h_prime_count : (Finset.filter Nat.Prime (Finset.range p.m)).card ≥ 1 := by
      have h_m_ge_4 : 4 ≤ p.m := by
        exact p.hm4
      exact Finset.card_pos.mpr ⟨ 2, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), by norm_num ⟩ ⟩
    exact h_contra (by norm_num) |> not_lt_of_ge (Nat.succ_le_of_lt h_prime_count) |> False.elim

/-
The valuation of n_{j+1} is at least k.
-/
theorem n_seq_v4_valuation_ge_k (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) :
    let n_next := n_seq_v4 p (j + 1)
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s n_next ≥ k := by
      -- Since $e_{\sigma(j)}(n_{j+1}) \geq e_{\sigma(j)}(r_{n_{j+1}}) + k_j$ and $e_{\sigma(j)}(r_{n_{j+1}}) \geq 0$, it follows that $e_{\sigma(j)}(n_{j+1}) \geq k_j$.
      have h_val_n_next : e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) ≥ e p (sigma p (n_seq_v4 p j)) (p.r (n_seq_v4 p (j + 1))) + k_exp p (sigma p (n_seq_v4 p j)) j := by
        convert n_seq_v4_prop p j hj using 1;
      exact le_trans ( Nat.le_add_left _ _ ) h_val_n_next

/-
S2 is divisible by p^(e(L_n) - k + 1) as an integer.
-/
theorem S2_divisible_int (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    ((p_i p s) : ℤ) ^ (e p s (L n) - k + 1) ∣ S2 p j n := by
      -- By definition of $S2$, each term in the sum is divisible by $p^{e(L_n) - k + 1}$.
      have hS2_term_div : ∀ i ∈ Finset.Ioc (n_seq_v4 p j) (n_seq_v4 p (j + 1) - 1), (p_i p (sigma p (n_seq_v4 p j))) ^ ((e p (sigma p (n_seq_v4 p j)) (L n)) - (k_exp p (sigma p (n_seq_v4 p j)) j) + 1) ∣ Int.natAbs (p.r i * ((L n) / i : ℕ)) := by
        exact fun i a => term_divisible p j hj n hn i a;
      convert Finset.dvd_sum fun i hi => Int.natCast_dvd.mpr ( hS2_term_div i hi ) using 1

/-
For all $i$ in the range $(n_{j+1}, n]$, the valuation of the term $r_i L_n / i$ is at least $e(L_n) - k + 1$.
-/
theorem S4_term_valuation_ge (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (i : ℕ) (hi : i ∈ Finset.Ioc (n_seq_v4 p (j + 1)) n) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    e p s (p.r i * ((L n) / i : ℕ)) ≥ e p s (L n) - k + 1 := by
      have h_valuation_term : let s := sigma p (n_seq_v4 p j); let k := k_exp p s j; e p s i < k := by
        have h_val_i : i < n_seq_v4 p (j + 1) + (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) := by
          have h_i_lt : n < n_seq_v4 p (j + 1) + (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) := by
            unfold I_set_v4 I_j_v4 at hn; aesop;
          exact lt_of_le_of_lt ( Finset.mem_Ioc.mp hi |>.2 ) h_i_lt;
        -- Since $e_s(i) \geq k$ would imply $p^k \mid i$, but $i < n_{j+1} + p^k$ and $n_{j+1} \equiv 0 \pmod{p^k}$, this leads to a contradiction.
        have h_contradiction : ∀ k, e p (sigma p (n_seq_v4 p j)) i ≥ k → (p_i p (sigma p (n_seq_v4 p j))) ^ k ∣ i := by
          intros k hk
          have h_div : (p_i p (sigma p (n_seq_v4 p j))) ^ k ∣ i := by
            have h_div : (p_i p (sigma p (n_seq_v4 p j))) ^ k ∣ i := by
              have h_val : padicValNat (p_i p (sigma p (n_seq_v4 p j))) i ≥ k := by
                unfold e at hk; aesop;
              have h_div : (p_i p (sigma p (n_seq_v4 p j))) ^ (padicValNat (p_i p (sigma p (n_seq_v4 p j))) i) ∣ i := by
                exact pow_padicValNat_dvd;
              exact dvd_trans ( pow_dvd_pow _ h_val ) h_div;
            exact h_div
          exact h_div;
        have h_contradiction : (p_i p (sigma p (n_seq_v4 p j))) ^ (k_exp p (sigma p (n_seq_v4 p j)) j) ∣ n_seq_v4 p (j + 1) := by
          have h_contradiction : e p (sigma p (n_seq_v4 p j)) (n_seq_v4 p (j + 1)) ≥ k_exp p (sigma p (n_seq_v4 p j)) j := by
            convert n_seq_v4_valuation_ge_k p j hj using 1;
          convert pow_dvd_of_le_valuation p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ( n_seq_v4 p ( j + 1 ) ) ( k_exp p ( sigma p ( n_seq_v4 p j ) ) j ) h_contradiction using 1;
        exact lt_of_not_ge fun h => by have := Nat.dvd_sub ( ‹∀ k, e p ( sigma p ( n_seq_v4 p j ) ) i ≥ k → p_i p ( sigma p ( n_seq_v4 p j ) ) ^ k ∣ i› _ h ) h_contradiction; exact absurd this ( Nat.not_dvd_of_pos_of_lt ( Nat.sub_pos_of_lt <| by linarith [ Finset.mem_Ioc.mp hi ] ) <| by rw [ Nat.sub_lt_iff_lt_add ] <;> linarith [ Finset.mem_Ioc.mp hi ] ) ;
      have h_valuation_term : let s := sigma p (n_seq_v4 p j); let k := k_exp p s j; e p s (p.r i * ((L n) / i : ℕ)) = e p s (p.r i) + e p s (L n) - e p s i := by
        have h_valuation_term : let s := sigma p (n_seq_v4 p j); let k := k_exp p s j; e p s (i * ((L n) / i : ℕ)) = e p s (L n) := by
          have h_valuation_term : let s := sigma p (n_seq_v4 p j); let k := k_exp p s j; i * ((L n) / i : ℕ) = L n := by
            rw [ Nat.mul_div_cancel' ];
            exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p j ( Finset.mem_Icc.mp hj |>.1 ) ], by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p j ( Finset.mem_Icc.mp hj |>.1 ) ] ⟩ );
          grind;
        have h_valuation_term : let s := sigma p (n_seq_v4 p j); let k := k_exp p s j; e p s (p.r i * ((L n) / i : ℕ)) + e p s i = e p s (p.r i) + e p s (i * ((L n) / i : ℕ)) := by
          have h_valuation_term : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → e p (sigma p (n_seq_v4 p j)) (a * b) = e p (sigma p (n_seq_v4 p j)) a + e p (sigma p (n_seq_v4 p j)) b := by
            intros a b ha hb; exact (by
            convert padicValNat.mul ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ha ) ) ( Nat.ne_of_gt ( Nat.pos_of_ne_zero hb ) ) using 1;
            exact ⟨ p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ⟩);
          have h_valuation_term : e p (sigma p (n_seq_v4 p j)) (p.r i * ((L n) / i : ℕ)) = e p (sigma p (n_seq_v4 p j)) (p.r i) + e p (sigma p (n_seq_v4 p j)) ((L n) / i : ℕ) := by
            convert h_valuation_term ( Int.natAbs ( p.r i ) ) ( L n / i ) _ _ using 1 <;> norm_num [ Int.natAbs_mul ];
            · cases abs_cases ( p.r i ) <;> simp +decide [ * ];
              unfold e; norm_num;
            · exact p.h_r_nz i;
            · exact ⟨ by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p ( j + 1 ) ( by linarith [ Finset.mem_Icc.mp hj ] ) ], Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( show 0 < L n from Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) ) ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p ( j + 1 ) ( by linarith [ Finset.mem_Icc.mp hj ] ) ], by linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p ( j + 1 ) ( by linarith [ Finset.mem_Icc.mp hj ] ) ] ⟩ ) ) ⟩;
          have h_valuation_term : e p (sigma p (n_seq_v4 p j)) (i * ((L n) / i : ℕ)) = e p (sigma p (n_seq_v4 p j)) i + e p (sigma p (n_seq_v4 p j)) ((L n) / i : ℕ) := by
            apply_assumption;
            · linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p j ( by linarith [ Finset.mem_Icc.mp hj ] ) ];
            · refine Nat.ne_of_gt ( Nat.div_pos ?_ ?_ );
              · refine le_trans ( Finset.mem_Ioc.mp hi |>.2 ) ?_;
                exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_iff_ne_zero.mpr ( by aesop ), le_rfl ⟩ ) );
              · linarith [ Finset.mem_Ioc.mp hi, n_seq_v4_increasing' p j ( Finset.mem_Icc.mp hj |>.1 ) ];
          grind;
        exact eq_tsub_of_add_eq ( by linarith );
      simp_all +decide;
      have hLge : e p (sigma p (n_seq_v4 p j)) (L n) ≥ k_exp p (sigma p (n_seq_v4 p j)) j := by
        exact e_L_n_ge_k p j (Finset.mem_Icc.mpr hj) n hn
      omega

/-
The sum $S4$ is divisible by $p^{e(L_n) - k + 1}$.
-/
theorem S4_divisible_int (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    ((p_i p s) : ℤ) ^ (e p s (L n) - k + 1) ∣ S4 p j n := by
      -- By definition of $S4$, each term in the sum has valuation at least $e_s(L_n) - k + 1$.
      have h_S4_term_val : ∀ i ∈ Finset.Ioc (n_seq_v4 p (j + 1)) n, e p (sigma p (n_seq_v4 p j)) (p.r i * ((L n) / i : ℕ)) ≥ e p (sigma p (n_seq_v4 p j)) (L n) - k_exp p (sigma p (n_seq_v4 p j)) j + 1 := by
        convert S4_term_valuation_ge p j hj n hn using 1;
      refine Finset.dvd_sum fun i hi => ?_;
      have h_div : ∀ {x : ℤ}, x ≠ 0 → (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) x) ∣ Int.natAbs x := by
        intros x hx_nonzero
        have h_div : (p_i p (sigma p (n_seq_v4 p j))) ^ (padicValNat (p_i p (sigma p (n_seq_v4 p j))) (Int.natAbs x)) ∣ Int.natAbs x := by
          exact pow_padicValNat_dvd;
        convert h_div using 1;
      by_cases hi : p.r i * ( L n / i : ℕ ) = 0 <;> simp_all +decide [ ← Int.natCast_dvd_natCast ];
      · cases hi <;> simp_all +decide;
      · exact dvd_trans ( pow_dvd_pow _ ( h_S4_term_val i ( by linarith ) ( by linarith ) ) ) ( h_div ( mul_ne_zero hi.1 hi.2 ) )

/-
The valuation of $S1$ is at least $e(L_n) + 1$.
-/
theorem S1_valuation_ge (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (h_sigma : (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    e p s (S1 p j n) ≥ e p s (L n) + 1 := by
      -- By `part1_valuation_v2` (using `h_sigma`), we know that $v(X_{n_j}) \ge v(L_{n_j}) + 1$.
      have h_X_val : let s := sigma p (n_seq_v4 p j);
        e p s (X_int p.r (n_seq_v4 p j)) ≥ e p s (L (n_seq_v4 p j)) + 1 := by
          convert part1_valuation_v2 p j hj _ using 1;
          · rw [ n_seq_eq_n_seq_v4 p j ( Finset.mem_Icc.mp hj |>.2 ) ];
          · use sigma p (n_seq_v4 p j);
            convert sigma_mem p ( n_seq_v4 p j ) _ using 1;
            · rw [ n_seq_eq_n_seq_v4 p j ( Finset.mem_Icc.mp hj |>.2 ) ] at * ; aesop;
            · exact ⟨ _, sigma_in_range p _, h_sigma ⟩;
      have h_S1_val : let s := sigma p (n_seq_v4 p j);
        e p s (S1 p j n) = e p s (L n) - e p s (L (n_seq_v4 p j)) + e p s (X_int p.r (n_seq_v4 p j)) := by
          convert part1_valuation_eq p j hj n _ using 1;
          · rw [ show n_seq p j = n_seq_v4 p j from n_seq_eq_n_seq_v4 p j ( Finset.mem_Icc.mp hj |>.2 ) ];
            by_cases h : X_int p.r ( n_seq_v4 p j ) = 0 <;> simp_all +decide [ S1 ];
            exact absurd h_X_val ( by linarith [ show e p ( sigma p ( n_seq_v4 p j ) ) 0 = 0 from by unfold e; aesop ] );
          · rcases j with ( _ | j ) <;> simp_all +decide [ I_set_v4 ];
            -- Since $n \in I_j_v4 p (j + 1)$, we have $n \geq n_seq_v4 p (j + 2)$.
            have h_n_ge_n_seq_v4 : n ≥ n_seq_v4 p (j + 2) := by
              exact Finset.mem_Ico.mp hn |>.1;
            exact le_trans ( n_seq_eq_n_seq_v4 p ( j + 1 ) ( by linarith ) |> le_of_eq ) ( Nat.le_trans ( n_seq_v4_increasing p ( j + 1 ) ( by linarith ) |> le_of_lt ) h_n_ge_n_seq_v4 )
      generalize_proofs at *; (
      grind)

/-
The sum $S1 + S2 + S4$ is divisible by $p^{e(L_n) - k + 1}$.
-/
theorem sum_S1_S2_S4_divisible (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (h_sigma : (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    let k := k_exp p s j
    ((p_i p s) : ℤ) ^ (e p s (L n) - k + 1) ∣ S1 p j n + S2 p j n + S4 p j n := by
      have h_S1_div : ((p_i p (sigma p (n_seq_v4 p j)) : ℤ) ^ (e p (sigma p (n_seq_v4 p j)) (L n) - k_exp p (sigma p (n_seq_v4 p j)) j + 1) ∣ S1 p j n) := by
        have h_S1_div : e p (sigma p (n_seq_v4 p j)) (S1 p j n) ≥ e p (sigma p (n_seq_v4 p j)) (L n) + 1 := by
          convert S1_valuation_ge p j hj n hn h_sigma using 1;
        have h_S1_div : e p (sigma p (n_seq_v4 p j)) (S1 p j n) ≥ e p (sigma p (n_seq_v4 p j)) (L n) - k_exp p (sigma p (n_seq_v4 p j)) j + 1 := by
          exact le_trans ( by omega ) h_S1_div;
        convert pow_dvd_of_le_valuation p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ( S1 p j n ) ( e p ( sigma p ( n_seq_v4 p j ) ) ( L n ) - k_exp p ( sigma p ( n_seq_v4 p j ) ) j + 1 ) h_S1_div using 1;
        norm_num [ ← Int.natCast_dvd_natCast ];
      exact dvd_add ( dvd_add h_S1_div ( S2_divisible_int p j hj n hn ) ) ( S4_divisible_int p j hj n hn )

/-
The term $T3$ is non-zero.
-/
theorem T3_ne_zero (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j) : T3 p j n ≠ 0 := by
  refine mul_ne_zero ?_ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.div_pos ?_ ?_ );
  · exact p.h_r_nz (n_seq_v4 p (j + 1));
  · exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by
      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop; ) ) ( n_next_dvd_L_n_v4 p j hj n hn );
  · exact n_seq_v4_increasing' p _ ( by linarith [ Finset.mem_Icc.mp hj ] ) |> lt_trans ( n_seq_v4_pos p _ ( by aesop ) )

/-
If $p^k$ divides $a$ and $k > v_p(b)$, then $v_p(a+b) = v_p(b)$.
-/
theorem padicValNat_add_eq_of_dvd (p : ℕ) (hp : p.Prime) (a b : ℤ) (hb : b ≠ 0) (k : ℕ)
    (ha : (p : ℤ) ^ k ∣ a) (hk : k > padicValNat p (Int.natAbs b)) :
    padicValNat p (Int.natAbs (a + b)) = padicValNat p (Int.natAbs b) := by
      have h_val : padicValNat p (Int.natAbs (a + b)) = padicValNat p (Int.natAbs b) := by
        have h_div : (p : ℤ) ^ padicValNat p (Int.natAbs b) ∣ (a + b) := by
          refine dvd_add ( dvd_trans ( pow_dvd_pow _ hk.le ) ha ) ?_;
          have h_div : (p : ℕ) ^ (padicValNat p (Int.natAbs b)) ∣ Int.natAbs b := by
            exact pow_padicValNat_dvd;
          simpa [ ← Int.natCast_dvd_natCast ] using h_div.modEq_zero_nat.dvd
        have h_not_div : ¬((p : ℤ) ^ (padicValNat p (Int.natAbs b) + 1) ∣ (a + b)) := by
          have h_not_div : ¬((p : ℤ) ^ (padicValNat p (Int.natAbs b) + 1) ∣ b) := by
            rw [ ← Int.natAbs_dvd_natAbs, Int.natAbs_pow ] ; intro H; have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 H; simp_all +decide [ Nat.factorization ] ;
            replace := this p ; simp_all +decide [ Nat.primeFactors_pow ] ;
          exact fun h => h_not_div <| by simpa using dvd_sub h ( dvd_trans ( pow_dvd_pow _ hk ) ha ) ;
        have h_val : padicValNat p (Int.natAbs (a + b)) = Nat.factorization (Int.natAbs (a + b)) p := by
          rw [ Nat.factorization_def ] ; aesop;
        have h_val : Nat.factorization (Int.natAbs (a + b)) p = padicValNat p (Int.natAbs b) := by
          have h_val : (p : ℕ) ^ padicValNat p (Int.natAbs b) ∣ Int.natAbs (a + b) ∧ ¬(p : ℕ) ^ (padicValNat p (Int.natAbs b) + 1) ∣ Int.natAbs (a + b) := by
            exact ⟨ by simpa [ ← Int.natCast_dvd_natCast ] using h_div, by simpa [ ← Int.natCast_dvd_natCast ] using h_not_div ⟩;
          exact le_antisymm ( Nat.le_of_not_lt fun h => h_val.2 <| Nat.dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _ ) ( Nat.le_of_not_lt fun h => by exact absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) h_val.1 ) <| Nat.pow_succ_factorization_not_dvd ( by aesop ) <| by aesop );
        convert h_val using 1;
      exact h_val

/-
The valuation of $X_n$ is equal to the valuation of $T3$.
-/
theorem X_n_valuation_eq_T3_valuation (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (h_sigma : (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    e p s (X_int p.r n) = e p s (T3 p j n) := by
      field_simp;
      have h_val : let s := sigma p (n_seq_v4 p j)
        let k := k_exp p s j
        (p_i p s : ℤ) ^ (e p s (L n) - k + 1) ∣ S1 p j n + S2 p j n + S4 p j n := by
          convert sum_S1_S2_S4_divisible p j hj n hn h_sigma using 1
      generalize_proofs at *; (
      have h_val_T3 : let s := sigma p (n_seq_v4 p j)
        let k := k_exp p s j
        e p s (T3 p j n) ≤ e p s (L n) - k := by
          convert T3_valuation_le p j hj n hn using 1
      generalize_proofs at *; (
      have h_val_T3 : let s := sigma p (n_seq_v4 p j)
        let k := k_exp p s j
        padicValNat (p_i p s) (Int.natAbs (S1 p j n + S2 p j n + S4 p j n + T3 p j n)) = padicValNat (p_i p s) (Int.natAbs (T3 p j n)) := by
          apply padicValNat_add_eq_of_dvd
          focus
            generalize_proofs at *
            exact p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) |> fun h => by simpa using h;
          focus
            exact T3_ne_zero p j hj n hn
          all_goals generalize_proofs at *;
          focus
            exact h_val
          generalize_proofs at *; (
          exact Nat.lt_succ_of_le h_val_T3)
      generalize_proofs at *; (
      convert h_val_T3 using 1
      generalize_proofs at *; (
      convert rfl using 2 ; rw [ X_int_decomp p j hj n hn ] ; ring_nf!;
      unfold e; aesop;))))

/-
For all $n \in I_j$, $p_{\sigma(j)}^{e_{\sigma(j)}(X_n)} \le n$.
-/
theorem pfree (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m)) (n : ℕ) (hn : n ∈ I_set_v4 p j)
    (h_sigma : (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j) :
    let s := sigma p (n_seq_v4 p j)
    (p_i p s) ^ (e p s (X_int p.r n)) ≤ n := by
      convert Nat.le_div_iff_mul_le ( pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ) ) ( k_exp p ( sigma p ( n_seq_v4 p j ) ) j ) ) |>.2 _ using 1;
      rotate_left;
      focus
        exact n * p_i p ( sigma p ( n_seq_v4 p j ) ) ^ k_exp p ( sigma p ( n_seq_v4 p j ) ) j;
      · have h_val : e p (sigma p (n_seq_v4 p j)) (X_int p.r n) ≤ e p (sigma p (n_seq_v4 p j)) (L n) - k_exp p (sigma p (n_seq_v4 p j)) j := by
          convert T3_valuation_le p j hj n hn using 1;
          exact X_n_valuation_eq_T3_valuation p j hj n hn h_sigma;
        have h_val : p_i p (sigma p (n_seq_v4 p j)) ^ (e p (sigma p (n_seq_v4 p j)) (L n)) ≤ n := by
          apply valuation_lcm_le;
          · -- Since $n$ is in the interval $I_set_v4 p j$, and $I_set_v4 p j$ is a subset of $I_set_v4 p (j-1)$, which is a subset of $I_set_v4 p 0$, and $I_set_v4 p 0$ starts at $n_seq_v4 p 1$, which is positive, $n$ must be at least $1$.
            have h_n_pos : 1 ≤ n := by
              have h_n_in_I0 : n ∈ I_set_v4 p 0 := by
                have h_n_in_I0 : ∀ j ∈ Finset.Icc 1 (z p.m), I_set_v4 p j ⊆ I_set_v4 p 0 := by
                  intros j hj
                  have h_subset : ∀ k ∈ Finset.Icc 1 j, I_set_v4 p k ⊆ I_set_v4 p (k - 1) := by
                    intros k hk;
                    apply decreasing_intervals_v4 p k (Finset.mem_Icc.mpr ⟨by linarith [Finset.mem_Icc.mp hk], by linarith [Finset.mem_Icc.mp hk, Finset.mem_Icc.mp hj]⟩);
                  have h_subset : ∀ k ∈ Finset.Icc 1 j, I_set_v4 p k ⊆ I_set_v4 p 0 := by
                    intro k hk
                    induction k with
                    | zero => norm_num at hk
                    | succ k ih =>
                      exact Set.Subset.trans ( h_subset _ hk ) ( if h : 1 ≤ k then ih ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ) else by aesop );
                  exact h_subset j ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hj |>.1, le_rfl ⟩ );
                exact h_n_in_I0 j hj hn
              have h_n_pos : n ∈ Finset.Ico (n_seq_v4 p 1) (n_seq_v4 p 1 + p.m ^ (2 * z p.m - 1)) := by
                exact I0_eq_Ico_v4 p ▸ h_n_in_I0;
              exact le_trans ( Nat.succ_le_of_lt ( n_seq_v4_1_pos p ) ) ( Finset.mem_Ico.mp h_n_pos |>.1 );
            exact h_n_pos;
          · exact p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) );
        gcongr;
        refine le_trans ?_ h_val;
        refine pow_le_pow_right₀ ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ) ) ?_;
        exact le_trans ‹_› ( Nat.sub_le _ _ );
      · rw [ Nat.mul_div_cancel _ ( pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p j ) ) ( sigma_in_range p ( n_seq_v4 p j ) ) ) ) _ ) ]

/-
If $d(n) > n^z$, then there exists a prime power factor of $d(n)$ greater than $n$.
-/
theorem exists_prime_power_gt_of_d_gt (p : ProblemParameters) (n : ℕ) (h : d p n > n ^ (z p.m)) :
    ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n := by
      by_contra h_contra; push Not at h_contra; (
      exact h.not_ge ( le_trans ( Finset.prod_le_prod' fun i hi => h_contra i hi ) ( by norm_num ) ))

/-
If $d(n) < |X_n|$, then $X_n$ has a prime divisor $\ge m$.
-/
theorem exists_large_prime_of_d_lt_X (p : ProblemParameters) (n : ℕ) (h : d p n < Int.natAbs (X_int p.r n)) :
    ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
      -- Since $d(n) < X_n$, let $k = X_n / d(n)$. Then $k > 1$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 < k ∧ (X_int p.r n).natAbs = d p n * k := by
        -- Apply the lemma that states if $a \mid b$ and $a < b$, then there exists a $k > 1$ such that $b = a * k$.
        have h_div : d p n ∣ Int.natAbs (X_int p.r n) := by
          exact d_dvd_X_int p n;
        exact Exists.elim h_div fun k hk => ⟨ k, by nlinarith [ show 0 < d p n from Nat.pos_of_dvd_of_pos h_div ( pos_of_gt h ) ], hk ⟩;
      -- Let $q$ be a prime factor of $k$. Then $q \mid X$.
      obtain ⟨q, hq_prime, hq_div_k⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ k := by
        exact Nat.exists_prime_and_dvd hk.1.ne'
      generalize_proofs at *; (
      -- We claim $q \ge m$.
      by_contra hq_lt_m
      have hq_lt_m' : q < p.m := by
        exact lt_of_not_ge fun h => hq_lt_m ⟨ q, hq_prime, h, hk.2.symm ▸ dvd_mul_of_dvd_right hq_div_k _ ⟩
      generalize_proofs at *; (
      -- Since $q < m$, we have $v_q(X) = v_q(d(n)) + v_q(k)$.
      have hq_val : padicValNat q (Int.natAbs (X_int p.r n)) = padicValNat q (d p n) + padicValNat q k := by
        haveI := Fact.mk hq_prime; rw [ hk.2, padicValNat.mul ] <;> aesop;
      generalize_proofs at *; (
      -- Since $q < m$, we have $v_q(d(n)) = v_q(X)$ by definition of $d$.
      have hq_val_d : padicValNat q (d p n) = padicValNat q (Int.natAbs (X_int p.r n)) := by
        convert valuation_d_eq_valuation_X_int p n q hq_lt_m' hq_prime using 1
      generalize_proofs at *; (
      linarith [ show padicValNat q k > 0 from Nat.pos_of_ne_zero ( by aesop ) ]))))

/-
For $n \in I_0$, $|X_{int}(n)| > n^z$.
-/
theorem X_abs_gt_pow (p : ProblemParameters) (n : ℕ) (hn : n ∈ I0 p) : Int.natAbs (X_int p.r n) > n ^ (z p.m) := by
  -- Since $X_n = X_{int}(n)$ and $|X_n| > n^z$, it follows that $|X_{int}(n)| > n^z$.
  have h_abs : Int.natAbs (X_int p.r n) = Int.natAbs (X p.r n : ℚ).num := by
    rw [ show X p.r n = ( X_int p.r n : ℚ ) by exact X_eq_X_int p.r n ];
    norm_cast;
  convert I0_prop p n hn |> lt_of_lt_of_le <| ?_ using 1;
  focus
    convert Int.ofNat_lt.symm;
  rotate_left;
  focus
    exact ( X p.r n |> Rat.num |> Int.natAbs |> Nat.cast );
  · rw [ Rat.abs_def ];
    rw [ Rat.divInt_eq_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ Rat.den_nz ];
    · exact le_mul_of_one_le_right ( abs_nonneg _ ) ( mod_cast Nat.one_le_iff_ne_zero.mpr ( Rat.den_nz _ ) );
    · exact Rat.pos _;
  · norm_num [ h_abs ];
    norm_cast

/-
If $d(n) \le n^z$ for $n \in I_0$, then $X_n$ has a prime divisor $\ge m$.
-/
theorem d_le_pow_implies_exists_large_prime (p : ProblemParameters) (n : ℕ) (hn : n ∈ I0 p) (hd : d p n ≤ n ^ (z p.m)) :
    ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
      apply exists_large_prime_of_d_lt_X p n (by
      exact lt_of_le_of_lt hd ( X_abs_gt_pow p n hn ) |> lt_of_lt_of_le <| by norm_num;)

/-
If $d(n) > n^z$, then $p_{\sigma(n)}^{e_{\sigma(n)}(X_n)} > n$.
-/
theorem sigma_prop_of_d_gt (p : ProblemParameters) (n : ℕ) (h : d p n > n ^ (z p.m)) :
    (p_i p (sigma p n)) ^ (e p (sigma p n) (X_int p.r n)) > n := by
      -- By definition of `sigma`, we know that `(p_i p (sigma p n)) ^ (e p (sigma p n) (X_int p.r n)) > n` because `sigma` is defined as the smallest index `i` such that `(p_i p i) ^ (e p i (X_int p.r n)) > n`.
      have h_sigma_def : ∃ i ∈ Finset.Icc 1 (z p.m), (p_i p i) ^ (e p i (X_int p.r n)) > n := by
        exact exists_prime_power_gt_of_d_gt p n h
      generalize_proofs at *; (
      exact sigma_prop p n h_sigma_def)

/-
If $d(n_j) > n_j^z$ for all $j \in \{1, \dots, z\}$, then $\sigma(n_j)$ are distinct.
-/
theorem sigma_distinct (p : ProblemParameters)
    (h_d_gt : ∀ j ∈ Finset.Icc 1 (z p.m), d p (n_seq_v4 p j) > (n_seq_v4 p j) ^ (z p.m)) :
    ∀ i j, i ∈ Finset.Icc 1 (z p.m) → j ∈ Finset.Icc 1 (z p.m) → i < j →
    sigma p (n_seq_v4 p i) ≠ sigma p (n_seq_v4 p j) := by
      intro i j hi hj hij h_sigma_eq
      have h_nj_in_Ii : n_seq_v4 p j ∈ I_set_v4 p i := by
        have h_nj_in_Ii : ∀ k, i + 1 ≤ k → k ≤ j → n_seq_v4 p k ∈ I_set_v4 p i := by
          intros k hk₁ hk₂
          have h_nk_in_Ii : ∀ l, i + 1 ≤ l → l ≤ k → n_seq_v4 p l ∈ I_set_v4 p (l - 1) := by
            intros l hl₁ hl₂
            have h_nk_in_Ii : n_seq_v4 p l ∈ I_j_v4 p (l - 1) := by
              rcases l with ( _ | _ | l ) <;> simp_all +decide [ I_j_v4 ];
              exact pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p ( l + 1 ) ) ) ( sigma_in_range p ( n_seq_v4 p ( l + 1 ) ) ) ) ) _
            generalize_proofs at *; (
            rcases l with ( _ | _ | l ) <;> simp_all +decide [ Finset.mem_Icc ] ; tauto)
          generalize_proofs at *; (
          have h_nk_in_Ii : ∀ l, i + 1 ≤ l → l ≤ k → n_seq_v4 p l ∈ I_set_v4 p i := by
            intros l hl₁ hl₂
            have h_nk_in_Ii : n_seq_v4 p l ∈ I_set_v4 p (l - 1) := h_nk_in_Ii l hl₁ hl₂
            have h_nk_in_Ii : ∀ m, i ≤ m → m < l → I_set_v4 p m ⊇ I_set_v4 p (m + 1) := by
              intros m hm₁ hm₂
              have h_nk_in_Ii : I_set_v4 p (m + 1) ⊆ I_set_v4 p m := by
                apply decreasing_intervals_v4
                generalize_proofs at *; (
                exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hj ] ⟩)
              generalize_proofs at *; exact h_nk_in_Ii
            generalize_proofs at *; (
            have h_nk_in_Ii : ∀ m, i ≤ m → m < l → I_set_v4 p i ⊇ I_set_v4 p m := by
              intros m hm₁ hm₂
              induction hm₁ with
              | refl =>
                generalize_proofs at *; (
                exact Set.Subset.refl _)
              | @step m hm ih =>
              exact Set.Subset.trans ( h_nk_in_Ii m hm ( Nat.lt_of_succ_lt hm₂ ) ) ( ih ( Nat.lt_of_succ_lt hm₂ ) )
            generalize_proofs at *; (
            grind))
          generalize_proofs at *; (
          exact h_nk_in_Ii k hk₁ le_rfl))
        generalize_proofs at *; (
        exact h_nj_in_Ii j hij le_rfl)
      have h_pfree : (p_i p (sigma p (n_seq_v4 p i))) ^ (e p (sigma p (n_seq_v4 p i)) (X_int p.r (n_seq_v4 p j))) ≤ n_seq_v4 p j := by
        apply pfree p i hi (n_seq_v4 p j) h_nj_in_Ii;
        convert sigma_prop_of_d_gt p ( n_seq_v4 p i ) ( h_d_gt i hi ) using 1
      have h_sigma_prop : (p_i p (sigma p (n_seq_v4 p i))) ^ (e p (sigma p (n_seq_v4 p i)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j := by
        have h_sigma_prop : (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p j))) > n_seq_v4 p j := by
          convert sigma_prop_of_d_gt p ( n_seq_v4 p j ) ( h_d_gt j hj ) using 1
        generalize_proofs at *; (
        grind)
      linarith [h_pfree, h_sigma_prop]

/-
There exists an index $j \in \{1, \dots, z+1\}$ such that $d(n_j) \le n_j^z$.
-/
theorem exists_n_le_pow (p : ProblemParameters) :
    ∃ j ∈ Finset.Icc 1 (z p.m + 1), d p (n_seq_v4 p j) ≤ (n_seq_v4 p j) ^ (z p.m) := by
      -- Assume that for all $j \in \{1, \dots, z+1\}$, $d(n_j) > n_j^z$.
      by_contra h_contra
      have h_distinct : ∀ i j, i ∈ Finset.Icc 1 (z p.m) → j ∈ Finset.Icc 1 (z p.m) → i < j → sigma p (n_seq_v4 p i) ≠ sigma p (n_seq_v4 p j) := by
        apply sigma_distinct;
        exact fun j hj => not_le.mp fun h => h_contra ⟨ j, Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hj |>.1, Nat.le_succ_of_le ( Finset.mem_Icc.mp hj |>.2 ) ⟩, h ⟩;
      -- By `pfree`, for each $j \in \{1, \dots, z\}$, $p_{\sigma(n_j)}^{e_{\sigma(n_j)}(X_{n_{z+1}})} \le n_{z+1}$.
      have h_pfree : ∀ j ∈ Finset.Icc 1 (z p.m), (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p (z p.m + 1)))) ≤ n_seq_v4 p (z p.m + 1) := by
        intros j hj
        have h_nz1_in_Ij : n_seq_v4 p (z p.m + 1) ∈ I_set_v4 p j := by
          -- By definition of $I_set_v4$, we know that $n_{z+1} \in I_j$ for all $j \in \{1, \dots, z\}$.
          have h_nz1_in_Ij : ∀ j ∈ Finset.Icc 1 (z p.m), n_seq_v4 p (z p.m + 1) ∈ I_set_v4 p j := by
            intros j hj
            have h_nz1_in_Ij : n_seq_v4 p (z p.m + 1) ∈ I_set_v4 p (z p.m) := by
              -- By definition of $I_j_v4$, we know that $n_{z+1} \in I_j_v4 p (z p.m)$.
              simp [I_set_v4, I_j_v4];
              rw [ if_neg ] <;> norm_num
              focus
                generalize_proofs at *
                exact pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p ( z p.m ) ) ) ( sigma_in_range p ( n_seq_v4 p ( z p.m ) ) ) ) ) _;
              exact Nat.ne_of_gt ( Finset.mem_Icc.mp hj |>.2.trans_lt' ( Finset.mem_Icc.mp hj |>.1 ) )
            generalize_proofs at *; (
            have h_decreasing : ∀ j k, j ∈ Finset.Icc 1 (z p.m) → k ∈ Finset.Icc 1 (z p.m) → j ≤ k → I_set_v4 p k ⊆ I_set_v4 p j := by
              intros j k hj hk hjk
              induction hjk with
              | refl =>
                generalize_proofs at *; (
                exact Set.Subset.rfl)
              | @step k hk ih =>
              exact Finset.Subset.trans ( decreasing_intervals_v4 p _ hk ) ( ih <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hj, Nat.succ_le_succ ‹j.le k› ], by linarith [ Finset.mem_Icc.mp hj, Finset.mem_Icc.mp hk ] ⟩ )
            generalize_proofs at *; (
            exact h_decreasing _ _ hj ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hj ], by linarith [ Finset.mem_Icc.mp hj ] ⟩ ) ( by linarith [ Finset.mem_Icc.mp hj ] ) h_nz1_in_Ij |> fun h => by simpa using h;));
          exact h_nz1_in_Ij j hj;
        apply pfree p j hj (n_seq_v4 p (z p.m + 1)) h_nz1_in_Ij;
        have h_sigma_prop : d p (n_seq_v4 p j) > (n_seq_v4 p j) ^ (z p.m) := by
          exact not_le.mp fun h => h_contra ⟨ j, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hj ], by linarith [ Finset.mem_Icc.mp hj ] ⟩, h ⟩;
        apply sigma_prop_of_d_gt p (n_seq_v4 p j) h_sigma_prop;
      -- Since $\sigma(n_j)$ runs through all indices $1 \dots z$, the product of these prime powers is exactly $d(n_{z+1})$.
      have h_prod : ∏ j ∈ Finset.Icc 1 (z p.m), (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p (z p.m + 1)))) = d p (n_seq_v4 p (z p.m + 1)) := by
        have h_prod : Finset.image (fun j => sigma p (n_seq_v4 p j)) (Finset.Icc 1 (z p.m)) = Finset.Icc 1 (z p.m) := by
          refine Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun j hj => ?_ ) ?_;
          · exact sigma_in_range p _;
          · rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( le_of_not_gt fun hi' => h_distinct _ _ hj hi hi' hij.symm ) ( le_of_not_gt fun hj' => h_distinct _ _ hi hj hj' hij ) ];
        have h_prod : ∏ j ∈ Finset.Icc 1 (z p.m), (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p (z p.m + 1)))) = ∏ s ∈ Finset.Icc 1 (z p.m), (p_i p s) ^ (e p s (X_int p.r (n_seq_v4 p (z p.m + 1)))) := by
          conv_rhs => rw [ ← h_prod, Finset.prod_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
        convert h_prod using 1;
      have h_prod_le : ∏ j ∈ Finset.Icc 1 (z p.m), (p_i p (sigma p (n_seq_v4 p j))) ^ (e p (sigma p (n_seq_v4 p j)) (X_int p.r (n_seq_v4 p (z p.m + 1)))) ≤ (n_seq_v4 p (z p.m + 1)) ^ (z p.m) := by
        exact le_trans ( Finset.prod_le_prod' h_pfree ) ( by norm_num );
      exact h_contra ⟨ z p.m + 1, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( sigma_in_range p ( n_seq_v4 p ( z p.m + 1 ) ) ) ], by linarith [ Finset.mem_Icc.mp ( sigma_in_range p ( n_seq_v4 p ( z p.m + 1 ) ) ) ] ⟩, by linarith ⟩

/-
For all $j \in \{1, \dots, z+1\}$, $n_j \in I_0$.
-/
theorem n_seq_mem_I0 (p : ProblemParameters) (j : ℕ) (hj : j ∈ Finset.Icc 1 (z p.m + 1)) :
    n_seq_v4 p j ∈ I0 p := by
      have h_subset : ∀ k ∈ Finset.Icc 1 (z p.m), n_seq_v4 p (k + 1) ∈ I_set_v4 p k := by
        intro k hk
        have h_subset : n_seq_v4 p (k + 1) ∈ I_j_v4 p k := by
          exact Finset.left_mem_Ico.mpr ( Nat.lt_add_of_pos_right ( pow_pos ( Nat.Prime.pos ( p_i_prime p ( sigma p ( n_seq_v4 p k ) ) ( by
            exact sigma_in_range p (n_seq_v4 p k) ) ) ) _ ) );
        unfold I_set_v4; aesop;
      -- By induction on $j$, we can show that $n_seq_v4 p j \in I0 p$ for all $j \in \{1, \dots, z+1\}$.
      induction j with
      | zero => norm_num at hj
      | succ j ih =>
        by_cases hj' : j = 0;
        · have h_min : n_seq_v4 p 1 ∈ I0 p := by
            have h_nonempty : (I0 p).Nonempty := by
              exact I0_nonempty p
            have h_min : n_seq_v4 p 1 = (I0 p).min' h_nonempty := by
              have h_def : n_seq_v4 p 1 = if h : (I0 p).Nonempty then (I0 p).min' h else 0 := by
                rfl
              aesop;
            exact h_min.symm ▸ Finset.min'_mem _ h_nonempty;
          aesop;
        · have h_subset : n_seq_v4 p (j + 1) ∈ I_set_v4 p j := by
            exact h_subset j ( Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero hj', Nat.le_of_lt_succ ( Finset.mem_Icc.mp hj |>.2 ) ⟩ )
          have h_subset_I0 : I_set_v4 p j ⊆ I0 p := by
            have h_subset_I0 : ∀ k ∈ Finset.Icc 1 (z p.m), I_set_v4 p k ⊆ I_set_v4 p (k - 1) := by
              exact fun k a => decreasing_intervals_v4 p k a;
            have h_subset_I0 : ∀ k ∈ Finset.Icc 1 (z p.m), I_set_v4 p k ⊆ I0 p := by
              intro k hk
              induction k with
              | zero => norm_num at hk
              | succ k ih =>
                exact Set.Subset.trans ( h_subset_I0 _ hk ) ( if h : 1 ≤ k then ih ( Finset.mem_Icc.mpr ⟨ h, by linarith [ Finset.mem_Icc.mp hk ] ⟩ ) else by aesop );
            exact h_subset_I0 j ( Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero hj', Nat.le_of_lt_succ ( Finset.mem_Icc.mp hj |>.2 ) ⟩ )
          exact h_subset_I0 h_subset

/-
All integers in the interval $I_0$ are positive.
-/
lemma I0_pos (p : ProblemParameters) : ∀ n ∈ I0 p, n > 0 := by
  -- Since $p.tilde_m > 20 * p.m^(2 * z p.m)$ and $p.m \geq 4$, we have $p.tilde_m > p.m^(2 * z p.m - 1)$.
  have h_tilde_m_gt : p.tilde_m > p.m^(2 * z p.m - 1) := by
    -- Since $p.tilde_m \geq 280$ and $p.m \geq 4$, we have $p.m^{2z p.m} \leq p.m^{2z p.m}$.
    have h_m_ge_4 : 4 ≤ p.m := by
      exact p.hm4
    generalize_proofs at *; (
    have h_m_ge_4 : p.tilde_m > 20 * p.m^(2 * z p.m) := by
      exact p.htilde_m
    generalize_proofs at *; (
    exact lt_of_le_of_lt ( Nat.pow_le_pow_right ( by linarith ) ( Nat.sub_le _ _ ) ) ( lt_of_le_of_lt ( by nlinarith [ pow_pos ( by linarith : 0 < p.m ) ( 2 * z p.m ) ] ) h_m_ge_4 )))
  generalize_proofs at *; (
  -- Since $p.tilde_m > p.m^{2z-1}$ and $p.tilde_m > 20p.m^{2z}$, the lower bound of $J1' p$ is positive.
  have h_J1'_pos : ∀ n ∈ J1' p, 0 < n := by
    exact fun n hn => lt_of_lt_of_le ( Nat.sub_pos_of_lt ( by linarith ) ) ( Finset.mem_Ico.mp hn |>.1 ) ;
  generalize_proofs at *; (
  -- Since $p.tilde_m > 20 * p.m^(2 * z p.m)$ and $p.m \geq 4$, we have $p.tilde_m > p.m^(2 * z p.m - 1)$, thus the lower bound of $J2' p$ is positive.
  have h_J2'_pos : ∀ n ∈ J2' p, 0 < n := by
    -- Since $p.tilde_m > 20 * p.m^(2 * z p.m)$ and $p.m \geq 4$, we have $p.tilde_m > 0$.
    have h_tilde_m_pos : 0 < p.tilde_m := by
      grind
    generalize_proofs at *; (
    exact fun n hn => lt_of_lt_of_le h_tilde_m_pos ( Finset.mem_Ico.mp hn |>.1 ) |> lt_of_lt_of_le <| Nat.le_refl _;)
  generalize_proofs at *; (
  unfold I0; aesop;)))

/-
If a sequence $r$ is periodic with positive period $t$, then it is bounded.
-/
lemma periodic_bounded (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t) :
    ∃ M, ∀ i, |r i| ≤ M := by
      -- By Lemma~\ref{lem:max_periodic}, a periodic function with a positive period is bounded.
      have h_bounded : BddAbove (Set.range fun i => abs (r i)) := by
        -- Since $r$ is periodic with period $t$, the values of $r$ are determined by the values on $0, \dots, t-1$. The set of values is finite, so it is bounded.
        have h_finite : Set.Finite (Set.range (fun i => r (i % t))) := by
          exact Set.Finite.subset ( Set.toFinite ( Finset.image ( fun i => r i ) ( Finset.range t ) ) ) ( Set.range_subset_iff.mpr fun i => Finset.mem_image.mpr ⟨ i % t, Finset.mem_range.mpr ( Nat.mod_lt _ ht ), rfl ⟩ );
        -- Since $r$ is periodic with period $t$, we have $r i = r (i % t)$ for all $i$.
        have h_eq : ∀ i, r i = r (i % t) := by
          exact fun i => by rw [ ← Nat.mod_add_div i t, Function.Periodic.map_mod_nat h_per ] ;
        exact ⟨ ∑ x ∈ h_finite.toFinset, |x|, Set.forall_mem_range.mpr fun i => by simpa [ h_eq ] using Finset.single_le_sum ( fun x _ => abs_nonneg x ) ( h_finite.mem_toFinset.mpr <| Set.mem_range_self i ) ⟩;
      exact ⟨ h_bounded.choose, fun i => h_bounded.choose_spec ⟨ i, rfl ⟩ ⟩

/-
For any positive integer $t$, $p^{\varphi(t)}$ divides $L(n p^{\varphi(t)})$.
-/
lemma pow_totient_dvd_Lb (n : ℕ) (p : ℕ) (t : ℕ) (hp : p.Prime) (_ht : t > 0) (hn : n ≥ 1) :
    p ^ (Nat.totient t) ∣ L (n * p ^ (Nat.totient t)) := by
      -- By definition of $L$, we know that $p^{\varphi(t)}$ is one of the numbers in the range $1$ to $n \cdot p^{\varphi(t)}$.
      have h_p_phi_t_range : p ^ Nat.totient t ∈ Finset.Icc 1 (n * p ^ Nat.totient t) := by
        exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, Nat.le_mul_of_pos_left _ hn ⟩;
      exact Finset.dvd_lcm h_p_phi_t_range

/-
If $r$ is periodic with period $t$ and $a \equiv b \pmod t$, then $r(a) = r(b)$.
-/
lemma periodic_mod_eq {r : ℕ → ℤ} {t : ℕ} (h : Function.Periodic r t) (a b : ℕ) (hab : a ≡ b [MOD t]) :
    r a = r b := by
      -- By definition of periodicity, we have $r(a) = r(b)$ if $a \equiv b \pmod{t}$.
      have h_periodic : ∀ a b, a ≡ b [MOD t] → r a = r b := by
        intro a b hab
        have h_periodic : ∀ k : ℕ, r (a + k * t) = r a := by
          exact fun k => Nat.recOn k ( by norm_num ) fun k ih => by rw [ Nat.succ_mul, ← add_assoc, h, ih ] ;
        rw [ ← Nat.mod_add_div a t, ← Nat.mod_add_div b t, hab ];
        induction a / t generalizing b with
        | zero =>
          simp_all +decide;
          exact Nat.recOn ( b / t ) rfl fun n hn => by rw [ Nat.mul_succ, ← add_assoc, h, hn ] ;
        | succ k hk =>
          simp_all +decide [ Nat.mul_succ, ← add_assoc ];
      exact h_periodic a b hab

/-
If $r$ is periodic with period $t$ and $b = n p^{\varphi(t)}$, then $p \mid X_n$ implies $p \mid X_b$.
-/
lemma X_b_congruence (r : ℕ → ℤ) (t : ℕ) (n : ℕ) (p : ℕ)
    (ht : t > 0) (hp : p.Prime) (hp_gt_t : p > t) (hn_pos : n > 0) (hn_lt_p : n < p)
    (h_per : Function.Periodic r t)
    (h_div : p ∣ Int.natAbs (X_int r n)) :
    let b := n * p ^ Nat.totient t
    p ∣ Int.natAbs (X_int r b) := by
      -- Thus, modulo $p$, the sum restricts to these terms:
      have h_sum_restrict : (X_int r (n * p ^ (Nat.totient t))) ≡ (∑ j ∈ Finset.Icc 1 n, r (j * p ^ (Nat.totient t)) * ((L (n * p ^ (Nat.totient t))) / (j * p ^ (Nat.totient t)) : ℤ)) [ZMOD p] := by
        have h_sum_restrict : (X_int r (n * p ^ (Nat.totient t))) ≡ (∑ i ∈ Finset.filter (fun i => i % p ^ (Nat.totient t) = 0) (Finset.Icc 1 (n * p ^ (Nat.totient t))), r i * ((L (n * p ^ (Nat.totient t))) / i : ℤ)) [ZMOD p] := by
          have h_sum_restrict : (∑ i ∈ Finset.Icc 1 (n * p ^ (Nat.totient t)), r i * ((L (n * p ^ (Nat.totient t))) / i : ℤ)) ≡ (∑ i ∈ Finset.filter (fun i => i % p ^ (Nat.totient t) = 0) (Finset.Icc 1 (n * p ^ (Nat.totient t))), r i * ((L (n * p ^ (Nat.totient t))) / i : ℤ)) [ZMOD p] := by
            -- For each $i$ not divisible by $p^{\varphi(t)}$, the term $r_i \frac{L_b}{i}$ is divisible by $p$.
            have h_not_div : ∀ i ∈ Finset.Icc 1 (n * p ^ (Nat.totient t)), ¬(p ^ (Nat.totient t) ∣ i) → (p : ℤ) ∣ r i * ((L (n * p ^ (Nat.totient t))) / i : ℤ) := by
              intros i hi h_not_div
              have h_div_term : (p : ℤ) ∣ (L (n * p ^ (Nat.totient t))) / i := by
                have h_div_term : (p : ℤ) ^ (Nat.totient t) ∣ (L (n * p ^ (Nat.totient t))) := by
                  exact_mod_cast pow_totient_dvd_Lb n p t hp ht hn_pos |> dvd_trans <| by aesop;
                generalize_proofs at *; (
                norm_cast at *; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp ] ;
                refine fun h => h_not_div <| Nat.Coprime.dvd_of_dvd_mul_left
                  (m := L (n * p ^ (Nat.totient t)) / i) ?_ ?_;
                focus
                  convert Nat.Coprime.pow_left _ h using 1
                generalize_proofs at *; (
                rw [ Nat.div_mul_cancel ]
                focus
                  aesop
                generalize_proofs at *; (
                exact Nat.dvd_trans ( Nat.dvd_of_mod_eq_zero <| Nat.mod_eq_zero_of_dvd <| by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ))))
              generalize_proofs at *; (
              exact dvd_mul_of_dvd_right h_div_term _);
            rw [ ← Finset.sum_filter_add_sum_filter_not ( Finset.Icc 1 ( n * p ^ φ t ) ) fun i => i % p ^ φ t = 0 ];
            norm_num [ Int.modEq_iff_dvd ];
            exact Finset.dvd_sum fun x hx => h_not_div x ( Finset.mem_filter.mp hx |>.1 ) ( by simpa [ Nat.dvd_iff_mod_eq_zero ] using Finset.mem_filter.mp hx |>.2 );
          convert h_sum_restrict using 1;
        have h_filter : Finset.filter (fun i => i % p ^ (Nat.totient t) = 0) (Finset.Icc 1 (n * p ^ (Nat.totient t))) = Finset.image (fun j => j * p ^ (Nat.totient t)) (Finset.Icc 1 n) := by
          ext i; simp [Finset.mem_image];
          exact ⟨ fun hi => ⟨ i / p ^ φ t, ⟨ Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.dvd_of_mod_eq_zero hi.2 ) ) ( pow_pos hp.pos _ ), Nat.div_le_of_le_mul <| by linarith ⟩, Nat.div_mul_cancel <| Nat.dvd_of_mod_eq_zero hi.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ pow_pos hp.pos ( φ t ) ], by nlinarith [ pow_pos hp.pos ( φ t ) ] ⟩, by norm_num ⟩ ⟩;
        simp_all +decide [ Int.ModEq ];
        rw [ Finset.sum_image ] <;> norm_num [ hp.ne_zero ];
      -- Since $p$ is prime and $t$ is positive, $\gcd(p, t) = 1$. By Euler's theorem, $p^{\varphi(t)} \equiv 1 \pmod t$.
      have h_euler : p ^ (Nat.totient t) ≡ 1 [MOD t] := by
        exact Nat.ModEq.pow_totient <| Nat.coprime_iff_gcd_eq_one.mpr <| hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ht hp_gt_t;
      -- Since $r$ is periodic with period $t$, $r_{j p^{\varphi(t)}} = r_j$.
      have h_periodic : ∀ j ∈ Finset.Icc 1 n, r (j * p ^ (Nat.totient t)) = r j := by
        -- Since $j * p^{\varphi(t)} \equiv j \pmod{t}$ and $r$ is periodic with period $t$, we have $r(j * p^{\varphi(t)}) = r(j)$.
        intros j hj
        have h_cong : j * p ^ (Nat.totient t) ≡ j [MOD t] := by
          simpa using h_euler.mul_left j;
        exact periodic_mod_eq h_per (j * p ^ φ t) j h_cong;
      -- We can factor out $\frac{L_b}{L_n p^{\varphi(t)}}$. Note that $L_n$ is not divisible by $p$ since $n < p$.
      have h_factor : (∑ j ∈ Finset.Icc 1 n, r j * ((L (n * p ^ (Nat.totient t))) / (j * p ^ (Nat.totient t)) : ℤ)) = ((L (n * p ^ (Nat.totient t))) / (L n * p ^ (Nat.totient t)) : ℤ) * (∑ j ∈ Finset.Icc 1 n, r j * ((L n) / j : ℤ)) := by
        have h_factor : ∀ j ∈ Finset.Icc 1 n, ((L (n * p ^ (Nat.totient t))) / (j * p ^ (Nat.totient t)) : ℤ) = ((L (n * p ^ (Nat.totient t))) / (L n * p ^ (Nat.totient t)) : ℤ) * ((L n) / j : ℤ) := by
          intro j hj
          have h_div : (L (n * p ^ (Nat.totient t))) = (L n) * (p ^ (Nat.totient t)) * ((L (n * p ^ (Nat.totient t))) / ((L n) * (p ^ (Nat.totient t)))) := by
            rw [ Nat.mul_div_cancel' ];
            refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_;
            · refine Nat.Coprime.pow_right ?_ ?_;
              refine Nat.Coprime.symm ( hp.coprime_iff_not_dvd.mpr ?_ );
              -- Since $p$ is prime and $n < p$, $p$ cannot divide any number in the range $1$ to $n$, hence $p$ cannot divide $L(n)$.
              have h_not_div : ∀ k ∈ Finset.Icc 1 n, ¬(p ∣ k) := by
                exact fun k hk => Nat.not_dvd_of_pos_of_lt ( Finset.mem_Icc.mp hk |>.1 ) ( lt_of_le_of_lt ( Finset.mem_Icc.mp hk |>.2 ) hn_lt_p );
              have h_not_div_L : ∀ {S : Finset ℕ}, (∀ k ∈ S, ¬(p ∣ k)) → ¬(p ∣ Finset.lcm S id) := by
                intros S hS; induction S using Finset.induction <;> simp_all +decide ;
                · exact hp.ne_one;
                · exact fun h => hS.1 <| hp.dvd_mul.mp ( dvd_trans h <| Nat.lcm_dvd_mul _ _ ) |> Or.resolve_right <| by aesop;
              exact h_not_div_L h_not_div;
            · exact Finset.lcm_dvd fun i hi => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by nlinarith [ Finset.mem_Icc.mp hi, pow_pos hp.pos ( φ t ) ], by nlinarith [ Finset.mem_Icc.mp hi, pow_pos hp.pos ( φ t ) ] ⟩ );
            · exact pow_totient_dvd_Lb n p t hp ht hn_pos;
          rw [ Int.ediv_eq_of_eq_mul_left ];
          · exact mul_ne_zero ( Nat.cast_ne_zero.mpr ( by linarith [ Finset.mem_Icc.mp hj ] ) ) ( pow_ne_zero _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) );
          · norm_cast at *;
            rw [ mul_assoc, ← mul_assoc ( L n / j ), Nat.div_mul_cancel ];
            · grind;
            · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hj ], by linarith [ Finset.mem_Icc.mp hj ] ⟩ );
        rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ h_factor x hx ] ; ring;
      simp_all +decide [ ← Int.natCast_dvd_natCast, Int.ModEq ];
      exact Int.dvd_of_emod_eq_zero ( h_sum_restrict.trans ( Int.emod_eq_zero_of_dvd <| dvd_mul_of_dvd_right ( by simpa [ X_int ] using h_div ) _ ) )

/-
If $r$ is periodic with period $t$, $p \mid X_n$ and $p > t$, then there exists $b$ such that $p \mid \gcd(X_b, L_b)$.
-/
lemma exists_b_gcd_ge_p (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t)
    (n : ℕ) (hn : n ≥ 1) (p : ℕ) (hp : p.Prime) (hp_gt_t : p > t) (h_div : p ∣ Int.natAbs (X_int r n)) :
    ∃ b, p ∣ Nat.gcd (Int.natAbs (X_int r b)) (L b) := by
      by_cases hn_lt_p : n < p;
      · -- Let $b = n p^{\varphi(t)}$.
        use n * p ^ Nat.totient t;
        refine Nat.dvd_gcd ?_ ?_;
        · convert X_b_congruence r t n p ht hp hp_gt_t hn hn_lt_p h_per h_div using 1;
        · have h_pow_totient_dvd_Lb : p ^ (Nat.totient t) ∣ L (n * p ^ (Nat.totient t)) := by
            apply pow_totient_dvd_Lb n p t hp ht hn;
          exact dvd_trans ( dvd_pow_self _ ( by linarith [ Nat.totient_pos.mpr ht ] ) ) h_pow_totient_dvd_Lb;
      · refine ⟨ n, Nat.dvd_gcd h_div ?_ ⟩;
        exact Nat.dvd_trans ( by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ : p ∈ Finset.Icc 1 n ) )

/-
There exists an integer $n \in I_0$ for which $X_n$ is divisible by a prime larger than or equal to $m$. (note: this does not assume periodicity)
-/
theorem ohyeah1 (p : ProblemParameters) :
    ∃ n ∈ I0 p, ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
      -- By `exists_n_le_pow`, there exists $j \in \{1, \dots, z+1\}$ such that $d(n_j) \le n_j^z$.
      obtain ⟨j, hj₁, hj₂⟩ : ∃ j ∈ Finset.Icc 1 (z p.m + 1), d p (n_seq_v4 p j) ≤ (n_seq_v4 p j) ^ (z p.m) := by
        exact exists_n_le_pow p;
      exact ⟨ n_seq_v4 p j, n_seq_mem_I0 p j hj₁, by have := d_le_pow_implies_exists_large_prime p ( n_seq_v4 p j ) ( n_seq_mem_I0 p j hj₁ ) hj₂; tauto ⟩

/-
If the sequence of numerators r is periodic, then limsup gcd(X_b, L_b) = infinity.
-/
theorem generalErdos291 (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t)
    (h_r_nz : ∀ i, r i ≠ 0)
    (h_priemteller : ∀ m : ℕ, m ≥ 4 → (m : ℝ)^(2 * z m) < Real.exp (2.52 * m))
    (h_bla0 : ∀ n : ℕ, n ≥ 100 → L n > 2^n) :
    ∀ N, ∃ b, Nat.gcd (Int.natAbs (X_int r b)) (L b) > N := by
      intro N;
      -- By Lemma `periodic_bounded`, there exists a bound $M$ such that $|r_i| \le M$.
      obtain ⟨M, hM⟩ : ∃ M, ∀ i, |r i| ≤ M := by
        apply periodic_bounded r t ht h_per;
      -- Let $m \ge 4$ be any integer larger than $\max(M, t, N)$.
      obtain ⟨m, hm⟩ : ∃ m, 4 ≤ m ∧ M < m ∧ t < m ∧ N < m := by
        exact ⟨ ⌊M⌋₊ + t + N + 4, by linarith [ Nat.lt_floor_add_one M ], by linarith [ Nat.lt_floor_add_one M ], by linarith, by linarith ⟩;
      -- By `exists_good_p`, there exists a `ProblemParameters` structure $p$ with $p.m = m$ and $p.r = r$.
      obtain ⟨p, hp⟩ : ∃ p : ProblemParameters, p.r = r ∧ p.m = m.natAbs := by
        apply exists_good_p;
        · grind;
        · assumption;
        · grind;
        · grind;
        · assumption;
      -- By `ohyeah1`, there exists an $n \in I_0$ such that $X_n$ is divisible by a prime $q$ with $q \ge m$.
      obtain ⟨n, hn⟩ : ∃ n ∈ I0 p, ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
        convert ohyeah1 p;
      -- We then claim that $b = n q^{\varphi(t)}$ works.
      obtain ⟨b, hb⟩ : ∃ b, hn.right.choose ∣ Nat.gcd (Int.natAbs (X_int r b)) (L b) := by
        apply exists_b_gcd_ge_p r t ht h_per n (by
        exact Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( I0_pos p 0 ( by simpa using hn.1 ) ) ( by norm_num ) )) hn.right.choose hn.right.choose_spec.left (by
        linarith [ hn.2.choose_spec.2.1, abs_of_nonneg ( by linarith : 0 ≤ m ) ]) (by
        simpa only [ hp.1 ] using hn.2.choose_spec.2.2);
      use b;
      refine lt_of_lt_of_le ?_ ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_right _ <| Nat.pos_of_ne_zero <| ?_ ) hb );
      · linarith [ hn.2.choose_spec.2.1, abs_of_nonneg ( by linarith : 0 ≤ m ) ];
      · exact ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;

#print axioms ohyeah1
-- 'Erdos291b.ohyeah1' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms generalErdos291
-- 'Erdos291b.generalErdos291' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos291b
