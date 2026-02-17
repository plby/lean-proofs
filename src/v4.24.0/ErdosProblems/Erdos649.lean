/-

This is a Lean formalization of a solution to Erdős Problem 649.
https://www.erdosproblems.com/649


The results from the link above were auto-formalized by ChatGPT (from
OpenAI) and Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized and proved the following results regarding the greatest prime factor function P(n):
1. The conjecture that for any primes p, q there exists n such that P(n)=p and P(n+1)=q is false. Specifically, we proved `conjecture_false` for p=2, q=7.
2. We proved `tong_counterexamples` showing that for any prime p, there are infinitely many primes q such that the conjecture fails.
3. We formalized Tong's question about the existence of infinitely many p for a given q as `tong_question`.
4. We proved `sampaio_counterexample` showing there is no n with P(n)=19 and P(n+1)=2.
-/

/-
5. Solution to RMM 2020 Problem 6:

We formalize the proof that there exist infinitely many strange pairs of primes.
We define a strange pair $\{p, q\}$ as a pair of distinct primes such that no $n \ge 2$ satisfies $P(n)P(n+1) = pq$.
We prove that if $2 < q_1 < q_2$ are primes with $\text{ord}_{q_1}(2) = \text{ord}_{q_2}(2)$, then $\{2, q_1\}$ is a strange pair.
We then show that for any prime $p > 5$, $N = 2^{2p} + 1$ has at least two prime factors $q_1, q_2 > 5$, both satisfying $\text{ord}_{q}(2) = 4p$.
This allows us to construct infinitely many strange pairs of the form $\{2, q\}$.
-/

import Mathlib


namespace Erdos368

/-
For an integer m >= 1 define P^+(m) by P^+(1)=1, and for m >= 2 let P^+(m) be the largest prime divisor of m.
-/
def P_plus (m : ℕ) : ℕ :=
  match (Nat.primeFactorsList m).maximum with
  | some p => p
  | none => 1

def is_d_number (d : ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ∣ d

/-
Define integers delta_i and even integers beta_i >= 0 by the cases given in the lemma. Check that alpha_i = delta_i + beta_i.
-/
def split_exponent (α : ℕ) : ℕ × ℕ :=
  if α = 0 then (0, 0)
  else if α % 2 = 1 then (1, α - 1)
  else if α = 2 then (2, 0)
  else (2, α - 2)

/-
Define d and b as in the lemma. Then M = d * b^2.
-/
def calc_d (M : ℕ) : ℕ :=
  M.factorization.support.prod (fun p => p ^ (split_exponent (M.factorization p)).1)

def calc_b (M : ℕ) : ℕ :=
  M.factorization.support.prod (fun p => p ^ ((split_exponent (M.factorization p)).2 / 2))

theorem M_eq_d_b_sq (M : ℕ) (hM : M > 0) : M = calc_d M * (calc_b M)^2 := by
  unfold calc_d calc_b;
  conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hM.ne' ];
  simp +decide only [Finsupp.prod, ← Finset.prod_pow];
  rw [ ← Finset.prod_mul_distrib ] ; refine' Finset.prod_congr rfl fun p hp => _ ; rcases Nat.even_or_odd' ( M.factorization p ) with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ pow_add, pow_mul ] ;
  · unfold split_exponent
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ ]
    norm_num [ Nat.mul_succ, pow_succ', pow_mul ]
    ring
  · unfold split_exponent
    simp +decide
    ring

/-
b is a d-number.
-/
theorem b_is_d_number (M : ℕ) : is_d_number (calc_d M) (calc_b M) := by
  constructor;
  · exact Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) _;
  · intro p pp dp; contrapose! dp; simp_all +decide [ calc_d, calc_b ] ;
    simp_all +decide [ Nat.Prime.dvd_iff_not_coprime pp, Nat.coprime_prod_right_iff ];
    intro x hx hx' hx''; specialize dp x hx hx' hx''; rcases k : ( split_exponent ( Nat.factorization M x ) ).1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.coprime_pow_right_iff ] ;
    · unfold split_exponent at *; aesop;
    · exact Nat.Coprime.pow_right _ dp;
    · exact dp.pow_right _

/-
As M varies over all S-numbers, d can assume at most 3^r distinct values.
-/
def possible_ds (S : Finset ℕ) : Finset ℕ :=
  (Finset.pi S (fun _ => {0, 1, 2})).image (fun f => S.attach.prod (fun ⟨p, hp⟩ => p ^ (f p hp)))

/-
For n >= 1 define integers a_n, b_n by (a_1 + b_1 sqrt(d))^n = a_n + b_n sqrt(d). Then (a_n, b_n) is a solution.
-/
def pell_seq (d : ℤ) (sol : Pell.Solution₁ d) (n : ℕ) : Pell.Solution₁ d :=
  sol ^ n

set_option maxHeartbeats 1000000 in
/-
Every solution (x,y) in N^2 of x^2 - dy^2 = 1 equals (a_n, b_n) for a unique n >= 1.
-/
theorem pell_solutions_structure (d : ℤ) (hd : d > 1)
    (fund : Pell.Solution₁ d) (h_fund : Pell.IsFundamental fund)
    (sol : Pell.Solution₁ d) (h_sol_pos : sol.x > 0 ∧ sol.y > 0) :
    ∃! n : ℕ, n ≥ 1 ∧ sol = pell_seq d fund n := by
      -- By definition of Pell solutions, there exists some $n \geq 1$ such that $sol = pell_seq d fund n$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, n ≥ 1 ∧ sol = pell_seq d fund n := by
        -- By definition of the fundamental solution, every solution can be written as fund^n for some n.
        have h_sol_form : ∃ n : ℕ, sol = fund ^ n := by
          have := @Pell.IsFundamental.eq_pow_of_nonneg;
          exact this h_fund h_sol_pos.1 h_sol_pos.2.le;
        obtain ⟨ n, rfl ⟩ := h_sol_form; use n; cases n <;> aesop;
      refine' ⟨ n, hn, fun m hm => _ ⟩;
      -- By definition of $pell_seq$, we know that $fund^m = fund^n$ implies $m = n$.
      have h_exp : fund ^ m = fund ^ n := by
        aesop;
      have h_exp : ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → fund ^ m = fund ^ n → m = n := by
        intros m n hm hn h_exp
        have h_exp : (fund.x + fund.y * Real.sqrt d) ^ m = (fund.x + fund.y * Real.sqrt d) ^ n := by
          convert congr_arg ( fun x : Pell.Solution₁ d => x.x + x.y * Real.sqrt d ) h_exp using 1;
          · refine' Nat.recOn m _ _ <;> simp_all +decide [ pow_succ' ];
            intro n hn; ring_nf; norm_num [ show d ≥ 0 by positivity ] ; ring;
          · refine' Nat.recOn n _ _ <;> simp_all +decide [ pow_succ' ];
            intro n hn; ring_nf; norm_num [ show d ≥ 0 by positivity ] ; ring;
        have h_exp : (fund.x + fund.y * Real.sqrt d) > 1 := by
          have := h_fund.1;
          exact lt_add_of_lt_of_nonneg ( mod_cast this ) ( mul_nonneg ( Int.cast_nonneg.mpr ( by linarith [ h_fund.2.1 ] ) ) ( Real.sqrt_nonneg _ ) );
        rw [ pow_right_inj₀ ] at * <;> linarith;
      exact h_exp m n hm.1 hn.1 ‹_›

/-
If m divides n then b_m divides b_n.
-/
theorem pell_y_divisibility (d : ℤ) (fund : Pell.Solution₁ d) (m n : ℕ) (h : m ∣ n) :
    (pell_seq d fund m).y ∣ (pell_seq d fund n).y := by
      -- Let's express the sequence in terms of the fundamental solution.
      obtain ⟨k, rfl⟩ : ∃ k, n = m * k := h;
      induction' k with k ih;
      · unfold pell_seq; aesop;
      · unfold pell_seq at *;
        simp +decide [ pow_add, pow_mul ];
        exact dvd_mul_of_dvd_left ( by simpa [ pow_mul ] using ih ) _

/-
gcd(a_1, d) = 1.
-/
theorem pell_fund_x_coprime_d (d : ℤ) (fund : Pell.Solution₁ d) :
    Int.gcd fund.x d = 1 := by
      -- Since $(fund.x)^2 - d*(fund.y)^2 = 1$, any common divisor of $fund.x$ and $d$ must also divide $d*(fund.y)^2$, and thus 1.
      have h_div : ∀ p : ℕ, Nat.Prime p → p ∣ Int.natAbs (fund.x) → p ∣ Int.natAbs d → False := by
        intros p pp dp dd; have := congr_arg ( ·.natAbs : ℤ → ℕ ) fund.prop; norm_num [ Int.natAbs_mul, Int.natAbs_pow ] at this; simp_all +decide [ ← Int.natCast_dvd_natCast, sq ] ;
        exact absurd ( this ▸ Int.natAbs_dvd_natAbs.mpr ( dvd_sub ( dvd_mul_of_dvd_left dp _ ) ( dvd_mul_of_dvd_left dd _ ) ) ) ( by norm_cast; aesop );
      exact Nat.coprime_of_dvd <| by aesop;

/-
(a_1, b_1) is the first term of the sequence, and b_1 divides b_p.
-/
theorem pell_seq_1_eq_fund (d : ℤ) (fund : Pell.Solution₁ d) :
    pell_seq d fund 1 = fund := by
      -- By definition of pell_seq, we have pell_seq d fund 1 = fund^1.
      simp [pell_seq]

theorem pell_c_p_is_int (d : ℤ) (fund : Pell.Solution₁ d) (p : ℕ) :
    fund.y ∣ (pell_seq d fund p).y := by
      convert pell_y_divisibility d fund 1 p _;
      · -- By definition of pell_seq, we have pell_seq d fund 1 = fund^1 = fund.
        simp [pell_seq];
      · norm_num

/-
c_p = b_p / b_1 is a d-number.
-/
def c_p (d : ℤ) (fund : Pell.Solution₁ d) (p : ℕ) : ℕ :=
  (pell_seq d fund p).y.natAbs / fund.y.natAbs

theorem c_p_is_d_number (d : ℤ) (fund : Pell.Solution₁ d) (p : ℕ)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat) :
    is_d_number (d.toNat) (c_p d fund p) := by
      unfold is_d_number at *;
      unfold c_p;
      have h_div : fund.y.natAbs ∣ (pell_seq d fund p).y.natAbs := by
        convert pell_c_p_is_int d fund p using 1;
        norm_num [ ← Int.natCast_dvd_natCast ];
      rw [ gt_iff_lt, Nat.div_pos_iff ];
      refine' ⟨ ⟨ _, Nat.le_of_dvd _ h_div ⟩, _ ⟩;
      · contrapose! h_d_num; aesop;
      · grind;
      · intro q hq hq';
        refine' h_d_num.2 q hq _;
        convert hq'.trans ( Nat.div_dvd_of_dvd h_div ) using 1;
        grind

/-
The imaginary part of (a + b*sqrt(d))^n is the sum of binom(n, 2k+1) * a^(n-(2k+1)) * b^(2k+1) * d^k.
-/
def binomial_sum_y (n : ℕ) (a b d : ℤ) : ℤ :=
  Finset.sum (Finset.range ((n+1)/2)) (fun k => (Nat.choose n (2*k+1) : ℤ) * a^(n-(2*k+1)) * b^(2*k+1) * d^k)

set_option maxHeartbeats 1000000 in
theorem Zsqrtd_pow_im {d : ℤ} (z : Zsqrtd d) (n : ℕ) :
    (z ^ n).im = binomial_sum_y n z.re z.im d := by
      -- By definition of $z^n$, we have $(z^n).im = \sum_{k=0}^{n/2} \binom{n}{2k+1} a^{n-(2k+1)} b^{2k+1} d^k$.
      have h_im_def : ∀ n : ℕ, (z^n).im = ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k + 1) * z.re ^ (n - (2 * k + 1)) * z.im ^ (2 * k + 1) * d ^ k := by
        intro n
        have h_sum_y : (z ^ n).im = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * z.re ^ (n - k) * (z.im ^ k * (if k % 2 = 1 then d ^ (k / 2) else 0)) := by
          -- By definition of exponentiation, we know that $(a + b\sqrt{d})^n = \sum_{k=0}^{n} \binom{n}{k} a^{n-k} (b\sqrt{d})^k$.
          have h_expansion : ∀ n : ℕ, (z ^ n) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * z.re ^ (n - k) * (z.im * (⟨0, 1⟩ : ℤ√d)) ^ k := by
            intro n
            have h_sum_y : (z ^ n) = ((z.re : ℤ√d) + (z.im : ℤ√d) * ⟨0, 1⟩) ^ n := by
              congr ; ext <;> simp +decide
            exact h_sum_y.trans ( by rw [ add_comm, add_pow ] ; ac_rfl );
          -- By definition of exponentiation, we know that $(b\sqrt{d})^k = b^k d^{k/2}$ if $k$ is even, and $b^k d^{(k-1)/2} \sqrt{d}$ if $k$ is odd.
          have h_expansion_parts : ∀ k : ℕ, (z.im * (⟨0, 1⟩ : ℤ√d)) ^ k = ⟨z.im ^ k * (if k % 2 = 0 then d ^ (k / 2) else 0), z.im ^ k * (if k % 2 = 1 then d ^ (k / 2) else 0)⟩ := by
            intro k; induction k <;> simp_all +decide [ pow_succ, mul_assoc ] ;
            · rfl;
            · cases Nat.mod_two_eq_zero_or_one ‹_› <;> simp_all +decide [ Nat.add_mod, Nat.add_div ] ; ring_nf;
              · ext <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
              · ext <;> simp +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
          simp_all +decide [ mul_assoc, mul_left_comm ];
          induction ( Finset.range ( n + 1 ) ) using Finset.induction <;> simp_all +decide [ mul_left_comm ];
          cases Nat.mod_two_eq_zero_or_one ‹_› <;> simp +decide [ * ];
          · exact Or.inr <| Or.inl <| by induction n - ‹_› <;> simp_all +decide [ pow_succ' ] ;
          · exact Or.inl <| Or.inl <| by induction n - ‹_› <;> simp_all +decide [ pow_succ' ] ;
        -- Split the sum into two parts: one for even $k$ and one for odd $k$.
        have h_split : Finset.sum (Finset.range (n + 1)) (fun k => Nat.choose n k * z.re ^ (n - k) * (if k % 2 = 1 then z.im ^ k * d ^ (k / 2) else 0)) = Finset.sum (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))) (fun k => Nat.choose n k * z.re ^ (n - k) * z.im ^ k * d ^ (k / 2)) := by
          simp +decide [ Finset.sum_ite, mul_assoc ];
        -- Notice that Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1)) is equivalent to Finset.image (fun k => 2 * k + 1) (Finset.range ((n + 1) / 2)).
        have h_filter : Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1)) = Finset.image (fun k => 2 * k + 1) (Finset.range ((n + 1) / 2)) := by
          ext ( _ | k ) <;> simp +arith +decide [ Nat.add_mod ];
          exact ⟨ fun h => ⟨ k / 2, by omega, by omega ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ by omega, by omega ⟩ ⟩;
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        norm_num [ Nat.add_div ];
        cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ * ];
        simp +decide [ Finset.sum_range_succ ];
        exact Or.inr <| Or.inr <| Or.inr <| Nat.choose_eq_zero_of_lt <| by linarith [ Nat.mod_add_div n 2, Nat.sub_add_cancel <| show n / 2 * 2 ≤ n from Nat.div_mul_le_self n 2 ] ;
      convert h_im_def n using 1;
      unfold binomial_sum_y; ring_nf;
      rw [ Nat.add_comm, Nat.add_div ] <;> norm_num [ mul_comm ];
      split_ifs <;> simp_all +decide [ add_comm, mul_assoc, mul_comm, mul_left_comm ];
      rw [ add_comm, Finset.sum_range_succ ] ; norm_num;
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Nat.choose_eq_zero_of_lt <| by omega;

/-
b_n is equal to b_1 times the sum expansion.
-/
def pell_y_div_y_sum (n : ℕ) (a b d : ℤ) : ℤ :=
  Finset.sum (Finset.range ((n+1)/2)) (fun k => (Nat.choose n (2*k+1) : ℤ) * a^(n-(2*k+1)) * b^(2*k) * d^k)

theorem pell_y_eq_y_mul_div_sum (d : ℤ) (fund : Pell.Solution₁ d) (n : ℕ) :
    (pell_seq d fund n).y = fund.y * pell_y_div_y_sum n fund.x fund.y d := by
      unfold pell_y_div_y_sum;
      convert Zsqrtd_pow_im ( fund : Zsqrtd d ) n using 1;
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; ring!;

/-
The sum is congruent to n * a^(n-1) modulo any divisor of d.
-/
theorem pell_y_div_y_sum_congruence (n : ℕ) (a b d : ℤ) (q : ℤ) (hq : q ∣ d) (hn : n ≥ 1) :
    pell_y_div_y_sum n a b d ≡ n * a ^ (n - 1) [ZMOD q] := by
      unfold pell_y_div_y_sum;
      rw [ Finset.sum_eq_sum_diff_singleton_add ( Finset.mem_range.mpr <| Nat.div_pos ( by linarith ) zero_lt_two ) ];
      norm_num [ Int.modEq_iff_dvd ];
      exact Finset.dvd_sum fun x hx => dvd_mul_of_dvd_right ( dvd_pow hq ( by aesop ) ) _

/-
c_p is the absolute value of the sum S_p.
-/
theorem c_p_eq_abs_sum (d : ℤ) (fund : Pell.Solution₁ d) (p : ℕ) (h_fund_y : fund.y ≠ 0) :
    c_p d fund p = Int.natAbs (pell_y_div_y_sum p fund.x fund.y d) := by
      unfold c_p;
      rw [ pell_y_eq_y_mul_div_sum ];
      rw [ Int.natAbs_mul, Nat.mul_div_cancel_left _ ( Int.natAbs_pos.mpr h_fund_y ) ]

/-
If a prime q divides p * a^k and is coprime to a, then q = p.
-/
theorem prime_dvd_of_dvd_mul_pow_coprime {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q ∣ p * a ^ k) (h_coprime : Nat.gcd a q = 1) : q = p := by
      simp_all +decide [ Nat.Prime.dvd_mul, Nat.coprime_comm ];
      exact h.resolve_right ( mt ( hq.dvd_of_dvd_pow ) ( fun h => by have := Nat.dvd_gcd ( dvd_refl q ) h; aesop ) ) |> fun h => by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto;

/-
If q is a prime divisor of c_p, then q divides d.toNat.
-/
theorem q_dvd_d_nat_of_dvd_c_p (d : ℤ) (fund : Pell.Solution₁ d) (p : ℕ)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat)
    (q : ℕ) (hq : q.Prime) (hq_dvd : q ∣ c_p d fund p) :
    q ∣ d.toNat := by
      -- By definition of $c_p$ being a $d$-number, every prime factor of $c_p$ must divide $d.toNat$.
      have h_prime_divides_d : ∀ q : ℕ, Nat.Prime q → q ∣ c_p d fund p → q ∣ d.toNat := by
        intro q hq hq_dvd
        have h_c_p_dvd_d : is_d_number (d.toNat) (c_p d fund p) := by
          apply c_p_is_d_number; assumption;
        exact h_c_p_dvd_d.2 q hq hq_dvd;
      exact h_prime_divides_d q hq hq_dvd

/-
If q divides c_p, then q divides p * a^(p-1).
-/
theorem dvd_p_mul_pow_of_dvd_c_p (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (p : ℕ) (hp : p.Prime)
    (h_fund_y_pos : fund.y > 0)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat)
    (q : ℕ) (hq : q.Prime) (hq_dvd : q ∣ c_p d fund p) :
    (q : ℤ) ∣ p * fund.x ^ (p - 1) := by
      -- Since q divides c_p and c_p is the absolute value of S_p, we have that q divides S_p.
      have hq_div_S_p : (q : ℤ) ∣ pell_y_div_y_sum p fund.x fund.y d := by
        rw [ ← Int.natCast_dvd_natCast ] at *;
        rw [ c_p_eq_abs_sum ] at hq_dvd;
        · simpa using hq_dvd;
        · grind;
      -- Since $q$ divides $d.toNat$ and $d.toNat = d$, we have $q \mid d$.
      have hq_dvd_d : (q : ℤ) ∣ d := by
        have hq_dvd_d : q ∣ d.toNat := by
          exact q_dvd_d_nat_of_dvd_c_p d fund p h_d_num q hq hq_dvd;
        simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg ( zero_le_one.trans hd.le ) ] using hq_dvd_d.modEq_zero_nat.dvd;
      have := pell_y_div_y_sum_congruence p fund.x fund.y d ( q : ℤ ) hq_dvd_d ( Nat.Prime.pos hp );
      exact Int.dvd_of_emod_eq_zero ( this ▸ Int.emod_eq_zero_of_dvd hq_div_S_p )

/-
Every prime divisor of c_p is p.
-/
theorem c_p_prime_factors (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (p : ℕ) (hp : p.Prime)
    (h_fund_y_pos : fund.y > 0)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat)
    (q : ℕ) (hq : q.Prime) (hq_dvd : q ∣ c_p d fund p) :
    q = p := by
      have h_div : q ∣ p * (Int.natAbs fund.x) ^ (p - 1) := by
        have := dvd_p_mul_pow_of_dvd_c_p d hd fund p hp h_fund_y_pos h_d_num q hq hq_dvd; simp_all +decide [ ← Int.natCast_dvd_natCast ] ;
        cases abs_cases fund.x <;> simp +decide [ * ];
        rcases hp.eq_two_or_odd' with rfl | ⟨ m, rfl ⟩ <;> simp_all +decide [ parity_simps ];
      apply prime_dvd_of_dvd_mul_pow_coprime hp hq h_div;
      have h_coprime : Nat.gcd (Int.natAbs fund.x) (Int.natAbs d) = 1 := by
        have := pell_fund_x_coprime_d d fund; aesop;
      refine' Nat.Coprime.coprime_dvd_right _ h_coprime;
      convert q_dvd_d_nat_of_dvd_c_p d fund p h_d_num q hq hq_dvd using 1;
      cases d <;> trivial

/-
The x-coordinate of a solution with positive x and y is at least 2.
-/
theorem pell_fund_x_ge_2 (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_x_pos : fund.x > 0) (h_fund_y_pos : fund.y > 0) :
    fund.x ≥ 2 := by
      nlinarith [ show d * fund.y ^ 2 > 0 by positivity, fund.prop ]

/-
c_p is a power of p.
-/
theorem c_p_eq_pow_p (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (p : ℕ) (hp : p.Prime)
    (h_fund_y_pos : fund.y > 0)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat) :
    ∃ k : ℕ, c_p d fund p = p ^ k := by
      -- Apply the fact that if all prime factors of a number are p, then the number must be a power of p.
      have h_prime_factors : ∀ {n : ℕ}, (∀ q : ℕ, Nat.Prime q → q ∣ n → q = p) → ∃ k : ℕ, n = p ^ k := by
        intros n hn
        have h_factors : n.primeFactors ⊆ {p} := by
          intro q hq; specialize hn q; aesop;
        by_cases hn_zero : n = 0 <;> simp_all +decide [ Finset.subset_singleton_iff ];
        · linarith [ hn 2 Nat.prime_two, hn 3 Nat.prime_three ];
        · exact ⟨ n.factorization p, by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hn_zero ] ; rw [ Finsupp.prod ] ; aesop ⟩;
      exact h_prime_factors fun q hq hq' => c_p_prime_factors d hd fund p hp h_fund_y_pos h_d_num q hq hq' ▸ rfl

/-
The sum defining c_p is congruent to p*a^(p-1) modulo p^2.
-/
theorem pell_y_div_y_sum_congruence_p_square (p : ℕ) (hp : p.Prime) (hp_ge_5 : p ≥ 5)
    (a b d : ℤ) (h_p_dvd_d : (p : ℤ) ∣ d) :
    pell_y_div_y_sum p a b d ≡ p * a ^ (p - 1) [ZMOD p ^ 2] := by
      -- Split the sum into the term when $k=0$ and the sum when $k \geq 1$.
      have h_split_sum : pell_y_div_y_sum p a b d = (Nat.choose p 1 : ℤ) * a^(p-1) * b^0 * d^0 + ∑ k ∈ Finset.Ico 1 ((p+1)/2), (Nat.choose p (2*k+1) : ℤ) * a^(p-(2*k+1)) * b^(2*k) * d^k := by
        rw [ Finset.sum_Ico_eq_sub _ ];
        · unfold pell_y_div_y_sum; norm_num [ Finset.sum_range_succ' ] ;
        · omega;
      -- For $k \ge 1$, the term contains $d^k$. Since $p \mid d$, $p^k \mid d^k$.
      have h_term_div : ∀ k ∈ Finset.Ico 1 ((p+1)/2), (Nat.choose p (2*k+1) : ℤ) * a^(p-(2*k+1)) * b^(2*k) * d^k ≡ 0 [ZMOD p^2] := by
        intro k hk; rw [ Int.modEq_zero_iff_dvd ] ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ, mul_assoc ] ;
        · -- Since $p$ is prime and $p \geq 5$, we know that $p \mid \binom{p}{3}$.
          have h_binom_div : (p : ℤ) ∣ Nat.choose p 3 := by
            norm_cast; exact hp.dvd_choose_self ( by linarith ) ( by linarith ) ;
          generalize_proofs at *; simp_all +decide [ ← mul_assoc ] ;
          exact dvd_trans ( mul_dvd_mul h_binom_div h_p_dvd_d ) ( by exact ⟨ a ^ ( p - 3 ) * b * b, by ring ⟩ ) ;
        · refine' dvd_mul_of_dvd_right _ _;
          refine' dvd_mul_of_dvd_right _ _;
          exact dvd_mul_of_dvd_right ( dvd_mul_of_dvd_right ( by obtain ⟨ q, rfl ⟩ := h_p_dvd_d; exact ⟨ q * q, by ring ⟩ ) _ ) _;
      simpa [ h_split_sum, Int.modEq_iff_dvd ] using Finset.dvd_sum fun x hx => Int.modEq_iff_dvd.mp ( h_term_div x hx )

/-
The prime p cannot be 2.
-/
theorem pell_p_ne_2 (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_y_pos : fund.y > 0)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund 2).y.toNat) :
    False := by
      -- If $c_2 = 2a_1$, then $c_2$ is not a d-number since $a_1$ is odd and $d$ is even.
      have h_c2_not_d_num : ¬ is_d_number (d.toNat) (2 * fund.x).toNat := by
        intro h
        have h_a_odd : Odd fund.x := by
          -- Since $a_1$ and $d$ are coprime and $d$ is even, $a_1$ must be odd.
          have h_a1_odd : Int.gcd fund.x d = 1 := by
            exact pell_fund_x_coprime_d d fund
          have h_d_even : Even d := by
            have := h.2 2 Nat.prime_two
            generalize_proofs at *; (
            grind)
          have h_a1_odd_final : Odd fund.x := by
            exact Int.odd_iff.mpr ( Int.emod_two_ne_zero.mp fun con => by have := Int.dvd_gcd ( Int.dvd_of_emod_eq_zero con ) ( even_iff_two_dvd.mp h_d_even ) ; simp_all +decide ) ;
          exact h_a1_odd_final
        have h_c2_not_d_num : ¬ is_d_number (d.toNat) (2 * fund.x).toNat := by
          intro h
          have h_prime_factor : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (2 * fund.x).toNat ∧ ¬(q ∣ d.toNat) := by
            obtain ⟨q, hq_prime, hq_div⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (2 * fund.x).toNat ∧ q ≠ 2 := by
              obtain ⟨ k, hk ⟩ := h_a_odd;
              rcases k with ⟨ _ | k ⟩ <;> simp_all +decide [ Int.toNat ];
              · have := fund.prop; aesop;
              · exact ⟨ Nat.minFac ( 2 * ( k + 1 ) + 1 ), Nat.minFac_prime ( by linarith ), Nat.dvd_trans ( Nat.minFac_dvd _ ) ( by norm_cast; exact ⟨ 2, by ring ⟩ ), fun h => by have := Nat.minFac_dvd ( 2 * ( k + 1 ) + 1 ) ; simp_all +decide [ Nat.dvd_add_right ] ⟩;
              · cases h;
                tauto;
            have hq_not_div_d : ¬(q ∣ d.toNat) := by
              intro hq_div_d
              have hq_div_a : q ∣ Int.natAbs fund.x := by
                cases fund_x_nonneg : fund.x <;> simp_all +decide [ ← Int.natCast_dvd_natCast ];
                · exact Or.resolve_left ( Int.Prime.dvd_mul' hq_prime hq_div.1 ) ( by norm_cast; intros h; have := Nat.le_of_dvd ( by linarith ) h; interval_cases q <;> simp_all +decide );
                · cases h ; aesop
              have hq_div_a_sq : q ∣ Int.natAbs (fund.x ^ 2 - d * fund.y ^ 2) := by
                rw [ ← Int.natCast_dvd ] at *;
                exact dvd_sub ( hq_div_a.pow two_ne_zero ) ( dvd_mul_of_dvd_left ( by simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg ( zero_le_one.trans hd.le ) ] using hq_div_d ) _ );
              have hq_div_a_sq : q ∣ Int.natAbs 1 := by
                convert hq_div_a_sq using 1;
                rw [ show fund.x ^ 2 - d * fund.y ^ 2 = 1 by linarith [ fund.prop ] ];
              exact hq_prime.not_dvd_one hq_div_a_sq;
            exact ⟨ q, hq_prime, hq_div.1, hq_not_div_d ⟩
          obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := h_prime_factor; have := h.2 q hq₁; simp_all +decide
        exact h_c2_not_d_num h;
      -- By definition of $c_p$, we have $c_2 = \frac{b_2}{b_1}$.
      have h_c2_def : (pell_seq d fund 2).y = 2 * fund.x * fund.y := by
        unfold pell_seq; norm_num [ pow_succ ] ; ring;
      unfold is_d_number at *;
      simp_all +decide [ mul_assoc ];
      obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_c2_not_d_num;
      refine' hp₃ ( h_d_num.2 p hp₁ _ );
      convert hp₂.mul_right ( Int.toNat fund.y ) using 1;
      grind

/-
The prime p cannot be 3.
-/
theorem pell_p_ne_3 (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_y_pos : fund.y > 0)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund 3).y.toNat) :
    False := by
      -- From Lemma 2, we know that $c_3 = 4a_1^2 - 1$.
      have h_c3 : c_p d fund 3 = 4 * fund.x ^ 2 - 1 := by
        unfold c_p pell_seq; norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
        rw [ abs_of_nonneg, abs_of_nonneg, Int.ediv_eq_of_eq_mul_left ] <;> nlinarith [ Pell.Solution₁.prop fund, pow_pos h_fund_y_pos 3 ];
      -- If $c_3$ is a power of $3$, then both factors are powers of $3$ (their gcd divides $2$), and
      -- $(2a_1+1)-(2a_1-1)=2$ forces $\{2a_1-1,2a_1+1\}=\{1,3\}$, hence $a_1=1$, contradicting $a_1\ge 2$. Thus $p\ne 3$.
      have h_contra : ∃ k : ℕ, c_p d fund 3 = 3 ^ k := by
        apply_rules [ c_p_eq_pow_p ] ; aesop ( simp_config := { decide := true } ) ;
      rcases h_contra with ⟨ k, hk ⟩ ; rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
      · nlinarith [ show fund.x > 0 from by nlinarith [ Pell.Solution₁.prop fund ] ];
      · -- Since $a_1$ is a positive integer and $a_1^2 = 1$, we have $a_1 = 1$.
        have h_a1 : fund.x = 1 := by
          nlinarith [ show fund.x > 0 from by nlinarith [ show 0 < fund.x ^ 2 - d * fund.y ^ 2 from by nlinarith [ fund.prop ] ] ];
        have := fund.prop; aesop;
      · -- Since $2 * fund.x - 1$ and $2 * fund.x + 1$ are consecutive odd numbers, they are coprime.
        have h_coprime : Nat.gcd (2 * fund.x - 1).natAbs (2 * fund.x + 1).natAbs = 1 := by
          refine' Nat.coprime_of_dvd' _;
          intro k hk hk₁ hk₂; have := Int.natAbs_dvd_natAbs.mpr ( Int.dvd_sub ( Int.natCast_dvd.mpr hk₂ ) ( Int.natCast_dvd.mpr hk₁ ) ) ; norm_num at this;
          have := Nat.le_of_dvd ( by decide ) this; interval_cases k <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
        -- Since $2 * fund.x - 1$ and $2 * fund.x + 1$ are coprime and their product is $3^{k+2}$, each must be a power of $3$.
        have h_power_of_three : ∃ a b : ℕ, (2 * fund.x - 1).natAbs = 3 ^ a ∧ (2 * fund.x + 1).natAbs = 3 ^ b := by
          have h_power_of_three : (2 * fund.x - 1).natAbs * (2 * fund.x + 1).natAbs = 3 ^ (k + 2) := by
            grind;
          have : ( 2 * fund.x - 1 |> Int.natAbs ) ∣ 3 ^ ( k + 2 ) := h_power_of_three ▸ dvd_mul_right _ _; ( have : ( 2 * fund.x + 1 |> Int.natAbs ) ∣ 3 ^ ( k + 2 ) := h_power_of_three ▸ dvd_mul_left _ _; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at *; aesop; ) );
        rcases h_power_of_three with ⟨ a, b, ha, hb ⟩ ; rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> simp_all +decide [ Nat.pow_succ' ] ;
        · grind;
        · grind;
        · cases abs_cases ( 2 * fund.x + 1 ) <;> linarith [ show fund.x > 0 from by nlinarith [ pow_pos ( show 0 < 3 by decide ) k ] ];
        · norm_num [ Nat.gcd_mul_left ] at h_coprime

/-
The sum defining c_p is strictly greater than its first term.
-/
theorem pell_y_div_y_sum_gt_term_zero (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d)
    (h_fund_x_pos : fund.x > 0) (h_fund_y_pos : fund.y > 0)
    (p : ℕ) (hp_ge_5 : p ≥ 5) :
    pell_y_div_y_sum p fund.x fund.y d > p * fund.x ^ (p - 1) := by
      unfold pell_y_div_y_sum;
      rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr ( by omega : 0 < ( p + 1 ) / 2 ) ) ];
      refine' lt_add_of_le_of_pos _ _ <;> norm_num;
      refine' Finset.sum_pos _ _;
      · exact fun i hi => mul_pos ( mul_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith [ Finset.mem_range.mp ( Finset.mem_sdiff.mp hi |>.1 ), Nat.div_mul_le_self ( p + 1 ) 2 ] ) ) ) ( pow_pos h_fund_x_pos _ ) ) ( pow_pos h_fund_y_pos _ ) ) ( pow_pos ( by linarith ) _ );
      · exact ⟨ 1, by norm_num; omega ⟩

/-
If p^k is congruent to p*u mod p^2 and p does not divide u, then k=1.
-/
theorem pow_p_congruence_contradiction (p : ℕ) (hp : p.Prime) (u : ℤ) (k : ℕ)
    (h_coprime : ¬ (p : ℤ) ∣ u) (h_cong : (p : ℤ) ^ k ≡ p * u [ZMOD p ^ 2]) (hk : k ≥ 1) :
    k = 1 := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Int.ModEq ];
      norm_num [ pow_succ' ] at h_cong ⊢
      have h_div : (p : ℤ) ^ 2 ∣ p * u := by
        norm_num [ sq, Int.mul_emod_mul_of_pos, hp.pos ] at h_cong ⊢ ; aesop;
      have h_div_u : (p : ℤ) ∣ u := by
        exact Int.dvd_of_mul_dvd_mul_left ( Nat.cast_ne_zero.mpr hp.ne_zero ) ( dvd_trans ( by ring_nf; norm_num ) h_div )
      contradiction

/-
c_p is equal to the sum S_p (without absolute value).
-/
theorem c_p_eq_sum (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_x_pos : fund.x > 0) (h_fund_y_pos : fund.y > 0)
    (p : ℕ) :
    (c_p d fund p : ℤ) = pell_y_div_y_sum p fund.x fund.y d := by
      rw [ c_p_eq_abs_sum ];
      · rw [ Int.natAbs_of_nonneg ];
        exact Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg h_fund_x_pos.le _ ) ) ( pow_nonneg h_fund_y_pos.le _ ) ) ( pow_nonneg ( by linarith ) _ );
      · positivity

/-
c_p is equal to p.
-/
theorem c_p_eq_p (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_x_pos : fund.x > 0) (h_fund_y_pos : fund.y > 0)
    (p : ℕ) (hp : p.Prime) (hp_ge_5 : p ≥ 5)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat) :
    c_p d fund p = p := by
      obtain ⟨ k, hk ⟩ := c_p_eq_pow_p d hd fund p hp h_fund_y_pos h_d_num;
      by_cases hk_zero : k = 0 <;> simp_all +decide;
      · have := pell_y_div_y_sum_gt_term_zero d hd fund h_fund_x_pos h_fund_y_pos p hp_ge_5
        -- By `c_p_eq_sum`, $c_p = S_p$ (the sum).
        have h_c_p_eq_sum : (c_p d fund p : ℤ) = pell_y_div_y_sum p fund.x fund.y d := by
          exact c_p_eq_sum d hd fund h_fund_x_pos h_fund_y_pos p
        nlinarith [ pow_pos h_fund_x_pos ( p - 1 ) ];
      · -- Since $p \mid c_p$, we have $p \mid d$.
        have h_p_div_d : (p : ℤ) ∣ d := by
          have h_p_div_d : ∀ q : ℕ, Nat.Prime q → q ∣ c_p d fund p → q ∣ d.toNat := by
            exact fun q a a_1 => q_dvd_d_nat_of_dvd_c_p d fund p h_d_num q a a_1;
          simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg ( zero_le_one.trans hd.le ) ] using h_p_div_d p hp ( hk.symm ▸ dvd_pow_self _ hk_zero );
        -- By `pell_y_div_y_sum_congruence_p_square`, $S_p \equiv p \cdot a_1^{p-1} \pmod{p^2}$.
        have h_cong : (c_p d fund p : ℤ) ≡ p * fund.x ^ (p - 1) [ZMOD p ^ 2] := by
          convert pell_y_div_y_sum_congruence_p_square p hp hp_ge_5 fund.x fund.y d h_p_div_d using 1;
          convert c_p_eq_sum d hd fund h_fund_x_pos h_fund_y_pos p using 1;
        -- Since $\gcd(a_1, d) = 1$ and $p \mid d$, we have $p \nmid a_1$. Thus $p \nmid a_1^{p-1}$.
        have h_not_div_a1 : ¬(p : ℤ) ∣ fund.x := by
          have h_coprime : Int.gcd fund.x d = 1 := by
            exact pell_fund_x_coprime_d d fund;
          exact fun h => hp.not_dvd_one <| h_coprime ▸ Int.natCast_dvd_natCast.mp ( Int.dvd_coe_gcd h h_p_div_d );
        -- Apply `pow_p_congruence_contradiction` with $u = a_1^{p-1}$ to conclude $k=1$.
        have h_k_one : k = 1 := by
          apply pow_p_congruence_contradiction p hp (fund.x ^ (p - 1)) k;
          · exact mt ( Int.Prime.dvd_pow' hp ) h_not_div_a1;
          · aesop;
          · exact Nat.pos_of_ne_zero hk_zero;
        rw [ h_k_one, pow_one ]

/-
If p >= 5 is a prime and c_p is a d-number, we get a contradiction.
-/
theorem pell_p_ge_5_contradiction (d : ℤ) (hd : d > 1) (fund : Pell.Solution₁ d) (h_fund_x_pos : fund.x > 0) (h_fund_y_pos : fund.y > 0)
    (p : ℕ) (hp : p.Prime) (hp_ge_5 : p ≥ 5)
    (h_d_num : is_d_number (d.toNat) (pell_seq d fund p).y.toNat) :
    False := by
      -- By `c_p_eq_p`, $c_p = p$.
      have h_c_p_eq_p : c_p d fund p = p := by
        exact c_p_eq_p d hd fund h_fund_x_pos h_fund_y_pos p hp hp_ge_5 h_d_num
      -- By `c_p_eq_sum`, $c_p = S_p$.
      have h_c_p_eq_sum : (c_p d fund p : ℤ) = pell_y_div_y_sum p fund.x fund.y d := by
        exact c_p_eq_sum d hd fund h_fund_x_pos h_fund_y_pos p
      -- By `pell_y_div_y_sum_gt_term_zero`, $S_p > p a_1^{p-1}$.
      have h_pell_y_div_y_sum_gt_term_zero : pell_y_div_y_sum p fund.x fund.y d > p * fund.x ^ (p - 1) := by
        exact pell_y_div_y_sum_gt_term_zero d hd fund h_fund_x_pos h_fund_y_pos p hp_ge_5
      -- By `pell_fund_x_ge_2`, $a_1 \ge 2$.
      have h_fund_x_ge_2 : fund.x ≥ 2 := by
        exact pell_fund_x_ge_2 d hd fund h_fund_x_pos h_fund_y_pos
      -- Thus $S_p > p \cdot 2^{p-1}$.
      have h_pell_y_div_y_sum_gt_p_two_pow : pell_y_div_y_sum p fund.x fund.y d > p * 2 ^ (p - 1) := by
        exact lt_of_le_of_lt ( by gcongr ) h_pell_y_div_y_sum_gt_term_zero
      -- Since $p \ge 5$, $2^{p-1} \ge 2^4 = 16 > 1$.
      have h_two_pow_ge_16 : 2 ^ (p - 1) > 1 := by
        exact one_lt_pow₀ ( by decide ) ( Nat.sub_ne_zero_of_lt hp.one_lt )
      -- So $S_p > p$.
      have h_pell_y_div_y_sum_gt_p : pell_y_div_y_sum p fund.x fund.y d > p := by
        exact lt_of_le_of_lt ( by nlinarith ) h_pell_y_div_y_sum_gt_p_two_pow
      -- But $S_p = c_p = p$. Contradiction.
      have h_contradiction : pell_y_div_y_sum p fund.x fund.y d = p := by
        exact h_c_p_eq_sum.symm.trans ( mod_cast h_c_p_eq_p )
      linarith [h_pell_y_div_y_sum_gt_p]

/-
Among all solutions (x,y) of Pell equation, at most one has y a d-number. If such a solution exists, it is (a1,b1).
-/
theorem pell_solution_unique_d_number (d : ℤ) (hd : d > 1) (h_nonsquare : ¬ IsSquare d)
    (fund : Pell.Solution₁ d) (h_fund : Pell.IsFundamental fund)
    (h_fund_pos : fund.x > 0 ∧ fund.y > 0)
    (sol : Pell.Solution₁ d) (h_sol_pos : sol.x > 0 ∧ sol.y > 0)
    (h_d_num : is_d_number (d.toNat) sol.y.toNat) :
    sol = fund := by
      have := pell_solutions_structure d hd fund h_fund sol h_sol_pos;
      obtain ⟨n, hn_ge_1, hn_unique⟩ := this.exists
      have hn_eq_1 : n = 1 := by
        -- If $n > 1$, let $p$ be a prime divisor of $n$.
        by_cases hn_gt_1 : n > 1;
        · -- Let $p$ be a prime divisor of $n$.
          obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
            exact Nat.exists_prime_and_dvd hn_gt_1.ne';
          -- Then $b_p \mid b_n$ by \ref{it:pell-div}, so $b_p$ is also a $d$-number.
          have h_b_p_div_b_n : (pell_seq d fund p).y ∣ (pell_seq d fund n).y := by
            exact pell_y_divisibility d fund p n hp_div
          have h_b_p_d_num : is_d_number d.toNat (pell_seq d fund p).y.toNat := by
            have h_b_p_d_num : (pell_seq d fund p).y.toNat ∣ (pell_seq d fund n).y.toNat := by
              convert Int.natAbs_dvd_natAbs.mpr h_b_p_div_b_n using 1;
              · rw [ ← Int.natAbs_of_nonneg ( show 0 ≤ ( pell_seq d fund p |> Pell.Solution₁.y ) from ?_ ) ];
                · norm_cast;
                · have h_b_p_pos : ∀ n : ℕ, n ≥ 1 → 0 ≤ (pell_seq d fund n).y := by
                    intro n hn; induction hn <;> simp_all +decide [ pell_seq ] ;
                    · linarith;
                    · rename_i k hk ih;
                      have h_b_p_pos : ∀ n : ℕ, n ≥ 1 → 0 ≤ (fund ^ n).x ∧ 0 ≤ (fund ^ n).y := by
                        intro n hn; induction hn <;> simp_all +decide [ pow_succ, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul ] ;
                        · exact ⟨ le_of_lt h_fund_pos.1, le_of_lt h_fund_pos.2 ⟩;
                        · constructor <;> nlinarith [ mul_nonneg ( by linarith : 0 ≤ ( fund ^ ‹_› |> Pell.Solution₁.x ) ) ( by linarith : 0 ≤ fund.x ), mul_nonneg ( by linarith : 0 ≤ ( fund ^ ‹_› |> Pell.Solution₁.y ) ) ( by linarith : 0 ≤ fund.y ) ];
                      exact add_nonneg ( mul_nonneg ( h_b_p_pos k hk |>.1 ) h_fund_pos.2.le ) ( mul_nonneg ( h_b_p_pos k hk |>.2 ) h_fund_pos.1.le );
                  exact h_b_p_pos p hp_prime.pos;
              · grind;
            refine' ⟨ _, _ ⟩;
            · refine' Nat.pos_of_dvd_of_pos h_b_p_d_num _;
              grind;
            · intro q hq hq_div
              have hq_div_d : q ∣ sol.y.toNat := by
                exact hn_unique.symm ▸ dvd_trans hq_div h_b_p_d_num;
              exact h_d_num.2 q hq hq_div_d;
          -- If $p = 2$, `pell_p_ne_2` gives a contradiction.
          by_cases hp_eq_2 : p = 2;
          · exact absurd h_b_p_d_num ( by subst hp_eq_2; exact pell_p_ne_2 d hd fund h_fund_pos.2 );
          · -- If $p = 3$, `pell_p_ne_3` gives a contradiction.
            by_cases hp_eq_3 : p = 3;
            · exact absurd h_b_p_d_num ( by subst hp_eq_3; exact pell_p_ne_3 d hd fund h_fund_pos.2 );
            · -- If $p \geq 5$, `pell_p_ge_5_contradiction` gives a contradiction.
              have hp_ge_5 : p ≥ 5 := by
                exact le_of_not_gt fun h => by interval_cases p <;> trivial;
              have := pell_p_ge_5_contradiction d hd fund h_fund_pos.left h_fund_pos.right p hp_prime hp_ge_5 h_b_p_d_num
              aesop;
        · linarith;
      exact hn_unique.trans ( hn_eq_1.symm ▸ pell_seq_1_eq_fund d fund )

/-
The d calculated from (2n+1)^2 - 1 is not a perfect square.
-/
theorem calc_d_not_square (n : ℕ) (hn : n ≥ 1) :
    ¬ IsSquare (calc_d ((2 * n + 1) ^ 2 - 1)) := by
      -- Let $a = 2n+1$. Then $M = a^2 - 1$.
      set a : ℕ := 2 * n + 1
      have hM : (2 * n + 1) ^ 2 - 1 = a ^ 2 - 1 := by
        rfl;
      -- Suppose $d = \text{calc\_d}(M)$ is a square.
      by_contra h_square;
      -- Then $M = d b^2$ implies $M$ is a square.
      have hM_square : IsSquare ((a ^ 2 - 1)) := by
        -- By definition of $d$, we know that $M = d b^2$.
        have hM_eq : (2 * n + 1) ^ 2 - 1 = calc_d ((2 * n + 1) ^ 2 - 1) * (calc_b ((2 * n + 1) ^ 2 - 1)) ^ 2 := by
          exact M_eq_d_b_sq _ ( Nat.sub_pos_of_lt ( by nlinarith ) );
        exact hM ▸ hM_eq.symm ▸ by obtain ⟨ k, hk ⟩ := h_square; exact ⟨ k * calc_b _, by rw [ hk ] ; ring ⟩ ;
      obtain ⟨ k, hk ⟩ := hM_square;
      rw [ Nat.sub_eq_iff_eq_add ] at hk;
      · simp +zetaDelta at *;
        nlinarith [ show k < 2 * n + 1 by nlinarith ];
      · exact Nat.one_le_pow _ _ ( Nat.succ_pos _ )

/-
If P+(n(n+1)) <= B, then the calculated d is in the set of possible d's for primes <= B.
-/
def primes_le_B (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

set_option maxHeartbeats 1000000 in
theorem calc_d_mem_possible_ds (n : ℕ) (B : ℕ) (h : P_plus (n * (n + 1)) ≤ B) (hn : n ≥ 1) :
    calc_d ((2 * n + 1) ^ 2 - 1) ∈ possible_ds (primes_le_B B) := by
      -- By definition of calc_d, we know that calc_d(M) is a product of primes in S raised to some exponent.
      have h_calc_d : ∀ p ∈ (Nat.factorization ((2 * n + 1) ^ 2 - 1)).support, p ∈ primes_le_B B := by
        -- Since $p$ divides $(2n+1)^2 - 1$, it must also divide $4n(n+1)$.
        intro p hp
        have h_div : p ∣ 4 * n * (n + 1) := by
          convert Nat.dvd_of_mem_primeFactors hp using 1 ; rw [ show ( 2 * n + 1 ) ^ 2 - 1 = 4 * n * ( n + 1 ) by exact Nat.sub_eq_of_eq_add <| by ring ];
        -- Since $p$ divides $4n(n+1)$, it must also divide $n(n+1)$ or $4$.
        by_cases h_div_n : p ∣ n * (n + 1);
        · -- Since $p$ divides $n(n+1)$, it must also divide $P^+(n(n+1))$.
          have h_div_P_plus : p ≤ P_plus (n * (n + 1)) := by
            unfold P_plus;
            rcases x : ( n * ( n + 1 ) |> Nat.primeFactorsList |> List.maximum ) with ( _ | _ | p ) <;> simp_all +decide
            · simp_all +decide [ List.maximum ];
              rw [ List.argmax_eq_none ] at x ; aesop;
            · have := List.maximum_mem x; aesop;
            · have := List.argmax_eq_some_iff.mp x; aesop;
          exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( lt_of_le_of_lt h_div_P_plus ( lt_of_le_of_lt h ( Nat.lt_succ_self _ ) ) ), Nat.prime_of_mem_primeFactors hp ⟩;
        · simp_all +decide [ mul_assoc, Nat.Prime.dvd_mul ];
          have := Nat.le_of_dvd ( by decide ) h_div; interval_cases p <;> simp_all +decide;
          omega;
      refine' Finset.mem_image.mpr _;
      refine' ⟨ fun p hp => if p ∈ ( Nat.factorization ( ( 2 * n + 1 ) ^ 2 - 1 ) |> Finsupp.support ) then ( split_exponent ( Nat.factorization ( ( 2 * n + 1 ) ^ 2 - 1 ) p ) |> Prod.fst ) else 0, _, _ ⟩ <;> simp_all +decide [ Finset.prod_ite ];
      · intro p hp; split_ifs <;> simp_all +decide [ split_exponent ] ;
        split_ifs <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
      · refine' Finset.prod_bij ( fun p hp => p ) _ _ _ _ <;> simp_all +decide

/-
The calculated d is greater than 1.
-/
def bad_set (B : ℕ) : Set ℕ := {n | n ≥ 1 ∧ P_plus (n * (n + 1)) ≤ B}

set_option maxHeartbeats 1000000 in
/-
For a fixed d, there is at most one n such that calc_d((2n+1)^2-1) = d.
-/
theorem unique_n_for_d (d : ℕ) (hd : d > 1) (h_nonsquare : ¬ IsSquare d) :
    {n : ℕ | n ≥ 1 ∧ calc_d ((2 * n + 1) ^ 2 - 1) = d}.Subsingleton := by
      intro n hn m hm;
      have h_sol1 : ∃ sol1 : Pell.Solution₁ d, sol1.x = 2 * n + 1 ∧ sol1.y = calc_b ((2 * n + 1) ^ 2 - 1) := by
        have h_sol1 : (2 * n + 1) ^ 2 - d * (calc_b ((2 * n + 1) ^ 2 - 1)) ^ 2 = 1 := by
          rw [ ← hn.2, Nat.sub_eq_of_eq_add ];
          rw [ ← M_eq_d_b_sq ];
          · rw [ add_tsub_cancel_of_le ( Nat.one_le_pow _ _ ( Nat.succ_pos _ ) ) ];
          · exact Nat.sub_pos_of_lt ( by nlinarith only [ hn.1 ] );
        rw [ Nat.sub_eq_iff_eq_add ] at h_sol1;
        · refine' ⟨ ⟨ ⟨ 2 * n + 1, calc_b ( ( 2 * n + 1 ) ^ 2 - 1 ) ⟩, _ ⟩, _, _ ⟩;
          all_goals norm_num [ Pell.Solution₁.x, Pell.Solution₁.y ];
          constructor <;> ext <;> norm_num <;> nlinarith;
        · exact le_of_lt ( Nat.lt_of_sub_eq_succ h_sol1 )
      have h_sol2 : ∃ sol2 : Pell.Solution₁ d, sol2.x = 2 * m + 1 ∧ sol2.y = calc_b ((2 * m + 1) ^ 2 - 1) := by
        have h_sol2 : (2 * m + 1 : ℤ) ^ 2 - d * (calc_b ((2 * m + 1) ^ 2 - 1)) ^ 2 = 1 := by
          have h_sol2 : (2 * m + 1 : ℤ) ^ 2 - d * (calc_b ((2 * m + 1) ^ 2 - 1)) ^ 2 = (2 * m + 1 : ℤ) ^ 2 - (calc_d ((2 * m + 1) ^ 2 - 1)) * (calc_b ((2 * m + 1) ^ 2 - 1)) ^ 2 := by
            aesop;
          convert M_eq_d_b_sq ( ( 2 * m + 1 ) ^ 2 - 1 ) _ using 1;
          · rw [ ← @Nat.cast_inj ℤ ] ; norm_num [ h_sol2 ];
            constructor <;> intro <;> linarith;
          · exact Nat.sub_pos_of_lt ( by nlinarith only [ hm.1 ] );
        refine' ⟨ ⟨ ⟨ 2 * m + 1, calc_b ( ( 2 * m + 1 ) ^ 2 - 1 ) ⟩, _ ⟩, rfl, rfl ⟩;
        rw [ unitary ];
        simp +decide [ mul_comm ];
        ext <;> norm_num ; ring_nf at * ; linarith;
        ring;
      obtain ⟨sol1, hsol1⟩ := h_sol1
      obtain ⟨sol2, hsol2⟩ := h_sol2
      have h_sol1_pos : sol1.x > 0 ∧ sol1.y > 0 := by
        exact ⟨ by linarith [ hn.1 ], by linarith [ show 0 < calc_b ( ( 2 * n + 1 ) ^ 2 - 1 ) from Nat.pos_of_ne_zero fun h => by have := b_is_d_number ( ( 2 * n + 1 ) ^ 2 - 1 ) ; simp_all +decide [ is_d_number ] ] ⟩
      have h_sol2_pos : sol2.x > 0 ∧ sol2.y > 0 := by
        exact ⟨ by linarith, by linarith [ show 0 < calc_b ( ( 2 * m + 1 ) ^ 2 - 1 ) from Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos <| by aesop ) _ ] ⟩
      have h_sol1_d_num : is_d_number d (calc_b ((2 * n + 1) ^ 2 - 1)) := by
        have := b_is_d_number ( ( 2 * n + 1 ) ^ 2 - 1 ) ; aesop;
      have h_sol2_d_num : is_d_number d (calc_b ((2 * m + 1) ^ 2 - 1)) := by
        have := b_is_d_number ( ( 2 * m + 1 ) ^ 2 - 1 ) ; aesop;
      have h_sol1_fund : sol1 = (Classical.choose (show ∃ fund : Pell.Solution₁ d, Pell.IsFundamental fund from by
                                                    exact ⟨ Pell.IsFundamental.exists_of_not_isSquare ( by linarith ) ( mod_cast h_nonsquare ) |> Classical.choose, Pell.IsFundamental.exists_of_not_isSquare ( by linarith ) ( mod_cast h_nonsquare ) |> Classical.choose_spec ⟩)) := by
                                                    all_goals generalize_proofs at *;
                                                    apply pell_solution_unique_d_number
                                                    generalize_proofs at *;
                                                    all_goals norm_cast;
                                                    · exact Classical.choose_spec ‹∃ x : Pell.Solution₁ d, Pell.IsFundamental x›;
                                                    · exact ⟨ by linarith [ Classical.choose_spec ‹∃ x : Pell.Solution₁ d, Pell.IsFundamental x› |>.1 ], by linarith [ Classical.choose_spec ‹∃ x : Pell.Solution₁ d, Pell.IsFundamental x› |>.2 ] ⟩;
                                                    · aesop
      generalize_proofs at *;
      have h_sol2_fund : sol2 = (Classical.choose (show ∃ fund : Pell.Solution₁ d, Pell.IsFundamental fund from by
                                                    assumption)) := by
                                                    apply pell_solution_unique_d_number;
                                                    all_goals norm_cast;
                                                    · exact Classical.choose_spec ‹∃ x : Pell.Solution₁ ( d : ℤ ), Pell.IsFundamental x›;
                                                    · exact h_sol1_fund ▸ h_sol1_pos;
                                                    · aesop
      generalize_proofs at *;
      grind +ring

/-
The set of n such that P+(n(n+1)) <= B is finite.
-/
theorem bad_set_finite (B : ℕ) : (bad_set B).Finite := by
  -- By definition of $D$, we know that for any $n \in \text{bad\_set}(B)$, $\text{calc\_d}((2n+1)^2-1) \in D$.
  have h_mem_D : ∀ n ∈ bad_set B, calc_d ((2 * n + 1) ^ 2 - 1) ∈ possible_ds (primes_le_B B) := by
    exact fun n hn => calc_d_mem_possible_ds n B hn.2 hn.1;
  -- For each $d \in D$, let $A_d = \{n \in \text{bad\_set}(B) \mid \text{calc\_d}((2n+1)^2-1) = d\}$.
  have h_A_d_finite : ∀ d ∈ possible_ds (primes_le_B B), Set.Subsingleton {n | n ≥ 1 ∧ calc_d ((2 * n + 1) ^ 2 - 1) = d} := by
    intro d hd;
    by_cases hd_sq : IsSquare d;
    · intro n hn m hm; have := calc_d_not_square n hn.1; have := calc_d_not_square m hm.1; aesop;
    · exact unique_n_for_d d ( by
        contrapose! hd_sq; interval_cases d <;> simp_all +decide ; ) hd_sq;
  refine Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet ( possible_ds ( primes_le_B B ) ) ) fun d hd => Set.Subsingleton.finite ( h_A_d_finite d hd ) ) ?_;
  exact fun n hn => Set.mem_iUnion₂.mpr ⟨ _, h_mem_D n hn, hn.1, rfl ⟩

/-
The largest prime factor of n(n+1) tends to infinity as n tends to infinity.
-/
theorem n_n_plus_one_inf : Filter.Tendsto (fun n => P_plus (n * (n + 1))) Filter.atTop Filter.atTop := by
  -- By definition of $P^+$, we know that $P^+(n(n+1)) \ge B$ for all $n \ge N$ if and only if $n \notin \text{bad\_set } B$.
  have h_eq : ∀ B : ℕ, {n : ℕ | n ≥ 1 ∧ P_plus (n * (n + 1)) ≤ B}.Finite := by
    intro B;
    convert bad_set_finite B using 1;
  refine' Filter.tendsto_atTop_atTop.mpr fun B => _;
  exact Exists.elim ( Set.Finite.bddAbove ( h_eq B ) ) fun N hN => ⟨ N + 1, fun n hn => not_lt.1 fun contra => not_lt_of_ge ( hN ⟨ by linarith, contra.le ⟩ ) hn ⟩

end Erdos368

namespace Erdos649

/-
Let $P(n)$ denote the greatest prime factor of $n$.
-/
def P (n : ℕ) : ℕ := (n.primeFactors).max.getD 0

/-
It is not true that for any two primes $p,q$, there exists some integer $n$ such that $P(n)=p$ and $P(n+1)=q$. Specifically, there is no solution for $p=2$ and $q=7$.
-/
theorem conjecture_false : ¬ ∀ (p q : ℕ), p.Prime → q.Prime → ∃ (n : ℕ), P n = p ∧ P (n + 1) = q := by
  simp +zetaDelta at *;
  use 2, Nat.prime_two, 7, by norm_num;
  unfold P;
  -- Suppose there exists some integer $n$ such that $P(n)=2$ and $P(n+1)=7$.
  intro x hx hx'
  have h_pow_2 : ∃ k : ℕ, x = 2 ^ k := by
    have h_pow_2 : ∀ p ∈ Nat.primeFactors x, p = 2 := by
      -- Since $p$ is a prime factor of $x$, we have $p \leq 2$.
      intros p hp
      have hp_le_2 : p ≤ 2 := by
        have h_le_two : p ≤ Finset.max x.primeFactors := by
          exact Finset.le_max hp;
        cases h : Finset.max x.primeFactors <;> aesop;
      interval_cases p <;> simp_all +decide;
    rw [ ← Nat.prod_primeFactorsList ( show x ≠ 0 from _ ) ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
    · exact fun p hp h => False.elim <| hp <| h_pow_2 p <| by simpa using h;
    · aesop_cat;
  -- Then $P(x+1)=7$ implies that the greatest prime factor of $2^k+1$ is 7.
  obtain ⟨k, rfl⟩ := h_pow_2
  have h_max_prime_factor : (2 ^ k + 1).primeFactors.max = some 7 := by
    rw [ Option.getD_eq_iff ] at hx' ; aesop;
  -- This implies that $7$ divides $2^k+1$, so $2^k \equiv -1 \equiv 6 \pmod{7}$.
  have h_div : 7 ∣ (2 ^ k + 1) := by
    exact Nat.dvd_of_mem_primeFactors <| Finset.mem_of_max h_max_prime_factor;
  rw [ Nat.dvd_iff_mod_eq_zero ] at h_div; rw [ ← Nat.mod_add_div k 3 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k zero_lt_three; interval_cases k % 3 <;> norm_num at *;

theorem solutions_finite_without_mahler (p q : ℕ) : {n | P n = p ∧ P (n + 1) = q}.Finite := by
  -- Let $S$ be the set of $n$ such that $P(n) = p$ and $P(n+1) = q$.
  set S := {n : ℕ | Erdos649.P n = p ∧ Erdos649.P (n + 1) = q};
  -- Let $B = \max(p, q)$.
  set B := max p q with hB_def;
  -- For any $n \in S$, we have $P(n(n+1)) \leq B$.
  have h_bound : ∀ n ∈ S, Erdos649.P (n * (n + 1)) ≤ B := by
    -- By definition of $S$, we know that $P(n) = p$ and $P(n+1) = q$.
    intro n hn
    obtain ⟨hn_p, hn_q⟩ := hn
    generalize_proofs at *;
    by_cases hn : n = 0 <;> by_cases hn' : n + 1 = 0 <;> simp_all +decide [ Erdos649.P ];
    rw [ Nat.primeFactors_mul ( by positivity ) ( by positivity ) ] ; simp_all +decide [ Finset.max ] ;
    -- Since the prime factors of $n$ and $n+1$ are disjoint, their union's supremum is the maximum of the two suprema.
    have h_sup_union : (n.primeFactors ∪ (n + 1).primeFactors).sup WithBot.some = max (n.primeFactors.sup WithBot.some) ((n + 1).primeFactors.sup WithBot.some) := by
      rw [ Finset.sup_union ]
    generalize_proofs at *; (
    grind);
  -- The set of n such that P(n(n+1)) ≤ B is finite.
  have h_finite_bad_set : Set.Finite {n : ℕ | n ≥ 1 ∧ Erdos649.P (n * (n + 1)) ≤ B} := by
    convert Erdos368.bad_set_finite B using 1;
    -- The two sets are equal because the conditions are equivalent.
    ext n
    simp [Erdos649.P];
    -- The two sets are equal because the conditions are equivalent. The prime factors of n(n+1) are the same as the prime factors of n and n+1 combined.
    simp [Erdos368.bad_set, Erdos368.P_plus];
    rcases x : ( n * ( n + 1 ) |> Nat.primeFactorsList |> List.maximum ) with ( _ | ⟨ p, hp ⟩ ) <;> simp_all +decide
    · simp_all +decide [ List.maximum ]
      rw [ List.argmax_eq_none ] at x
      aesop
    · have := List.maximum_mem x
      aesop
    · -- Since the maximum of the prime factors list is the same as the maximum of the prime factors set, the two conditions are equivalent.
      have h_max_eq : (n * (n + 1)).primeFactorsList.maximum = (n * (n + 1)).primeFactors.max := by
        have h_max_eq : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.Prime p) → List.maximum l = Finset.max (l.toFinset) := by
          -- The maximum of a list is the same as the maximum of the set of its elements.
          intros l hl
          induction' l with p l ih;
          · rfl;
          · simp_all +decide [ List.maximum_cons ];
        convert h_max_eq _;
        exact fun p hp => Nat.prime_of_mem_primeFactorsList hp;
      grind;
  refine Set.Finite.subset ( h_finite_bad_set.union ( Set.finite_singleton 0 ) ) ?_ ; intro n hn ; cases n <;> aesop

/-
There are infinitely many primes congruent to -1 modulo k for k > 2.
-/
lemma infinite_primes_mod_neg_one (k : ℕ) (hk : 2 < k) : {p : ℕ | p.Prime ∧ (p : ℤ) ≡ -1 [ZMOD k]}.Infinite := by
  have h_dirichlet : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ k - 1 [MOD k]} := by
    have := @Nat.setOf_prime_and_eq_mod_infinite;
    convert @this k ?_ ( k - 1 : ZMod k ) ?_ using 1;
    · rcases k with ( _ | _ | k ) <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      norm_cast;
    · exact ⟨ by linarith ⟩;
    · rcases k with ( _ | _ | k ) <;> norm_num at *;
  exact h_dirichlet.mono fun p hp => ⟨ hp.1, Int.ModEq.trans ( Int.natCast_modEq_iff.mpr hp.2 ) ( Int.modEq_iff_dvd.mpr ⟨ -1, by cases k <;> norm_num at * ; linarith ⟩ ) ⟩

/-
If l <= p and q = -1 mod 4p#, then q = -1 mod l.
-/
lemma q_mod_l_eq_neg_one (p q l : ℕ) (hl : l.Prime) (h_le : l ≤ p)
    (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) : (q : ℤ) ≡ -1 [ZMOD l] := by
      -- Since $l \le p$, $l$ divides $4 * primorial p$.
      have h_div : l ∣ 4 * primorial p := by
        refine' dvd_mul_of_dvd_right _ _;
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le h_le ), hl ⟩ );
      exact h_q_mod.of_dvd <| Int.natCast_dvd_natCast.mpr h_div

/-
If q = -1 mod 4, then (q-1)/2 is odd.
-/
lemma odd_div_two_of_mod_four_eq_neg_one (q : ℕ) (hq : (q : ℤ) ≡ -1 [ZMOD 4]) : Odd ((q - 1) / 2) := by
  rcases Nat.even_or_odd' q with ⟨ k, rfl | rfl ⟩ <;> ( ( have := hq.sub_right 1 ; norm_num [ Int.ModEq, Int.add_emod, Int.mul_emod ] at *; ) );
  · grind;
  · exact Nat.odd_iff.mpr ( by omega )

/-
If q = -1 mod l, then (q/l) = (-1)^((l-1)/2).
-/
lemma jacobi_q_l_eq_neg_one_pow (q l : ℕ) (hl : l.Prime) (hl_odd : l ≠ 2)
    (h_q_mod_l : (q : ℤ) ≡ -1 [ZMOD l]) :
    jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2) := by
      -- Since $q \equiv -1 \pmod{l}$, we have $\left(\frac{q}{l}\right) = \left(\frac{-1}{l}\right)$.
      have h_jacobi_neg_one : jacobiSym (q : ℤ) l = jacobiSym (-1 : ℤ) l := by
        exact jacobiSym.mod_left' h_q_mod_l;
      rw [ h_jacobi_neg_one, jacobiSym.mod_right ];
      · rw [ ← Nat.mod_add_div l 4 ] ; have := Nat.mod_lt l zero_lt_four; interval_cases _ : l % 4 <;> norm_num [ Nat.even_div, Nat.add_mod, Nat.mul_mod ] ;
        simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero, hl.dvd_iff_eq ];
      · exact hl.odd_of_ne_two hl_odd

/-
If q = -1 mod 4p#, then q = -1 mod 8.
-/
lemma q_mod_eight_eq_neg_one (p q : ℕ) (hp : p.Prime)
    (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) : (q : ℤ) ≡ -1 [ZMOD 8] := by
      refine h_q_mod.of_dvd ?_;
      rcases p with ( _ | _ | _ | _ | p ) <;> simp_all +arith +decide [ primorial ];
      exact dvd_trans ( by norm_num ) ( Finset.dvd_prod_of_mem _ ( show 2 ∈ Finset.filter Nat.Prime ( Finset.range ( p + 5 ) ) from Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), by norm_num ⟩ ) )

/-
If q = -1 mod 8, then (2/q) = 1.
-/
lemma jacobi_two_q_eq_one (q : ℕ) (hq : q.Prime) (hq_mod_8 : (q : ℤ) ≡ -1 [ZMOD 8]) :
    jacobiSym 2 q = 1 := by
      rw [ jacobiSym.mod_right ] ; norm_num [ hq_mod_8 ];
      · rw [ ← Nat.mod_add_div q 8, show q % 8 = 7 by exact Nat.cast_injective hq_mod_8 ] ; norm_num;
      · exact hq.odd_of_ne_two <| by rintro rfl; contradiction;

/-
If l <= p and q = -1 mod 4p#, then (l/q) = 1.
-/
lemma jacobi_of_factor_le_p (p q l : ℕ) (hp : p.Prime) (hq : q.Prime) (hl : l.Prime)
    (h_le : l ≤ p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    jacobiSym l q = 1 := by
      by_cases hl_two : l = 2;
      · -- Since $q \equiv -1 \pmod{8}$, we have $\left(\frac{2}{q}\right) = 1$ by `jacobi_two_q_eq_one`.
        have h_jacobi_two_q : jacobiSym 2 q = 1 := by
          apply jacobi_two_q_eq_one q hq (q_mod_eight_eq_neg_one p q hp h_q_mod);
        aesop;
      · -- Since $l$ is an odd prime, we can use the properties of the Jacobi symbol and quadratic reciprocity.
        have h_jacobi : jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2) := by
          convert jacobi_q_l_eq_neg_one_pow q l hl hl_two _;
          exact q_mod_l_eq_neg_one p q l hl h_le h_q_mod;
        -- By quadratic reciprocity, we have $\left(\frac{l}{q}\right)\left(\frac{q}{l}\right) = (-1)^{\frac{l-1}{2} \frac{q-1}{2}}$.
        have h_reciprocity : jacobiSym l q * jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2 * ((q - 1) / 2)) := by
          rw [ jacobiSym.quadratic_reciprocity ];
          · rcases Nat.even_or_odd' l with ⟨ k, rfl | rfl ⟩ <;> rcases Nat.even_or_odd' q with ⟨ m, rfl | rfl ⟩ <;> norm_num at *;
            · simp_all +decide [ Nat.prime_mul_iff ];
            · simp_all +decide [ Nat.prime_mul_iff ];
            · simp_all +decide [ Nat.prime_mul_iff ];
              norm_num [ Int.modEq_iff_dvd ] at h_q_mod;
              exact absurd ( Int.le_of_dvd ( by decide ) h_q_mod ) ( by linarith [ show ( primorial p : ℤ ) > 0 from Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ] );
            · norm_num [ Nat.add_div, h_jacobi ];
              by_cases hk : Even k <;> simp_all +decide [ parity_simps ];
          · exact hl.odd_of_ne_two hl_two;
          · exact hq.odd_of_ne_two <| by rintro rfl; exact absurd ( h_q_mod.symm.dvd ) ( by norm_num; intros h; obtain ⟨ k, hk ⟩ := h; replace hk := congr_arg ( · % 4 ) hk ; norm_num [ Int.add_emod, Int.mul_emod ] at hk ) ;
        -- Since $q \equiv -1 \pmod{4}$, we have $\frac{q-1}{2}$ is odd.
        have h_q_mod_four : (q : ℤ) ≡ -1 [ZMOD 4] := by
          exact h_q_mod.of_dvd <| dvd_mul_right _ _
        have h_q_odd : Odd ((q - 1) / 2) := by
          exact odd_div_two_of_mod_four_eq_neg_one q h_q_mod_four;
        by_cases h : Even ( ( l - 1 ) / 2 ) <;> simp_all +decide

/-
If (l/q)=1 for all prime factors l of n, then (n/q)=1.
-/
lemma jacobi_eq_one_of_prime_factors_eq_one {n q : ℕ} (hn : n ≠ 0)
    (h : ∀ l, l.Prime → l ∣ n → jacobiSym l q = 1) : jacobiSym n q = 1 := by
      induction' n using Nat.strongRecOn with n ih;
      by_cases h₁ : n = 1;
      · aesop;
      · obtain ⟨ l, hl₁, hl₂ ⟩ := Nat.exists_prime_and_dvd h₁;
        obtain ⟨ k, rfl ⟩ := hl₂; simp_all +decide [ jacobiSym.mul_left ] ;
        exact ih k ( lt_mul_of_one_lt_left ( Nat.pos_of_ne_zero hn.2 ) hl₁.one_lt ) hn.2 fun p hp hpk => h p hp ( dvd_mul_of_dvd_right hpk _ )

/-
If P(n)=p and q = -1 mod 4p#, then (n/q) = 1.
-/
lemma jacobi_of_P_eq_p (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (hn : n ≠ 0)
    (h_max_prime : P n = p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    jacobiSym n q = 1 := by
      -- Since $P(n) = p$, all prime factors of $n$ are $\le p$.
      have h_factors_le_p : ∀ l, l.Prime → l ∣ n → l ≤ p := by
        intro l hl hl_div
        have h_prime_factor : l ∈ n.primeFactors := by
          aesop;
        -- Since $P(n) = p$, the greatest prime factor of $n$ is $p$. Therefore, any prime factor $l$ of $n$ must satisfy $l \leq p$.
        have h_max_prime_factor : ∀ l ∈ n.primeFactors, l ≤ (n.primeFactors).max.getD 0 := by
          exact fun x hx => by have := Finset.le_max hx; cases h : n.primeFactors.max <;> aesop;
        exact h_max_prime ▸ h_max_prime_factor l h_prime_factor;
      -- By `jacobi_of_factor_le_p`, for any prime factor $l$ of $n$, we have $\left(\frac{l}{q}\right) = 1$.
      have h_jacobi_l_q : ∀ l, l.Prime → l ∣ n → jacobiSym l q = 1 := by
        exact fun l a a_1 => jacobi_of_factor_le_p p q l hp hq a (h_factors_le_p l a a_1) h_q_mod;
      convert jacobi_eq_one_of_prime_factors_eq_one hn h_jacobi_l_q

/-
If P(n)=p and q = -1 mod 4p#, then n is not -1 mod q.
-/
lemma n_not_equiv_neg_one_mod_q (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (hn : n ≠ 0)
    (h_max_prime : P n = p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    ¬ ((n : ℤ) ≡ -1 [ZMOD q]) := by
      -- From `jacobi_of_P_eq_p`, we know that $\left(\frac{n}{q}\right) = 1$.
      have h_jacobi : jacobiSym n q = 1 := by
        exact jacobi_of_P_eq_p p q n hp hq hn h_max_prime h_q_mod;
      -- Since $q \equiv -1 \pmod{4p\#}$, we have that $\left(\frac{-1}{q}\right) = -1$.
      have h_jacobi_neg_one : jacobiSym (-1 : ℤ) q = -1 := by
        -- Since $q \equiv -1 \pmod{8}$, we have that $(q : ℤ) \equiv -1 \pmod{4}$.
        have h_q_mod_four : (q : ℤ) ≡ -1 [ZMOD 4] := by
          exact h_q_mod.of_dvd <| dvd_mul_right _ _;
        rw [ jacobiSym.mod_right ] ; norm_num;
        · rw [ ← Nat.mod_add_div q 4 ] at *; have := Nat.mod_lt q zero_lt_four; interval_cases q % 4 <;> norm_num [ Int.ModEq ] at *;
        · exact hq.odd_of_ne_two <| by rintro rfl; contradiction;
      by_contra h_contra;
      have h_jacobi_eq : jacobiSym (n : ℤ) q = jacobiSym (-1 : ℤ) q := by
        have h_cong : (n : ℤ) ≡ -1 [ZMOD q] := by
          exact h_contra
        exact jacobiSym.mod_left' h_contra;
      linarith

/-
For any prime p, there are infinitely many primes q such that no n satisfies P(n)=p and P(n+1)=q.
-/
theorem tong_counterexamples (p : ℕ) (hp : p.Prime) : {q | q.Prime ∧ ¬ ∃ n, P n = p ∧ P (n + 1) = q}.Infinite := by
  -- By `infinite_primes_mod_neg_one` with $k = 4m$, there are infinitely many primes $q \equiv -1 \pmod{4m}$.
  have h_inf : Set.Infinite {q : ℕ | Nat.Prime q ∧ (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]} := by
    -- Apply the lemma that states there are infinitely many primes congruent to -1 modulo k for k > 2.
    apply infinite_primes_mod_neg_one;
    linarith [ show 1 ≤ primorial p from Nat.pos_of_ne_zero ( by rw [ primorial ] ; exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.Prime.ne_zero <| by aesop ) ];
  refine Set.Infinite.mono ?_ h_inf;
  intro q hqaesop;
  refine' ⟨ hqaesop.1, _ ⟩;
  rintro ⟨ n, hn₁, hn₂ ⟩;
  -- Since $P(n+1)=q$, we have $q \mid n+1$.
  have hq_div_n1 : q ∣ n + 1 := by
    unfold P at hn₂;
    have := Finset.mem_of_max <| show ( n + 1 |> Nat.primeFactors |> Finset.max ) = some q from by { unfold Option.getD at hn₂; aesop } ; aesop;
  -- By `n_not_equiv_neg_one_mod_q`, $n \not\equiv -1 \pmod q$.
  have hq_not_equiv_neg_one : ¬((n : ℤ) ≡ -1 [ZMOD q]) := by
    apply n_not_equiv_neg_one_mod_q p q n hp hqaesop.left;
    · aesop;
    · assumption;
    · exact hqaesop.2;
  exact hq_not_equiv_neg_one <| Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hq_div_n1;

/-
Tong's question: For any odd prime q, are there infinitely many primes p such that no n satisfies P(n)=p and P(n+1)=q?
-/
def tong_question : Prop := ∀ q, q.Prime → q % 2 = 1 → {p | p.Prime ∧ ¬ ∃ n, P n = p ∧ P (n + 1) = q}.Infinite

/-
$P(m)=2$ if and only if $m$ is a power of 2 (greater than 1).
-/
lemma P_eq_two_iff_pow_two {m : ℕ} (hm : m ≠ 0) : P m = 2 ↔ ∃ k > 0, m = 2 ^ k := by
  constructor <;> intro h;
  · -- If $P(m)=2$, then the greatest prime factor of $m$ is 2. This means all prime factors of $m$ are $\le 2$. Since 2 is the smallest prime, all prime factors must be 2. Thus $m$ is a power of 2. Let $m = 2^k$ for some $k \geq 0$.
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 ^ k := by
      -- By definition of $P$, we know that every prime factor of $m$ is less than or equal to $2$.
      have h_prime_factors : ∀ p ∈ m.primeFactors, p ≤ 2 := by
        unfold P at h;
        have h_prime_factors : ∀ p ∈ m.primeFactors, p ≤ Finset.max m.primeFactors := by
          exact fun p hp => Finset.le_max hp;
        cases h' : Finset.max m.primeFactors <;> aesop;
      rw [ ← Nat.prod_primeFactorsList hm ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
      intro p hp hprime; have := h_prime_factors p ( by aesop ) ; interval_cases p <;> simp_all +decide ;
    exact ⟨ k, Nat.pos_of_ne_zero ( by rintro rfl; exact absurd h ( by native_decide ) ), rfl ⟩;
  · unfold P;
    rcases h with ⟨ k, hk, rfl ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.primeFactors_pow ] ;

/-
If $18 \mid k$, then $73 \mid 2^k - 1$.
-/
lemma seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd {k : ℕ} (hk : 18 ∣ k) : 73 ∣ 2^k - 1 := by
  -- Since $18 \mid k$, we can write $k = 18m$ for some integer $m$.
  obtain ⟨m, rfl⟩ : ∃ m, k = 18 * m := hk;
  rw [ pow_mul ] ; erw [ ← Nat.mod_add_div ( 2 ^ 18 ) 73 ] ; norm_num [ Nat.pow_mod, Nat.add_mod, Nat.mul_mod ] ; induction' m with m IH <;> norm_num [ pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod ] at * ; omega;

/-
If $2^k \equiv 1 \pmod{19}$, then $18 \mid k$.
-/
lemma eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one {k : ℕ} (h : 2^k ≡ 1 [MOD 19]) : 18 ∣ k := by
  exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div k 18 ] at h; norm_num [ Nat.ModEq, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at h; have := Nat.mod_lt k ( by decide : 0 < 18 ) ; interval_cases k % 18 <;> trivial )

/-
There is no integer $n$ such that $P(n)=19$ and $P(n+1)=2$.
-/
theorem sampaio_counterexample : ¬ ∃ n, P n = 19 ∧ P (n + 1) = 2 := by
  -- Assume there exists $n$ such that $P(n)=19$ and $P(n+1)=2$.
  by_contra h
  obtain ⟨n, hn1, hn2⟩ := h;
  -- Since $P(n+1)=2$, by `P_eq_two_iff_pow_two`, $n+1 = 2^k$ for some $k>0$. Thus $n = 2^k - 1$.
  have hn_form : ∃ k > 0, n = 2 ^ k - 1 := by
    -- By `P_eq_two_iff_pow_two`, $n+1 = 2^k$ for some $k>0$. Thus $n = 2^k - 1$.
    have hn1_form : ∃ k > 0, n + 1 = 2 ^ k := by
      exact P_eq_two_iff_pow_two ( Nat.succ_ne_zero _ ) |>.1 hn2;
    exact ⟨ hn1_form.choose, hn1_form.choose_spec.1, eq_tsub_of_add_eq hn1_form.choose_spec.2 ⟩;
  obtain ⟨ k, hk_pos, rfl ⟩ := hn_form; simp_all +decide
  -- Since $P(n)=19$, $19 \mid n$, so $2^k - 1 \equiv 0 \pmod{19}$, which means $2^k \equiv 1 \pmod{19}$.
  have h_mod : 2 ^ k ≡ 1 [MOD 19] := by
    -- Since $P(n)=19$, we know that $19$ divides $n$.
    have h_div : 19 ∣ (2 ^ k - 1) := by
      unfold P at hn1;
      have := Finset.mem_of_max ( show ( 2 ^ k - 1 |> Nat.primeFactors |> Finset.max ) = some 19 from by { rw [ Option.getD_eq_iff ] at hn1; aesop } ) ; aesop;
    simpa [ Nat.modEq_iff_dvd ] using h_div.modEq_zero_nat;
  -- By `eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one`, we have $18 \mid k$.
  have h_div : 18 ∣ k := by
    exact eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one h_mod;
  -- By `seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd`, since $18 \mid k$, we have $73 \mid 2^k - 1$.
  have h_div_73 : 73 ∣ 2 ^ k - 1 := by
    exact seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd h_div;
  -- Since $73$ is a prime factor of $n$ (as $73 \mid n$), we must have $73 \le 19$, which is a contradiction.
  have h_contra : 73 ∈ (2 ^ k - 1).primeFactors := by
    norm_num +zetaDelta at *;
    exact ⟨ h_div_73, Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide ) hk_pos.ne' ) ⟩;
  have h_contra : (2 ^ k - 1).primeFactors.max.getD 0 ≥ 73 := by
    have h_contra : ∀ {s : Finset ℕ}, 73 ∈ s → s.max.getD 0 ≥ 73 := by
      intros s hs; exact (by
      have h_contra : ∀ {s : Finset ℕ}, 73 ∈ s → s.max.getD 0 ≥ 73 := by
        intros s hs
        have h_max : s.max ≤ s.max.getD 0 := by
          cases h : s.max <;> aesop
        exact Nat.cast_le.mp ( le_trans ( Finset.le_max hs ) h_max );
      exact h_contra hs);
    exact h_contra ‹_›;
  unfold P at * ; aesop

/-
A strange pair is a pair of distinct primes p and q such that there is no integer n >= 2 for which P(n) P(n + 1) = pq.
-/
def StrangePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ ∀ n ≥ 2, P n * P (n + 1) ≠ p * q

lemma P_mul_P_eq_mul_prime_factors {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
  (h : P n * P (n + 1) = p * q) :
  (P n = p ∧ P (n + 1) = q) ∨ (P n = q ∧ P (n + 1) = p) := by
    -- Since $p$ and $q$ are distinct primes, their product $pq$ can only be factored into primes as $p$ and $q$.
    have h_factors : ∀ {x y : ℕ}, Nat.Prime x → Nat.Prime y → x * y = p * q → (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
      intro x y hx hy hxy; have := Nat.Prime.dvd_mul hx |>.1 ( hxy ▸ dvd_mul_right _ _ ) ; have := Nat.Prime.dvd_mul hy |>.1 ( hxy ▸ dvd_mul_left _ _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      aesop;
    -- Apply the fact that $P(n)$ and $P(n+1)$ are primes.
    have h_prime_factors : Nat.Prime (P n) ∧ Nat.Prime (P (n + 1)) := by
      unfold P at *;
      rcases x : n.primeFactors.max with ( _ | x ) <;> rcases y : ( n + 1 ).primeFactors.max with ( _ | y ) <;> simp_all +decide
      · aesop;
      · aesop;
      · aesop;
      · exact ⟨ Nat.prime_of_mem_primeFactors <| Finset.mem_of_max x, Nat.prime_of_mem_primeFactors <| Finset.mem_of_max y ⟩;
    exact h_factors h_prime_factors.1 h_prime_factors.2 h

/-
If $a^k = -1$ in $\mathbb{Z}/n\mathbb{Z}$ with $n > 2$, then the order of $a$ divides $2k$ but not $k$.
-/
lemma order_properties_of_neg_one {n : ℕ} (hn : n > 2) {a : ZMod n} {k : ℕ} (h : a^k = -1) : orderOf a ∣ 2 * k ∧ ¬ orderOf a ∣ k := by
  norm_num [ orderOf_dvd_iff_pow_eq_one ];
  simp_all +decide [ pow_mul' ];
  intro h'; rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ ZMod, Fin.ext_iff ] ;

/-
If $\ord_{q_1}(a)=\ord_{q_2}(a)$ and $a^k \equiv -1 \pmod{q_1}$, then $a^k \equiv -1 \pmod{q_2}$.
-/
lemma same_order_neg_one_power {q1 q2 : ℕ} (hq2 : q2.Prime) (h_odd1 : q1 > 2)
  (a : ℕ) (k : ℕ)
  (h_ord : orderOf (a : ZMod q1) = orderOf (a : ZMod q2))
  (h_pow : (a : ZMod q1)^k = -1) :
  (a : ZMod q2)^k = -1 := by
    -- By `order_properties_of_neg_one`, we know that `orderOf (a : ZMod q1) 2 * k` and `orderOf (a : ZMod q1) ∤ k`.
    have h_div : orderOf (a : ZMod q1) ∣ 2 * k ∧ ¬orderOf (a : ZMod q1) ∣ k := by
      exact order_properties_of_neg_one h_odd1 h_pow;
    simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
    haveI := Fact.mk hq2; exact Or.resolve_left ( eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h_div.1 ) h_div.2;

/-
If the greatest prime factor of $n$ is 2, then $n$ is a power of 2.
-/
lemma P_eq_2_implies_power_two {n : ℕ} (h : P n = 2) : ∃ k : ℕ, n = 2^k := by
  by_cases hn : n = 0;
  · simp_all +decide [ P ];
  · unfold P at h;
    -- Since $P(n) = 2$, we have that the maximum prime factor of $n$ is 2. This implies that all prime factors of $n$ are 2.
    have h_prime_factors : n.primeFactors ⊆ {2} := by
      have h_prime_factors : ∀ p ∈ n.primeFactors, p ≤ 2 := by
        have h_prime_factors : ∀ p ∈ n.primeFactors, p ≤ Finset.max n.primeFactors := by
          exact fun p hp => Finset.le_max hp;
        cases h' : n.primeFactors.max <;> aesop;
      intro p hp; specialize h_prime_factors p hp; interval_cases p <;> simp_all +decide ;
    rw [ ← Nat.factorization_prod_pow_eq_self hn ] ; exact ⟨ n.factorization 2, by rw [ Finsupp.prod ] ; aesop ⟩ ;

/-
Under the assumptions, it is impossible that $P(n)=2$ and $P(n+1)=q_1$.
-/
lemma case1_impossible {q1 q2 n : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime)
  (h_odd1 : q1 > 2)
  (h_q1_lt_q2 : q1 < q2)
  (h_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2))
  (hPn : P n = 2) (hPn1 : P (n + 1) = q1) : False := by
    -- Since $P(n)=2$, $n=2^k$ for some $k$. Since $P(n+1)=q_1 �$,� $q_1 \mid n+1 = 2^k+1$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2^k := by
      exact P_eq_2_implies_power_two hPn
    have hq1_div : q1 ∣ 2^k + 1 := by
      unfold P at hPn1;
      replace hPn1 := Finset.mem_of_max ( show ( n + 1 |> Nat.primeFactors |> Finset.max ) = some q1 from by { unfold Option.getD at hPn1; aesop } ) ; aesop;
    -- Thus $2^k \equiv -1 \pmod{q_2}$. Thus $q_2 \mid 2^k+1 = n+1$.
    have hq2_div : q2 ∣ 2^k + 1 := by
      have hq2_div : (2 : ZMod q2)^k = -1 := by
        have hq1_cong : (2 ^ k : ZMod q1) = -1 := by
          exact eq_neg_of_add_eq_zero_left ( by simpa [ ← ZMod.natCast_eq_zero_iff ] using hq1_div );
        have := same_order_neg_one_power hq2 h_odd1 2 k h_ord hq1_cong; aesop;
      simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
    -- So $P(n+1) \ge q_2$.
    have hPn1_ge_q2 : q2 ≤ P (2^k + 1) := by
      -- Since $q2$ is a prime factor of $2^k + 1$, it must be less than or equal to the maximum prime factor of $2^k + 1$.
      have hq2_le_max_prime_factor : q2 ≤ (2^k + 1).primeFactors.max.getD 0 := by
        have hq2_prime_factor : q2 ∈ (2^k + 1).primeFactors := by
          aesop
        have hq2_le_max_prime_factor : ∀ {S : Finset ℕ}, q2 ∈ S → q2 ≤ S.max.getD 0 := by
          intros S hq2_in_S; exact (by
          have := Finset.le_max hq2_in_S; cases h : Finset.max S <;> aesop;);
        exact hq2_le_max_prime_factor hq2_prime_factor;
      exact hq2_le_max_prime_factor;
    grind

/-
Under the assumptions, it is impossible that $P(n)=q_1$ and $P(n+1)=2$.
-/
lemma case2_impossible {q1 q2 n : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime)
  (h_odd1 : q1 > 2)
  (h_q1_lt_q2 : q1 < q2)
  (h_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2))
  (hPn : P n = q1) (hPn1 : P (n + 1) = 2) : False := by
    -- Since $P(n+1)=2 �$,� $n+1=2^k$ for some $k$.
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 ^ k := by
      exact P_eq_2_implies_power_two hPn1;
    -- Since $q1 \mid n = 2^k - 1$, we have $2^k \equiv 1 \p �mod�{q1}$.
    have h_mod_q1 : 2 ^ k ≡ 1 [MOD q1] := by
      refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
      simp +decide [ ← hk ];
      -- Since $q1$ is the greatest prime factor of $n$, it must divide $n$.
      have h_div : q1 ∈ n.primeFactors := by
        unfold P at hPn;
        have hq1_div_n : n.primeFactors.max = some q1 := by
          unfold Option.getD at hPn; aesop;
        exact Finset.mem_of_max hq1_div_n;
      exact_mod_cast Nat.dvd_of_mem_primeFactors h_div;
    -- Since $\ord_{q_2}(2)=s$, $s$ is the order of 2 mod $q_2$. Thus $2^k \equiv 1 � \�pmod{q_2}$.
    have h_mod_q2 : 2 ^ k ≡ 1 [MOD q2] := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      rw [ ← orderOf_dvd_iff_pow_eq_one ] at * ; aesop;
    -- Since $q2 \mid 2^k - 1 = n$, we have $P(n) \ge q2 �$�.
    have h_div_q2 : q2 ∣ n := by
      rw [ ← Int.natCast_dvd_natCast ] ; simpa [ ← hk ] using h_mod_q2.symm.dvd;
    -- Since $q2 \mid n$, we have $P(n) \ge q2$.
    have h_Pn_ge_q2 : P n ≥ q2 := by
      have h_Pn_ge_q2 : q2 ∈ n.primeFactors := by
        rcases n with ( _ | _ | n ) <;> simp_all +decide
        cases hPn.symm.trans ( by native_decide : P 0 = 0 );
        contradiction;
      have h_Pn_ge_q2 : ∀ {S : Finset ℕ}, q2 ∈ S → S.max.getD 0 ≥ q2 := by
        intros S hS; exact (by
        have := Finset.le_max hS; cases h : S.max <;> aesop;);
      (expose_names; exact h_Pn_ge_q2 h_Pn_ge_q2_1);
    linarith

/-
Let $2<q_1<q_2$ be primes. If $\ord_{q_1}(2)=\ord_{q_2}(2)$, then the pair $\{2,q_1\}$ is strange.
-/
lemma equal_order_strange {q1 q2 : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime) (h_order : 2 < q1) (h_q1_lt_q2 : q1 < q2) (h_eq_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2)) : StrangePair 2 q1 := by
  refine' ⟨ Nat.prime_two, hq1, _, _ ⟩;
  · linarith;
  · -- Assume, for contradiction, that $\{2,q_1\}$ is not strange. Then there exists $n\ge 2 �$� such that
    -- \[
    -- F(n)\,F(n+1)=2q_1.
    -- \]
    intro n hn
    by_contra h_contra
    have h_cases : P n = 2 ∧ P (n + 1) = q1 ∨ P n = q1 ∧ P (n + 1) = 2 := by
      have := P_mul_P_eq_mul_prime_factors Nat.prime_two hq1 ( by linarith ) h_contra; aesop;
    cases h_cases <;> simp_all +decide;
    · exact case1_impossible hq1 hq2 h_order ( by linarith ) h_eq_ord ( by tauto ) ( by tauto );
    · apply case2_impossible hq1 hq2 h_order ( by linarith ) h_eq_ord ( by tauto ) ( by tauto )

/-
For a prime $p > 5$, $N = 2^{2p} + 1$ satisfies $N \equiv 2 \pmod 3$, $N \equiv 0 \pmod 5$, and $N \not\equiv 0 \pmod{25}$.
-/
lemma N_mod_3_and_5 {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  (2^(2*p) + 1) % 3 = 2 ∧ (2^(2*p) + 1) % 5 = 0 ∧ (2^(2*p) + 1) % 25 ≠ 0 := by
    norm_num [ Nat.pow_mul, Nat.add_mod, Nat.pow_mod ];
    rw [ ← Nat.mod_add_div p 20 ] at *; have := Nat.mod_lt p ( by decide : 0 < 20 ) ; interval_cases p % 20 <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *;
    all_goals have := Nat.Prime.eq_two_or_odd hp; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.dvd_iff_mod_eq_zero ] at this;
    any_goals omega;
    · norm_num [ show 5 + 20 * ( p / 20 ) = 5 * ( 1 + 4 * ( p / 20 ) ) by ring, Nat.prime_mul_iff ] at hp;
      interval_cases p;
    · norm_num [ show 15 + 20 * ( p / 20 ) = 5 * ( 3 + 4 * ( p / 20 ) ) by ring, Nat.prime_mul_iff ] at hp;
      omega

/-
$2^{2p} + 1$ factors as $(2^p - 2^r + 1)(2^p + 2^r + 1)$ where $r = (p+1)/2$.
-/
lemma N_factorization {p : ℕ} (hp : Odd p) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  2^(2*p) + 1 = A * B := by
    obtain ⟨ k, rfl ⟩ : ∃ k, p = 2 * k + 1 := hp; ring_nf;
    norm_num [ Nat.add_div ] ; ring_nf;
    zify ; ring_nf;
    rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring

/-
The factors $A = 2^p - 2^r + 1$ and $B = 2^p + 2^r + 1$ are coprime.
-/
lemma N_factors_coprime {p : ℕ} (hp : Odd p) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  Nat.gcd A B = 1 := by
    -- Since $B - A = 2 �^{�r+1}$ and $A$ is odd, any common divisor of $A$ and $B$ must also divide $2^{r+1}$. However, since $A$ is odd, the only possible common divisor is $1$.
    have h_div : ∀ d, d ∣ (2 ^ p - 2 ^ ((p + 1) / 2) + 1) → d ∣ (2 ^ p + 2 ^ ((p + 1) / 2) + 1) → d ∣ 2 ^ ((p + 1) / 2 + 1) := by
      intro d hd₁ hd₂; convert Nat.dvd_sub hd₂ hd₁ using 1; rw [ Nat.sub_eq_of_eq_add ] ; ring_nf;
      linarith [ Nat.sub_add_cancel ( show 2 ^ p ≥ 2 ^ ( ( 1 + p ) / 2 ) from pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith [ hp.pos ] ) ) ];
    have h_odd : Odd (2 ^ p - 2 ^ ((p + 1) / 2) + 1) := by
      norm_num [ Nat.one_le_iff_ne_zero, parity_simps ];
      exact even_iff_two_dvd.mpr ( Nat.dvd_sub ( dvd_pow_self _ hp.pos.ne' ) ( dvd_pow_self _ ( Nat.ne_of_gt ( Nat.div_pos ( by linarith [ hp.pos ] ) zero_lt_two ) ) ) );
    have := h_div _ ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ) ; ( have := Nat.dvd_gcd ( Nat.gcd_dvd_left _ _ ) this; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ; )

/-
Neither $A$ nor $B$ is divisible by 3, and exactly one of them is divisible by 5 (but not 25).
-/
lemma N_factors_divisibility {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  ¬(3 ∣ A) ∧ ¬(3 ∣ B) ∧ ((5 ∣ A ∧ ¬(25 ∣ A) ∧ ¬(5 ∣ B)) ∨ (5 ∣ B ∧ ¬(25 ∣ B) ∧ ¬(5 ∣ A))) := by
    -- Since $N = A \cdot B$ and $N \equiv 0 \pmod 5$, $5 \mid N$ but $25 \nmid N$.
    have h_mod_5 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (5 ∣ A ∧ ¬25 ∣ A ∧ ¬5 ∣ B) ∨ (5 ∣ B ∧ ¬25 ∣ B ∧ ¬5 ∣ A) := by
      have h_mod_5 : (2^(2*p) + 1) % 5 = 0 ∧ (2^(2*p) + 1) % 25 ≠ 0 := by
        exact N_mod_3_and_5 hp hp5 |>.2;
      have h_mod_5 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (A * B) % 5 = 0 ∧ (A * B) % 25 ≠ 0 := by
        convert h_mod_5 using 2;
        · rw [ ← N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) ];
        · rw [ show ( 2 ^ ( 2 * p ) + 1 : ℕ ) = ( 2 ^ p - 2 ^ ( ( p + 1 ) / 2 ) + 1 ) * ( 2 ^ p + 2 ^ ( ( p + 1 ) / 2 ) + 1 ) from ?_ ];
          convert N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) using 1;
      by_cases h5A : 5 ∣ (2^p - 2^((p + 1) / 2) + 1) <;> by_cases h5B : 5 ∣ (2^p + 2^((p + 1) / 2) + 1) <;> simp_all +decide
      · exact h_mod_5.2 ( Nat.mod_eq_zero_of_dvd ( dvd_trans ( by decide ) ( mul_dvd_mul h5A h5B ) ) );
      · exact fun h => h_mod_5.2 <| Nat.mod_eq_zero_of_dvd <| dvd_trans h <| dvd_mul_right _ _;
      · exact fun h => h_mod_5.2 <| Nat.mod_eq_zero_of_dvd <| dvd_trans h <| dvd_mul_left _ _;
      · exact absurd ( Nat.Prime.dvd_mul ( by norm_num : Nat.Prime 5 ) |>.1 ( Nat.dvd_of_mod_eq_zero h_mod_5.1 ) ) ( by tauto );
    -- Since $N = A \cdot B$ and $N \equiv 2 \pmod 3$, $3 \nmid N$, so $3 \nmid A$ and $3 \nmid B$.
    have h_mod_3 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; ¬(3 ∣ A) ∧ ¬(3 ∣ B) := by
      have h_mod_3 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (A * B) % 3 = 2 := by
        convert N_mod_3_and_5 hp hp5 |>.1 using 1;
        rw [ N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) ];
      exact ⟨ fun h => by have := Nat.mod_eq_zero_of_dvd h; simp_all +decide [ Nat.mul_mod ], fun h => by have := Nat.mod_eq_zero_of_dvd h; simp_all +decide [ Nat.mul_mod ] ⟩;
    exact ⟨ h_mod_3.1, h_mod_3.2, h_mod_5 ⟩

/-
For $p \ge 7$, the factors $A$ and $B$ are strictly greater than 5.
-/
lemma N_factors_large {p : ℕ} (hp : p ≥ 7) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  A > 5 ∧ B > 5 := by
    refine ⟨ ?_, ?_ ⟩ <;> norm_num [ Nat.pow_succ' ] at *;
    · refine lt_add_of_le_of_pos ( Nat.le_sub_of_add_le ?_ ) zero_lt_one;
      rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ];
      · rw [ pow_mul' ] ; nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : c ≥ 3 ) ];
      · ring_nf;
        rw [ pow_mul ] ; nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : c ≥ 3 ) ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hp, pow_pos ( by decide : 0 < 2 ) ( ( p + 1 ) / 2 ) ]

/-
If $n > 1$ is odd and not divisible by 3 or 5, then it has a prime factor greater than 5.
-/
lemma exists_prime_gt_five {n : ℕ} (h_odd : Odd n) (h_not_3 : ¬ 3 ∣ n) (h_not_5 : ¬ 5 ∣ n) (h_gt_1 : n > 1) :
  ∃ q, q.Prime ∧ q ∣ n ∧ q > 5 := by
    -- Since $n$ is odd and greater than 1, it must � have� at least one prime factor. Let $q$ be � the� smallest prime factor of $n$.
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ n := by
      exact Nat.exists_prime_and_dvd h_gt_1.ne';
    rcases q with ( _ | _ | _ | _ | _ | _ | q ) <;> simp_all +arith +decide
    · exact absurd ( even_iff_two_dvd.mpr hq_div ) ( by simpa using h_odd );
    · exact ⟨ _, hq_prime, hq_div, by linarith ⟩

set_option maxHeartbeats 0 in
/-
Let $p>5$ be a prime and set $N=2^{2p}+1$. Then $N$ has at least two distinct prime divisors greater than $5$.
-/
lemma two_large_primes {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  ∃ q1 q2 : ℕ, q1.Prime ∧ q2.Prime ∧ q1 ≠ q2 ∧ q1 > 5 ∧ q2 > 5 ∧ q1 ∣ (2^(2*p) + 1) ∧ q2 ∣ (2^(2*p) + 1) := by
    -- Let $r = (p+1)/2$, $A = 2^p - 2^r + 1$, and $B = 2^p + 2^r + 1$.
    set r := (p + 1) / 2
    set A := 2^p - 2^r + 1
    set B := 2^p + 2^r + 1
    have hN : 2^(2*p) + 1 = A * B := by
      convert N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) using 1
    have h_coprime : Nat.gcd A B = 1 := by
      apply N_factors_coprime; exact hp.odd_of_ne_two (by linarith)
    have h_divisibility : ¬(3 ∣ A) ∧ ¬(3 ∣ B) ∧ ((5 ∣ A ∧ ¬(25 ∣ A) ∧ ¬(5 ∣ B)) ∨ (5 ∣ B ∧ ¬(25 ∣ B) ∧ ¬(5 ∣ A))) := by
      exact N_factors_divisibility hp hp5
    have h_large : A > 5 ∧ B > 5 := by
      exact N_factors_large ( show p ≥ 7 by contrapose! hp5; interval_cases p <;> trivial ) |> fun h => ⟨ h.1, h.2 ⟩;
    -- Case 1: $5 \mid A$. Then $5 \nmid B$.
    by_cases h5A : 5 ∣ A;
    · -- Since $A$ is divisible by 5, $ �A�/5$ is odd and greater than 1. Also �,� $A$ is not divisible by 3 or 25.
      have hA_div_5 : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ A / 5 ∧ q1 > 5 := by
        -- Since $A/5$ is odd and greater � than� 1, it must have a prime factor greater � than� 5.
        have hA_div_5_odd : Odd (A / 5) := by
          have hA_odd : Odd A := by
            simp +zetaDelta at *;
            cases le_total ( 2 ^ p ) ( 2 ^ ( ( p + 1 ) / 2 ) ) <;> simp_all +decide [ Nat.one_le_iff_ne_zero, parity_simps ];
          exact hA_odd.of_dvd_nat ( Nat.div_dvd_of_dvd h5A )
        have hA_div_5_gt_1 : 1 < A / 5 := by
          omega
        have hA_div_5_not_div_3 : ¬(3 ∣ A / 5) := by
          exact fun h => h_divisibility.1 ( dvd_trans h ( Nat.div_dvd_of_dvd h5A ) )
        have hA_div_5_not_div_5 : ¬(5 ∣ A / 5) := by
          omega
        have hA_div_5_prime_factor : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ A / 5 ∧ q1 > 5 := by
          apply exists_prime_gt_five; assumption; assumption; assumption; assumption;
        exact hA_div_5_prime_factor;
      obtain ⟨q1, hq1⟩ := hA_div_5
      use q1, Nat.minFac B;
      -- Since $B$ is not divisible by 3 or 5, its minimal prime factor must be greater than 5.
      have hB_min_fac_gt_5 : Nat.minFac B > 5 := by
        by_contra h_contra
        have hB_div_3_or_5 : 3 ∣ B ∨ 5 ∣ B := by
          have := Nat.minFac_prime ( by linarith : B ≠ 1 ) ; ( have := Nat.minFac_dvd B; ( interval_cases _ : Nat.minFac B <;> simp_all +decide ) );
          simp +zetaDelta at *;
          norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hp.ne_zero ] at this;
          norm_num [ Nat.zero_pow ( Nat.div_pos ( by linarith : p + 1 ≥ 2 ) zero_lt_two ) ] at this
        aesop;
      exact ⟨ hq1.1, Nat.minFac_prime ( by linarith ), fun h => by have := Nat.dvd_gcd ( show q1 ∣ A from dvd_trans hq1.2.1 ( Nat.div_dvd_of_dvd h5A ) ) ( show q1 ∣ B from h.symm ▸ Nat.minFac_dvd _ ) ; aesop, hq1.2.2, hB_min_fac_gt_5, dvd_trans hq1.2.1 ( Nat.div_dvd_of_dvd h5A ) |> fun x => dvd_trans x ( hN.symm ▸ dvd_mul_right _ _ ), Nat.minFac_dvd _ |> fun x => dvd_trans x ( hN.symm ▸ dvd_mul_left _ _ ) ⟩;
    · -- Since $5 \mid B$, we can apply `exists_prime_gt_five` to $B/5$ to find a prime factor $ �q�_1 > 5$.
      obtain ⟨q1, hq1⟩ : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ B / 5 ∧ q1 > 5 := by
        apply exists_prime_gt_five;
        · rcases h_divisibility.2.2 with h | h <;> simp_all +decide
          simp +zetaDelta at *;
          rcases h.1 with ⟨ k, hk ⟩ ; simp_all +decide [ parity_simps ];
          replace hk := congr_arg Even hk; simp_all +decide [ parity_simps ] ;
          cases p <;> aesop;
        · omega;
        · omega;
        · grind;
      -- Since $A$ is not divisible by 3 or 5, and $A > 5$, it must have a prime factor greater � than� 5.
      obtain ⟨q2, hq2⟩ : ∃ q2 : ℕ, Nat.Prime q2 ∧ q2 ∣ A ∧ q2 > 5 := by
        apply exists_prime_gt_five;
        · rw [ Nat.odd_add, Nat.odd_sub ] <;> norm_num [ Nat.even_pow ];
          · grind;
          · exact pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith );
        · tauto;
        · assumption;
        · linarith;
      use q1, q2;
      exact ⟨ hq1.left, hq2.left, fun h => by have := Nat.dvd_gcd ( hq2.right.left ) ( h.symm ▸ hq1.right.left.trans ( Nat.div_dvd_of_dvd ( show 5 ∣ B from h_divisibility.right.right.elim ( fun h => by tauto ) fun h => by tauto ) ) ) ; aesop, hq1.right.right, hq2.right.right, hN.symm ▸ dvd_mul_of_dvd_right ( hq1.right.left.trans ( Nat.div_dvd_of_dvd ( show 5 ∣ B from h_divisibility.right.right.elim ( fun h => by tauto ) fun h => by tauto ) ) ) _, hN.symm ▸ dvd_mul_of_dvd_left hq2.right.left _ ⟩

/-
Let $p>5$ be a prime, let $N=2^{2p}+1$, and let $q>5$ be a prime divisor of $N$. Then $\ord_q(2)=4p$.
-/
lemma order_4p {p q : ℕ} (hp : p.Prime) (hp5 : p > 5) (hq : q.Prime) (hq5 : q > 5) (h_div : q ∣ 2^(2*p) + 1) :
  orderOf (2 : ZMod q) = 4 * p := by
    refine' orderOf_eq_of_pow_and_pow_div_prime _ _ _;
    · linarith;
    · haveI := Fact.mk hq; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, pow_mul' ] ;
      linear_combination' h_div * ( ( 2 ^ p ) ^ 2 - 1 );
    · intro r hr hr' hr''; haveI := Fact.mk hq; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
      -- Since $r$ is a prime divisor of $4p$, and $p$ is prime and greater than 5, $r$ must be 2 � or� $p$.
      have hr_cases : r = 2 ∨ r = p := by
        have hr_cases : r ∣ 4 * p := by
          simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
        rw [ Nat.Prime.dvd_mul hr ] at hr_cases;
        exact Or.imp ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; interval_cases r <;> trivial ) ( fun h => by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto ) hr_cases;
      rcases hr_cases with ( rfl | rfl ) <;> simp_all +decide [ pow_mul' ];
      · norm_num [ show 4 * p / 2 = 2 * p by rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; ring ] at hr'' ; simp_all +decide [ pow_mul', pow_two ];
        rcases q with ( _ | _ | _ | q ) <;> cases h_div <;> contradiction;
      · norm_num [ hp.ne_zero ] at hr'';
        rcases q with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q ) <;> cases hr'' <;> contradiction

/-
For every prime $p > 5$, there exists a prime $q$ such that $\{2, q\}$ is a strange pair and $\ord_q(2) = 4p$.
-/
lemma exists_strange_q_for_p {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  ∃ q, StrangePair 2 q ∧ orderOf (2 : ZMod q) = 4 * p := by
    obtain ⟨ q1, q2, hq1, hq2, hne, hgt1, hgt2, hdvd1, hdvd2 ⟩ := two_large_primes hp hp5; simp_all +decide
    -- By `order_4p`, $\ord_{q_1}(2) = 4p$ and $\ord_{q_2}(2) = 4p$.
    have h_order_q1 : orderOf (2 : ZMod q1) = 4 * p := by
      apply order_4p hp hp5 hq1 hgt1 hdvd1
    have h_order_q2 : orderOf (2 : ZMod q2) = 4 * p := by
      convert order_4p hp hp5 hq2 hgt2 hdvd2 using 1;
    cases lt_or_gt_of_ne hne <;> [ exact ⟨ q1, equal_order_strange hq1 hq2 ( by linarith ) ( by linarith ) ( by aesop ), h_order_q1 ⟩ ; exact ⟨ q2, equal_order_strange hq2 hq1 ( by linarith ) ( by linarith ) ( by aesop ), h_order_q2 ⟩ ]

/-
There are infinitely many primes $q$ such that $\{2, q\}$ is a strange pair.
-/
theorem infinite_strange_pairs : { q | StrangePair 2 q }.Infinite := by
  -- The set of primes is infinite, and the set of primes greater than 5 is also infinite. Therefore, the image of this set under an injective function is also infinite.
  have h_infinite_primes_gt_5 : Set.Infinite {n : ℕ | n.Prime ∧ n > 5} := by
    exact Set.Infinite.mono ( by aesop_cat ) ( Nat.infinite_setOf_prime.diff ( Set.finite_le_nat 5 ) );
  rw [ Set.infinite_iff_exists_gt ] at *;
  -- For any prime $p > 5$, we can find a prime $ �q�$ such that $\{2, q\}$ is a strange pair and $\ord_q(2) = 4p$.
  have h_exists_q : ∀ p : ℕ, Nat.Prime p → 5 < p → ∃ q : ℕ, StrangePair 2 q ∧ orderOf (2 : ZMod q) = 4 * p ∧ q > p := by
    intro p hp hp5
    obtain ⟨q, hq⟩ := exists_strange_q_for_p hp hp5
    use q;
    -- Since $q$ divides $2^{4p} - 1$, the order of $2$ modulo $q$ must divide $q - 1$.
    have h_div : orderOf (2 : ZMod q) ∣ q - 1 := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      haveI := Fact.mk hq.1.2.1; simpa [ ← ZMod.natCast_eq_zero_iff ] using ZMod.pow_card_sub_one_eq_one ( by intro h; simp_all +decide ) ;
    rcases q with ( _ | _ | q ) <;> simp_all +decide;
    · exact absurd hq.1.2.1 ( by norm_num );
    · cases hq.1.2.1 ; contradiction;
    · linarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) h_div ];
  exact fun a => by obtain ⟨ p, hp₁, hp₂ ⟩ := h_infinite_primes_gt_5 a; obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := h_exists_q p hp₁.left hp₁.right; exact ⟨ q, hq₁, by linarith ⟩ ;

end Erdos649
