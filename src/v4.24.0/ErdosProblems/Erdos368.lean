/-

This is a Lean formalization of a solution to a small/weak part of
Erdős Problem 368.

https://www.erdosproblems.com/forum/thread/368

The original proof was found by: Pólya

[Po18] Pólya, Georg, Zur arithmetischen {U}ntersuchung der
{P}olynome. Math. Z. (1918), 143--148.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/
/-
I have formalized the main results of the provided paper.
Specifically, I have proved:
1. `pell_solution_unique_d_number`: Corresponding to Proposition 1(4), showing that among all solutions to the Pell equation, at most one has a y-coordinate that is a d-number, and if it exists, it is the fundamental solution.
2. `main_theorem`: Corresponding to Theorem 2, showing that the largest prime factor of n(n+1) tends to infinity as n tends to infinity.

I also proved several helper lemmas required for these results, including:
- `pell_p_ne_2`, `pell_p_ne_3`, `pell_p_ge_5_contradiction`: Handling the cases for prime divisors in the proof of Proposition 1(4).
- `c_p_eq_p`, `c_p_eq_sum`, `pell_y_div_y_sum_gt_term_zero`: Properties of the sequence c_p used in the proof.
- `bad_set_finite`, `unique_n_for_d`, `calc_d_mem_possible_ds`: Lemmas used to prove the main theorem by bounding the set of n with small prime factors.

The definitions and lemmas provided in the initial workspace (Lemma 1 and parts of Proposition 1) were assumed to be proved as per instructions.
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

#print axioms n_n_plus_one_inf
-- 'Erdos368.n_n_plus_one_inf' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos368
