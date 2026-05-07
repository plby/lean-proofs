/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
For integers $2 ≤ i < j ≤ n/2$ we aim to show that the greatest common divisor of $\binom{n}{i}$ and $\binom{n}{j}$ is strictly greater than $\frac{2^i\sqrt{n}}{4i\sqrt{i-1}}$, solving Erdős problem #698 (see https://www.erdosproblems.com/698). The proof of this lower bound (with a slightly worse constant) was found by Bergman;

Bergman, George M., On common divisors of multinomial coefficients. Bull. Aust. Math. Soc. (2011), 138--157

I (Wouter van Doorn) rewrote his proof a little bit, and gave it to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun). Aristotle then formalized it in Lean, after which only minor changes were required to make sure it fully compiles.

-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.multiGoal false
set_option maxHeartbeats 0

namespace Erdos698

/-
Let $Q_h = \binom{n}{i} \binom{i}{h} \binom{n-i}{j-i+h}$. Then $Q_h \cdot h! (i-h)! (j-i+h)! (n-j-h)! = n!$.
-/
def Q (n i j h : ℕ) : ℕ := Nat.choose n i * Nat.choose i h * Nat.choose (n - i) (j - i + h)

theorem Q_mul_factorials (n i j h : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (hhi : h ≤ i) (hhj : j - i + h ≤ n - i) :
    Q n i j h * (Nat.factorial h * Nat.factorial (i - h) * Nat.factorial (j - i + h) * Nat.factorial (n - j - h)) = Nat.factorial n := by
      simp_all +arith +decide [ Q, Nat.choose_eq_factorial_div_factorial ];
      rw [ ← Nat.choose_mul_factorial_mul_factorial ( show i ≤ n by linarith ) ];
      rw [ show n - j - h = n - i - ( h + ( j - i ) ) by omega ];
      simp +decide [ ← mul_assoc, ← Nat.choose_mul_factorial_mul_factorial ( show h ≤ i by linarith ), ← Nat.choose_mul_factorial_mul_factorial ( show h + ( j - i ) ≤ n - i by linarith ) ];
      simp +decide [mul_assoc, mul_comm, mul_left_comm, Nat.factorial_ne_zero]

/-
Let $Q_h = \binom{n}{i} \binom{i}{h} \binom{n-i}{j-i+h}$. Then $Q_h = \binom{n}{j} \binom{j}{i-h} \binom{n-j}{h}$.
-/
theorem Q_eq (n i j h : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (hhi : h ≤ i) (hhj : j - i + h ≤ n - i) :
    Q n i j h = Nat.choose n j * Nat.choose j (i - h) * Nat.choose (n - j) h := by
      -- We have established that $Q \cdot h! (i-h)! (j-i+h)! (n-j-h)! = n!$.
      have eq1 : Q n i j h * (Nat.factorial h * Nat.factorial (i - h) * Nat.factorial (j - i + h) * Nat.factorial (n - j - h)) = Nat.factorial n := by
        exact Q_mul_factorials n i j h hij hjn hhi hhj;
      -- Now we show that the RHS also satisfies this:
      have eq2 : Nat.choose n j * Nat.choose j (i - h) * Nat.choose (n - j) h * (Nat.factorial h * Nat.factorial (i - h) * Nat.factorial (j - i + h) * Nat.factorial (n - j - h)) = Nat.factorial n := by
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( by linarith : j ≤ n ), ← Nat.choose_mul_factorial_mul_factorial ( by omega : i - h ≤ j ) ] ; ring_nf;
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( show h ≤ n - j from by omega ), ← Nat.choose_mul_factorial_mul_factorial ( show j - i + h ≤ j - ( i - h ) from by omega ) ] ; ring_nf;
        simp +decide [ show j - ( i - h ) = j - i + h by omega ];
      nlinarith [ Nat.factorial_pos h, Nat.factorial_pos ( i - h ), Nat.factorial_pos ( j - i + h ), Nat.factorial_pos ( n - j - h ), mul_pos ( mul_pos ( mul_pos ( Nat.factorial_pos h ) ( Nat.factorial_pos ( i - h ) ) ) ( Nat.factorial_pos ( j - i + h ) ) ) ( Nat.factorial_pos ( n - j - h ) ) ]

/-
$L = \text{lcm}(\binom{n}{i}, \binom{n}{j})$ divides $Q_h$.
-/
theorem L_dvd_Q (n i j h : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (hhi : h ≤ i) (hhj : j - i + h ≤ n - i) :
    Nat.lcm (Nat.choose n i) (Nat.choose n j) ∣ Q n i j h := by
      refine' Nat.lcm_dvd _ _;
      · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
      · exact ⟨ Nat.choose j ( i - h ) * Nat.choose ( n - j ) h, by rw [ Q_eq n i j h hij hjn hhi hhj ] ; ring ⟩

/-
The linear combination $(i-1)Q_1^2 - 2iQ_0Q_2$ is divisible by $L^2$.
-/
def linear_comb (n i j : ℕ) : ℤ :=
  (i - 1 : ℤ) * (Q n i j 1 : ℤ)^2 - 2 * i * (Q n i j 0 : ℤ) * (Q n i j 2 : ℤ)

theorem L_sq_dvd_linear_comb (n i j : ℕ) (h2 : 2 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) (hhj : j - i + 2 ≤ n - i) :
    (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℤ)^2 ∣ linear_comb n i j := by
      -- Since $L$ divides $Q_0$, $Q_1$, and $Q_2$, we have $L^2$ divides $Q_1^2$ and $Q_0 Q_2$.
      have h_div_Q1_sq : (Nat.lcm (Nat.choose n i) (Nat.choose n j)) ^ 2 ∣ (Q n i j 1) ^ 2 := by
        exact pow_dvd_pow_of_dvd ( L_dvd_Q n i j 1 hij hjn ( by omega ) ( by omega ) ) 2
      have h_div_Q0Q2 : (Nat.lcm (Nat.choose n i) (Nat.choose n j)) ^ 2 ∣ (Q n i j 0) * (Q n i j 2) := by
        simpa only [ sq ] using mul_dvd_mul ( L_dvd_Q n i j 0 hij hjn ( by linarith ) ( by omega ) ) ( L_dvd_Q n i j 2 hij hjn ( by linarith ) ( by omega ) );
      exact dvd_sub ( dvd_mul_of_dvd_right ( mod_cast h_div_Q1_sq ) _ ) ( by convert Int.natCast_dvd_natCast.mpr ( h_div_Q0Q2.mul_left ( 2 * i ) ) using 1 ; push_cast ; ring )

/-
$Q_0 = \binom{n}{j} \binom{j}{i}$.
-/
theorem Q0_eq (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    Q n i j 0 = Nat.choose n j * Nat.choose j i := by
      -- By definition of $Q$, we have $Q n i j 0 = n.choose i * i.choose 0 * (n - i).choose (j - i)$.
      have hQ_def : Q n i j 0 = n.choose i * i.choose 0 * (n - i).choose (j - i) := by
        exact rfl;
      rw [ hQ_def, Nat.choose_mul ] <;> norm_num [ hij, hjn ];
      · rw [ ← Nat.choose_mul ] <;> omega;

/-
$Q_1 = \binom{n}{j} \binom{j}{i-1} (n-j)$.
-/
theorem Q1_eq (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (hi : 1 ≤ i) (hjn1 : 1 ≤ n - j) :
    Q n i j 1 = Nat.choose n j * Nat.choose j (i - 1) * (n - j) := by
      have h := Q_eq n i j 1 hij hjn ( by linarith ) ( by omega ) ; aesop;

/-
$Q_2 = \binom{n}{j} \binom{j}{i-2} \binom{n-j}{2}$.
-/
theorem Q2_eq (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) (hi : 2 ≤ i) (hjn2 : 2 ≤ n - j) :
    Q n i j 2 = Nat.choose n j * Nat.choose j (i - 2) * Nat.choose (n - j) 2 := by
      exact Q_eq n i j 2 ( by omega ) ( by omega ) ( by omega ) ( by omega )

/-
$(i-1)\binom{j}{i-1} = \binom{j}{i-2}(j-i+2)$.
-/
theorem binom_identity_1 (i j : ℕ) (h2 : 2 ≤ i) (hij : i ≤ j) :
    (i - 1 : ℤ) * Nat.choose j (i - 1) = (Nat.choose j (i - 2) : ℤ) * (j - i + 2) := by
      induction' h2 with i h2 ih <;> norm_num [ Nat.choose ] at *;
      rcases i with ( _ | _ | i ) <;> norm_num at *;
      nlinarith! [ Nat.succ_mul_choose_eq j ( i + 1 ), Nat.choose_succ_succ j ( i + 1 ), ih ( by linarith ) ]

/-
$i(i-1)\binom{j}{i} = \binom{j}{i-2}(j-i+2)(j-i+1)$.
-/
theorem binom_identity_2 (i j : ℕ) (h2 : 2 ≤ i) (hij : i ≤ j) :
    (i : ℤ) * (i - 1) * Nat.choose j i = (Nat.choose j (i - 2) : ℤ) * (j - i + 2) * (j - i + 1) := by
      rcases i with ( _ | _ | i ) <;> simp_all +decide;
      have := Nat.choose_succ_right_eq j i;
      have := Nat.choose_succ_right_eq j ( i + 1 );
      zify at *;
      grind

/-
$2\binom{n-j}{2} = (n-j)(n-j-1)$.
-/
theorem binom_identity_3 (n j : ℕ) (hjn : j ≤ n) :
    2 * (Nat.choose (n - j) 2 : ℤ) = (n - j : ℤ) * (n - j - 1) := by
      norm_num [ Nat.choose_two_right ];
      cases k : n - j <;> simp_all +decide;
      · omega;
      · nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( ↑‹ℕ› + 1 ) * ↑‹ℕ› from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ), Nat.sub_add_cancel hjn ]

/-
$(i-1) \cdot \text{linear\_comb} = \binom{n}{j}^2 \binom{j}{i-2}^2 (j-i+2)(n-j)(n-i+1)$.
-/
theorem linear_comb_eq (n i j : ℕ) (h2 : 2 ≤ i) (hij : i < j) (hjn : j ≤ n) :
    linear_comb n i j * (i - 1) =
    (Nat.choose n j : ℤ)^2 * (Nat.choose j (i - 2) : ℤ)^2 * (j - i + 2) * (n - j) * (n - i + 1) := by
      -- Substitute $Q_0, Q_1, Q_2$ and use the binomial identities.
      have h_sub : linear_comb n i j * (i - 1 : ℤ) = (i - 1 : ℤ)^2 * (Nat.choose n j * Nat.choose j (i - 1) * (n - j))^2 - 2 * i * (i - 1 : ℤ) * (Nat.choose n j * Nat.choose j i) * (Nat.choose n j * Nat.choose j (i - 2) * Nat.choose (n - j) 2) := by
        unfold linear_comb;
        rw [ show Q n i j 1 = Nat.choose n j * Nat.choose j ( i - 1 ) * ( n - j ) from ?_, show Q n i j 0 = Nat.choose n j * Nat.choose j i from ?_, show Q n i j 2 = Nat.choose n j * Nat.choose j ( i - 2 ) * Nat.choose ( n - j ) 2 from ?_ ] <;> norm_num [ Nat.choose_two_right ] ; ring_nf;
        · grind;
        · convert Q2_eq n i j hij.le hjn h2 using 1;
          rcases n' : n - j with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose_two_right ];
          · unfold Q; simp +decide ;
            exact Or.inr <| Nat.choose_eq_zero_of_lt <| by omega;
          · unfold Q; simp +decide [*] ;
            exact Or.inr <| Nat.choose_eq_zero_of_lt <| by omega;
        · exact Q0_eq n i j hij.le hjn;
        · -- By definition of $Q$, we have $Q n i j 1 = \binom{n}{i} \binom{i}{1} \binom{n-i}{j-i+1}$.
          have hQ1 : Q n i j 1 = Nat.choose n i * Nat.choose i 1 * Nat.choose (n - i) (j - i + 1) := by
            rfl;
          rcases n with ( _ | _ | n ) <;> rcases i with ( _ | _ | i ) <;> rcases j with ( _ | _ | j ) <;> simp_all +decide;
          rw [ Nat.choose_succ_right_eq ];
          rw [ Nat.choose_mul ];
          · simp +decide [ Nat.succ_sub ( by linarith : i ≤ j ), Nat.succ_sub ( by linarith : i ≤ n ), mul_assoc ];
            exact Or.inl ( by nlinarith only [ Nat.succ_mul_choose_eq ( n - i ) ( j - i ), Nat.choose_succ_succ ( n - i ) ( j - i ), Nat.sub_add_cancel ( show i ≤ n from by linarith ), Nat.sub_add_cancel ( show j ≤ n from by linarith ), Nat.sub_add_cancel ( show j ≥ i from by linarith ) ] );
          · linarith;
      -- Apply the binomial identities to simplify the expression.
      have h_binom_id : (i - 1 : ℤ) * Nat.choose j (i - 1) = Nat.choose j (i - 2) * (j - i + 2) ∧ (i : ℤ) * (i - 1) * Nat.choose j i = Nat.choose j (i - 2) * (j - i + 2) * (j - i + 1) ∧ 2 * (Nat.choose (n - j) 2 : ℤ) = (n - j : ℤ) * (n - j - 1) := by
        have := binom_identity_1 i j h2 hij.le; have := binom_identity_2 i j h2 hij.le; have := binom_identity_3 n j hjn; norm_num at *; aesop;
      linear_combination' h_sub + h_binom_id.1 * h_binom_id.1 * ( n.choose j ^ 2 * ( n - j ) ^ 2 ) - h_binom_id.2.1 * h_binom_id.2.2 * ( n.choose j ^ 2 * j.choose ( i - 2 ) )

/-
$(i-1)L^2 \le (i-1)\text{linear\_comb}$.
-/
theorem L_sq_le_linear_comb_mul_i_sub_1 (n i j : ℕ) (h2 : 2 ≤ i) (hij : i < j) (hjn : j ≤ n) (hhj : j - i + 2 ≤ n - i) :
    (i - 1 : ℤ) * (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℤ)^2 ≤ linear_comb n i j * (i - 1) := by
      rw [ mul_comm ];
      -- Since $L^2$ divides $\text{linear\_comb}$, we have $L^2 \leq \text{linear\_comb}$.
      have h_div : ((Nat.lcm (Nat.choose n i) (Nat.choose n j)) : ℤ)^2 ∣ linear_comb n i j := by
        convert L_sq_dvd_linear_comb n i j h2 hij.le hjn hhj using 1;
      refine' mul_le_mul_of_nonneg_right ( Int.le_of_dvd _ h_div ) ( by norm_num; linarith );
      have h_pos : (Nat.choose n j : ℤ)^2 * (Nat.choose j (i - 2) : ℤ)^2 * (j - i + 2) * (n - j) * (n - i + 1) > 0 := by
        exact mul_pos ( mul_pos ( mul_pos ( mul_pos ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by omega ) ) ) ) ) ( by linarith ) ) ( by omega ) ) ( by omega );
      exact lt_of_not_ge fun h => h_pos.not_ge <| by nlinarith [ linear_comb_eq n i j h2 hij hjn ] ;

/-
$\prod_{k=0}^{m-1} (j-k) \le (1/2)^m \prod_{k=0}^{m-1} (n-k)$.
-/
theorem product_le_pow_two (n j m : ℕ) (hjn : j ≤ n / 2) :
    (∏ k ∈ Finset.range m, (j - k : ℝ)) ≤ (1 / 2) ^ m * (∏ k ∈ Finset.range m, (n - k : ℝ)) := by
      induction' m with m ih <;> simp_all +decide [ Finset.prod_range_succ ];
      by_cases hm : m ≤ j;
      · refine le_trans ( mul_le_mul_of_nonneg_right ih ( sub_nonneg.mpr <| Nat.cast_le.mpr hm ) ) ?_;
        norm_num [ pow_succ, mul_assoc ];
        nlinarith only [ show ( 0 : ℝ ) ≤ ( 2 ^ m ) ⁻¹ * ( ∏ k ∈ Finset.range m, ( n - k : ℝ ) ) by exact mul_nonneg ( inv_nonneg.2 ( pow_nonneg zero_le_two _ ) ) ( Finset.prod_nonneg fun x hx => sub_nonneg.2 <| Nat.cast_le.2 <| by linarith [ Finset.mem_range.1 hx, Nat.div_mul_le_self n 2 ] ), show ( j : ℝ ) - m ≤ ( n - m ) / 2 by linarith [ show ( j : ℝ ) ≤ n / 2 by exact le_div_iff₀' zero_lt_two |>.2 <| by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ] ];
      · rw [ Finset.prod_eq_zero ( Finset.mem_range.mpr ( by linarith : j < m ) ) ] <;> norm_num;
        by_cases hm : m ≤ n;
        · exact mul_nonneg ( Finset.prod_nonneg fun x hx => sub_nonneg_of_le ( by norm_cast; linarith [ Finset.mem_range.mp hx ] ) ) ( sub_nonneg_of_le ( by norm_cast ) );
        · rw [ Finset.prod_eq_zero ( Finset.mem_range.mpr ( by linarith : n < m ) ) ] <;> norm_num

/-
$\binom{j}{i-2} \le \binom{n}{i-2} / 2^{i-2}$.
-/
theorem binom_le_binom_div_pow_two (n j i : ℕ) (h2 : 2 ≤ i) (hij : i ≤ j) (hjn : j ≤ n / 2) :
    (Nat.choose j (i - 2) : ℝ) ≤ (Nat.choose n (i - 2) : ℝ) / 2 ^ (i - 2) := by
      rw [ le_div_iff₀ ] <;> norm_cast <;> try positivity;
      -- By `product_le_pow_two` with $m=i-2$, we have $j^{\underline{i-2}} \le (1/2)^{i-2} n^{\underline{i-2}}$.
      have h_prod_le_pow_two : (∏ k ∈ Finset.range (i - 2), (j - k : ℝ)) ≤ (1 / 2) ^ (i - 2) * (∏ k ∈ Finset.range (i - 2), (n - k : ℝ)) := by
        exact product_le_pow_two n j (i - 2) hjn
      -- Recognize that $\prod_{k=0}^{i-3} (j-k) = \frac{j!}{(j-(i-2))!}$ and $\prod_{k=0}^{i-3} (n-k) = \frac{n!}{(n-(i-2))!}$.
      have h_prod_eq_factorial : (∏ k ∈ Finset.range (i - 2), (j - k : ℝ)) = (Nat.descFactorial j (i - 2) : ℝ) ∧ (∏ k ∈ Finset.range (i - 2), (n - k : ℝ)) = (Nat.descFactorial n (i - 2) : ℝ) := by
        norm_num [ Nat.descFactorial_eq_prod_range ];
        exact ⟨ Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel h2 ] ) ], Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel h2, Nat.div_mul_le_self n 2 ] ) ] ⟩;
      simp_all +decide [ Nat.descFactorial_eq_factorial_mul_choose ];
      rw [ inv_mul_eq_div, le_div_iff₀ ] at h_prod_le_pow_two <;> norm_cast at * <;> first | positivity | nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( i - 2 ), Nat.factorial_pos ( i - 2 ) ] ;

/-
$\binom{n}{i} = \binom{n}{i-2} \frac{(n-i+2)(n-i+1)}{i(i-1)}$.
-/
theorem binom_n_i_eq_binom_n_i_sub_2 (n i : ℕ) (h2 : 2 ≤ i) (hin : i ≤ n) :
    (Nat.choose n i : ℝ) = (Nat.choose n (i - 2) : ℝ) * ((n - i + 2) * (n - i + 1)) / (i * (i - 1)) := by
      -- By definition of binomial coefficients, we can write them as factorials.
      have h_factorial : (Nat.choose n i : ℝ) = Nat.factorial n / (Nat.factorial i * Nat.factorial (n - i)) ∧ (Nat.choose n (i - 2) : ℝ) = Nat.factorial n / (Nat.factorial (i - 2) * Nat.factorial (n - (i - 2))) := by
        exact ⟨ by rw [ Nat.cast_choose ] ; linarith, by rw [ Nat.cast_choose ] ; omega ⟩;
      rcases i with ( _ | _ | i ) <;> simp_all +decide [ Nat.factorial ];
      rw [ show n - i = ( n - ( i + 1 + 1 ) ) + 2 by omega ] ; norm_num [ Nat.factorial_succ ] ; ring_nf;
      field_simp;
      rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith only [ hin ]

/-
$(j-i+2)(n-j)n < (n-i+2)^2(n-i+1)$.
-/
theorem algebraic_inequality (n i j : ℕ) (h2 : 2 ≤ i) (hij : i < j) (hjn : j ≤ n / 2) :
    ((j - i + 2) * (n - j) * n : ℝ) < (n - i + 2)^2 * (n - i + 1) := by
      rw [ Nat.le_div_iff_mul_le ] at hjn <;> norm_num at *;
      norm_cast;
      rw [ Int.subNatNat_eq_coe, Int.subNatNat_eq_coe, Int.subNatNat_eq_coe ] ; nlinarith [ mul_le_mul_of_nonneg_left hij.le ( Nat.zero_le j ), mul_le_mul_of_nonneg_left hjn ( Nat.zero_le j ), mul_le_mul_of_nonneg_left hij.le ( Nat.zero_le n ), mul_le_mul_of_nonneg_left hjn ( Nat.zero_le n ) ]

/-
For all integers $i, j, n$ with $2 \le i < j \le \frac{n}{2}$ we have $$G := \gcd\left(\binom{n}{i}, \binom{n}{j} \right) > \frac{2^i\sqrt{n} }{4i\sqrt{i-1}}.$$
-/
theorem binomial_gcd_lower_bound (n i j : ℕ) (h2 : 2 ≤ i) (hij : i < j) (hjn : j ≤ n / 2) :
    (Nat.gcd (Nat.choose n i) (Nat.choose n j) : ℝ) > (2 ^ i * Real.sqrt n) / (4 * i * Real.sqrt (i - 1)) := by
      have h_sqrt : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℝ) < (Nat.choose n j * Nat.choose n i) * (4 * i * Real.sqrt (i - 1)) / (2 ^ i * Real.sqrt n) := by
        -- Using the inequality from linear_comb_eq and binom_le_binom_div_pow_two, we get:
        have h_ineq : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℝ) ^ 2 < (Nat.choose n j) ^ 2 * (Nat.choose n i) ^ 2 * (16 * i ^ 2 * (i - 1)) / (2 ^ (2 * i) * n) := by
          have h_sqrt : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℝ) ^ 2 ≤ (Nat.choose n j) ^ 2 * (Nat.choose n i) ^ 2 * (i ^ 2 * (i - 1)) * (j - i + 2) * (n - j) / (2 ^ (2 * i - 4) * (n - i + 2) ^ 2 * (n - i + 1)) := by
            have h_sqrt : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℝ) ^ 2 ≤ (Nat.choose n j) ^ 2 * (Nat.choose j (i - 2)) ^ 2 * (j - i + 2) * (n - j) * (n - i + 1) / (i - 1) := by
              have h_sqrt : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℝ) ^ 2 * (i - 1) ≤ (Nat.choose n j) ^ 2 * (Nat.choose j (i - 2)) ^ 2 * (j - i + 2) * (n - j) * (n - i + 1) := by
                have h_sqrt : (Nat.lcm (Nat.choose n i) (Nat.choose n j) : ℤ) ^ 2 * (i - 1) ≤ (Nat.choose n j : ℤ) ^ 2 * (Nat.choose j (i - 2) : ℤ) ^ 2 * (j - i + 2) * (n - j) * (n - i + 1) := by
                  convert L_sq_le_linear_comb_mul_i_sub_1 n i j h2 hij ( by linarith [ Nat.div_mul_le_self n 2 ] ) ( by omega ) using 1;
                  · ring;
                  · convert linear_comb_eq n i j h2 hij ( by linarith [ Nat.div_mul_le_self n 2 ] ) |> Eq.symm using 1;
                exact_mod_cast h_sqrt;
              rwa [ le_div_iff₀ ( by norm_num; linarith ) ];
            have h_sqrt : (Nat.choose j (i - 2) : ℝ) ^ 2 ≤ (Nat.choose n (i - 2) : ℝ) ^ 2 / (2 ^ (2 * i - 4)) := by
              have h_sqrt : (Nat.choose j (i - 2) : ℝ) ≤ (Nat.choose n (i - 2) : ℝ) / (2 ^ (i - 2)) := by
                convert binom_le_binom_div_pow_two n j i h2 ( by omega ) ( by omega ) using 1;
              convert pow_le_pow_left₀ ( Nat.cast_nonneg _ ) h_sqrt 2 using 1 ; ring_nf;
              rw [ tsub_mul ] ; ring_nf;
            have h_sqrt : (Nat.choose n i : ℝ) ^ 2 = (Nat.choose n (i - 2) : ℝ) ^ 2 * ((n - i + 2) * (n - i + 1)) ^ 2 / (i ^ 2 * (i - 1) ^ 2) := by
              have h_sqrt : (Nat.choose n i : ℝ) = (Nat.choose n (i - 2) : ℝ) * ((n - i + 2) * (n - i + 1)) / (i * (i - 1)) := by
                convert binom_n_i_eq_binom_n_i_sub_2 n i h2 ( by linarith [ Nat.div_mul_le_self n 2 ] ) using 1;
              rw [ h_sqrt, div_pow, mul_pow ];
              ring;
            refine le_trans ‹_› ?_;
            rw [ h_sqrt ];
            convert mul_le_mul_of_nonneg_right ‹ ( j.choose ( i - 2 ) : ℝ ) ^ 2 ≤ ( n.choose ( i - 2 ) : ℝ ) ^ 2 / 2 ^ ( 2 * i - 4 ) › ( show ( 0 :ℝ ) ≤ ( n.choose j :ℝ ) ^ 2 * ( ( j - i + 2 ) * ( n - j ) * ( n - i + 1 ) ) / ( i - 1 ) by exact div_nonneg ( mul_nonneg ( sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ( by linarith [ show ( i :ℝ ) < j by norm_cast ] ) ( by linarith [ show ( j :ℝ ) ≤ n / 2 by exact le_div_iff₀' ( by positivity ) |>.2 <| by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ] ) ) ( by linarith [ show ( i :ℝ ) < j by norm_cast, show ( j :ℝ ) ≤ n / 2 by exact le_div_iff₀' ( by positivity ) |>.2 <| by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ] ) ) ) ( by linarith [ show ( i :ℝ ) ≥ 2 by norm_cast ] ) ) using 1 ; ring;
            field_simp;
            rw [ div_eq_div_iff ] <;> nlinarith only [ show ( i : ℝ ) ≥ 2 by norm_cast, show ( j : ℝ ) ≥ i + 1 by norm_cast, show ( n : ℝ ) ≥ j * 2 by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ];
          -- Using the inequality from algebraic_inequality, we get:
          have h_ineq : (j - i + 2) * (n - j) < (n - i + 2) ^ 2 * (n - i + 1) / (n : ℝ) := by
            have h_ineq : ((j - i + 2) * (n - j) * n : ℝ) < (n - i + 2) ^ 2 * (n - i + 1) := by
              exact algebraic_inequality n i j h2 hij hjn;
            rw [ lt_div_iff₀ ] <;> norm_cast at * ; nlinarith [ Nat.div_mul_le_self n 2 ];
          refine lt_of_le_of_lt h_sqrt ?_;
          rw [ lt_div_iff₀ ] at *;
          · rw [ div_mul_eq_mul_div, div_lt_iff₀ ];
            · rcases i with ( _ | _ | _ | i ) <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
              · nlinarith [ show 0 < ( Nat.choose n j : ℝ ) * ( Nat.choose n j : ℝ ) * ( Nat.choose n 2 * Nat.choose n 2 : ℝ ) by exact mul_pos ( mul_pos ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) ) ( mul_pos ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) ) ];
              · convert mul_lt_mul_of_pos_left h_ineq ( show 0 < ( n.choose j : ℝ ) * ( n.choose j : ℝ ) * ( ( n.choose ( i + 1 + 1 + 1 ) : ℝ ) * ( n.choose ( i + 1 + 1 + 1 ) : ℝ ) ) * ( ( i + 1 + 1 + 1 ) * ( i + 1 + 1 + 1 ) * ( i + 1 + 1 ) ) * ( 2 * ( 2 * ( 2 * ( 2 * ( 2 * ( 2 * 2 ^ ( 2 * i ) ) ) ) ) ) ) by exact mul_pos ( mul_pos ( mul_pos ( mul_pos ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) <| Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) <| mul_pos ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) <| Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith [ Nat.div_mul_le_self n 2 ] ) <| by positivity ) <| by positivity ) using 1 ; ring;
                grind;
            · exact mul_pos ( mul_pos ( pow_pos ( by norm_num ) _ ) ( sq_pos_of_pos ( by linarith [ show ( i : ℝ ) < j by norm_cast, show ( j : ℝ ) ≤ n / 2 by exact le_div_iff₀' ( by norm_num ) |>.2 ( by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ) ] ) ) ) ( by linarith [ show ( i : ℝ ) < j by norm_cast, show ( j : ℝ ) ≤ n / 2 by exact le_div_iff₀' ( by norm_num ) |>.2 ( by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ) ] );
          · norm_cast ; linarith [ Nat.div_mul_le_self n 2 ];
          · exact mul_pos ( pow_pos ( by norm_num ) _ ) ( Nat.cast_pos.mpr ( by linarith [ Nat.div_mul_le_self n 2 ] ) );
        convert Real.lt_sqrt_of_sq_lt h_ineq using 1;
        rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> try positivity;
        · ring_nf;
          rw [ Real.sq_sqrt ( by linarith [ show ( i : ℝ ) ≥ 2 by norm_cast ] ) ] ; norm_num ; ring;
        · exact div_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) ) ( by positivity );
      rw [ lt_div_iff₀ ] at *;
      · rw [ gt_iff_lt, div_lt_iff₀ ];
        · contrapose! h_sqrt;
          convert mul_le_mul_of_nonneg_left h_sqrt ( Nat.cast_nonneg ( Nat.lcm ( Nat.choose n i ) ( Nat.choose n j ) ) ) using 1;
          norm_num [ ← mul_assoc, ← Nat.cast_mul, Nat.gcd_mul_lcm ];
          exact Or.inl <| Or.inl <| mul_comm _ _;
        · exact mul_pos ( by positivity ) ( Real.sqrt_pos.mpr ( by norm_num; linarith ) );
      · exact mul_pos ( by positivity ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith [ Nat.div_mul_le_self n 2 ] ) ) )

#print axioms binomial_gcd_lower_bound
-- 'Erdos698.binomial_gcd_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos698
