/-

This is a Lean formalization of a solution to Erdős Problem 367.
https://www.erdosproblems.com/367

The original human proof was found by Wouter van Doorn and posted at
https://www.erdosproblems.com/forum/thread/367#post-1766

This proof follows an elaboration of the argument given by Terence
Tao with the assistance of Gemini Deepthink from Google DeepMind.

Aristotle from Harmonic auto-formalized the result from the LaTeX
source given in the next comment block.  Afterwards, the statement of
the Erdős problem was written, somewhat by hand, and Aristotle was
asked to finish off the proof.  This process was operated by Boris
Alexeev.

The proof is verified by Lean.  The exact version numbers below may be
necessary to type-check this proof.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

-/

/-

\documentclass{amsart}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\begin{document}
\begin{definition}
A positive integer $n$ is \emph{2-full} (or ``powerful'') if for every prime $p$ dividing $n$, $p^2$ also divides $n$.
\end{definition}
\begin{definition}
For a positive integer $n$, let $B_2(n)$ denote the \emph{$2$-full part} of $n$,
that is, the largest divisor $d$ of $n$ such that $d$ is powerful.
\end{definition}

1. Define $n_j = (\alpha^{2j} - 2 + \alpha^{-2j})/4$, where $\alpha = 3 +
\sqrt{8}$ (so $\alpha^{-1} = 3 - \sqrt{8}$).  Then
\begin{align*}
n_j &= 8 \times \left[\frac{\alpha^j - \alpha^{-j}}{2\sqrt{8}}\right]^2 \\
n_j+1 &= \left[\frac{\alpha^j + \alpha^{-j}}{2}\right]^2 \\
n_j+2 &= \frac{\alpha^{2j} + 6 + \alpha^{-2j}}{4}
\end{align*}
and both expressions in brackets integers (OEIS A001109 and A001541
respectively). In particular, $n_j$ is a natural number (OEIS A132592), with
$n_j, n_j+1$ already $2$-full.

2.  Observe the identity $\alpha^{\pm 3} = 99 \pm 35 \sqrt{8} = - 1 + 5
\times(20 \pm 7 \sqrt{8})$.

By induction one can show that $\alpha^{\pm 3 \times 5^{t-1}} = -1 + 5^t (a_t \pm b_t \sqrt{8})$ for various integers $a_t,b_t$ and
all $t \geq 1$.

Now we set $j_t :=(3 \times 5^{t-1}-1)/2$ (which is an integer) and compute
\begin{align*}
 4(n_{j_t}+2) &= \alpha^{-1} \alpha^{3 \times 5^{t-1}} + 6 + \alpha \alpha^{-3 \times 5^{t-1}} \\
&= (3-\sqrt{8}) (-1 + 5^t (a_t + b_t \sqrt{8})) + 6 + (3+\sqrt{8}) (-1 + 5^t (a_t - b_t \sqrt{8}))\\
&= 5^t (6 a_t - 16 b_t)
\end{align*}
giving the key claim $5^t | n_{j_t}+2$.  Thus for $t \geq 2$
$$ \prod_{n_{j_t} \leq m < n_{j_t}+3} B_2(m) \geq n_{j_t} (n_{j_t}+1) 5^t \gg n_{j_t}^2 \log n_{j_t}.$$
\end{document}

-/

import Mathlib

namespace Erdos367

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open scoped Classical

def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

noncomputable def powerfulPart (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.divisors.filter IsPowerful).max.getD 1

noncomputable def alpha : ℝ := 3 + Real.sqrt 8

noncomputable def n_real (j : ℕ) : ℝ := (alpha ^ (2 * j) - 2 + alpha ^ (-(2 * j : ℤ))) / 4

theorem n_real_is_nat (j : ℕ) : ∃ k : ℕ, n_real j = k := by
  -- Let's denote α = 3 + sqrt(8). Then α^(2j) is a number of the form a + b*sqrt(8) where a and b are integers.
  set α := 3 + Real.sqrt 8
  have h_alpha_pow : ∃ a b : ℕ, α^(2*j) = a + b * Real.sqrt 8 ∧ α^(-2*j : ℤ) = a - b * Real.sqrt 8 := by
    induction' j with j ih;
    · exact ⟨ 1, 0, by norm_num, by norm_num ⟩;
    · -- By the induction hypothesis, we have α^(2*j) = a + b*sqrt(8) and α^(-2*j) = a - b*sqrt(8).
      obtain ⟨a, b, ha, hb⟩ := ih;
      use 17 * a + 48 * b, 6 * a + 17 * b;
      aesop;
      · -- Now use the induction hypothesis to simplify the expression.
        have h_expand : (3 + Real.sqrt 8) ^ (2 * (j + 1)) = (a + b * Real.sqrt 8) * (17 + 6 * Real.sqrt 8) := by
          rw [ ← ha ] ; ring ; norm_num ; ring;
        exact h_expand.trans ( by ring_nf; norm_num ; ring );
      · convert congr_arg ( fun x : ℝ => x / ( 3 + Real.sqrt 8 ) ^ 2 ) hb using 1 <;> ring;
        · rw [ ← mul_inv ] ; norm_cast ; ring;
        · rw [ show ( Real.sqrt 8 ) ^ 2 = 8 by norm_num ] ; ring;
          nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), inv_mul_cancel_left₀ ( show ( 17 + Real.sqrt 8 * 6 ) ≠ 0 by positivity ) ( a : ℝ ), inv_mul_cancel_left₀ ( show ( 17 + Real.sqrt 8 * 6 ) ≠ 0 by positivity ) ( b : ℝ ) ];
  -- Substitute the expressions for α^(2j) and α^(-2j) into the formula for n_j.
  obtain ⟨a, b, ha, hb⟩ := h_alpha_pow
  have h_n_j : n_real j = (a - 1) / 2 := by
    -- Substitute the expressions for α^(2j) and α^(-2j) into the formula for n_real j and simplify.
    have h_n_j : n_real j = ((a + b * Real.sqrt 8) - 2 + (a - b * Real.sqrt 8)) / 4 := by
      -- Substitute the expressions for α^(2j) and α^(-2j) into the formula for n_real j and simplify using the definitions of ha and hb.
      rw [show n_real j = (α^(2*j) - 2 + α^(-2*j : ℤ)) / 4 from rfl]
      rw [ha, hb];
    -- Combine like terms in the numerator and simplify the expression.
    rw [h_n_j]
    ring;
  -- Since $a$ is odd, $(a - 1)$ is even, and thus $(a - 1) / 2$ is a natural number.
  have h_a_odd : Odd a := by
    -- From the equation $a^2 - 8b^2 = 1$, we know that $a$ must be odd.
    have h_a_odd : a^2 = 8 * b^2 + 1 := by
      have h_eq : (a + b * Real.sqrt 8) * (a - b * Real.sqrt 8) = 1 := by
        rw [ ← ha, ← hb ] ; group ; norm_num;
        exact mul_inv_cancel₀ ( by positivity );
      exact_mod_cast ( by ring_nf at h_eq; norm_num at h_eq; linarith : ( a : ℝ ) ^ 2 = 8 * b ^ 2 + 1 );
    simpa [ parity_simps ] using congr_arg Even h_a_odd;
  obtain ⟨ k, rfl ⟩ := h_a_odd; exact ⟨ k, by push_cast [ h_n_j ] ; ring ⟩ ;

noncomputable def n_nat (j : ℕ) : ℕ := (n_real_is_nat j).choose

theorem n_nat_eq_n_real (j : ℕ) : (n_nat j : ℝ) = n_real j := (n_real_is_nat j).choose_spec.symm

def x_j (j : ℕ) : ℕ := Pell.xn (show 1 < 3 by norm_num) j
def y_j (j : ℕ) : ℕ := Pell.yn (show 1 < 3 by norm_num) j

theorem n_nat_eq_8_y_sq (j : ℕ) : n_nat j = 8 * (y_j j)^2 := by
  -- By definition of $n_real$, we know that $n_real j = 8 * y_j j^2$.
  have h_n_real : n_real j = 8 * y_j j ^ 2 := by
    -- By definition of $x_j$ and $y_j$, we know that $x_j + y_j \sqrt{8} = \alpha^j$ and $x_j - y_j \sqrt{8} = \alpha^{-j}$.
    have h_alpha : (x_j j : ℝ) + y_j j * Real.sqrt 8 = alpha ^ j ∧ (x_j j : ℝ) - y_j j * Real.sqrt 8 = alpha ^ (-j : ℤ) := by
      -- By definition of $x_j$ and $y_j$, we know that $(3 + \sqrt{8})^j = x_j + y_j \sqrt{8}$ and $(3 - \sqrt{8})^j = x_j - y_j \sqrt{8}$.
      have h_pell : ∀ j : ℕ, (3 + Real.sqrt 8) ^ j = x_j j + y_j j * Real.sqrt 8 ∧ (3 - Real.sqrt 8) ^ j = x_j j - y_j j * Real.sqrt 8 := by
        intro j; induction j <;> simp_all +decide [ pow_succ, Pell.xn_succ, Pell.yn_succ ] ; ring_nf ;
        · unfold x_j y_j; norm_num;
        · unfold x_j y_j; norm_num [ pow_succ' ] ; ring_nf ; norm_num;
          exact Or.inl rfl;
      unfold alpha; aesop;
      exact eq_inv_of_mul_eq_one_right ( by rw [ ← h_pell j |>.1, ← h_pell j |>.2 ] ; rw [ ← mul_pow ] ; ring_nf; norm_num );
    -- By squaring the equations from h_alpha and adding them, we can eliminate the cross terms and solve for alpha^(2j) + alpha^(-2j).
    have h_sq : (x_j j : ℝ)^2 + 2 * x_j j * y_j j * Real.sqrt 8 + 8 * y_j j^2 = alpha^(2 * j) ∧ (x_j j : ℝ)^2 - 2 * x_j j * y_j j * Real.sqrt 8 + 8 * y_j j^2 = alpha^(-2 * j : ℤ) := by
      convert And.intro ( congr_arg ( · ^ 2 ) h_alpha.1 ) ( congr_arg ( · ^ 2 ) h_alpha.2 ) using 1 <;> ring <;> norm_num [ pow_mul' ];
      norm_cast ; ring;
    unfold n_real;
    have h_pell : (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 = 1 := by
      have h_pell : (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 = (x_j j + y_j j * Real.sqrt 8) * (x_j j - y_j j * Real.sqrt 8) := by
        ring ; norm_num;
      aesop;
      exact mul_inv_cancel₀ ( by exact ne_of_gt ( pow_pos ( show 0 < alpha by exact add_pos_of_pos_of_nonneg zero_lt_three ( Real.sqrt_nonneg _ ) ) _ ) );
    norm_num [ zpow_mul ] at * ; linarith;
  exact_mod_cast n_nat_eq_n_real j ▸ h_n_real

theorem n_nat_succ_eq_x_sq (j : ℕ) : n_nat j + 1 = (x_j j)^2 := by
  -- By definition of $n_nat$, we know that $n_nat j = 8 * y_j j^2$.
  have h_n_nat_def : n_nat j = 8 * y_j j^2 := by
    -- By definition of $n_real$, we know that $n_real j = 8 * y_j j^2$.
    have h_n_real : n_real j = 8 * y_j j ^ 2 := by
      -- By definition of $x_j$ and $y_j$, we know that $x_j + y_j \sqrt{8} = \alpha^j$ and $x_j - y_j \sqrt{8} = \alpha^{-j}$.
      have h_alpha : (x_j j : ℝ) + y_j j * Real.sqrt 8 = alpha ^ j ∧ (x_j j : ℝ) - y_j j * Real.sqrt 8 = alpha ^ (-j : ℤ) := by
        -- By definition of $x_j$ and $y_j$, we know that $(3 + \sqrt{8})^j = x_j + y_j \sqrt{8}$ and $(3 - \sqrt{8})^j = x_j - y_j \sqrt{8}$.
        have h_pell : ∀ j : ℕ, (3 + Real.sqrt 8) ^ j = x_j j + y_j j * Real.sqrt 8 ∧ (3 - Real.sqrt 8) ^ j = x_j j - y_j j * Real.sqrt 8 := by
          intro j; induction j <;> simp_all +decide [ pow_succ, Pell.xn_succ, Pell.yn_succ ] ; ring_nf ;
          · unfold x_j y_j; norm_num;
          · unfold x_j y_j; norm_num [ pow_succ' ] ; ring_nf ; norm_num;
            exact Or.inl rfl;
        unfold alpha; aesop;
        exact eq_inv_of_mul_eq_one_right ( by rw [ ← h_pell j |>.1, ← h_pell j |>.2 ] ; rw [ ← mul_pow ] ; ring_nf; norm_num );
      -- By squaring the equations from h_alpha and adding them, we can eliminate the cross terms and solve for alpha^(2j) + alpha^(-2j).
      have h_sq : (x_j j : ℝ)^2 + 2 * x_j j * y_j j * Real.sqrt 8 + 8 * y_j j^2 = alpha^(2 * j) ∧ (x_j j : ℝ)^2 - 2 * x_j j * y_j j * Real.sqrt 8 + 8 * y_j j^2 = alpha^(-2 * j : ℤ) := by
        convert And.intro ( congr_arg ( · ^ 2 ) h_alpha.1 ) ( congr_arg ( · ^ 2 ) h_alpha.2 ) using 1 <;> ring <;> norm_num [ pow_mul' ];
        norm_cast ; ring;
      unfold n_real;
      have h_pell : (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 = 1 := by
        have h_pell : (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 = (x_j j + y_j j * Real.sqrt 8) * (x_j j - y_j j * Real.sqrt 8) := by
          ring ; norm_num;
        aesop;
        exact mul_inv_cancel₀ ( by exact ne_of_gt ( pow_pos ( show 0 < alpha by exact add_pos_of_pos_of_nonneg zero_lt_three ( Real.sqrt_nonneg _ ) ) _ ) );
      norm_num [ zpow_mul ] at * ; linarith;
    exact_mod_cast n_nat_eq_n_real j ▸ h_n_real;
  -- By definition of $x_j$ and $y_j$, we know that $x_j^2 - 8 * y_j^2 = 1$.
  have h_pell : x_j j ^ 2 - 8 * y_j j ^ 2 = 1 := by
    -- By definition of $x_j$ and $y_j$, we know that $x_j^2 - 8y_j^2 = 1$ follows directly from the Pell equation.
    have h_pell : ∀ j, x_j j ^ 2 - 8 * y_j j ^ 2 = 1 := by
      intro j;
      -- We can prove this by induction on $j$.
      induction' j with j ih;
      · native_decide +revert;
      · rw [ Nat.sub_eq_of_eq_add ];
        rw [ Nat.sub_eq_iff_eq_add ] at ih;
        · rw [ show x_j ( j + 1 ) = x_j j * 3 + 8 * y_j j from rfl, show y_j ( j + 1 ) = x_j j + y_j j * 3 from rfl ] ; linarith;
        · exact le_of_lt ( Nat.lt_of_sub_eq_succ ih );
    exact h_pell j;
  linarith [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_eq_succ h_pell ) ) ]

theorem n_nat_is_powerful (j : ℕ) : IsPowerful (n_nat j) := by
  -- By definition of $n_j$, we know that $n_j = 8 * y_j^2$ and $n_j + 1 = x_j^2$, where $x_j$ and $y_j$ are the solutions to the Pell equation. Therefore, $n_j$ is powerful because it is a product of squares and cubes.
  have h_pell : n_nat j = 8 * (Nat.sqrt (n_nat j / 8))^2 := by
    -- By definition of $n_j$, we know that $n_j = 8 * y_j^2$, where $y_j$ is the $j$-th solution to the Pell equation.
    have h_pell : ∃ y : ℕ, n_nat j = 8 * y^2 := by
      have h_pell : ∃ x y : ℕ, n_nat j = 8 * y^2 ∧ x^2 - 8 * y^2 = 1 := by
        have h_pell_eq : ∃ x y : ℕ, n_real j = 8 * y^2 ∧ x^2 - 8 * y^2 = 1 := by
          -- By definition of $n_real$, we know that $n_real j = 8 * y_j^2$ and $x_j^2 - 8 * y_j^2 = 1$.
          obtain ⟨x, y, hx⟩ : ∃ x y : ℕ, (x + y * Real.sqrt 8) = (3 + Real.sqrt 8) ^ j ∧ (x - y * Real.sqrt 8) = (3 - Real.sqrt 8) ^ j := by
            induction j <;> aesop;
            · exact ⟨ 1, 0, by norm_num, by norm_num ⟩;
            · exact ⟨ w * 3 + w_1 * 8, w + w_1 * 3, by push_cast [ pow_succ' ] ; rw [ ← left ] ; ring_nf ; norm_num ; ring_nf, by push_cast [ pow_succ' ] ; rw [ ← right ] ; ring_nf ; norm_num ; ring_nf ⟩;
          -- By definition of $n_real$, we know that $n_real j = \frac{(3 + \sqrt{8})^{2j} - 2 + (3 - \sqrt{8})^{2j}}{4}$.
          have h_n_real : n_real j = ((x + y * Real.sqrt 8) ^ 2 - 2 + (x - y * Real.sqrt 8) ^ 2) / 4 := by
            unfold n_real; aesop;
            unfold alpha; norm_cast; norm_num [ pow_mul' ] ; ring;
            simp +zetaDelta at *;
            rw [ ← inv_pow, inv_eq_of_mul_eq_one_right ] ; ring ; norm_num;
          bound;
          -- By definition of $x$ and $y$, we know that $x^2 - 8y^2 = 1$.
          have h_pell : x^2 - 8 * y^2 = 1 := by
            have h_pell : (x + y * Real.sqrt 8) * (x - y * Real.sqrt 8) = 1 := by
              rw [ left, right ] ; rw [ ← mul_pow ] ; ring ; norm_num;
            exact Nat.sub_eq_of_eq_add <| by rw [ ← @Nat.cast_inj ℝ ] ; push_cast; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 8 by norm_num ) ] ;
          exact ⟨ x, y, by rw [ h_n_real ] ; rw [ Nat.sub_eq_iff_eq_add <| Nat.le_of_lt <| Nat.lt_of_sub_eq_succ h_pell ] at h_pell; push_cast [ ← @Nat.cast_inj ℝ .. ] at *; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 8 by norm_num ) ], h_pell ⟩
        obtain ⟨ x, y, hx, hy ⟩ := h_pell_eq; use x, y; aesop;
        exact_mod_cast n_nat_eq_n_real j ▸ hx;
      aesop;
    aesop;
    norm_num [ sq ];
    norm_num [ Nat.sqrt_eq ];
  -- Since $8 = 2^3$ and $(Nat.sqrt (n_nat j / 8))^2$ is a square, their product is powerful.
  have h_powerful : IsPowerful (8 * (Nat.sqrt (n_nat j / 8))^2) := by
    intro p pp dp; norm_num [ Nat.Prime.dvd_mul pp ] at dp ⊢;
    bound;
    · have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> norm_num at *;
      exact dvd_mul_of_dvd_left ( by decide ) _;
    · exact dvd_mul_of_dvd_right ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow h_1 ) 2 ) _;
  exact h_pell ▸ h_powerful

theorem n_nat_succ_is_powerful (j : ℕ) : IsPowerful (n_nat j + 1) := by
  -- By definition of $n_j$, we know that $n_j + 1 = x_j^2$, where $x_j$ is the j-th solution to the Pell equation $x^2 - 8y^2 = 1$.
  have h_pell : ∃ x y : ℕ, n_nat j + 1 = x^2 ∧ x^2 - 8 * y^2 = 1 := by
    -- By definition of $n_j$, we know that $n_j = 8 * y_j^2$ and $n_j + 1 = x_j^2$, where $x_j$ and $y_j$ are solutions to the Pell equation $x^2 - 8y^2 = 1$. Use this fact.
    obtain ⟨x, y, hx⟩ : ∃ x y : ℕ, n_real j = 8 * y^2 ∧ x^2 - 8 * y^2 = 1 := by
      -- By definition of $n_real$, we know that $n_real j = 8 * y_j^2$ and $x_j^2 - 8 * y_j^2 = 1$.
      obtain ⟨x, y, hx⟩ : ∃ x y : ℕ, (x + y * Real.sqrt 8) = (3 + Real.sqrt 8) ^ j ∧ (x - y * Real.sqrt 8) = (3 - Real.sqrt 8) ^ j := by
        induction j <;> aesop;
        · exact ⟨ 1, 0, by norm_num, by norm_num ⟩;
        · exact ⟨ w * 3 + w_1 * 8, w + w_1 * 3, by push_cast [ pow_succ' ] ; rw [ ← left ] ; ring_nf ; norm_num ; ring_nf, by push_cast [ pow_succ' ] ; rw [ ← right ] ; ring_nf ; norm_num ; ring_nf ⟩;
      -- By definition of $n_real$, we know that $n_real j = \frac{(3 + \sqrt{8})^{2j} - 2 + (3 - \sqrt{8})^{2j}}{4}$.
      have h_n_real : n_real j = ((x + y * Real.sqrt 8) ^ 2 - 2 + (x - y * Real.sqrt 8) ^ 2) / 4 := by
        unfold n_real; aesop;
        unfold alpha; norm_cast; norm_num [ pow_mul' ] ; ring;
        simp +zetaDelta at *;
        rw [ ← inv_pow, inv_eq_of_mul_eq_one_right ] ; ring ; norm_num;
      bound;
      -- By definition of $x$ and $y$, we know that $x^2 - 8y^2 = 1$.
      have h_pell : x^2 - 8 * y^2 = 1 := by
        have h_pell : (x + y * Real.sqrt 8) * (x - y * Real.sqrt 8) = 1 := by
          rw [ left, right ] ; rw [ ← mul_pow ] ; ring ; norm_num;
        exact Nat.sub_eq_of_eq_add <| by rw [ ← @Nat.cast_inj ℝ ] ; push_cast; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 8 by norm_num ) ] ;
      exact ⟨ x, y, by rw [ h_n_real ] ; rw [ Nat.sub_eq_iff_eq_add <| Nat.le_of_lt <| Nat.lt_of_sub_eq_succ h_pell ] at h_pell; push_cast [ ← @Nat.cast_inj ℝ .. ] at *; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 8 by norm_num ) ], h_pell ⟩;
    use x, y;
    rw [ Nat.sub_eq_iff_eq_add ] at hx <;> aesop;
    · linarith [ show n_nat j = 8 * y ^ 2 from by exact_mod_cast n_nat_eq_n_real j ▸ left ];
    · exact le_of_lt ( Nat.lt_of_sub_eq_succ right );
  aesop;
  exact fun p pp dp => by exact pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2;


def j_t (t : ℕ) : ℕ := (3 * 5^(t-1) - 1) / 2

theorem j_t_well_defined (t : ℕ) : 2 ∣ 3 * 5^(t-1) - 1 := by
  norm_num [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ]

theorem alpha_pow_K_t (t : ℕ) (ht : t ≥ 1) :
  ∃ a b : ℤ, alpha ^ (3 * 5^(t-1)) = -1 + 5^t * (a + b * Real.sqrt 8) ∧
             (3 - Real.sqrt 8) ^ (3 * 5^(t-1)) = -1 + 5^t * (a - b * Real.sqrt 8) := by
               -- By the binomial theorem, we can expand $(3 + \sqrt{8})^{3 \cdot 5^{t-1}}$ and $(3 - \sqrt{8})^{3 \cdot 5^{t-1}}$ into sums of terms involving $\sqrt{8}$.
               have h_binom : ∃ a b : ℤ, (3 + Real.sqrt 8)^(3 * 5^(t-1)) = a + b * Real.sqrt 8 ∧ (3 - Real.sqrt 8)^(3 * 5^(t-1)) = a - b * Real.sqrt 8 := by
                 induction' 3 * 5 ^ ( t - 1 ) <;> aesop;
                 · exact ⟨ 1, 0, by norm_num, by norm_num ⟩;
                 · exact ⟨ w * 3 + w_1 * 8, w + w_1 * 3, by push_cast [ pow_succ' ] ; rw [ left ] ; ring_nf ; norm_num ; ring_nf, by push_cast [ pow_succ' ] ; rw [ right ] ; ring_nf ; norm_num ; ring_nf ⟩;
               unfold alpha;
               -- We'll use that $a$ and $b$ are integers to show that $5^t$ divides $a + 1$ and $b$.
               have h_div : 5 ^ t ∣ (h_binom.choose + 1) ∧ 5 ^ t ∣ h_binom.choose_spec.choose := by
                 -- We'll use induction to prove that the coefficients $a$ and $b$ satisfy the divisibility conditions.
                 have h_ind : ∀ t : ℕ, 1 ≤ t → ∃ a b : ℤ, (3 + Real.sqrt 8)^(3 * 5^(t-1)) = a + b * Real.sqrt 8 ∧ (3 - Real.sqrt 8)^(3 * 5^(t-1)) = a - b * Real.sqrt 8 ∧ 5 ^ t ∣ (a + 1) ∧ 5 ^ t ∣ b := by
                   -- We proceed by induction on $t$.
                   intro t ht
                   induction' ht with t ih;
                   · norm_num [ show ( 3 + Real.sqrt 8 ) ^ 3 = ( 3 + Real.sqrt 8 ) * ( 3 + Real.sqrt 8 ) * ( 3 + Real.sqrt 8 ) by ring, show ( 3 - Real.sqrt 8 ) ^ 3 = ( 3 - Real.sqrt 8 ) * ( 3 - Real.sqrt 8 ) * ( 3 - Real.sqrt 8 ) by ring ] ; ring_nf ; norm_num;
                     exact ⟨ 27 + 72, 27 + 8, by norm_num [ pow_three ] ; ring, by norm_num [ pow_three ] ; ring, by norm_num, by norm_num ⟩;
                   · rcases t <;> simp_all +decide [ pow_succ, pow_mul ];
                     -- By the induction hypothesis, we know that $a + 1$ and $b$ are divisible by $5^n$. We need to show that $a'^5 + 1$ and $b'$ are divisible by $5^{n+1}$.
                     obtain ⟨a, b, ha, hb, ha_div, hb_div⟩ := ‹∃ a b : ℤ, _›;
                     use a^5 + 10 * a^3 * b^2 * 8 + 5 * a * b^4 * 8^2, 5 * a^4 * b + 10 * a^2 * b^3 * 8 + b^5 * 8^2;
                     aesop;
                     · rw [ ← left_1 ] ; ring ; norm_num [ pow_three ] ; ring;
                       rw [ show ( Real.sqrt 8 ) ^ 4 = ( Real.sqrt 8 ^ 2 ) ^ 2 by ring, show ( Real.sqrt 8 ) ^ 5 = ( Real.sqrt 8 ^ 2 ) ^ 2 * Real.sqrt 8 by ring ] ; norm_num ; ring;
                     · rw [ ← left_2 ] ; ring;
                       rw [ show ( Real.sqrt 8 ) ^ 4 = ( Real.sqrt 8 ^ 2 ) ^ 2 by ring, show ( Real.sqrt 8 ) ^ 5 = ( Real.sqrt 8 ^ 2 ) ^ 2 * Real.sqrt 8 by ring, show ( Real.sqrt 8 ) ^ 3 = ( Real.sqrt 8 ^ 2 ) * Real.sqrt 8 by ring, Real.sq_sqrt ( by norm_num ) ] ; ring;
                     · obtain ⟨ k, hk ⟩ := ha_div; obtain ⟨ l, hl ⟩ := hb_div; norm_num [ show a = -1 + k * ( 5 ^ n * 5 ) by linarith, show b = l * ( 5 ^ n * 5 ) by linarith ] ; ring_nf;
                       refine' dvd_add ( dvd_add _ _ ) _;
                       · refine' dvd_add ( dvd_add _ _ ) _;
                         · refine' dvd_add ( dvd_add _ _ ) _;
                           · exact ⟨ k * l ^ 2 * 5 ^ ( n * 2 ) * 1200 + k * l ^ 4 * 5 ^ ( n * 4 ) * 40000, by ring ⟩;
                           · exact ⟨ k, by ring ⟩;
                           · refine' dvd_sub _ _;
                             · exact ⟨ -k ^ 2 * l ^ 2 * 5 ^ ( n * 3 ) * 6000, by ring ⟩;
                             · exact ⟨ k ^ 2 * 5 ^ n * 10, by ring ⟩;
                         · exact ⟨ k ^ 3 * l ^ 2 * 5 ^ ( n * 4 ) * 10000, by ring ⟩;
                         · exact ⟨ k ^ 3 * 5 ^ ( n * 2 ) * 50 - k ^ 4 * 5 ^ ( n * 3 ) * 125, by ring ⟩;
                       · exact ⟨ k ^ 5 * 5 ^ ( n * 4 ) * 125, by ring ⟩;
                       · exact ⟨ -l ^ 2 * 5 ^ n * 80 - l ^ 4 * 5 ^ ( n * 3 ) * 8000, by ring ⟩;
                     · obtain ⟨ k, hk ⟩ := hb_div;
                       rw [ hk ] ; ring_nf;
                       exact ⟨ a ^ 2 * k ^ 3 * 5 ^ ( n * 2 ) * 400 + a ^ 4 * k + k ^ 5 * 5 ^ ( n * 4 ) * 8000, by ring ⟩;
                 -- By the uniqueness of the coefficients in the binomial expansion, the a and b from h_ind must be the same as those from h_binom.
                 obtain ⟨a, b, h_eq, h_div⟩ := h_ind t ht;
                 have h_unique : h_binom.choose = a ∧ h_binom.choose_spec.choose = b := by
                   have h_unique : ∀ a b c d : ℤ, (a + b * Real.sqrt 8 = c + d * Real.sqrt 8) → (a = c ∧ b = d) := by
                     intros a b c d h_eq
                     by_contra h_neq;
                     -- If $b \neq d$, then $\sqrt{8}$ must be rational, which is a contradiction.
                     have h_sqrt8_rat : ∃ q : ℚ, Real.sqrt 8 = q := by
                       exact ⟨ ( c - a ) / ( b - d ), by simpa [ field_simps, sub_eq_zero, show b ≠ d by aesop ] using by linarith ⟩;
                     exact h_sqrt8_rat.elim fun q hq => by have := congr_arg ( · ^ 2 ) hq; norm_num at this; norm_cast at this; exact absurd ( congr_arg ( ·.num ) this ) ( by norm_num [ sq, Rat.mul_self_num ] ; intros h; nlinarith [ show q.num ≤ 2 by nlinarith, show q.num ≥ -2 by nlinarith ] ) ;
                   exact h_unique _ _ _ _ ( by linarith [ h_binom.choose_spec.choose_spec ] );
                 aesop;
               obtain ⟨a, ha⟩ : ∃ a : ℤ, h_binom.choose + 1 = 5 ^ t * a := h_div.left
               obtain ⟨b, hb⟩ : ∃ b : ℤ, h_binom.choose_spec.choose = 5 ^ t * b := h_div.right;
               use a, b;
               have := h_binom.choose_spec.choose_spec; norm_num [ ← @Int.cast_inj ℝ ] at *; constructor <;> nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ) ] ;

theorem five_pow_t_dvd_n_jt_plus_two (t : ℕ) (ht : t ≥ 1) :
  5^t ∣ n_nat (j_t t) + 2 := by
    -- Using the identity $4(n_j + 2) = \alpha^{2j} + 6 + \alpha^{-2j}$, we substitute $j = j_t$.
    have h_identity : 4 * (n_nat (j_t t) + 2) = (alpha ^ (2 * j_t t) + 6 + alpha ^ (-(2 * j_t t) : ℤ)) := by
      rw [ n_nat_eq_n_real ];
      unfold n_real; ring;
    -- Since $2j_t = 3 \cdot 5^{t-1} - 1 = K_t - 1$, we can rewrite the identity as $4(n_{j_t} + 2) = \alpha^{K_t - 1} + 6 + \alpha^{-(K_t - 1)}$.
    have h_rewrite : 4 * (n_nat (j_t t) + 2) = (alpha ^ (j_t t + j_t t + 1) + 6 * alpha + alpha ^ (-(j_t t + j_t t + 1) : ℤ) * alpha ^ 2) / alpha := by
      -- Factor out $\alpha$ from the numerator.
      have h_factor : alpha ^ (j_t t + j_t t + 1) + 6 * alpha + alpha ^ (-(j_t t + j_t t + 1) : ℤ) * alpha ^ 2 = alpha * (alpha ^ (2 * j_t t) + 6 + alpha ^ (-(2 * j_t t) : ℤ)) := by
        norm_cast ; norm_num ; ring;
        norm_cast ; norm_num [ sq, mul_assoc, ne_of_gt ( show 0 < alpha from by exact add_pos_of_pos_of_nonneg zero_lt_three <| Real.sqrt_nonneg _ ) ];
      rw [ h_factor, mul_div_cancel_left₀ _ ( by rw [ show alpha = 3 + Real.sqrt 8 by rfl ] ; positivity ) ] ; aesop;
    -- Using the result from `alpha_pow_K_t`, we know that $\alpha^{K_t} = -1 + 5^t(a + b\sqrt{8})$.
    obtain ⟨a, b, ha⟩ : ∃ a b : ℤ, alpha ^ (j_t t + j_t t + 1) = -1 + 5 ^ t * (a + b * Real.sqrt 8) ∧ alpha ^ (-(j_t t + j_t t + 1) : ℤ) = -1 + 5 ^ t * (a - b * Real.sqrt 8) := by
      have := alpha_pow_K_t t ht; aesop;
      -- Since $j_t t = \frac{3 \cdot 5^{t-1} - 1}{2}$, we have $j_t t + j_t t + 1 = 3 \cdot 5^{t-1}$.
      have h_exp : j_t t + j_t t + 1 = 3 * 5 ^ (t - 1) := by
        unfold j_t; ring;
        rw [ Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by simp +decide [ Nat.one_le_iff_ne_zero, parity_simps ] ) ), add_tsub_cancel_of_le ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ];
      use w, w_1; aesop;
      convert right using 1;
      rw [ ← h_exp ] ; group;
      rw [ show ( alpha : ℝ ) = 3 + Real.sqrt 8 by rfl ] ; rw [ show ( 3 - Real.sqrt 8 ) = ( 3 + Real.sqrt 8 ) ⁻¹ by exact eq_inv_of_mul_eq_one_right ( by ring_nf; norm_num ) ] ; group;
    -- Substitute $\alpha^{K_t}$ and $\alpha^{-K_t}$ into the rewritten identity.
    have h_subst : 4 * (n_nat (j_t t) + 2) = (5 ^ t * (6 * a - 16 * b)) / 1 := by
      rw [ ← @Int.cast_inj ℝ ] ; aesop;
      rw [ ← h_identity ] ; rw [ show ( alpha : ℝ ) = 3 + Real.sqrt 8 by rfl ] ; ring;
      norm_num [ pow_three ] ; ring;
      nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), inv_mul_cancel_left₀ ( show ( 3 + Real.sqrt 8 ) ≠ 0 by positivity ) ( ( a : ℝ ) * 5 ^ t ), inv_mul_cancel_left₀ ( show ( 3 + Real.sqrt 8 ) ≠ 0 by positivity ) ( ( b : ℝ ) * 5 ^ t ) ];
    norm_num at *;
    exact_mod_cast Int.dvd_of_dvd_mul_right_of_gcd_one ( h_subst.symm ▸ dvd_mul_right _ _ ) ( by cases t <;> norm_num [ Int.gcd, Int.natAbs_pow ] at * )

theorem five_pow_t_is_powerful (t : ℕ) (ht : t ≥ 2) : IsPowerful (5^t) := by
  -- Since $5^t$ is a power of a prime, it is powerful.
  intros p hp hdiv
  have h_prime : p = 5 := by
    have := hp.dvd_of_dvd_pow hdiv; ( have := Nat.le_of_dvd ( by decide ) this; interval_cases p <;> trivial; );
  exact h_prime.symm ▸ pow_dvd_pow _ ht

theorem powerful_dvd_le_powerfulPart {n d : ℕ} (hn : n ≠ 0) (hd : IsPowerful d) (hdn : d ∣ n) : d ≤ powerfulPart n := by
  -- Since $d$ is a powerful divisor of $n$, it is included in the set of powerful divisors of $n$.
  have h_d_in_set : d ∈ (Nat.divisors n).filter IsPowerful := by
    aesop;
  unfold powerfulPart;
  have := Finset.le_max h_d_in_set; aesop;
  -- Since the maximum is a WithBot ℕ, we can use the fact that if the maximum is some value, then that value is indeed the maximum. If the maximum is none, then the default value is 1, but since d is a divisor of n and n is not zero, d must be at least 1. Therefore, in either case, d is less than or equal to the maximum value.
  cases h : Finset.max (Finset.filter IsPowerful n.divisors) <;> aesop

theorem final_inequality (t : ℕ) (ht : t ≥ 2) :
  (Finset.Ico (n_nat (j_t t)) (n_nat (j_t t) + 3)).prod powerfulPart ≥ n_nat (j_t t) * (n_nat (j_t t) + 1) * 5^t := by
    -- By definition of $B_2$, we know that $B_2(n) = n$, $B_2(n+1) = n+1$, and $B_2(n+2) \geq 5^t$.
    have h_B2_n : powerfulPart (n_nat (j_t t)) = n_nat (j_t t) := by
      unfold powerfulPart; aesop;
      -- Since $n_nat (j_t t)$ is powerful, it is in the set of powerful divisors.
      have h_in_set : n_nat (j_t t) ∈ Finset.filter IsPowerful (Nat.divisors (n_nat (j_t t))) := by
        field_simp;
        exact ⟨ h, n_nat_is_powerful _ ⟩;
      have h_max : Finset.max (Finset.filter IsPowerful (Nat.divisors (n_nat (j_t t)))) = some (n_nat (j_t t)) := by
        exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Nat.le_of_dvd ( Nat.pos_of_ne_zero h ) <| Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hx |>.1 ) ( Finset.le_sup ( f := WithBot.some ) h_in_set );
      exact h_max.symm ▸ rfl
    have h_B2_n1 : powerfulPart (n_nat (j_t t) + 1) = n_nat (j_t t) + 1 := by
      refine' le_antisymm _ _;
      · unfold powerfulPart; aesop;
        unfold Option.getD; aesop;
        exact Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp ( Finset.mem_of_max heq ) |>.1 ) );
      · unfold powerfulPart; aesop;
        have := Finset.le_max ( Finset.mem_filter.mpr ⟨ Nat.mem_divisors_self _ ( Nat.succ_ne_zero _ ), n_nat_succ_is_powerful ( j_t t ) ⟩ ) ; aesop;
        cases h : Finset.max ( Finset.filter IsPowerful ( n_nat ( j_t t ) + 1 |> Nat.divisors ) ) <;> aesop;
        exact Nat.cast_le.mp this
    have h_B2_n2 : powerfulPart (n_nat (j_t t) + 2) ≥ 5 ^ t := by
      -- By definition of $B_2$, we know that $5^t \mid n_j + 2$ and $5^t$ is powerful.
      have h_B2_n2_div : 5 ^ t ∣ n_nat (j_t t) + 2 := by
        convert five_pow_t_dvd_n_jt_plus_two t ( by linarith ) using 1
      have h_B2_n2_pow : IsPowerful (5 ^ t) := by
        exact?;
      unfold powerfulPart;
      have := Finset.le_max ( show 5 ^ t ∈ Finset.filter IsPowerful ( Nat.divisors ( n_nat ( j_t t ) + 2 ) ) from ?_ ) ; aesop;
      · cases h : Finset.max ( Finset.filter IsPowerful ( n_nat ( j_t t ) + 2 |> Nat.divisors ) ) <;> aesop;
        · contradiction;
        · exact Nat.cast_le.mp this;
      · aesop;
    rw [ show ( Finset.Ico ( n_nat ( j_t t ) ) ( n_nat ( j_t t ) + 3 ) ) = { ( n_nat ( j_t t ) ), ( n_nat ( j_t t ) + 1 ), ( n_nat ( j_t t ) + 2 ) } by ext1; aesop ; omega ] ; simp +decide [ *, mul_assoc ];
    gcongr

theorem neg_powerfulPart_bound_k3 :
  ¬ (∃ C : ℝ, ∀ n : ℕ,
    (∏ m ∈ Finset.Ico n (n + 3), (powerfulPart m : ℝ))
      ≤ C * (n : ℝ) * (n : ℝ)) := by
  by_contra h_contra
  obtain ⟨C, hC⟩ := h_contra
  have h_final_ineq : ∀ t ≥ 2, (n_nat (j_t t) * (n_nat (j_t t) + 1) * 5 ^ t : ℝ) ≤ C * (n_nat (j_t t))^2 := by
    intro t ht
    specialize hC (n_nat (j_t t));
    -- Applying the inequality from `final_inequality` to the assumption `hC`.
    have h_final : (n_nat (j_t t) * (n_nat (j_t t) + 1) * 5 ^ t : ℝ) ≤ ∏ m in Finset.Ico (n_nat (j_t t)) (n_nat (j_t t) + 3), (powerfulPart m : ℝ) := by
      exact_mod_cast final_inequality t ht |> le_trans <| mod_cast le_rfl;
    linarith
  have h_contradiction : ∀ t ≥ 2, (8 * y_j (j_t t)) ^ 2 * (8 * y_j (j_t t)) ^ 2 * 5 ^ t ≤ C * (8 * y_j (j_t t)) ^ 4 := by
    have h_contradiction : ∀ t ≥ 2, (n_nat (j_t t)) = 8 * (y_j (j_t t)) ^ 2 := by
      exact?;
    -- Substitute h_contradiction into h_final_ineq and simplify.
    intros t ht
    specialize h_final_ineq t ht
    rw [h_contradiction t ht] at h_final_ineq
    norm_cast at h_final_ineq ⊢
    ring_nf at h_final_ineq ⊢
    aesop;
    nlinarith [ show ( 0 : ℝ ) ≤ ( y_j ( j_t t ) ) ^ 2 * 5 ^ t by positivity, show ( 0 : ℝ ) ≤ ( y_j ( j_t t ) ) ^ 4 * 5 ^ t by positivity ]
  have h_contradiction : ∀ t ≥ 2, 5 ^ t ≤ C * 8 := by
    intros t ht
    specialize h_contradiction t ht
    have h_y_pos : 0 < y_j (j_t t) := by
      -- Since $j_t t$ is a positive integer for $t \geq 2$, and $y_j$ is positive for all positive $j$, we have $y_j (j_t t) > 0$.
      have h_y_pos : ∀ j : ℕ, 0 < j → 0 < Pell.yn (show 1 < 3 by norm_num) j := by
                                                    intro j hj; induction hj <;> aesop;
      exact h_y_pos _ ( Nat.div_pos ( Nat.le_sub_one_of_lt ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 5 ) ( Nat.le_sub_one_of_lt ht ) ] ) ) ( by decide ) )
    have h_div : (8 * y_j (j_t t)) ^ 4 > 0 := by
      positivity
    have h_div_ineq : 5 ^ t ≤ C * 8 := by
      -- By dividing both sides of the inequality by $(8 * y_j (j_t t))^4$, we get $5^t \leq C$.
      have h_div_ineq : 5 ^ t ≤ C := by
        nlinarith [ ( by positivity : 0 < ( 8 * y_j ( j_t t ) : ℝ ) ^ 4 ) ];
      exact le_trans h_div_ineq ( le_mul_of_one_le_right ( by linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 5 ) t ] ) ( by norm_num ) )
    exact h_div_ineq
  have h_contradiction : ∃ t ≥ 2, 5 ^ t > C * 8 := by
    rcases pow_unbounded_of_one_lt ( C * 8 ) ( by norm_num : ( 1 : ℝ ) < 5 ) with ⟨ t, ht ⟩ ; exact ⟨ t + 2, by linarith, by exact ht.trans_le <| pow_le_pow_right₀ ( by norm_num ) <| by linarith ⟩ ;
  obtain ⟨t, ht1, ht2⟩ := h_contradiction
  linarith [h_contradiction t ht1]

theorem neg_powerfulPart_bound_k3' :
  ∀ C : ℝ, ∃ n : ℕ,
    C * (n : ℝ) * (n : ℝ) <
      (∏ m ∈ Finset.Ico n (n + 3), (powerfulPart m : ℝ)) := by
  -- By combining the results from the previous steps, we conclude that the statement holds.
  intro C
  by_contra h_contra
  push_neg at h_contra;
  -- Apply the theorem neg_powerfulPart_bound_k3 to the assumption h_contra.
  apply neg_powerfulPart_bound_k3; exact ⟨C, h_contra⟩

/--
**Erdős Problem 367, strong form.**

An integer n is "powerful" is for every prime p that divides n, p^2
also divides n.

The "powerful part" of a number n is the largest powerful divisor d of
n.

Erdős asked about the size of the product of the powerful parts of the
k consecutive numbers m in the interval n <= m < k, as a function of
n.  The stronger conjecture was that this product is always << n^2,
with the constant allowed to depend on k.

We show in this file that this is not the case already for k=3 by
constructing an explicit counterexample.
-/
def erdos_367 : Prop :=
  ∀ k ≥ 1, ∃ C : ℝ, ∀ n : ℕ, (∏ m ∈ Finset.Ico n (n + k), (powerfulPart m : ℝ)) ≤ C * (n : ℝ) * (n : ℝ)

theorem disproof_367 : ¬ erdos_367 := by
  -- By contradiction, assume the conjecture is true.
  by_contra h_contra;
  -- Apply the contradiction assumption to obtain the required result.
  specialize h_contra 3 (by norm_num);
  -- Apply the negation of the conjecture for k=3 to obtain the required result.
  apply neg_powerfulPart_bound_k3; exact h_contra

end Erdos367
