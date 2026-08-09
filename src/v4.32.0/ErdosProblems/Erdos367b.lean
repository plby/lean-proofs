/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 367.
https://www.erdosproblems.com/forum/thread/367

Formalization status:
- Partial

Informal authors:
- Wouter van Doorn
- Terence Tao
- Gemini Deepthink

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/367#post-1766
- https://www.erdosproblems.com/forum/thread/367#post-1776
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos367.md
- https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos367.lean
-/
/-

\documentclass{amsart}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\begin{document}
\begin{definition}
A positive integer $n$ is \emph{2-full} (or ``powerful'') if for every prime
$p$ dividing $n$, $p^2$ also divides $n$.
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

By induction one can show that $\alpha^{\pm 3 \times 5^{t-1}} =
-1 + 5^t (a_t \pm b_t \sqrt{8})$ for various integers $a_t,b_t$ and
all $t \geq 1$.

Now we set $j_t :=(3 \times 5^{t-1}-1)/2$ (which is an integer) and compute
\begin{align*}
 4(n_{j_t}+2) &= \alpha^{-1} \alpha^{3 \times 5^{t-1}} + 6 + \alpha \alpha^{-3 \times 5^{t-1}} \\
&= (3-\sqrt{8}) (-1 + 5^t (a_t + b_t \sqrt{8})) + 6 + (3+\sqrt{8}) (-1 + 5^t (a_t - b_t \sqrt{8}))\\
&= 5^t (6 a_t - 16 b_t)
\end{align*}
giving the key claim $5^t | n_{j_t}+2$.  Thus for $t \geq 2$
$$ \prod_{n_{j_t} \leq m < n_{j_t}+3} B_2(m) \geq
n_{j_t} (n_{j_t}+1) 5^t \gg n_{j_t}^2 \log n_{j_t}.$$
\end{document}

-/

import Mathlib

namespace Erdos367b

def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

open Classical in
noncomputable def powerfulPart (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.divisors.filter IsPowerful).max.getD 1

noncomputable def alpha : ℝ := 3 + Real.sqrt 8

noncomputable def n_real (j : ℕ) : ℝ := (alpha ^ (2 * j) - 2 + alpha ^ (-(2 * j : ℤ))) / 4

set_option aesop.warn.nonterminal false in
theorem n_real_is_nat (j : ℕ) : ∃ k : ℕ, n_real j = k := by
  -- Let's denote α = 3 + sqrt(8). Then α^(2j) is a number of the form
  -- a + b*sqrt(8), where a and b are integers.
  set α := 3 + Real.sqrt 8
  have h_alpha_pow :
      ∃ a b : ℕ,
        α^(2*j) = a + b * Real.sqrt 8 ∧
          α^(-2*j : ℤ) = a - b * Real.sqrt 8 := by
    induction j with
    | zero => exact ⟨ 1, 0, by norm_num, by norm_num ⟩
    | succ j ih =>
      -- By the induction hypothesis, we have α^(2*j) = a + b*sqrt(8)
      -- and α^(-2*j) = a - b*sqrt(8).
      obtain ⟨a, b, ha, hb⟩ := ih
      use 17 * a + 48 * b, 6 * a + 17 * b
      aesop
      · -- Now use the induction hypothesis to simplify the expression.
        have h_expand :
            (3 + Real.sqrt 8) ^ (2 * (j + 1)) =
              (a + b * Real.sqrt 8) * (17 + 6 * Real.sqrt 8) := by
          rw [ ← ha ]
          ring_nf
          norm_num
          ring_nf
        exact h_expand.trans (by ring_nf; norm_num; ring_nf)
      · convert congr_arg ( fun x : ℝ => x / ( 3 + Real.sqrt 8 ) ^ 2 ) hb using 1 <;> ring_nf
        · rw [ ← mul_inv ]
          norm_cast
          ring_nf
        · rw [ show ( Real.sqrt 8 ) ^ 2 = 8 by norm_num ]
          ring_nf
          nlinarith [
            Real.sqrt_nonneg 8,
            Real.sq_sqrt (show 0 ≤ 8 by norm_num),
            inv_mul_cancel_left₀
              (show (17 + Real.sqrt 8 * 6) ≠ 0 by positivity) (a : ℝ),
            inv_mul_cancel_left₀
              (show (17 + Real.sqrt 8 * 6) ≠ 0 by positivity) (b : ℝ) ]
  -- Substitute the expressions for α^(2j) and α^(-2j) into the formula for
  -- n_j.
  obtain ⟨a, b, ha, hb⟩ := h_alpha_pow
  have h_n_j : n_real j = (a - 1) / 2 := by
    -- Substitute the expressions for α^(2j) and α^(-2j) into the formula for
    -- n_real j and simplify.
    have h_n_j : n_real j = ((a + b * Real.sqrt 8) - 2 + (a - b * Real.sqrt 8)) / 4 := by
      -- Substitute the expressions for α^(2j) and α^(-2j) into the formula
      -- for n_real j and simplify using the definitions of ha and hb.
      rw [show n_real j = (α^(2*j) - 2 + α^(-2*j : ℤ)) / 4 from rfl]
      rw [ha, hb]
    -- Combine like terms in the numerator and simplify the expression.
    rw [h_n_j]
    ring_nf
  -- Since $a$ is odd, $(a - 1)$ is even, and thus $(a - 1) / 2$ is a natural
  -- number.
  have h_a_odd : Odd a := by
    -- From the equation $a^2 - 8b^2 = 1$, we know that $a$ must be odd.
    have h_a_odd : a^2 = 8 * b^2 + 1 := by
      have h_eq : (a + b * Real.sqrt 8) * (a - b * Real.sqrt 8) = 1 := by
        rw [ ← ha, ← hb ]
        group
        norm_num
        exact mul_inv_cancel₀ (by positivity)
      exact_mod_cast
        (show (a : ℝ) ^ 2 = 8 * b ^ 2 + 1 by
          ring_nf at h_eq
          norm_num at h_eq
          linarith)
    simpa [ parity_simps ] using congr_arg Even h_a_odd
  obtain ⟨ k, rfl ⟩ := h_a_odd
  exact ⟨ k, by push_cast [ h_n_j ]; ring_nf ⟩

noncomputable def n_nat (j : ℕ) : ℕ := (n_real_is_nat j).choose

theorem n_nat_eq_n_real (j : ℕ) : (n_nat j : ℝ) = n_real j := (n_real_is_nat j).choose_spec.symm

def x_j (j : ℕ) : ℕ := Pell.xn (show 1 < 3 by norm_num) j
def y_j (j : ℕ) : ℕ := Pell.yn (show 1 < 3 by norm_num) j

set_option aesop.warn.nonterminal false in
theorem n_nat_eq_8_y_sq (j : ℕ) : n_nat j = 8 * (y_j j)^2 := by
  -- By definition of $n_real$, we know that
  -- $n_real j = ((alpha^(2*j) - 2 + alpha^(-(2*j))) / 4)$.
  have h_n_real :
      n_real j =
        ((3 + Real.sqrt 8) ^ (2 * j) - 2 + (3 - Real.sqrt 8) ^ (2 * j)) / 4 := by
    unfold n_real
    simp +zetaDelta only [zpow_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj'] at *
    unfold alpha
    norm_cast
    ring_nf
    norm_num
    ring_nf
    rw [ inv_eq_of_mul_eq_one_right ]
    ring_nf
    norm_num
  -- By definition of $n_real$, we know that $n_real j = 8 * y_j j^2$.
  have h_n_real_eq : n_real j = 8 * y_j j ^ 2 := by
    -- By definition of $x_j$ and $y_j$, we know that
    -- $(3 + \sqrt{8})^j = x_j + y_j \sqrt{8}$.
    have h_xy :
        (3 + Real.sqrt 8) ^ j = x_j j + y_j j * Real.sqrt 8 ∧
          (3 - Real.sqrt 8) ^ j = x_j j - y_j j * Real.sqrt 8 := by
      -- We proceed by induction on $j$.
      clear h_n_real
      induction j with
      | zero => norm_num [ x_j, y_j ]
      | succ j ihn =>
        simp_all +decide only [pow_succ] ; ring_nf
        unfold x_j y_j
        simp only [ Nat.add_comm 1 j ]
        norm_num [ Pell.xn_succ, Pell.yn_succ ]
        ring_nf
        norm_num
        exact Or.inl rfl
    aesop
    rw [ pow_mul', pow_mul' ]
    rw [ left, right ]
    ring_nf
    norm_num
    ring_nf
    -- By definition of $x_j$ and $y_j$, we know that $x_j^2 - 8y_j^2 = 1$.
    have h_pell : (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 = 1 := by
      have h_pell :
          (x_j j : ℝ)^2 - 8 * (y_j j : ℝ)^2 =
            ((3 + Real.sqrt 8) ^ j) * ((3 - Real.sqrt 8) ^ j) := by
        rw [ left, right ]
        ring_nf
        norm_num
      rw [ h_pell, ← mul_pow ]
      ring_nf
      norm_num
    linarith
  -- Since $n_real j = 8 * y_j j^2$ and $n_nat j$ is the natural number
  -- corresponding to $n_real j$, we can conclude that $n_nat j = 8 * y_j j^2$.
  have h_n_nat_eq : n_nat j = Nat.floor (n_real j) := by
    have h_n_nat_eq : n_nat j = Nat.floor (n_real j) := by
      have h_eq : (n_nat j : ℝ) = n_real j := by
        exact n_nat_eq_n_real j
      rw [ ← h_eq, Nat.floor_natCast ]
    exact h_n_nat_eq
  norm_num [ h_n_nat_eq, h_n_real_eq ]
  exact_mod_cast Nat.floor_natCast _

set_option aesop.warn.nonterminal false in
theorem n_nat_succ_eq_x_sq (j : ℕ) : n_nat j + 1 = (x_j j)^2 := by
  -- We'll use that $n_j + 1 = x_j^2$ to show that $n_j + 1$ can be powerful.
  have h_xj_sq : (n_nat j : ℝ) + 1 = (x_j j : ℝ) ^ 2 := by
    -- Substitute $n_j = 8y_j^2$ into the equation $x_j^2 = 8y_j^2 + 1$.
    have h_sub : (x_j j : ℝ)^2 = 8 * (y_j j : ℝ)^2 + 1 := by
      -- By definition of $x_j$ and $y_j$, we know that they satisfy the
      -- Pell equation $x^2 - 8y^2 = 1$.
      have h_pell :
          ∀ j,
            (Pell.xn (show 1 < 3 by norm_num) j : ℝ)^2 -
                8 * (Pell.yn (show 1 < 3 by norm_num) j : ℝ)^2 =
              1 := by
        intro j
        let a1 : 1 < 3 := by norm_num
        have hd := Pell.dz_val (a1 := a1)
        norm_num [Pell.az] at hd
        have hp := Pell.pell_eqz (a1 := a1) j
        rw [hd] at hp
        simp only [Pell.xz, Pell.yz] at hp
        rw [mul_assoc] at hp
        norm_num [pow_two]
        exact_mod_cast hp
      exact eq_add_of_sub_eq' ( h_pell j )
    rw [ h_sub, n_nat_eq_8_y_sq ]
    norm_cast
  exact_mod_cast h_xj_sq

theorem n_nat_is_powerful (j : ℕ) : IsPowerful (n_nat j) := by
  rw [n_nat_eq_8_y_sq]
  intro p hp hp_dvd
  rcases (Nat.Prime.dvd_mul hp).mp hp_dvd with h8 | hy
  · have hp_eq_two : p = 2 := by
      have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from by simpa using h8)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two
    subst p
    exact dvd_mul_of_dvd_left (by norm_num : 2 ^ 2 ∣ 8) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hy) 2) _

theorem n_nat_succ_is_powerful (j : ℕ) : IsPowerful (n_nat j + 1) := by
  rw [n_nat_succ_eq_x_sq]
  intro p hp hp_dvd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hp_dvd) 2


def j_t (t : ℕ) : ℕ := (3 * 5^(t-1) - 1) / 2

theorem j_t_well_defined (t : ℕ) : 2 ∣ 3 * 5^(t-1) - 1 := by
  norm_num [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ]

set_option aesop.warn.nonterminal false in
theorem alpha_pow_K_t (t : ℕ) (ht : t ≥ 1) :
  ∃ a b : ℤ,
    alpha ^ (3 * 5^(t-1)) = -1 + 5^t * (a + b * Real.sqrt 8) ∧
      (3 - Real.sqrt 8) ^ (3 * 5^(t-1)) =
        -1 + 5^t * (a - b * Real.sqrt 8) := by
  -- By the binomial theorem, we can expand $(3 + \sqrt{8})^{3 \cdot 5^{t-1}}$
  -- and $(3 - \sqrt{8})^{3 \cdot 5^{t-1}}$ into terms involving $\sqrt{8}$.
  have h_binom :
      ∃ a b : ℤ,
        (3 + Real.sqrt 8) ^ (3 * 5 ^ (t - 1)) = a + b * Real.sqrt 8 ∧
          (3 - Real.sqrt 8) ^ (3 * 5 ^ (t - 1)) =
            a - b * Real.sqrt 8 := by
    norm_num +zetaDelta at *
    induction (3 * 5 ^ (t - 1)) with
    | zero => aesop; exact ⟨ 1, 0, by norm_num, by norm_num ⟩
    | succ k ih =>
      aesop
      exact ⟨
        w * 3 + w_1 * 8,
        w + w_1 * 3,
        by
          push_cast [ pow_succ, * ]
          ring_nf
          norm_num
          ring_nf,
        by
          push_cast [ pow_succ, * ]
          ring_nf
          norm_num
          ring_nf ⟩
  -- We'll use that $a$ and $b$ satisfy the recurrence relations to show that
  -- $a \equiv -1 \pmod{5^t}$ and $b \equiv 0 \pmod{5^t}$.
  have h_recurrence :
      ∀ t : ℕ, t ≥ 1 →
        ∃ a b : ℤ,
          (3 + Real.sqrt 8) ^ (3 * 5 ^ (t - 1)) =
              a + b * Real.sqrt 8 ∧
            (3 - Real.sqrt 8) ^ (3 * 5 ^ (t - 1)) =
                a - b * Real.sqrt 8 ∧
              a ≡ -1 [ZMOD 5 ^ t] ∧ b ≡ 0 [ZMOD 5 ^ t] := by
    intro t ht
    induction ht with
    | refl =>
      -- For the base case $t = 1$, we can compute $(3 + \sqrt{8})^3$
      -- and $(3 - \sqrt{8})^3$ directly.
      use 99, 35
      norm_num
      constructor <;> nlinarith [
        Real.sqrt_nonneg 8,
        Real.sq_sqrt (show 0 ≤ 8 by norm_num) ]
    | step ht ih =>
      rename_i t
      rcases ih with ⟨ a, b, ha, hb, ha', hb' ⟩
      rcases t with ( _ | t ) <;>
        simp_all +decide [ pow_succ, pow_mul ] ;
        ring_nf at * ;
        norm_cast at * ;
        aesop;
      rw [
        show (Real.sqrt 8) ^ 4 = (Real.sqrt 8 ^ 2) ^ 2 by ring_nf,
        show (Real.sqrt 8) ^ 5 = (Real.sqrt 8 ^ 2) ^ 2 * Real.sqrt 8 by
          ring_nf,
        show (Real.sqrt 8) ^ 3 = (Real.sqrt 8 ^ 2) * Real.sqrt 8 by ring_nf,
        Real.sq_sqrt <| by norm_num ]
      ring_nf at *
      norm_cast at *
      aesop
      refine ⟨
        a ^ 5 + a ^ 3 * b ^ 2 * 80 + a * b ^ 4 * 320,
        a ^ 4 * b * 5 + a ^ 2 * b ^ 3 * 80 + b ^ 5 * 64,
        ?_, ?_, ?_, ?_ ⟩ <;>
        push_cast <;>
        ring_nf at * <;>
        norm_cast at * <;>
        aesop
      · rw [ Int.modEq_comm, Int.modEq_iff_dvd ] at *
        obtain ⟨ k, hk ⟩ := ha'
        obtain ⟨ l, hl ⟩ := hb'
        norm_num [
          show a = -1 + k * (5 ^ t * 5) by linarith,
          show b = l * (5 ^ t * 5) by linarith ]
        ring_nf
        exact ⟨
          k - k ^ 2 * 5 ^ t * 10 + k ^ 3 * 5 ^ (t * 2) * 50 -
            k ^ 4 * 5 ^ (t * 3) * 125 + k ^ 5 * 5 ^ (t * 4) * 125 -
            l ^ 2 * 5 ^ t * 80 + k * l ^ 2 * 5 ^ (t * 2) * 1200 -
            k ^ 2 * l ^ 2 * 5 ^ (t * 3) * 6000 +
            k ^ 3 * l ^ 2 * 5 ^ (t * 4) * 10000 -
            l ^ 4 * 5 ^ (t * 3) * 8000 +
            k * l ^ 4 * 5 ^ (t * 4) * 40000, by ring_nf ⟩
      · rw [ Int.modEq_zero_iff_dvd ] at *
        rcases hb' with ⟨ k, rfl ⟩
        ring_nf
        norm_num [ pow_succ, mul_assoc, dvd_mul_of_dvd_right ]
        aesop
        exact ⟨
          a ^ 2 * k ^ 3 * 5 ^ (t * 2) * 400 + a ^ 4 * k +
            k ^ 5 * 5 ^ (t * 4) * 8000,
          by ring_nf ⟩
  obtain ⟨ a, b, ha, hb, ha', hb' ⟩ := h_recurrence t ht
  obtain ⟨ k, hk ⟩ := ha'.symm.dvd
  obtain ⟨ l, hl ⟩ := hb'.symm.dvd
  use k, l
  aesop
  · unfold alpha
    norm_num [ show a = 5 ^ t * k - 1 by linarith ] at *
    linarith
  · push_cast [ ← @Int.cast_inj ℝ .. ] at *
    linarith

set_option aesop.warn.nonterminal false in
theorem five_pow_t_dvd_n_jt_plus_two (t : ℕ) (ht : t ≥ 1) :
  5^t ∣ n_nat (j_t t) + 2 := by
    -- Using the identity $4(n_j + 2) = \alpha^{2j} + 6 + \alpha^{-2j}$,
    -- we substitute $j = j_t$.
    have h_identity :
        4 * (n_nat (j_t t) + 2) =
          (alpha ^ (2 * j_t t) + 6 + alpha ^ (-(2 * j_t t) : ℤ)) := by
      rw [ n_nat_eq_n_real ]
      unfold n_real
      ring_nf
    -- Since $2j_t = 3 \cdot 5^{t-1} - 1 = K_t - 1$, we can rewrite the
    -- identity as $4(n_{j_t} + 2) = \alpha^{K_t - 1} + 6 +
    -- \alpha^{-(K_t - 1)}$.
    have h_rewrite :
        4 * (n_nat (j_t t) + 2) =
          (alpha ^ (j_t t + j_t t + 1) + 6 * alpha +
            alpha ^ (-(j_t t + j_t t + 1) : ℤ) * alpha ^ 2) / alpha := by
      -- Factor out $\alpha$ from the numerator.
      have h_factor :
          alpha ^ (j_t t + j_t t + 1) + 6 * alpha +
              alpha ^ (-(j_t t + j_t t + 1) : ℤ) * alpha ^ 2 =
            alpha * (alpha ^ (2 * j_t t) + 6 +
              alpha ^ (-(2 * j_t t) : ℤ)) := by
        norm_cast
        norm_num
        ring_nf
        norm_cast
        norm_num [
          sq,
          mul_assoc,
          ne_of_gt
            (show 0 < alpha from by
              exact add_pos_of_pos_of_nonneg zero_lt_three <| Real.sqrt_nonneg _) ]
      rw [
        h_factor,
        mul_div_cancel_left₀ _
          (by rw [ show alpha = 3 + Real.sqrt 8 by rfl ]; positivity) ]
      aesop
    -- Using the result from `alpha_pow_K_t`, we know that
    -- $\alpha^{K_t} = -1 + 5^t(a + b\sqrt{8})$.
    obtain ⟨a, b, ha⟩ :
        ∃ a b : ℤ,
          alpha ^ (j_t t + j_t t + 1) =
              -1 + 5 ^ t * (a + b * Real.sqrt 8) ∧
            alpha ^ (-(j_t t + j_t t + 1) : ℤ) =
              -1 + 5 ^ t * (a - b * Real.sqrt 8) := by
      have := alpha_pow_K_t t ht
      aesop
      -- Since $j_t t = \frac{3 \cdot 5^{t-1} - 1}{2}$, we have
      -- $j_t t + j_t t + 1 = 3 \cdot 5^{t-1}$.
      have h_exp : j_t t + j_t t + 1 = 3 * 5 ^ (t - 1) := by
        unfold j_t
        ring_nf
        rw [
          Nat.div_mul_cancel
            (even_iff_two_dvd.mp
              (by simp +decide [ Nat.one_le_iff_ne_zero, parity_simps ])),
          add_tsub_cancel_of_le
            (Nat.one_le_iff_ne_zero.mpr <| by positivity) ]
      use w, w_1
      aesop
      convert right using 1
      rw [ ← h_exp ]
      group
      rw [ show (alpha : ℝ) = 3 + Real.sqrt 8 by rfl ]
      rw [
        show (3 - Real.sqrt 8) = (3 + Real.sqrt 8)⁻¹ by
          exact eq_inv_of_mul_eq_one_right (by ring_nf; norm_num) ]
      group
    -- Substitute $\alpha^{K_t}$ and $\alpha^{-K_t}$ into the rewritten identity.
    have h_subst :
        4 * (n_nat (j_t t) + 2) = (5 ^ t * (6 * a - 16 * b)) / 1 := by
      rw [ ← @Int.cast_inj ℝ ]
      aesop
      rw [ ← h_identity ]
      rw [ show (alpha : ℝ) = 3 + Real.sqrt 8 by rfl ]
      ring_nf
      norm_num [ pow_three ]
      ring_nf
      nlinarith [
        Real.sqrt_nonneg 8,
        Real.sq_sqrt (show 0 ≤ 8 by norm_num),
        inv_mul_cancel_left₀
          (show (3 + Real.sqrt 8) ≠ 0 by positivity) ((a : ℝ) * 5 ^ t),
        inv_mul_cancel_left₀
          (show (3 + Real.sqrt 8) ≠ 0 by positivity) ((b : ℝ) * 5 ^ t) ]
    norm_num at *
    exact_mod_cast
      Int.dvd_of_dvd_mul_right_of_gcd_one
        (h_subst.symm ▸ dvd_mul_right _ _)
        (by cases t <;> norm_num [ Int.gcd, Int.natAbs_pow ] at *)

theorem five_pow_t_is_powerful (t : ℕ) (ht : t ≥ 2) : IsPowerful (5^t) := by
  -- Since $5^t$ is a power of a prime, it is powerful.
  intros p hp hdiv
  have h_prime : p = 5 := by
    have := hp.dvd_of_dvd_pow hdiv
    have := Nat.le_of_dvd ( by decide ) this
    interval_cases p <;> trivial
  exact h_prime.symm ▸ pow_dvd_pow _ ht

set_option aesop.warn.nonterminal false in
theorem powerful_dvd_le_powerfulPart {n d : ℕ} (hn : n ≠ 0)
    (hd : IsPowerful d) (hdn : d ∣ n) :
    d ≤ powerfulPart n := by
  classical
  -- Since $d$ is a powerful divisor of $n$, it is included in the set of
  -- powerful divisors of $n$.
  have h_d_in_set : d ∈ (Nat.divisors n).filter IsPowerful := by
    aesop
  unfold powerfulPart
  have := Finset.le_max h_d_in_set
  aesop
  -- Since the maximum is a WithBot ℕ, we can use the fact that if the
  -- maximum is some value, then that value is indeed the maximum. If the
  -- maximum is none, then the default value is 1, but since d is a divisor of
  -- n and n is not zero, d must be at least 1. Therefore, in either case, d is
  -- less than or equal to the maximum value.
  cases h : Finset.max (Finset.filter IsPowerful n.divisors) <;> aesop

set_option aesop.warn.nonterminal false in
theorem final_inequality (t : ℕ) (ht : t ≥ 2) :
  (Finset.Ico (n_nat (j_t t)) (n_nat (j_t t) + 3)).prod powerfulPart ≥
    n_nat (j_t t) * (n_nat (j_t t) + 1) * 5^t := by
  classical
  -- Since $n_{j_t}$, $n_{j_t} + 1$, and $n_{j_t} + 2$ are all powerful,
  -- their powerful parts are themselves.
  have h_powerful_parts :
      powerfulPart (n_nat (j_t t)) = n_nat (j_t t) ∧
        powerfulPart (n_nat (j_t t) + 1) = n_nat (j_t t) + 1 ∧
          powerfulPart (n_nat (j_t t) + 2) ≥ 5^t := by
    -- Since $n_{j_t}$ and $n_{j_t} + 1$ are powerful, their powerful parts are
    -- themselves.
    have h_powerful_parts_self :
        powerfulPart (n_nat (j_t t)) = n_nat (j_t t) ∧
          powerfulPart (n_nat (j_t t) + 1) = n_nat (j_t t) + 1 := by
      -- Since $n_{j_t}$ and $n_{j_t} + 1$ are powerful, their powerful parts
      -- are themselves by definition.
      have h_powerful_parts : ∀ n : ℕ, IsPowerful n → powerfulPart n = n := by
        intro n hn
        unfold powerfulPart
        aesop
        have h_max : Finset.max (Finset.filter IsPowerful (Nat.divisors n)) = some n := by
          -- Since $n$ is powerful, it is in the set of powerful divisors of $n$.
          have h_n_in_set : n ∈ Finset.filter IsPowerful (Nat.divisors n) := by
            aesop
          exact le_antisymm
            (Finset.sup_le fun x hx =>
              WithBot.coe_le_coe.mpr <|
                Nat.le_of_dvd (Nat.pos_of_ne_zero h) <|
                  Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hx)
            (Finset.le_sup h_n_in_set)
        -- Since the maximum is some n, the Option.getD will return n.
        simp [h_max, Option.getD]
      exact ⟨
        h_powerful_parts _ <| n_nat_is_powerful _,
        h_powerful_parts _ <| n_nat_succ_is_powerful _ ⟩
    refine ⟨ h_powerful_parts_self.left, h_powerful_parts_self.right, ?_ ⟩
    have := five_pow_t_dvd_n_jt_plus_two t ( by linarith )
    aesop
    refine powerful_dvd_le_powerfulPart ?_ ?_ this
    · aesop
    · -- Since $5$ is a prime and $t \geq 2$, $5^2$ divides $5^t$, so $5^t$ is
      -- powerful.
      apply five_pow_t_is_powerful t ht
  rw [
    show
        Finset.Ico (n_nat (j_t t)) (n_nat (j_t t) + 3) =
          { n_nat (j_t t), n_nat (j_t t) + 1, n_nat (j_t t) + 2 } by
      ext x
      aesop
      omega ]
  aesop
  simpa only [ mul_assoc ] using Nat.mul_le_mul_left _ ( Nat.mul_le_mul_left _ right )

set_option aesop.warn.nonterminal false in
theorem neg_powerfulPart_bound_k3 :
  ¬ (∃ C : ℝ, ∀ n : ℕ,
    (∏ m ∈ Finset.Ico n (n + 3), (powerfulPart m : ℝ))
      ≤ C * (n : ℝ) * (n : ℝ)) := by
  by_contra h_contra
  obtain ⟨C, hC⟩ := h_contra
  have h_final_ineq :
      ∀ t ≥ 2,
        (n_nat (j_t t) * (n_nat (j_t t) + 1) * 5 ^ t : ℝ) ≤
          C * (n_nat (j_t t))^2 := by
    intro t ht
    specialize hC (n_nat (j_t t))
    -- Applying the inequality from `final_inequality` to the assumption `hC`.
    have h_final :
        (n_nat (j_t t) * (n_nat (j_t t) + 1) * 5 ^ t : ℝ) ≤
          ∏ m ∈ Finset.Ico (n_nat (j_t t)) (n_nat (j_t t) + 3),
            (powerfulPart m : ℝ) := by
      exact_mod_cast final_inequality t ht |> le_trans <| mod_cast le_rfl
    linarith
  have h_contradiction :
      ∀ t ≥ 2,
        (8 * y_j (j_t t)) ^ 2 * (8 * y_j (j_t t)) ^ 2 * 5 ^ t ≤
          C * (8 * y_j (j_t t)) ^ 4 := by
    have h_contradiction : ∀ t ≥ 2, (n_nat (j_t t)) = 8 * (y_j (j_t t)) ^ 2 := by
      exact fun t a ↦ n_nat_eq_8_y_sq (j_t t)
    -- Substitute h_contradiction into h_final_ineq and simplify.
    intros t ht
    specialize h_final_ineq t ht
    rw [h_contradiction t ht] at h_final_ineq
    norm_cast at h_final_ineq ⊢
    ring_nf at h_final_ineq ⊢
    aesop
    nlinarith [
      show ( 0 : ℝ ) ≤ ( y_j ( j_t t ) ) ^ 2 * 5 ^ t by positivity,
      show ( 0 : ℝ ) ≤ ( y_j ( j_t t ) ) ^ 4 * 5 ^ t by positivity ]
  have h_contradiction : ∀ t ≥ 2, 5 ^ t ≤ C * 8 := by
    intros t ht
    specialize h_contradiction t ht
    have h_y_pos : 0 < y_j (j_t t) := by
      -- Since $j_t t$ is a positive integer for $t \geq 2$, and $y_j$ is
      -- positive for all positive $j$, we have $y_j (j_t t) > 0$.
      have h_y_pos : ∀ j : ℕ, 0 < j → 0 < Pell.yn (show 1 < 3 by norm_num) j := by
        intro j hj
        induction hj <;> aesop
      exact h_y_pos _
        (Nat.div_pos
          (Nat.le_sub_one_of_lt
            (by
              linarith [
                Nat.pow_le_pow_right
                  (by decide : 1 ≤ 5) (Nat.le_sub_one_of_lt ht) ]))
          (by decide))
    have h_div : (8 * y_j (j_t t)) ^ 4 > 0 := by
      positivity
    have h_div_ineq : 5 ^ t ≤ C * 8 := by
      -- By dividing both sides of the inequality by $(8 * y_j (j_t t))^4$, we get $5^t \leq C$.
      have h_div_ineq : 5 ^ t ≤ C := by
        nlinarith [ ( by positivity : 0 < ( 8 * y_j ( j_t t ) : ℝ ) ^ 4 ) ]
      exact le_trans h_div_ineq
        (le_mul_of_one_le_right
          (by linarith [ pow_pos (by norm_num : ( 0 : ℝ ) < 5) t ])
          (by norm_num))
    exact h_div_ineq
  have h_contradiction : ∃ t ≥ 2, 5 ^ t > C * 8 := by
    rcases pow_unbounded_of_one_lt ( C * 8 ) ( by norm_num : ( 1 : ℝ ) < 5 ) with
      ⟨ t, ht ⟩
    exact ⟨
      t + 2,
      by linarith,
      by exact ht.trans_le <| pow_le_pow_right₀ ( by norm_num ) <| by linarith ⟩
  obtain ⟨t, ht1, ht2⟩ := h_contradiction
  linarith [h_contradiction t ht1]

theorem neg_powerfulPart_bound_k3' :
  ∀ C : ℝ, ∃ n : ℕ,
    C * (n : ℝ) * (n : ℝ) <
      (∏ m ∈ Finset.Ico n (n + 3), (powerfulPart m : ℝ)) := by
  -- By combining the results from the previous steps, we conclude that the statement holds.
  intro C
  by_contra h_contra
  push Not at h_contra
  -- Apply the theorem neg_powerfulPart_bound_k3 to the assumption h_contra.
  apply neg_powerfulPart_bound_k3
  exact ⟨C, h_contra⟩

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
  ∀ k ≥ 1, ∃ C : ℝ, ∀ n : ℕ,
    (∏ m ∈ Finset.Ico n (n + k), (powerfulPart m : ℝ)) ≤
      C * (n : ℝ) * (n : ℝ)

theorem disproof_367 : ¬ erdos_367 := by
  -- By contradiction, assume the conjecture is true.
  by_contra h_contra
  -- Apply the contradiction assumption to obtain the required result.
  specialize h_contra 3 (by norm_num)
  -- Apply the negation of the conjecture for k=3 to obtain the required result.
  apply neg_powerfulPart_bound_k3
  exact h_contra

#print axioms disproof_367
-- 'Erdos367b.disproof_367' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos367b
