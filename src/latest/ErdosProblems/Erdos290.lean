/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 290.
https://www.erdosproblems.com/forum/thread/290

Informal authors:
- Wouter van Doorn

Formal authors:
- Aristotle
- Wouter van Doorn
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/290#post-3180
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem290.lean
-/
/-
For positive integers $a$ and $b$, let $u_{a,b}$ and $v_{a,b}$ be the coprime
positive integers with $\frac{u_{a,b}}{v_{a,b}} = \sum_{i=a}^b \frac{1}{i}$.
That is, $v_{a,b}$ is the denominator of the partial harmonic sum from $a$ to
$b$. Below you can find a Lean formalization of a proof that for every positive
integer $a$, there exists a positive integer $b$ with $a < b \le 6a$ such that
$v_{a,b} < v_{a,b-1}$. This provides a solution to Erdős problem #290;
https://www.erdosproblems.com/290. The mathematical content was written by me
and consisted of a highly simplified version of my 2024 paper on the subject.

W. van Doorn, On the non-monotonicity of the denominator of generalized
harmonic sums. arXiv:2411.03073 (2024).

I fed this simplified version into Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun) to get it formalized. Boris Alexeev then used
the output from Aristotle to completely finish the Lean proof, cleaning it all
up in the process. I owe him a huge thanks :)
-/

import Mathlib

namespace Erdos290

/-
The sum of reciprocals from a to b.
-/
def harmonicSum (a b : ℕ) : ℚ := ∑ i ∈ Finset.Icc a b, (1 : ℚ) / i

/-
u_{a,b} and v_{a,b} are the numerator and denominator of the harmonic sum.
-/
def u (a b : ℕ) : ℕ := (harmonicSum a b).num.natAbs

def v (a b : ℕ) : ℕ := (harmonicSum a b).den

/-
k is the unique integer such that 3^{k-1} <= a < 3^k, and b = 2 * 3^k.
-/
def k_val (a : ℕ) : ℕ := Nat.log 3 a + 1

def b_val (a : ℕ) : ℕ := 2 * 3 ^ (k_val a)

/-
We have $a < b$.
-/
lemma blargerthana (a : ℕ) (ha : a > 0) : a < b_val a := by
  -- By definition of $k$, we know that $3^k > a$.
  have h_exp : 3 ^ (Nat.log 3 a + 1) > a := by
    exact Nat.lt_pow_succ_log_self ( by decide ) _;
  exact h_exp.trans_le ( by rw [ show b_val a = 2 * 3 ^ ( Nat.log 3 a + 1 ) by rfl ] ; linarith )

/-
We have $1 <= b$.
-/
lemma batleast2 (a : ℕ) : 2 ≤ b_val a := by
  exact le_trans ( by decide ) ( Nat.mul_le_mul_left 2 ( Nat.one_le_pow _ _ ( by decide ) ) )

/-
We have $b \le 6a$.
-/
lemma bsmallerthansixa (a : ℕ) (ha : a > 0) : b_val a ≤ 6 * a := by
  -- By definition of $k_val$, we know that $3^{k_val a - 1} \leq a < 3^{k_val a}$.
  have h_bounds : 3 ^ (k_val a - 1) ≤ a ∧ a < 3 ^ (k_val a) := by
    exact ⟨
      Nat.pow_le_of_le_log (by positivity) (by norm_num [k_val]),
      Nat.lt_pow_of_log_lt (by norm_num) (by norm_num [k_val])⟩
  unfold b_val;
  cases n : k_val a <;> simp_all +decide [ pow_succ' ] ; linarith

/-
For all primes $p$ and all rationals $x$ and $y$, if $\nu_p(x) \neq \nu_p(y)$,
then $\nu_p(x+y) = \min(\nu_p(x), \nu_p(y)).$
-/
lemma eqmin (p : ℕ) [Fact p.Prime] (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) (h : padicValRat p x ≠ padicValRat p y) :
  padicValRat p (x + y) = min (padicValRat p x) (padicValRat p y) := by
    apply_rules [ padicValRat.add_eq_min ]

/-
For all primes $p > 3$ we have $\nu_p\left(\frac{-1}{b}\right) = 0$.
-/
lemma plargerthanthreevaluationofoneoverb (a : ℕ) (p : ℕ) [Fact p.Prime] (hp : p > 3) :
  padicValRat p (-1 / b_val a) = 0 := by
    rw [ padicValRat.div ] <;> norm_num;
    · unfold b_val;
      norm_num [ Nat.Prime.dvd_mul Fact.out ];
      exact Or.inr ⟨
        Nat.not_dvd_of_pos_of_lt (by norm_num) (by linarith),
        mt (Nat.Prime.dvd_of_dvd_pow Fact.out)
          (Nat.not_dvd_of_pos_of_lt (by norm_num) (by linarith))⟩;
    · exact mul_ne_zero two_ne_zero ( pow_ne_zero _ three_ne_zero )

/-
For all primes $p > 3$ dividing $v_{a,b}$ we have
$\nu_p\left(\frac{u_{a,b}}{v_{a,b}}\right) = -\nu_p(v_{a,b}) < 0$.
-/
set_option linter.flexible false in
lemma plargerthanthreevaluationofvab (a : ℕ) (p : ℕ) [Fact p.Prime]
    (hp : p > 3) (hpv : p ∣ v a (b_val a)) :
  padicValRat p (harmonicSum a (b_val a)) = -padicValRat p (v a (b_val a)) ∧
    padicValRat p (harmonicSum a (b_val a)) < 0 := by
    have h_u_denom :
        ∃ k : ℤ,
          harmonicSum a (b_val a) = (u a (b_val a) : ℚ) / (v a (b_val a) : ℚ) ∧
            Int.gcd (u a (b_val a)) (v a (b_val a)) = 1 := by
      unfold u v;
      norm_num [
        abs_of_nonneg
          (Rat.num_nonneg.mpr
            (show 0 ≤ harmonicSum a (b_val a) from
              Finset.sum_nonneg fun _ _ => by positivity))]
      exact ⟨ Eq.symm ( Rat.num_div_den _ ), Rat.reduced _ ⟩;
    by_cases h : u a ( b_val a ) = 0 <;>
      by_cases h' : v a ( b_val a ) = 0 <;>
      simp_all +decide [ padicValRat.div, padicValRat.of_nat ];
    · exact absurd h' ( Nat.ne_of_gt ( Rat.pos _ ) );
    · exact ⟨
        Or.inr fun h'' => absurd ( Nat.dvd_gcd h'' hpv ) ( by aesop ),
        by
          rw [ padicValNat.eq_zero_of_not_dvd
            (show ¬p ∣ u a ( b_val a ) from
              fun h'' => absurd ( Nat.dvd_gcd h'' hpv ) ( by aesop )) ]
          exact Nat.pos_of_ne_zero ( by aesop )⟩

/-
For all primes $p > 3$ dividing $v_{a,b}$ we have
$\nu_p(v_{a,b-1}) = \nu_p(v_{a,b})$.
-/
set_option linter.flexible false in
lemma plargerthanthreevaluationofvabminusone (a : ℕ) (p : ℕ) [Fact p.Prime]
    (hp : p > 3) (hpv : p ∣ v a (b_val a)) :
  padicValRat p (v a (b_val a - 1)) = padicValRat p (v a (b_val a)) := by
    -- We apply Lemma \ref{eqmin} with $x = \frac{u_{a,b}}{v_{a,b}}$ and
    -- $y = \frac{-1}{b}$, so that $x+y = \frac{u_{a,b-1}}{v_{a,b-1}}$.
    set x : ℚ := harmonicSum a (b_val a)
    set y : ℚ := -1 / b_val a
    have hxy : x + y = harmonicSum a (b_val a - 1) := by
      -- By definition of $x$ and $y$, this is cancellation of the final term.
      simp [x, y, harmonicSum];
      rcases n : b_val a with ( _ | _ | b ) <;> simp_all +decide
      · ring_nf
        unfold b_val at n
        aesop
      · erw [ Finset.sum_Ico_succ_top ] <;> norm_num
        · ring!
        · -- Since $b_val a = 2 * 3^{k_val a}$ and $k_val a = Nat.log 3 a + 1$,
          -- we have $b_val a \geq 2 * 3^{Nat.log 3 a + 1}$.
          have h_b_val_ge : b_val a ≥ 2 * 3 ^ (Nat.log 3 a + 1) := by
            exact Nat.le_refl (2 * 3 ^ (Nat.log 3 a + 1));
          linarith [
            Nat.lt_pow_of_log_lt (by norm_num)
              (by linarith : Nat.log 3 a < Nat.log 3 a + 1)]
    have hxy_pos : x + y ≠ 0 := by
      have h_pos :
          ∀ {n m : ℕ}, n ≤ m → n > 0 → ∑ i ∈ Finset.Icc n m, (1 : ℚ) / i > 0 := by
        exact fun {n m} hnm hn =>
          Finset.sum_pos
            (fun i hi =>
              one_div_pos.mpr <| Nat.cast_pos.mpr <| by
                linarith [ Finset.mem_Icc.mp hi ])
            (Finset.nonempty_Icc.mpr hnm)
      by_cases ha : a > 0 <;> simp_all +decide [ harmonicSum ];
      · exact ne_of_gt <|
          h_pos (Nat.le_sub_one_of_lt <| by linarith [ blargerthana a ha ]) ha;
      · set m : ℕ := b_val 0 - 1
        have hm : 1 ≤ m := by
          have hm2 : 2 ≤ b_val 0 := by
            exact batleast2 0
          exact Nat.le_sub_one_of_lt hm2
        have hpos1 : (0 : ℚ) < ∑ x ∈ Finset.Icc 1 m, (↑x)⁻¹ :=
          h_pos hm (by decide)
        have h0not : (0 : ℕ) ∉ Finset.Icc 1 m := by
          simp [Finset.mem_Icc]
        have hIcc : Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
          -- from insert_Icc_succ_left_eq_Icc, with a = 0
          simpa using
            (Finset.insert_Icc_succ_left_eq_Icc
              (a := (0 : ℕ)) (b := m) (Nat.zero_le m)).symm
        have hpos0 : (0 : ℚ) < ∑ x ∈ Finset.Icc 0 m, (↑x)⁻¹ := by
          -- rewrite the interval as an insert, split the sum, simplify inv 0 = 0
          simpa [hIcc, h0not] using hpos1
        exact (ne_of_gt hpos0)
    have hxy_neq : padicValRat p x ≠ padicValRat p y := by
      have := plargerthanthreevaluationofvab a p hp hpv;
      have := plargerthanthreevaluationofoneoverb a p hp; aesop;
    have hxy_val :
        padicValRat p (harmonicSum a (b_val a - 1)) =
          min (padicValRat p x) (padicValRat p y) := by
      have hxy_val : padicValRat p (x + y) = min (padicValRat p x) (padicValRat p y) := by
        have hx_ne_zero : x ≠ 0 := by
          intro hx_zero
          simp [hx_zero] at *;
          exact hxy_neq <| by rw [ plargerthanthreevaluationofoneoverb a p hp ] ;
        have hy_ne_zero : y ≠ 0 := by
          exact div_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr <| by
            exact ne_of_gt (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)))
        exact eqmin p x y hx_ne_zero hy_ne_zero hxy_pos hxy_neq;
      rw [ ← hxy, hxy_val ]
    have hxy_val_simplified : padicValRat p (harmonicSum a (b_val a - 1)) = padicValRat p x := by
      have hxy_val_simplified : padicValRat p x < 0 := by
        have := plargerthanthreevaluationofvab a p hp hpv; aesop;
      have hxy_val_simplified' : padicValRat p y = 0 := by
        exact plargerthanthreevaluationofoneoverb a p hp
      have hxy_val_simplified'' : min (padicValRat p x) (padicValRat p y) = padicValRat p x := by
        exact min_eq_left ( by linarith )
      rw [hxy_val, hxy_val_simplified'']
    have hxy_val_simplified' :
        padicValRat p (harmonicSum a (b_val a - 1)) =
          -padicValRat p (v a (b_val a)) := by
      have := plargerthanthreevaluationofvab a p hp hpv; aesop;
    have hxy_val_simplified'' :
        padicValRat p (harmonicSum a (b_val a - 1)) =
          padicValRat p (u a (b_val a - 1)) - padicValRat p (v a (b_val a - 1)) := by
      have hxy_val_simplified'' :
          padicValRat p (harmonicSum a (b_val a - 1)) =
            padicValRat p ((u a (b_val a - 1) : ℚ) / (v a (b_val a - 1))) := by
        unfold u v; norm_num;
        rw [
          abs_of_nonneg
            (mod_cast Rat.num_nonneg.mpr <|
              show 0 ≤ harmonicSum a ( b_val a - 1 ) from
                Finset.sum_nonneg fun _ _ => by positivity),
          Rat.num_div_den];
      rw [ hxy_val_simplified'', padicValRat.div ]
      · norm_num
        unfold u
        aesop
      · norm_num
        exact Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Rat.pos _
    have hxy_val_simplified''' : padicValRat p (u a (b_val a - 1)) = 0 := by
      by_contra h_contra;
      -- Since $u_{a,b-1}$ and $v_{a,b-1}$ are coprime, we have $\nu_p(u_{a,b-1}) = 0$.
      have h_coprime : Nat.gcd (u a (b_val a - 1)) (v a (b_val a - 1)) = 1 := by
        exact Rat.reduced _;
      have h_coprime_val :
          padicValRat p (u a (b_val a - 1)) = 0 ∨
            padicValRat p (v a (b_val a - 1)) = 0 := by
        simp_all +decide [ padicValRat ];
        exact Or.inr fun h =>
          Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p) <|
            h_coprime ▸ Nat.dvd_gcd h_contra.2.2 h;
      simp_all +decide;
      cases h_coprime_val <;> simp_all +decide [ padicValNat.eq_zero_of_not_dvd ];
      exact absurd
        (hxy_val_simplified'.symm ▸
          Int.ofNat_lt.mpr (Nat.pos_of_ne_zero (by aesop)))
        (by linarith [ Nat.zero_le (padicValNat p (v a (b_val a))) ])
    have hxy_val_simplified'''' :
        padicValRat p (v a (b_val a - 1)) = padicValRat p (v a (b_val a)) := by
      linarith
    exact hxy_val_simplified''''

/-
We have $l \ge 2$.
-/
def l_val (a : ℕ) : ℕ := Nat.log 2 (b_val a)

lemma latleasttwo (a : ℕ) : l_val a ≥ 2 := by
  -- Since $b = 2 \cdot 3^k$ and $k \geq 1$, we have $b \geq 6$.
  have hb_ge_6 : b_val a ≥ 6 := by
    exact le_trans (by decide)
      (Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (Nat.zero_le _))));
  exact Nat.le_log_of_pow_le ( by decide ) ( by linarith )

/-
We have $2^l \le b-1$.
-/
lemma twotothelsmallerthanb (a : ℕ) : 2 ^ (l_val a) ≤ b_val a - 1 := by
  refine Nat.le_sub_one_of_lt ?_;
  -- By definition of $l_val$, we know that $2^{l_val a} \le b_val a$.
  have h_l_le_b : 2 ^ (l_val a) ≤ b_val a := by
    refine Nat.pow_log_le_self 2 ?_;
    exact mul_ne_zero two_ne_zero ( pow_ne_zero _ three_ne_zero );
  refine lt_of_le_of_ne h_l_le_b ?_;
  unfold b_val at *;
  intro h; have := congr_arg ( ·.factorization 3 ) h; norm_num at this;
  unfold k_val at this; aesop

/-

The integer $3^k$ is the only positive integer smaller than $b$ which is
divisible by $3^k$. That is, for all $i < b$ with $i \neq 3^k$ we have
$\nu_3(i) \le k-1$.
-/
lemma threetothekisunique (a : ℕ) (i : ℕ) (hi_pos : 1 ≤ i)
    (hi_lt : i < b_val a) (hi_ne : i ≠ 3 ^ (k_val a)) :
  padicValNat 3 i ≤ k_val a - 1 := by
    -- By definition of $k_val$, we know that $3^{k_val a}$ is the smallest
    -- power of 3 greater than or equal to $a$.
    have h_k_val : ¬(3 ^ k_val a ∣ i) := by
      contrapose! hi_ne;
      rw [ b_val ] at hi_lt;
      obtain ⟨ k, rfl ⟩ := hi_ne;
      rcases k with ( _ | _ | k ) <;> norm_num at *
      nlinarith [ pow_pos ( show 0 < 3 by decide ) ( k_val a ) ];
    exact Nat.le_sub_one_of_lt
      (Nat.lt_of_not_ge fun h =>
        h_k_val <| dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _)

/-

For all primes $p$ and all rationals $x_1, x_2, \ldots, x_m$, we have
$\nu_p(x_1 + x_2 + \cdots + x_m) \ge
\min(\nu_p(x_1), \nu_p(x_2), \ldots \nu_p(x_m)).$
-/
lemma padicValRat_finset_sum_ge_min {α : Type*} (s : Finset α) (f : α → ℚ)
    (p : ℕ) [Fact p.Prime] (h : s.Nonempty) (hsum : (∑ i ∈ s, f i) ≠ 0) :
  padicValRat p (∑ i ∈ s, f i) ≥ s.inf' h (fun i => padicValRat p (f i)) := by
    induction h using Finset.Nonempty.cons_induction with
    | singleton a =>
      simp_all +decide
    | cons s ha hnot hs ih =>
      simp_all +decide;
      by_cases h' : f s = 0 <;>
        by_cases h'' : ∑ x ∈ ha, f x = 0 <;>
        simp_all +decide;
      by_cases h''' : padicValRat p (f s) = padicValRat p (∑ x ∈ ha, f x);
      · have h_val :
            padicValRat p (f s + ∑ x ∈ ha, f x) ≥
              min (padicValRat p (f s)) (padicValRat p (∑ x ∈ ha, f x)) := by
          exact padicValRat.min_le_padicValRat_add hsum;
        aesop;
      · cases min_cases ( padicValRat p ( f s ) ) ( padicValRat p ( ∑ x ∈ ha, f x ) ) <;>
          simp_all +decide [ padicValRat.add_eq_min ]

/-
We have $\nu_2(v_{a,b-1}) = \nu_2(v_{a,b}) = l$.
-/
set_option linter.flexible false in
lemma pequaltotwovaluationofvabminusoneandvb (a : ℕ) (ha : a > 0) :
  padicValRat 2 (v a (b_val a - 1)) = l_val a ∧
    padicValRat 2 (v a (b_val a)) = l_val a := by
    -- Let $b'$ be either $b-1$ or $b$, and consider
    -- $\frac{u}{v} := \frac{u_{a,b'}}{v_{a,b'}} - \frac{1}{2^l}$.
    -- Lemma \ref{twotothelisunique} gives the lower bound on all remaining
    -- summands, and Lemma \ref{eqmin} identifies the denominator valuation.
    have h2_val :
        ∀ b' ∈ [b_val a - 1, b_val a],
          padicValRat 2 (harmonicSum a b') = -l_val a := by
      intro b' hb'
      have h_frac :
          padicValRat 2 ((harmonicSum a b') - (1 / 2 ^ (l_val a) : ℚ)) ≥
            -(l_val a - 1 : ℤ) := by
        -- Lemma \ref{twotothelisunique} gives the valuation bound termwise.
        have h_frac_ge :
            padicValRat 2
              (∑ i ∈ Finset.Icc a b' \ {2 ^ (l_val a)}, (1 : ℚ) / i) ≥
              -(l_val a - 1 : ℤ) := by
          have h_frac_ge :
              ∀ i ∈ Finset.Icc a b' \ {2 ^ (l_val a)},
                padicValRat 2 (1 / (i : ℚ)) ≥ -(l_val a - 1 : ℤ) := by
            intros i hi
            have h_frac_ge : padicValNat 2 i ≤ l_val a - 1 := by
              have h_frac_ge : i < 2 ^ (l_val a + 1) := by
                have h_frac_ge : b' < 2 ^ (l_val a + 1) := by
                  simp +zetaDelta at *;
                  exact hb'.elim
                    (fun h =>
                      h.symm ▸ Nat.lt_of_le_of_lt ( Nat.sub_le _ _ )
                        (by exact Nat.lt_pow_succ_log_self ( by decide ) _))
                    fun h => h.symm ▸ Nat.lt_pow_succ_log_self ( by decide ) _;
                exact lt_of_le_of_lt
                  (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi |>.1) |>.2) h_frac_ge;
              have h_frac_ge : ¬(2 ^ (l_val a) ∣ i) := by
                contrapose! h_frac_ge;
                obtain ⟨ k, hk ⟩ := h_frac_ge;
                rcases k with ( _ | _ | k ) <;> simp_all +decide [pow_succ];
              contrapose! h_frac_ge;
              exact dvd_trans ( pow_dvd_pow _ ( Nat.le_of_pred_lt h_frac_ge ) )
                ( Nat.ordProj_dvd _ _ );
            by_cases hi0 : i = 0 <;> simp_all +decide [ padicValRat ];
            simp_all +decide [
              Int.sign_eq_one_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hi0 ) ) ];
            exact_mod_cast Nat.succ_le_of_lt
              (lt_of_le_of_lt h_frac_ge
                (Nat.pred_lt
                  (ne_bot_of_gt
                    (Nat.log_pos one_lt_two
                      (show b_val a ≥ 2 by
                        exact le_trans ( by decide )
                          (Nat.mul_le_mul_left 2
                            (Nat.pow_le_pow_right ( by decide )
                              (Nat.succ_le_succ ( Nat.zero_le _ )))))))))
          by_cases hsum :
              (∑ i ∈ Finset.Icc a b' \ {2 ^ (l_val a)}, (1 : ℚ) / i) = 0;
          · rw [ hsum, padicValRat.zero ]
            norm_num
            linarith [ show ( l_val a : ℤ ) ≥ 2 by exact_mod_cast latleasttwo a ];
          · have h_frac_ge :
                ∀ {s : Finset ℕ} {f : ℕ → ℚ}, s.Nonempty →
                  (∀ i ∈ s, padicValRat 2 (f i) ≥ -(l_val a - 1 : ℤ)) →
                  (∑ i ∈ s, f i) ≠ 0 →
                  padicValRat 2 (∑ i ∈ s, f i) ≥ -(l_val a - 1 : ℤ) := by
              intros s f hs h_frac_ge hsum; exact (by
              have := padicValRat_finset_sum_ge_min s f 2 hs hsum;
              exact le_trans ( by aesop ) this);
            apply h_frac_ge;
            · exact Finset.nonempty_of_ne_empty fun h => hsum <| by rw [ h ] ; norm_num;
            · assumption;
            · assumption;
        simp_all +decide [ harmonicSum ];
        rw [
          Finset.sum_eq_sum_diff_singleton_add
            ( show 2 ^ l_val a ∈ Finset.Icc a b' from ?_ ) ]
        · aesop
        · rcases hb' with ( rfl | rfl );
          · refine Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩;
            · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( b_val a );
              norm_num [ Nat.pow_succ ] at *;
              linarith! [
                show b_val a ≥ 2 * a by
                  exact Nat.mul_le_mul_left 2
                    ( show a ≤ 3 ^ ( Nat.log 3 a + 1 ) by
                      exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ) ];
            · exact twotothelsmallerthanb a;
          · refine Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩;
            · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( b_val a );
              norm_num [ Nat.pow_succ', b_val ] at *;
              exact le_trans
                ( Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) )
                ( Nat.le_of_lt this );
            · exact Nat.pow_le_of_le_log
                ( by
                  linarith [
                    show 0 < b_val a from
                      Nat.mul_pos zero_lt_two ( pow_pos ( by decide ) _ ) ] )
                ( by
                  linarith [ show l_val a ≤ Nat.log 2 ( b_val a ) from Nat.le_refl _ ] );
      by_cases h : harmonicSum a b' - 1 / 2 ^ l_val a = 0 <;> simp_all +decide;
      · rw [ sub_eq_zero ] at h;
        rw [ h, padicValRat.inv, padicValRat.pow ] <;> norm_num;
        erw [ padicValRat.of_nat ] ; norm_num;
      · have :=
          eqmin 2 ( harmonicSum a b' - 1 / 2 ^ l_val a )
            ( 1 / 2 ^ l_val a ) ?_ ?_ ?_ ?_ <;> norm_num at *;
        · simp_all +decide [ padicValRat.inv ];
          norm_num [ padicValRat.pow ] at *;
          erw [ padicValRat.of_nat ] ; norm_num;
          linarith;
        · exact h;
        · intro H; simp_all +decide ;
          exact absurd H <| ne_of_gt <|
            Finset.sum_pos
              ( fun x hx =>
                one_div_pos.mpr <| Nat.cast_pos.mpr <| by
                  linarith [ Finset.mem_Icc.mp hx ] )
              ( Finset.nonempty_Icc.mpr <| by
                rcases hb' with ( rfl | rfl )
                · exact Nat.le_sub_one_of_lt <| by linarith [ blargerthana a ha ]
                · exact by linarith [ blargerthana a ha ] );
        · rw [ padicValRat.inv ];
          rw [ padicValRat.pow ] <;> norm_num;
          erw [ padicValRat.of_nat ] ; norm_num ; linarith;
    have h2_val_denom :
        ∀ b' ∈ [b_val a - 1, b_val a],
          padicValRat 2 (v a b') = -padicValRat 2 (harmonicSum a b') := by
      intro b' hb'
      have h_eq :
          padicValRat 2 (harmonicSum a b') =
            padicValRat 2 (↑(u a b')) - padicValRat 2 (↑(v a b')) := by
        have h_eq : harmonicSum a b' = ↑(u a b') / ↑(v a b') := by
          unfold harmonicSum u v;
          unfold harmonicSum; norm_num [ abs_of_nonneg, Rat.num_div_den ] ;
          rw [
            abs_of_nonneg
              ( mod_cast Rat.num_nonneg.mpr <|
                Finset.sum_nonneg fun _ _ => inv_nonneg.mpr <| Nat.cast_nonneg _ ),
            Rat.num_div_den ];
        by_cases hu : u a b' = 0 <;>
          by_cases hv : v a b' = 0 <;>
          simp_all +decide [ padicValRat.div ];
        · exact absurd h_eq <| ne_of_gt <|
            Finset.sum_pos
              ( fun x hx =>
                one_div_pos.mpr <| Nat.cast_pos.mpr <| by
                  linarith [ Finset.mem_Icc.mp hx ] )
              ( Finset.nonempty_Icc.mpr <| by
                have hb_le : a ≤ b' := by
                  rcases hb' with ( rfl | rfl )
                  · exact Nat.le_sub_one_of_lt <| by linarith [ blargerthana a ha ]
                  · exact Nat.le_of_lt <| by linarith [ blargerthana a ha ]
                linarith [hb_le] );
        · exact absurd hv ( Nat.ne_of_gt ( Rat.pos _ ) )
      have h_coprime : Nat.gcd (u a b') (v a b') = 1 := by
        exact Rat.reduced _;
      have h_coprime_val : padicValRat 2 (↑(u a b')) = 0 := by
        norm_num [ padicValRat ];
        exact Classical.or_iff_not_imp_left.2 fun h =>
          Nat.mod_two_ne_zero.mp fun h' =>
            absurd
              ( Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero h' )
                ( Nat.dvd_of_mod_eq_zero
                  ( show v a b' % 2 = 0 from
                    Nat.mod_eq_zero_of_dvd <| by
                      contrapose! h2_val;
                      simp_all +decide [ padicValRat ];
                      cases hb' <;>
                        simp_all +decide
                          [ padicValNat.eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero ] ) ) )
              ( by aesop );
      linarith;
    grind

/-
We have $\nu_3(v_{a,b-1}) = k$.
-/
set_option linter.flexible false in
lemma pequaltothreevaluationofvabminusone (a : ℕ) (ha : a > 0) :
  padicValRat 3 (v a (b_val a - 1)) = k_val a := by
    -- Lemma~\ref{threetothekisunique} gives the termwise lower bound.
    have huv :
        padicValRat 3 (harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a)) ≥
          -(k_val a - 1) := by
      -- Simplify the sum with the $3^k$ term removed.
      have h_simplify :
          harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a) =
            ∑ i ∈ Finset.Icc a (b_val a - 1) \ {3 ^ (k_val a)}, (1 : ℚ) / i := by
        unfold harmonicSum;
        rw [
          Finset.sum_eq_sum_diff_singleton_add <|
            show 3 ^ k_val a ∈ Finset.Icc a ( b_val a - 1 ) from ?_ ]
        · aesop
        · unfold k_val b_val;
          norm_num [ k_val ];
          exact ⟨
            Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ),
            Nat.le_sub_one_of_lt
              ( by linarith [ pow_pos ( by decide : 0 < 3 ) ( Nat.log 3 a + 1 ) ] ) ⟩;
      have h_nu_ge :
          ∀ i ∈ Finset.Icc a (b_val a - 1) \ {3 ^ (k_val a)},
            padicValRat 3 (1 / (i : ℚ)) ≥ -(k_val a - 1) := by
        intro i hi
        have h_nu_ge_i : padicValNat 3 i ≤ k_val a - 1 := by
          have := threetothekisunique a i
            ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hi |>.1 ) ] )
            ( by
              linarith [
                Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hi |>.1 ),
                Nat.sub_add_cancel
                  ( show 1 ≤ b_val a from
                    Nat.mul_pos two_pos ( pow_pos ( by decide ) _ ) ) ] )
            ( by aesop )
          aesop
        simp_all +decide;
        rw [ padicValRat.inv ] ; norm_num;
        exact_mod_cast Nat.succ_le_of_lt
          ( lt_of_le_of_lt h_nu_ge_i
            ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < k_val a from Nat.succ_pos _ ) ) ) );
      have h_eqminmoregeneral :
          ∀ {s : Finset ℕ} {f : ℕ → ℚ}, s.Nonempty →
            (∀ i ∈ s, padicValRat 3 (f i) ≥ -(k_val a - 1)) →
            padicValRat 3 (∑ i ∈ s, f i) ≥ -(k_val a - 1) := by
        intros s f hs h_nu_ge; exact (by
        by_cases hsum : ∑ i ∈ s, f i = 0;
        · simp [hsum];
          exact Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by unfold k_val; aesop ) );
        · have := padicValRat_finset_sum_ge_min s f 3 hs hsum;
          exact le_trans ( by exact Finset.le_inf' _ _ fun i hi => h_nu_ge i hi ) this);
      by_cases h_empty : Finset.Icc a (b_val a - 1) \ {3 ^ (k_val a)} = ∅;
      · simp_all +decide [ Finset.ext_iff ];
        exact Nat.succ_pos _;
      · exact h_simplify.symm ▸
          h_eqminmoregeneral ( Finset.nonempty_of_ne_empty h_empty ) h_nu_ge;
    -- Apply Lemma~\ref{eqmin} with the separated $3^k$ term.
    have hnu3_v : padicValRat 3 (harmonicSum a (b_val a - 1)) = -k_val a := by
      have hnu3_v :
          padicValRat 3 (harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a)) ≠
            padicValRat 3 (1 / 3 ^ (k_val a)) := by
        simp +zetaDelta at *;
        erw [ padicValRat.inv, padicValRat.pow ] <;> norm_num;
        erw [ padicValRat.self ] <;> norm_num ; linarith;
      have hnu3_v :
          padicValRat 3
              (harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a) +
                1 / 3 ^ (k_val a)) =
            min
              (padicValRat 3
                (harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a)))
              (padicValRat 3 (1 / 3 ^ (k_val a))) := by
        apply_rules [ eqmin ];
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
          -- Since $a \geq 1$, we have $\sum_{i=a}^{b-1} \frac{1}{i} \geq \frac{1}{a}$.
          have h_sum_ge_inv_a :
              ∑ i ∈ Finset.Icc a (b_val a - 1), (1 / (i : ℚ)) ≥ 1 / (a : ℚ) := by
            exact le_trans ( by norm_num )
              ( Finset.single_le_sum ( fun x _ => by positivity )
                ( Finset.left_mem_Icc.mpr
                  ( Nat.le_sub_one_of_lt
                    ( show a < b_val a from by linarith [ blargerthana a ha ] ) ) ) );
          -- Since $a \geq 1$, we have $\frac{1}{a} > \frac{1}{3^k}$.
          have h_inv_a_gt_inv_3k : (1 / (a : ℚ)) > (1 / (3 ^ k_val a : ℚ)) := by
            gcongr ; norm_cast;
            exact Nat.lt_pow_succ_log_self ( by decide ) _;
          exact h_inv_a_gt_inv_3k.not_ge <| h_sum_ge_inv_a.trans <| h.le.trans <| by norm_num;
        · positivity;
        · aesop;
      simp_all +decide;
      rw [ padicValRat.inv, padicValRat.pow ] <;> norm_num;
      erw [ padicValRat.of_nat ] ; norm_num ; linarith;
    rw [ padicValRat ] at *;
    norm_num [ padicValInt ] at *;
    -- Since $u_{a,b-1}$ and $v_{a,b-1}$ are coprime, we have $\nu_3(u_{a,b-1}) = 0$.
    have h_coprime :
        Nat.gcd (harmonicSum a (b_val a - 1)).num.natAbs
          (harmonicSum a (b_val a - 1)).den = 1 := by
      exact Rat.reduced _;
    by_cases h : 3 ∣ ( harmonicSum a ( b_val a - 1 ) |> Rat.num |> Int.natAbs ) <;>
      simp_all +decide [Nat.dvd_iff_mod_eq_zero];
    · have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero h )
        ( Nat.dvd_of_mod_eq_zero
          ( show ( harmonicSum a ( b_val a - 1 ) |> Rat.den ) % 3 = 0 from ?_ ) )
      · aesop
      · contrapose! hnu3_v
        rw [ padicValNat.eq_zero_of_not_dvd
          ( show ¬ 3 ∣ ( harmonicSum a ( b_val a - 1 ) |> Rat.den ) from
            fun h => hnu3_v <| Nat.mod_eq_zero_of_dvd h ) ]
        norm_num;
        exact fun _ => Nat.ne_of_gt ( Nat.succ_pos _ );
    · simp_all +decide [ padicValNat.eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero ];
      exact hnu3_v

/-
We have $\nu_3\left(\sum_{\substack{a \le i \le b-1 \\ i \neq 3^k}} \frac{1}{i} \right) \ge -k+1$.
-/
set_option linter.flexible false in
lemma padicValRat_harmonicSum_diff_ge (a : ℕ) (ha : a > 0) :
  padicValRat 3 (harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a)) ≥ -(k_val a - 1 : ℤ) := by
    -- We have the harmonic sum with the $3^k$ term separated.
    have h_sum :
        harmonicSum a (b_val a - 1) - 1 / 3 ^ (k_val a) =
          ∑ i ∈ Finset.Icc a (b_val a - 1), (1 : ℚ) / i - 1 / 3 ^ (k_val a) := by
      rfl;
    -- By Lemma \ref{threetothekisunique}, for all $i$ in this sum, $\nu_3(i) \le k-1$.
    have h_val :
        ∀ i ∈ Finset.Icc a (b_val a - 1), i ≠ 3 ^ (k_val a) →
          padicValRat 3 (1 / (i : ℚ)) ≥ -(k_val a - 1) := by
      intros i hi hi_ne
      have h_val_i : padicValNat 3 i ≤ k_val a - 1 := by
        have := threetothekisunique a i
          ( Finset.mem_Icc.mp hi |>.1.trans_lt' ha )
          ( Finset.mem_Icc.mp hi |>.2.trans_lt
            ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) zero_lt_one ) )
          hi_ne
        aesop
      rcases k : k_val a with ( _ | k ) <;> simp_all +decide [ padicValRat.inv ];
      unfold k_val at k; aesop;
    by_cases h : 3 ^ k_val a ∈ Finset.Icc a ( b_val a - 1 ) <;> simp_all +decide;
    · have h_sum_val :
          padicValRat 3
              (∑ i ∈ Finset.Icc a (b_val a - 1) \ {3 ^ k_val a}, (1 : ℚ) / i) ≥
            -(k_val a - 1) := by
        have h_sum_val :
            ∀ {s : Finset ℕ},
              (∀ i ∈ s, padicValRat 3 (1 / (i : ℚ)) ≥ -(k_val a - 1)) →
              (∑ i ∈ s, (1 : ℚ) / i) ≠ 0 →
              padicValRat 3 (∑ i ∈ s, (1 : ℚ) / i) ≥ -(k_val a - 1) := by
          intros s hs hs_nonzero
          have h_sum_val :
              padicValRat 3 (∑ i ∈ s, (1 : ℚ) / i) ≥
                Finset.inf' s
                  (by exact Finset.nonempty_of_ne_empty ( by aesop_cat ))
                  (fun i => padicValRat 3 (1 / (i : ℚ))) := by
            all_goals generalize_proofs at *;
            convert
              padicValRat_finset_sum_ge_min s ( fun i => 1 / ( i : ℚ ) ) 3
                ‹_› hs_nonzero using 1
          generalize_proofs at *;
          exact le_trans ( Finset.le_inf' _ _ fun i hi => hs i hi ) h_sum_val;
        apply h_sum_val;
        · aesop;
        · refine ne_of_gt ( Finset.sum_pos ?_ ?_ );
          · exact fun i hi =>
              one_div_pos.mpr <| Nat.cast_pos.mpr <| by
                linarith [ Finset.mem_Icc.mp <| Finset.mem_sdiff.mp hi |>.1 ] ;
          · refine Finset.card_pos.mp ?_;
            rw [ Finset.card_sdiff ] ; norm_num [ h ];
            rw [ Nat.lt_sub_iff_add_lt ];
            rw [ add_comm ] ; gcongr;
            exact lt_of_lt_of_le
              ( show a < 3 ^ k_val a from Nat.lt_pow_succ_log_self ( by decide ) _ )
              h.2;
      simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    · contrapose! h;
      unfold b_val k_val;
      exact ⟨
        Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ),
        Nat.le_sub_one_of_lt
          ( by linarith [ pow_pos ( by decide : 0 < 3 ) ( Nat.log 3 a + 1 ) ] ) ⟩

/-
We have $\nu_3(v_{a,b}) \le k-1$.
-/
set_option linter.flexible false in
lemma pequaltothreevaluationofvab (a : ℕ) (ha : a > 0) :
  padicValRat 3 (v a (b_val a)) ≤ k_val a - 1 := by
    by_contra h_contra;
    have h_neg_val : padicValRat 3 (harmonicSum a (b_val a)) < -((k_val a : ℤ) - 1) := by
      rw [ show harmonicSum a ( b_val a ) = ( u a ( b_val a ) : ℚ ) / v a ( b_val a ) from ?_ ];
      · have h_val :
            padicValRat 3 (u a (b_val a) / v a (b_val a)) =
              -padicValRat 3 (v a (b_val a)) := by
          have h_coprime : Int.gcd (u a (b_val a)) (v a (b_val a)) = 1 := by
            exact Rat.reduced _
          have h_val :
              padicValRat 3 (u a (b_val a) / v a (b_val a)) =
                padicValRat 3 (u a (b_val a)) - padicValRat 3 (v a (b_val a)) := by
            convert padicValRat.div _ _ <;> norm_num [ h_coprime ];
            · exact ⟨ trivial ⟩;
            · intro h; simp_all +decide ;
              exact absurd h_contra ( Nat.ne_of_gt ( Nat.succ_pos _ ) );
            · exact Nat.ne_of_gt ( Rat.pos _ );
          have h_val : ¬(3 ∣ u a (b_val a)) := by
            intro h_div
            have h_contra : 3 ∣ v a (b_val a) := by
              have h_contra : padicValRat 3 (v a (b_val a)) > 0 := by
                linarith [
                  show ( k_val a : ℤ ) ≥ 1 from
                    mod_cast Nat.one_le_iff_ne_zero.mpr
                      ( Nat.ne_of_gt ( Nat.succ_pos _ ) ) ];
              exact Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| by
                contrapose! h_contra;
                simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] );
            exact absurd
              ( Int.dvd_coe_gcd
                ( Int.natCast_dvd_natCast.mpr h_div )
                ( Int.natCast_dvd_natCast.mpr h_contra ) )
              ( by norm_num [ h_coprime ] );
          rw [ padicValRat.of_nat ] ; aesop;
        linarith;
      · unfold u v;
        norm_num [
          abs_of_nonneg
            ( Rat.num_nonneg.mpr
              ( show 0 ≤ harmonicSum a ( b_val a ) from
                Finset.sum_nonneg fun _ _ => by positivity ) ),
          Rat.num_div_den ];
    -- Decompose $H_{a,b}$ into the part without $3^k$ and the remaining terms.
    obtain ⟨X, Y, hXY⟩ :
        ∃ X Y : ℚ,
          harmonicSum a (b_val a) = X + Y ∧
            padicValRat 3 X ≥ -(k_val a - 1 : ℤ) ∧
              padicValRat 3 Y = -(k_val a - 1 : ℤ) := by
      refine ⟨
        harmonicSum a ( b_val a - 1 ) - 1 / 3 ^ ( k_val a ),
        1 / 3 ^ ( k_val a ) + 1 / ( 2 * 3 ^ ( k_val a ) ), ?_, ?_, ?_ ⟩ <;>
        norm_num;
      · unfold harmonicSum;
        norm_num [ Finset.sum_Ioc_succ_top,
          (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring_nf;
        erw [ Finset.sum_Ico_succ_top ] <;> norm_num [ b_val ];
        · cases h : 2 * 3 ^ k_val a <;> aesop;
        · exact le_trans
            ( show a ≤ 3 ^ k_val a by
              exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) )
            ( by linarith [ pow_pos ( by decide : 0 < 3 ) ( k_val a ) ] );
      · have := padicValRat_harmonicSum_diff_ge a ha;
        grind;
      · field_simp;
        rw [ padicValRat.div, padicValRat.mul ] <;> norm_num;
        norm_num [ padicValRat.pow ];
        erw [ padicValRat.of_nat, padicValRat.of_nat ] ; norm_num;
    have h_ultra : padicValRat 3 (X + Y) ≥ min (padicValRat 3 X) (padicValRat 3 Y) := by
      apply_rules [ padicValRat.min_le_padicValRat_add ];
      intro h; simp_all +decide ;
      exact absurd hXY.1 <| ne_of_gt <|
        Finset.sum_pos
          ( fun x hx =>
            one_div_pos.mpr <| Nat.cast_pos.mpr <| by
              linarith [ Finset.mem_Icc.mp hx ] )
          ( Finset.nonempty_Icc.mpr <| by linarith [ blargerthana a ha ] );
    grind

/-

We have $\nu_3(v_{a,b}) \le k-1$.
-/
lemma pequaltothreevaluationofvab_final (a : ℕ) (ha : a > 0) :
  padicValRat 3 (v a (b_val a)) ≤ k_val a - 1 := by
    convert pequaltothreevaluationofvab a ha using 1

/-
For every positive integer $a$ there exists a positive integer $b$ with
$a < b \le 6a$ such that $v_{a,b} < v_{a,b-1}$.
-/
set_option linter.flexible false in
theorem main (a : ℕ) (ha : a > 0) : ∃ b, a < b ∧ b ≤ 6 * a ∧ v a b < v a (b - 1) := by
  use b_val a;
  -- By combining the results from the lemmas, we conclude that $v_{a,b} < v_{a,b-1}$.
  have h_div : v a (b_val a) ∣ v a (b_val a - 1) := by
    -- By definition of $v$, it suffices to compare prime-adic valuations.
    have h_denom_def :
        ∀ p : ℕ, Nat.Prime p →
          padicValRat p (v a (b_val a)) ≤ padicValRat p (v a (b_val a - 1)) := by
      intro p pp;
      by_cases hp : p > 3;
      · have := @plargerthanthreevaluationofvabminusone a p;
        by_cases h : p ∣ v a ( b_val a ) <;> simp_all +decide [ padicValNat.eq_zero_of_not_dvd ];
      · interval_cases p <;> simp_all +decide;
        · have := pequaltotwovaluationofvabminusoneandvb a ha; aesop;
        · have h_final := pequaltothreevaluationofvab_final a ha;
          have h_minus := pequaltothreevaluationofvabminusone a ha;
          norm_num [ padicValRat ] at h_final h_minus ⊢;
          omega;
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
    · exact Rat.den_nz _;
    · exact Nat.ne_of_gt <| Rat.pos _;
  refine ⟨
    blargerthana a ha,
    bsmallerthansixa a ha,
    lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ?_ ) h_div ) ?_ ⟩;
  · exact Rat.den_nz _;
  · have := pequaltothreevaluationofvab_final a ha
    have := pequaltothreevaluationofvabminusone a ha
    aesop;

end Erdos290

#print axioms Erdos290.main
-- 'Erdos290.main' depends on axioms: [propext, Classical.choice, Quot.sound]
