/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 459.
https://www.erdosproblems.com/forum/thread/459

Informal authors:
- Stijn Cambie

Formal authors:
- Aristotle
- Boris Alexeev
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/459#post-4716
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem459.lean
-/
/-
For a positive integer $u$, we define $f(u)$ to be the largest integer $v > u$
such that every integer $m$ with $u < m < v$ has a prime divisor that does not
divide $uv$. Equivalently, $f(u)$ is the smallest number $v > u$ such that all
prime factors of $v$ divide $u$. With this definition, estimating $f(u)$ is
Erdős Problem #459 (https://www.erdosproblems.com/459).

One can observe that we have $u+2 \le f(u) \le u^2$ for all
$u \in \mathbb{N}$. Furthermore, the upper bound is exact whenever $u$ is prime,
while the lower bound is tight for all $u = 2^k-2$ with $k \ge 2$. In February
2026 Boris Alexeev managed to formalize these results in Lean. He didn't
consider his formalization fully finished however, as it was still missing the
following result from Stijn Cambie:

For almost all $n$ we have $f(n) = (1 + o(1))n$. That is, for every
$\delta > 0$ and $\epsilon > 0$, there is an $x_0$ such that for all
$x \ge x_0$ at least $(1 - \delta)x$ integers $n \le x$ have
$f(n) < (1 + epsilon)n$.

Finishing what Boris started, Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun) managed to formalize the above result, and
below you can find the union of Boris' and Aristotle's fruits of labor.

-/

import Mathlib

namespace Erdos459

/-
f(u) is the smallest number v > u such that all prime factors of v are factors of u.
-/
def f (u : ℕ) : ℕ :=
  if h : u < 2 then 0
  else Nat.find (show ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors by
    -- Let $p$ be a prime factor of $u$. Then $u \cdot p$ is divisible by all
    -- prime factors of $u$.
    obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
      exact Nat.exists_prime_and_dvd ( by linarith )
    -- Let $v = u \cdot p$. Then $v$ is divisible by all prime factors of $u$
    -- and $v > u$.
    use u * p
    exact ⟨
      lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt,
      fun x hx => by
        rw [ Nat.primeFactors_mul ] at * <;> aesop⟩)

/-
For u ≥ 2, u + 2 ≤ f(u) ≤ u^2.
-/
set_option linter.flexible false in
theorem f_bounds {u : ℕ} (hu : 2 ≤ u) : u + 2 ≤ f u ∧ f u ≤ u ^ 2 := by
  -- Let's first prove that $u + 2 \leq f(u)$.
  have h_lower_bound : u + 2 ≤ f u := by
    -- By definition of $f$, we know that $f(u)$ is the smallest number greater
    -- than $u$ such that all prime factors of $f(u)$ are factors of $u$.
    have hf_def : ∀ v, u < v → v.primeFactors ⊆ u.primeFactors → u + 2 ≤ v := by
      intro v hv₁ hv₂
      rcases Nat.even_or_odd' v with ⟨ k, rfl | rfl ⟩ <;>
        rcases Nat.even_or_odd' u with ⟨ l, rfl | rfl ⟩ <;>
        simp_all +arith +decide only [Nat.reduceLeDiff, Order.add_one_le_iff,
          Order.lt_two_iff, mul_lt_mul_iff_right₀]
      · linarith [ show k > l by linarith ]
      · contrapose! hv₂
        norm_num [ show k = l + 1 by linarith ]
        norm_num [ Finset.subset_iff, Nat.primeFactors_mul ]
      · by_contra h_contra₁
        simp_all +arith +decide [ Finset.subset_iff ]
        norm_num [ show k = l by linarith ] at *
        exact absurd
          (hv₂ ( Nat.minFac_prime ( by linarith ) ) ( Nat.minFac_dvd _ ))
          (by
            intro t
            have := Nat.dvd_gcd t.1 ( Nat.minFac_dvd _ )
            aesop)
      · grind
    have h_exists : ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors := by
      -- Let $p$ be a prime factor of $u$. Then $u \cdot p$ is divisible by all
      -- prime factors of $u$ and $u \cdot p > u$.
      obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
        exact Nat.exists_prime_and_dvd ( by linarith )
      use u * p
      exact ⟨
        lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt,
        by
          rw [ Nat.primeFactors_mul ( by linarith ) ( by linarith [ hp.1.pos ] ) ]
          aesop_cat⟩
    convert hf_def _
      ( Nat.find_spec h_exists |>.1 )
      ( Nat.find_spec h_exists |>.2 )
      using 1
    unfold f
    split
    next h => exact (False.elim ((Nat.not_lt_of_ge hu) h))
    next h => rfl
  refine ⟨ h_lower_bound, ?_ ⟩
  -- By definition of $f$, we know that $f(u)$ is the smallest integer greater
  -- than $u$ such that all prime factors of $f(u)$ are factors of $u$.
  have h_def : ∀ v > u, v.primeFactors ⊆ u.primeFactors → f u ≤ v := by
    unfold f
    aesop
  exact h_def _ ( by nlinarith ) ( by rw [ Nat.primeFactors_pow ]; aesop )

/-
When p is prime, f(p) = p^2.
-/
set_option linter.flexible false in
theorem f_prime {p : ℕ} (hp : p.Prime) : f p = p ^ 2 := by
  apply le_antisymm
  · exact f_bounds hp.two_le |>.2
  -- By definition of $f$, we know that $p^2$ is the smallest integer greater
  -- than $p$ whose prime factors are all factors of $p$.
  · have h_fp_def : ∀ v, p < v ∧ v.primeFactors ⊆ {p} → p^2 ≤ v := by
    -- If $v$'s prime factors are all $p$, then $v$ must be $p^k$ for some $k$.
      intro v hv
      obtain ⟨k, hk⟩ : ∃ k, v = p^k := by
        rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : v ≠ 0 ) ]
        rw [ Finsupp.prod ]
        aesop
      exact hk.symm ▸ Nat.pow_le_pow_right hp.pos
        (show k ≥ 2 by
          contrapose! hv
          interval_cases k <;> aesop)
    unfold f at *
    split_ifs at * <;> simp_all +decide
    · interval_cases p <;> trivial
    · grind

/-
If u is a non-zero even number, the prime factors of any power of 2 are a
subset of the prime factors of u.
-/
set_option linter.flexible false in
theorem primeFactors_pow_two_subset_even {u k : ℕ} (hu : Even u) (hu0 : u ≠ 0) :
    (2 ^ k).primeFactors ⊆ u.primeFactors := by
  rcases k with ( _ | k ) <;> simp_all +decide [ Nat.primeFactors_pow ]
  exact even_iff_two_dvd.mp hu

/-
For n ≥ 1, n ≤ 2^(size(n-1)).
-/
theorem le_pow_size_sub_one {n : ℕ} (hn : 1 ≤ n) : n ≤ 2 ^ (n - 1).size := by
  -- Let $m = n - 1$. Then $n = m + 1$.
  set m : ℕ := n - 1
  -- By definition of size, we know that $m < 2^{\text{size}(m)}$.
  have h_size : m < 2 ^ (Nat.size m) := by
    exact Nat.lt_size_self m
  grind

/-
For any natural number u, u < 2^(u.size).
-/
theorem lt_pow_size (u : ℕ) : u < 2 ^ u.size := by
  exact Nat.lt_size_self u

/-
If u is even, then f(u) is at most the smallest power of 2 greater than u.
-/
theorem f_even_le_next_pow_two {u : ℕ} (hu_even : Even u) (hu_pos : 0 < u) :
    f u ≤ 2 ^ (Nat.log 2 u + 1) := by
  -- Since $u$ is even, $u$ has at least one factor of 2.
  have h_even_factor : u.primeFactors ⊇ {2} := by
    exact Finset.singleton_subset_iff.mpr
      ( Nat.mem_primeFactors.mpr
        ⟨ Nat.prime_two, even_iff_two_dvd.mp hu_even, by aesop ⟩ )
  -- Since $2^{Nat.log 2 u + 1}$ is greater than $u$ and all its prime factors
  -- are in $u$'s prime factors, it must be that
  -- $f(u) \leq 2^{Nat.log 2 u + 1}$.
  have h_f_le : ∀ v, u < v → v.primeFactors ⊆ u.primeFactors → f u ≤ v := by
    unfold f
    aesop
  exact h_f_le _ ( Nat.lt_pow_succ_log_self ( by decide ) _ )
    (by
      rw [ Nat.primeFactors_pow ] <;> norm_num
      aesop)

/-
For k ≥ 2, f(2^k - 2) = (2^k - 2) + 2.
-/
set_option linter.flexible false in
theorem f_eq_u_plus_two_of_u_eq_pow_two_sub_two {k : ℕ} (hk : 2 ≤ k) :
    f (2 ^ k - 2) = (2 ^ k - 2) + 2 := by
  apply le_antisymm
  · -- For $k \geq 2$, $2^k - 2$ is even, so we can apply the theorem
    -- $f_even_le_next_pow_two$.
    have h_even : Even (2 ^ k - 2) := by
      exact even_iff_two_dvd.mpr
        ( Nat.dvd_sub ( dvd_pow_self _ ( by linarith ) ) ( by norm_num ) )
    convert f_even_le_next_pow_two h_even
      ( Nat.sub_pos_of_lt <| by linarith [ Nat.pow_le_pow_right two_pos hk ] )
      using 1
    rw [ Nat.sub_add_cancel
      ( show 2 ≤ 2 ^ k from
        le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hk ) ) ]
    -- Since $2^k - 2$ is less than $2^k$, we have $\log_2(2^k - 2) = k - 1$.
    have h_log : Nat.log 2 (2 ^ k - 2) = k - 1 := by
      rw [ Nat.log_eq_iff ] <;> norm_num
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ]
        exact le_tsub_of_add_le_left ( by linarith [ Nat.one_le_pow k 2 zero_lt_two ] )
      · exact Or.inl ( Nat.sub_ne_zero_of_lt hk )
    cases k <;> aesop
  · have := f_bounds
      ( show 2 ≤ 2 ^ k - 2 from
        Nat.le_sub_of_add_le ( by linarith [ Nat.pow_le_pow_right two_pos hk ] ) )
    aesop

/-
There are infinitely many u such that f(u) = u + 2.
-/
theorem infinite_setOf_f_eq_self_add_two : Set.Infinite {u | f u = u + 2} := by
  -- By definition of $f$, we know that for any $k \geq 2$,
  -- $f(2^k - 2) = (2^k - 2) + 2$.
  have h_f_eq_add_two : ∀ k ≥ 2, f (2^k - 2) = (2^k - 2) + 2 := by
    exact fun k a => f_eq_u_plus_two_of_u_eq_pow_two_sub_two a;
  exact Set.infinite_of_forall_exists_gt fun n =>
    ⟨ _,
      h_f_eq_add_two ( n + 2 ) ( by linarith ),
      lt_tsub_iff_right.mpr (by
        induction n with
        | zero => norm_num
        | succ n ih =>
            norm_num [ Nat.pow_succ' ] at *
            linarith [ Nat.one_le_pow n 2 zero_lt_two ])⟩

/-
There are infinitely many u such that f(u) = u^2.
-/
theorem infinite_setOf_f_eq_sq : Set.Infinite {u | f u = u ^ 2} := by
  exact Nat.infinite_setOf_prime.mono
    ( fun p hp ↦ by simpa [ hp.ne_zero ] using f_prime hp )
    |> Set.Infinite.mono fun u hu ↦ by
      aesop

/-
A set $A \subseteq \mathbb{N}$ has natural density $d$ if
$\lim_{n \to \infty} \frac{|A \cap \{0, \dots, n-1\}|}{n} = d$. The natural
density is defined as this limit if it exists, and 0 otherwise.
-/
set_option linter.style.openClassical false

open Classical

def has_natural_density (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun n => (Finset.filter (fun k => k ∈ A) (Finset.range n)).card / (n : ℝ))
    Filter.atTop (nhds d)

/-
The natural density of the set of integers coprime to $k$ is $\phi(k)/k$.
-/
set_option linter.flexible false in
lemma density_coprime (k : ℕ) (hk : k > 0) :
  has_natural_density {n | k.Coprime n} ((Nat.totient k : ℝ) / k) := by
    have h_density :
        Filter.Tendsto
          (fun n => ∑ i ∈ Finset.range n,
            (if Nat.Coprime k i then 1 else 0) / (n : ℝ))
          Filter.atTop (nhds ((Nat.totient k : ℝ) / k)) := by
      -- We'll use the fact that the number of integers up to $n$ that are
      -- coprime to $k$ is approximately $\frac{n}{k} \phi(k)$ to show the
      -- limit.
      have h_approx :
          ∀ m : ℕ,
            ∑ i ∈ Finset.range (m * k), (if k.Coprime i then 1 else 0) =
              m * Nat.totient k := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          rw [ Nat.succ_mul, Finset.sum_range_add, ih ];
          simp +decide [add_mul];
          exact congr_arg Finset.card
            ( Finset.filter_congr fun x hx => by rw [ Nat.coprime_comm ] )
      -- Using the approximation, we can bound the sum.
      have h_bound :
          ∀ n : ℕ, n ≥ k →
            |∑ i ∈ Finset.range n, (if k.Coprime i then 1 else 0) -
              (n : ℝ) * Nat.totient k / k| ≤ k := by
        intros n hn
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m * k ≤ n ∧ n < (m + 1) * k := by
          exact ⟨
            n / k,
            Nat.div_mul_le_self _ _,
            by linarith [ Nat.div_add_mod n k, Nat.mod_lt n hk ]⟩
        -- Using the approximation, we can bound the sum for $n$ between
        -- $m * k$ and $(m + 1) * k$.
        have h_bound :
            ∑ i ∈ Finset.range n, (if k.Coprime i then 1 else 0) ≥
                m * Nat.totient k ∧
              ∑ i ∈ Finset.range n, (if k.Coprime i then 1 else 0) ≤
                (m + 1) * Nat.totient k := by
          exact ⟨
            by
              rw [ ← h_approx m ]
              exact Finset.sum_le_sum_of_subset ( Finset.range_mono hm.1 ),
            by
              rw [ ← h_approx ( m + 1 ) ]
              exact Finset.sum_le_sum_of_subset ( Finset.range_mono hm.2.le )⟩
        rw [ abs_le ]
        constructor <;>
          nlinarith [
            show ( k : ℝ ) > 0 by positivity,
            show ( Nat.totient k : ℝ ) ≤ k by exact_mod_cast Nat.totient_le k,
            mul_div_cancel₀ ( ( n : ℝ ) * Nat.totient k )
              ( by positivity : ( k : ℝ ) ≠ 0 ),
            show ( ∑ i ∈ Finset.range n, if k.Coprime i then 1 else 0 : ℝ ) ≥
                m * Nat.totient k by exact_mod_cast h_bound.1,
            show ( ∑ i ∈ Finset.range n, if k.Coprime i then 1 else 0 : ℝ ) ≤
                ( m + 1 ) * Nat.totient k by exact_mod_cast h_bound.2,
            show ( n : ℝ ) ≥ m * k by exact_mod_cast hm.1,
            show ( n : ℝ ) < ( m + 1 ) * k by exact_mod_cast hm.2]
      -- Using the bound, we can show that the limit of the average is $\frac{\phi(k)}{k}$.
      have h_limit :
          Filter.Tendsto
            (fun n =>
              (∑ i ∈ Finset.range n, (if k.Coprime i then 1 else 0) : ℝ) / n)
            Filter.atTop (nhds ((Nat.totient k : ℝ) / k)) := by
        have h_limit :
            Filter.Tendsto
              (fun n =>
                ((∑ i ∈ Finset.range n,
                    (if k.Coprime i then 1 else 0) : ℝ) -
                  (n : ℝ) * Nat.totient k / k) / n)
              Filter.atTop (nhds 0) := by
          refine squeeze_zero_norm' (a := fun n : ℕ => (k : ℝ) / n) ?_ ?_
          · exact Filter.eventually_atTop.mpr ⟨ k, fun n hn => by
              simpa [ abs_div ] using
                div_le_div_of_nonneg_right ( h_bound n hn ) ( Nat.cast_nonneg n )⟩
          · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        simpa using
          (h_limit.add_const ( k.totient / k : ℝ ) |>
            Filter.Tendsto.congr' (by
              filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn
              simp +decide [ sub_div, mul_div_assoc, hn.ne' ]))
      simpa only [ Finset.sum_div _ _ _ ] using h_limit;
    refine h_density.congr' ?_
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by
      rw [ ← Finset.sum_div, Finset.card_filter ]
      aesop

/-
If a set $A$ has natural density $d$, then the set scaled by $p$ has natural density $d/p$.
-/
set_option linter.flexible false in
set_option linter.style.multiGoal false in
lemma density_scaled (A : Set ℕ) (d : ℝ) (p : ℕ) (hp : p > 0)
    (hA : has_natural_density A d) :
  has_natural_density {n | ∃ a ∈ A, n = p * a} (d / p) := by
    -- By definition of natural density, we know that the density of $A$ is $d$.
    have hA_density :
        Filter.Tendsto
          (fun n => ((Finset.filter (fun k => k ∈ A) (Finset.range n)).card : ℝ) / n)
          Filter.atTop (nhds d) := by
      exact hA;
    -- We'll use the fact that if the density of $A$ is $d$, then the density
    -- of $pA$ is $d/p$.
    have h_subset :
        Filter.Tendsto
          (fun n =>
            ((Finset.filter (fun k => p * k ∈ {n | ∃ a ∈ A, n = p * a})
              (Finset.range n)).card : ℝ) / n)
          Filter.atTop (nhds d) := by
      simp_all +decide [hp.ne'];
    -- Let's simplify the expression inside the limit further.
    suffices h_simplified' :
        Filter.Tendsto
          (fun n =>
            ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
              (Finset.range (n * p))).card : ℝ) / (n * p))
          Filter.atTop (nhds (d / p)) by
      have h_final :
          Filter.Tendsto
            (fun n =>
              ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                (Finset.range n)).card : ℝ) / n)
            Filter.atTop (nhds (d / p)) := by
        have h_final :
            Filter.Tendsto
              (fun n =>
                ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                  (Finset.range (n * p))).card : ℝ) / (n * p))
              Filter.atTop (nhds (d / p)) →
            Filter.Tendsto
              (fun n =>
                ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                  (Finset.range n)).card : ℝ) / n)
              Filter.atTop (nhds (d / p)) := by
          intro h
          have :
              ∀ n,
                ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                  (Finset.range n)).card : ℝ) / n =
                ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                  (Finset.range (⌊n / p⌋₊ * p))).card : ℝ) /
                    (⌊n / p⌋₊ * p) * (⌊n / p⌋₊ * p / n) +
                  ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                    (Finset.Ico (⌊n / p⌋₊ * p) n)).card : ℝ) / n := by
            intro n
            by_cases hn : n < p;
            · simp +decide [ Nat.div_eq_of_lt hn ];
            · rw [ div_mul_div_cancel₀ ];
              · rw [ ← add_div, ← Nat.cast_add, Finset.card_filter,
                  Finset.card_filter, Finset.card_filter ];
                rw [ Finset.sum_range_add_sum_Ico _
                  ( show ⌊n / p⌋₊ * p ≤ n from Nat.div_mul_le_self _ _ ) ];
              · exact mul_ne_zero
                  ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <|
                    Nat.floor_pos.mpr <| Nat.div_pos ( le_of_not_gt hn ) hp )
                  ( Nat.cast_ne_zero.mpr hp.ne' )
          -- The second term tends to zero as $n$ tends to infinity.
          have h_second_term :
              Filter.Tendsto
                (fun n =>
                  ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                    (Finset.Ico (⌊n / p⌋₊ * p) n)).card : ℝ) / n)
                Filter.atTop (nhds 0) := by
            -- The cardinality of the set in this short interval is at most $p$.
            have h_card_bound :
                ∀ n,
                  ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                    (Finset.Ico (⌊n / p⌋₊ * p) n)).card : ℝ) ≤ p := by
              intro n
              have h_card_bound :
                  ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                    (Finset.Ico (⌊n / p⌋₊ * p) n)).card : ℝ) ≤
                    Finset.card (Finset.Ico (⌊n / p⌋₊ * p) n) := by
                exact_mod_cast Finset.card_filter_le _ _;
              simp +zetaDelta at *
              exact h_card_bound.trans
                ( Nat.sub_le_of_le_add <| by
                  nlinarith [ Nat.div_add_mod n p, Nat.mod_lt n hp ] )
            exact squeeze_zero
              ( fun n => by positivity )
              ( fun n => mul_le_mul_of_nonneg_right ( h_card_bound n ) ( by positivity ) )
              ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop )
          -- The first term tends to $d/p$ as $n$ tends to infinity.
          have h_first_term :
              Filter.Tendsto
                (fun n =>
                  ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                    (Finset.range (⌊n / p⌋₊ * p))).card : ℝ) /
                      (⌊n / p⌋₊ * p) * (⌊n / p⌋₊ * p / n))
                Filter.atTop (nhds (d / p)) := by
            have h_first_term :
                Filter.Tendsto
                  (fun n =>
                    ((Finset.filter (fun k => k ∈ {n | ∃ a ∈ A, n = p * a})
                      (Finset.range (⌊n / p⌋₊ * p))).card : ℝ) /
                        (⌊n / p⌋₊ * p))
                  Filter.atTop (nhds (d / p)) := by
              exact h.comp <| tendsto_nat_floor_atTop.comp <|
                Filter.tendsto_atTop_atTop.mpr fun x =>
                  ⟨ x * p, fun n hn => Nat.le_div_iff_mul_le hp |>.2 <| by nlinarith ⟩
            have h_second_term :
                Filter.Tendsto (fun n => (⌊n / p⌋₊ * p : ℝ) / n)
                  Filter.atTop (nhds 1) := by
              have h_second_term :
                  Filter.Tendsto (fun n => (⌊n / p⌋₊ : ℝ) / (n / p))
                    Filter.atTop (nhds 1) := by
                have h_second_term :
                    Filter.Tendsto (fun n => (⌊n⌋₊ : ℝ) / n) Filter.atTop
                      (nhds 1) := by
                  rw [ Metric.tendsto_nhds ];
                  intro ε hε
                  filter_upwards
                    [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( ε⁻¹ ) ]
                    with x hx₁ hx₂ using abs_lt.mpr ⟨
                      by
                        nlinarith [ Nat.floor_le hx₁.le, Nat.lt_floor_add_one x,
                          mul_inv_cancel₀ hε.ne',
                          div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₁.ne' ],
                      by
                        nlinarith [ Nat.floor_le hx₁.le, Nat.lt_floor_add_one x,
                          mul_inv_cancel₀ hε.ne',
                          div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₁.ne' ]⟩
                field_simp;
                convert h_second_term.comp
                  ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) / p ) Filter.atTop
                      Filter.atTop from
                    Filter.Tendsto.atTop_div_const ( by positivity )
                      tendsto_natCast_atTop_atTop )
                  using 2
                norm_num [ hp.ne' ];
                field_simp [mul_comm, mul_assoc, mul_left_comm];
                erw [ Nat.floor_div_natCast, Nat.floor_natCast ];
              simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hp.ne' ] using
                h_second_term
            simpa using h_first_term.mul h_second_term;
          simpa only [ this, add_zero ] using h_first_term.add h_second_term;
        exact h_final h_simplified';
      exact h_final;
    convert h_subset.comp
      ( show Filter.Tendsto ( fun n => n ) Filter.atTop Filter.atTop from
        Filter.tendsto_id ) |> fun h => h.div_const p using 2
    norm_num
    ring_nf
    rw [
      show
          ( Finset.filter ( fun n => ∃ a ∈ A, n = p * a ) ( Finset.range ( p * _ ) ) ) =
            Finset.image ( fun k => p * k )
              ( Finset.filter ( fun k => ∃ a ∈ A, k = a ∨ p = 0 )
                ( Finset.range ‹_› ) ) from ?_,
      Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hp.ne' hxy]
    ring
    aesop

/-
The density of integers divisible by $p \in S$ and no other prime in $S$ is
$\frac{1}{p} \prod_{q \in S \setminus \{p\}} (1 - \frac{1}{q})$.
-/
set_option linter.flexible false in
lemma density_exact_prime (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (p : ℕ) (hp : p ∈ S) :
  has_natural_density {n | p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬ q ∣ n}
    ((1 / p : ℝ) * (∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ)))) := by
    -- Let $A$ be the set of integers not divisible by any prime in $S$ except $p$.
    set A := {n : ℕ | ∀ q ∈ S, q ≠ p → ¬q ∣ n} with hA_def
    have hA_density : has_natural_density A (∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ))) := by
      -- The set $A$ is the set of integers coprime to the product of primes in $S \setminus \{p\}$.
      have hA_coprime : A = {n : ℕ | Nat.Coprime n (∏ q ∈ S \ {p}, q)} := by
        ext n; simp [hA_def];
        constructor <;> intro hn <;> simp_all +decide [Nat.coprime_prod_right_iff];
        · exact fun q hq hqp =>
            Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( hS q hq ) |>.2 <|
              hn q hq hqp
        · exact fun q hq hqp => fun hqn =>
            Nat.Prime.not_dvd_one ( hS q hq )
              ( hn q hq hqp ▸ Nat.dvd_gcd hqn ( dvd_refl q ) )
      convert density_coprime ( ∏ q ∈ S \ { p }, q ) _ using 1;
      · simpa only [ Nat.coprime_comm ] using hA_coprime;
      · field_simp;
        rw [ Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod ];
        · rw [ Nat.div_self
            ( Finset.prod_pos fun q hq =>
              Nat.Prime.pos ( hS q ( Finset.mem_sdiff.mp hq |>.1 ) ) ) ]
          norm_num
          rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ]
          intros
          rw [ Nat.cast_pred
            ( Nat.Prime.pos ( hS _ ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ) ]
          ring_nf
          norm_num [ Nat.Prime.ne_zero ( hS _ ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ]
        · aesop;
      · exact Finset.prod_pos fun q hq => Nat.Prime.pos ( hS q ( Finset.mem_sdiff.mp hq |>.1 ) );
    -- The set of integers divisible by $p$ and no other prime in $S$ is the
    -- intersection of $A$ and the set of multiples of $p$.
    have h_inter :
        {n : ℕ | p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬q ∣ n} =
          {n : ℕ | ∃ a ∈ A, n = p * a} := by
      ext n
      simp [hA_def];
      constructor <;> intro hn
      all_goals generalize_proofs at *;
      · exact ⟨
          n / p,
          fun q hq hqp => fun hq' =>
            hn.2 q hq hqp <| dvd_trans hq' <| Nat.div_dvd_of_dvd hn.1,
          by rw [ Nat.mul_div_cancel' hn.1 ]⟩
      · rcases hn with ⟨ a, ha, rfl ⟩ ; simp_all +decide [ Nat.Prime.dvd_mul ] ;
        exact fun q hq hqp => fun hqp' =>
          hqp <| Nat.prime_dvd_prime_iff_eq ( hS q hq ) ( hS p hp ) |>.1 hqp' ▸ rfl;
    field_simp;
    convert density_scaled A _ p ( Nat.Prime.pos ( hS p hp ) ) hA_density using 1

/-
The density of integers divisible by no prime in a finite set of primes $S$ is
$\prod_{p \in S} (1 - 1/p)$.
-/
set_option linter.flexible false in
lemma density_no_prime (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
  has_natural_density {n | ∀ p ∈ S, ¬ p ∣ n} (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
    by_contra h_contra;
    -- Let $q = \prod_{p \in S} p$.
    set q := ∏ p ∈ S, p with hq_def;
    -- Let $A$ be the set of integers coprime to $q$.
    set A := {n | Nat.Coprime n q} with hA_def;
    have hA_density : has_natural_density A ((Nat.totient q : ℝ) / q) := by
      convert density_coprime q ( Finset.prod_pos fun p hp => Nat.Prime.pos ( hS p hp ) ) using 1;
      exact Set.ext fun x => Nat.coprime_comm;
    refine h_contra ?_;
    convert hA_density using 2;
    · ext n; simp [hq_def];
      rw [ Nat.coprime_prod_right_iff ];
      exact ⟨
        fun h p hp =>
          Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( hS p hp ) |>.2 <|
            h p hp,
        fun h p hp => fun hpn =>
          Nat.Prime.not_dvd_one ( hS p hp ) <| h p hp ▸ Nat.dvd_gcd hpn ( dvd_refl _ )⟩
    · -- By definition of totient function, we know that
      -- $\phi(q) = q \prod_{p \in S} (1 - 1/p)$.
      have h_totient : Nat.totient q = q * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
        have hphi_q : Nat.totient q = q * (∏ p ∈ Nat.primeFactors q, (1 - 1 / (p : ℝ))) := by
          convert Nat.totient_eq_mul_prod_factors q using 1;
          norm_num [ ← @Rat.cast_inj ℝ ];
        rw [ hphi_q, Nat.primeFactors_prod ] ; aesop;
      rw [ h_totient, mul_div_cancel_left₀ _
        ( Nat.cast_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun p hp =>
          Nat.Prime.ne_zero <| hS p hp ) ]

/-
If two disjoint sets have natural densities, their union has the sum of their densities.
-/
set_option linter.flexible false in
set_option linter.style.multiGoal false in
lemma density_disjoint_union (A B : Set ℕ) (dA dB : ℝ)
    (hA : has_natural_density A dA) (hB : has_natural_density B dB)
    (hdisj : Disjoint A B) :
  has_natural_density (A ∪ B) (dA + dB) := by
    convert Filter.Tendsto.add hA hB using 1;
    unfold has_natural_density;
    congr! 1;
    ext; simp +decide [Finset.filter_or] ;
    rw [ ← add_div, Finset.card_union_of_disjoint ] ; aesop;
    exact Finset.disjoint_filter.mpr fun _ _ _ _ =>
      hdisj.le_bot ⟨ by assumption, by assumption ⟩

/-
The natural density of a finite disjoint union of sets is the sum of their natural densities.
-/
lemma density_finset_union {α : Type*} (I : Finset α) (A : α → Set ℕ) (d : α → ℝ)
  (hA : ∀ i ∈ I, has_natural_density (A i) (d i))
  (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
  has_natural_density (⋃ i ∈ I, A i) (∑ i ∈ I, d i) := by
    induction I using Finset.induction generalizing d with
    | empty =>
      unfold has_natural_density
      aesop
    | insert i I hi ih =>
      norm_num +zetaDelta at *;
      rw [ Finset.sum_insert hi ]
      exact density_disjoint_union _ _ _ _ hA.1
        ( ih _ hA.2 fun a ha => hdisj.2 a ha |>.2 )
        ( Set.disjoint_left.mpr fun x hx hx' => by
          rcases Set.mem_iUnion₂.mp hx' with ⟨ a, ha, ha' ⟩
          exact Set.disjoint_left.mp ( hdisj.1 a ha ( by aesop ) ) hx ha' )

/-
Algebraic identity:
$\sum_{p \in S} \frac{1}{p} \prod_{q \in S \setminus \{p\}}
(1 - \frac{1}{q}) =
\left( \prod_{p \in S} (1 - \frac{1}{p}) \right)
\sum_{p \in S} \frac{1}{p-1}$.
-/
lemma density_algebraic_identity (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
  (∑ p ∈ S, ((1 / p : ℝ) * ∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ)))) =
  (∏ p ∈ S, (1 - 1 / (p : ℝ))) * (∑ p ∈ S, (1 / (p - 1 : ℝ))) := by
    -- Rewrite the sum using the corresponding product with the $p$ term removed.
    have h_prod_identity :
        ∀ p ∈ S,
          (∏ q ∈ S \ {p}, (1 - 1 / q : ℝ)) =
            (∏ q ∈ S, (1 - 1 / q : ℝ)) / (1 - 1 / p : ℝ) := by
      intro p hp
      rw [ Finset.prod_eq_prod_diff_singleton_mul hp ]
      rw [ mul_div_cancel_right₀ _
        ( sub_ne_zero_of_ne <| by
          norm_num
          linarith [ Nat.Prime.one_lt ( hS p hp ) ] ) ]
    rw [ Finset.mul_sum _ _ _ ]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ h_prod_identity p hp ]
    ring_nf
    field_simp;
    rw [ mul_sub,
      mul_one_div_cancel ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hS p hp ) ]
    ring

/-
The set of integers with exactly one prime factor in $S$ is the disjoint union
of sets of non-zero integers divisible by exactly one specific prime $p \in S$.
-/
set_option linter.flexible false in
lemma set_decomposition_exactly_one_prime (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
  {n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card = 1} =
  ⋃ p ∈ S, {n : ℕ | n ≠ 0 ∧ p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬ q ∣ n} := by
    ext n; simp +zetaDelta at *; constructor <;> intro h;
    · obtain ⟨ p, hp ⟩ := Finset.card_eq_one.mp h;
      rw [ Finset.eq_singleton_iff_unique_mem ] at hp ; aesop;
    · obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h.2
      refine Finset.card_eq_one.mpr
        ⟨ x, Finset.eq_singleton_iff_unique_mem.mpr ⟨ ?_, fun p hp => ?_ ⟩ ⟩ <;>
        simp_all +decide
      exact Classical.not_not.1 fun h => hx₃ p hp.2 h hp.1.2

/-
Removing 0 from a set does not change its natural density.
-/
set_option linter.flexible false in
lemma density_diff_singleton_zero (A : Set ℕ) (d : ℝ) (h : has_natural_density A d) :
  has_natural_density (A \ {0}) d := by
    rw [ has_natural_density ] at *;
    -- Since the difference between the two sets is at most one element, their
    -- densities are the same.
    have h_diff :
        ∀ n,
          ((Finset.filter (fun k => k ∈ A) (Finset.range n)).card : ℝ) -
            ((Finset.filter (fun k => k ∈ A \ {0}) (Finset.range n)).card : ℝ) ≤
              1 := by
      intro n
      exact sub_le_iff_le_add'.mpr ( by
        norm_cast
        exact le_trans
          ( Finset.card_mono <|
            show
                Finset.filter ( fun k => k ∈ A ) ( Finset.range n ) ⊆
                  Finset.filter ( fun k => k ∈ A \ { 0 } ) ( Finset.range n ) ∪
                    { 0 } from
              fun x hx => by by_cases hx0 : x = 0 <;> aesop )
          ( Finset.card_union_le _ _ ) )
    have h_diff :
        Filter.Tendsto
          (fun n =>
            ((Finset.filter (fun k => k ∈ A) (Finset.range n)).card : ℝ) / n -
              ((Finset.filter (fun k => k ∈ A \ {0}) (Finset.range n)).card : ℝ) /
                n)
          Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (n : ℝ)) ?_ ?_
      · simp_all +decide [ ← sub_div ];
        exact ⟨ 1, fun n hn => by
          rw [ abs_of_nonneg
            ( sub_nonneg_of_le <| mod_cast Finset.card_mono <| by aesop_cat ) ]
          exact mul_le_of_le_one_left ( by positivity ) <| by linarith [ h_diff n ]⟩
      · exact tendsto_one_div_atTop_nhds_zero_nat;
    simpa using h.sub h_diff

/-
The set of integers with at most one prime factor less than $M$ has natural
density $\prod_{p < M} (1 - 1/p) \times
(1 + \sum_{p < M} \frac{1}{p-1})$.
-/
set_option linter.flexible false in
set_option linter.style.multiGoal false in
lemma density_at_most_one_prime (M : ℕ) :
  let S := (Finset.range M).filter Nat.Prime
  has_natural_density {n : ℕ | (n.primeFactors.filter (fun p => p < M)).card ≤ 1}
    ((∏ p ∈ S, (1 - 1 / (p : ℝ))) * (1 + ∑ p ∈ S, (1 / (p - 1 : ℝ)))) := by
      -- Apply the lemma that states the density of the set with at most one
      -- prime factor in S is given by the product and sum expressions.
      have h_density :
          ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
            has_natural_density
              {n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card ≤ 1}
              ((∏ p ∈ S, (1 - 1 / (p : ℝ))) *
                (1 + ∑ p ∈ S, (1 / (p - 1 : ℝ)))) := by
        intros S hS
        have h_density :
            has_natural_density
              {n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card = 0}
              (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
          -- Apply the lemma that states the density of the set of numbers not
          -- divisible by any prime in S is the product of (1 - 1/p) over primes
          -- p in S.
          have h_density_zero :
              has_natural_density {n : ℕ | ∀ p ∈ S, ¬ p ∣ n}
                (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
            convert density_no_prime S hS using 1;
          simp_all +decide [Finset.ext_iff];
          -- The natural density of a set minus a finite set is the same as the
          -- natural density of the original set.
          have h_density_zero :
              has_natural_density {n : ℕ | n = 0 ∨ ∀ p ∈ S, ¬p ∣ n}
                (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
            have h_density_zero : has_natural_density {n : ℕ | n = 0} 0 := by
              refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (n : ℝ)) ?_ ?_
              · norm_num [ Finset.filter_eq' ];
                exact ⟨ 1, fun n hn => by rw [ if_pos ( by linarith ) ] ; norm_num ⟩;
              · exact tendsto_one_div_atTop_nhds_zero_nat;
            convert density_disjoint_union _ _ _ _ _ _ using 1;
            rotate_left;
            exact { n | n = 0 };
            exact { n | ∀ p ∈ S, ¬p ∣ n } \ { 0 };
            exact 0;
            exact ∏ p ∈ S, ( 1 - ( p : ℝ ) ⁻¹ );
            · assumption;
            · convert density_diff_singleton_zero _ _
                ‹has_natural_density { n | ∀ p ∈ S, ¬p ∣ n }
                  ( ∏ p ∈ S, ( 1 - ( p : ℝ ) ⁻¹ ) )› using 1;
            · aesop;
          grind +ring
        have h_density_one :
            has_natural_density
              {n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card = 1}
              ((∏ p ∈ S, (1 - 1 / (p : ℝ))) *
                (∑ p ∈ S, (1 / (p - 1 : ℝ)))) := by
          have h_density_one :
              ∀ p ∈ S,
                has_natural_density
                  {n : ℕ | n ≠ 0 ∧ p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬ q ∣ n}
                  ((1 / p : ℝ) * (∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ)))) := by
            intros p hp
            have h_density_one :
                has_natural_density
                  {n : ℕ | p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬ q ∣ n}
                  ((1 / p : ℝ) * (∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ)))) := by
              convert density_exact_prime S hS p hp using 1
            have h_density_one_nonzero :
                has_natural_density
                  {n : ℕ | n ≠ 0 ∧ p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬ q ∣ n}
                  ((1 / p : ℝ) * (∏ q ∈ S \ {p}, (1 - 1 / (q : ℝ)))) := by
              convert density_diff_singleton_zero _ _ h_density_one using 1 ; ext ; aesop;
            exact h_density_one_nonzero
          convert density_finset_union S
              ( fun p => { n : ℕ | n ≠ 0 ∧ p ∣ n ∧ ∀ q ∈ S, q ≠ p → ¬q ∣ n } )
              ( fun p => 1 / ( p : ℝ ) * ∏ q ∈ S \ { p },
                ( 1 - 1 / ( q : ℝ ) ) ) _ _
            using 1;
          · convert set_decomposition_exactly_one_prime S hS using 1;
          · convert density_algebraic_identity S hS |> Eq.symm using 1;
          · assumption;
          · exact fun p hp q hq hpq => Set.disjoint_left.mpr fun x hx hx' =>
              hpq <| by
                have := hx.2.2 q hq
                have := hx'.2.2 p hp
                aesop
        have h_union :
            has_natural_density
              ({n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card = 0} ∪
                {n : ℕ | (n.primeFactors.filter (fun p => p ∈ S)).card = 1})
              ((∏ p ∈ S, (1 - 1 / (p : ℝ))) *
                (1 + ∑ p ∈ S, (1 / (p - 1 : ℝ)))) := by
          convert density_disjoint_union _ _ _ _ h_density h_density_one _ using 1 <;>
            norm_num [ Set.disjoint_left ]
          ring!
          intro n hn; rw [ Finset.card_eq_zero.mpr ] <;> aesop;
        exact (by
        convert h_union using 1;
        exact Set.ext fun x => by simp +decide [ le_iff_lt_or_eq ] ;);
      convert h_density ( Finset.filter Nat.Prime ( Finset.range M ) )
        ( fun p hp => Finset.mem_filter.mp hp |>.2 ) using 1;
      exact congr_arg _ ( by ext; congr! 2; aesop )

/-
For distinct primes $p$ and $q$, the ratio $\frac{\log p}{\log q}$ is irrational.
-/
lemma irrational_log_ratio (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
  Irrational (Real.log p / Real.log q) := by
    -- Assume for contradiction that $\frac{\log p}{\log q}$ is rational.
    by_contra h
    -- Then there exist positive integers $a$ and $b$ such that
    -- $\frac{\log p}{\log q} = \frac{a}{b}$.
    obtain ⟨a, b, ha, hb, hab⟩ :
        ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Real.log p = a * Real.log q / b := by
      obtain ⟨a, b, ha, hb, hab⟩ :
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Real.log p / Real.log q = a / b := by
        obtain ⟨a, b, ha, hb, hab⟩ :
            ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Real.log p / Real.log q = a / b := by
          have h_rat : ∃ r : ℚ, Real.log p / Real.log q = r := by
            simpa [ eq_comm ] using Classical.not_not.1 h
          obtain ⟨ r, hr ⟩ := h_rat
          exact ⟨
            r.num,
            r.den,
            mod_cast Rat.num_pos.mpr ( show 0 < r from by
              exact_mod_cast hr ▸
                div_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ) )
                  ( Real.log_pos ( Nat.one_lt_cast.mpr hq.one_lt ) ) ),
            mod_cast Nat.cast_pos.mpr r.pos,
            by simpa only [ Rat.cast_def ] using hr⟩
        cases a <;> cases b <;> aesop;
      exact ⟨ a, b, ha, hb, by
        rw [ div_eq_iff ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hq.one_lt ) ) ) ]
          at hab
        linear_combination hab⟩
    -- Exponentiating both sides, we get $p^b = q^a$.
    have h_exp : (p : ℝ) ^ b = q ^ a := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_natCast,
        Real.rpow_def_of_pos ( Nat.cast_pos.mpr hp.pos ),
        Real.rpow_def_of_pos ( Nat.cast_pos.mpr hq.pos ) ]
      norm_num
      rw [ eq_div_iff ( by positivity ) ] at *
      linarith
    norm_cast at h_exp
    have := congr_arg ( ·.factorization ( p : ℕ ) ) h_exp
    have := congr_arg ( ·.factorization ( q : ℕ ) ) h_exp
    norm_num at *
    aesop

/-
Given a dense set $D$ and a compact set $K$, for any $\epsilon > 0$, there is
a finite subset of $D$ that $\epsilon$-approximates $K$.
-/
lemma compact_approx_by_finite_subset (D : Set ℝ) (hD : Dense D) (K : Set ℝ)
    (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
  ∃ F : Finset ℝ, (F : Set ℝ) ⊆ D ∧ ∀ x ∈ K, ∃ y ∈ F, |x - y| < ε := by
    -- By compactness, there is a finite subcover corresponding to $x_1, \dots, x_n$.
    obtain ⟨x_fin, hx_fin⟩ :
        ∃ x_fin : Finset ℝ,
          (∀ x ∈ x_fin, x ∈ K) ∧ ∀ x ∈ K, ∃ y ∈ x_fin, |x - y| < ε / 2 := by
      have := hK.elim_nhds_subcover ( fun x => Metric.ball x ( ε / 2 ) )
        ( fun x _ => Metric.ball_mem_nhds _ ( half_pos hε ) )
      exact ⟨ this.choose, this.choose_spec.1, fun x hx => by
        rcases Set.mem_iUnion₂.1 ( this.choose_spec.2 hx ) with ⟨ y, hy, hy' ⟩
        exact ⟨ y, hy, hy' ⟩⟩
    -- For each $y \in x_fin$, there exists $z \in D$ such that
    -- $|y - z| < \epsilon / 2$.
    obtain ⟨z_fin, hz_fin⟩ :
        ∃ z_fin : Finset ℝ,
          (∀ y ∈ z_fin, y ∈ D) ∧
            (∀ y ∈ x_fin, ∃ z ∈ z_fin, |y - z| < ε / 2) := by
      have hz_fin : ∀ y ∈ x_fin, ∃ z ∈ D, |y - z| < ε / 2 := by
        exact fun y hy => by
          rcases hD.exists_dist_lt y ( half_pos hε ) with ⟨ z, hzD, hz ⟩
          exact ⟨ z, hzD, by simpa [ abs_sub_comm ] using hz ⟩
      choose! z hz using hz_fin; use Finset.image z x_fin; aesop;
    exact ⟨ z_fin, hz_fin.1, fun x hx => by
      obtain ⟨ y, hy, hy' ⟩ := hx_fin.2 x hx
      obtain ⟨ z, hz, hz' ⟩ := hz_fin.2 y hy
      exact ⟨ z, hz, abs_lt.mpr ⟨
        by linarith [ abs_lt.mp hy', abs_lt.mp hz' ],
        by linarith [ abs_lt.mp hy', abs_lt.mp hz' ]⟩⟩⟩

/-
For any positive irrational $\alpha$ and $\epsilon > 0$, there exist natural
numbers $n, m$ such that $0 < n \alpha - m < \epsilon$.
-/
set_option linter.flexible false in
lemma exists_nat_mul_sub_nat_small (α : ℝ) (hα_pos : 0 < α)
    (hα_irr : Irrational α) (ε : ℝ) (hε : 0 < ε) :
  ∃ n m : ℕ, 0 < (n : ℝ) * α - m ∧ (n : ℝ) * α - m < ε := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N > 0 ∧ 1 / (N : ℝ) < ε / 4 := by
      exact ⟨
        ⌊4 / ε⌋₊ + 1,
        Nat.succ_pos _,
        by
          rw [ div_lt_iff₀ ] <;> push_cast <;>
            nlinarith [ Nat.lt_floor_add_one ( 4 / ε ), mul_div_cancel₀ 4 hε.ne' ]⟩
    -- Consider the fractional parts $\{k \alpha\}$ for $k = 0, 1, \ldots, N$.
    -- By the pigeonhole principle, two of them fall into the same subinterval.
    obtain ⟨k, l, hkl, h_sub⟩ :
        ∃ k l : ℕ,
          k < l ∧ k ≤ N ∧ l ≤ N ∧
            |Int.fract (k * α) - Int.fract (l * α)| < 1 / (N : ℝ) := by
      -- There are $N+1$ numbers and only $N$ intervals.
      have h_pigeonhole :
          ∃ k l : ℕ,
            k < l ∧ k ≤ N ∧ l ≤ N ∧
              ⌊Int.fract (k * α) * N⌋ = ⌊Int.fract (l * α) * N⌋ := by
        by_contra! h;
        exact absurd
          ( Finset.card_le_card
            ( show
                Finset.image ( fun k : ℕ => ⌊Int.fract ( k * α ) * N⌋ )
                  ( Finset.Icc 0 N ) ⊆ Finset.Icc 0 ( N - 1 ) from
              Finset.image_subset_iff.mpr fun k hk =>
                Finset.mem_Icc.mpr ⟨
                  Int.floor_nonneg.mpr <|
                    mul_nonneg ( Int.fract_nonneg _ ) <| Nat.cast_nonneg _,
                  Int.le_sub_one_of_lt <|
                    Int.floor_lt.mpr <|
                      mul_lt_of_lt_one_left ( Nat.cast_pos.mpr hN.1 ) <|
                        Int.fract_lt_one _⟩ ) )
          ( by
            rw [ Finset.card_image_of_injOn fun k hk k' hk' hkk' =>
              le_antisymm
                ( not_lt.mp fun hlt =>
                  h _ _ hlt
                    ( by linarith [ Finset.mem_Icc.mp hk', Finset.mem_Icc.mp hk ] )
                    ( by linarith [ Finset.mem_Icc.mp hk', Finset.mem_Icc.mp hk ] )
                    hkk'.symm )
                ( not_lt.mp fun hlt =>
                  h _ _ hlt
                    ( by linarith [ Finset.mem_Icc.mp hk', Finset.mem_Icc.mp hk ] )
                    ( by linarith [ Finset.mem_Icc.mp hk', Finset.mem_Icc.mp hk ] )
                    hkk' ) ]
            simp +arith +decide )
      obtain ⟨ k, l, hkl, hk, hl, h ⟩ := h_pigeonhole
      refine ⟨ k, l, hkl, hk, hl, ?_ ⟩
      rw [ abs_lt ]
      constructor <;>
        nlinarith [
          Int.floor_le ( Int.fract ( ( k : ℝ ) * α ) * N ),
          Int.lt_floor_add_one ( Int.fract ( ( k : ℝ ) * α ) * N ),
          Int.floor_le ( Int.fract ( ( l : ℝ ) * α ) * N ),
          Int.lt_floor_add_one ( Int.fract ( ( l : ℝ ) * α ) * N ),
          show ( N : ℝ ) > 0 by exact Nat.cast_pos.mpr hN.1,
          mul_div_cancel₀ 1 ( show ( N : ℝ ) ≠ 0 by
            exact Nat.cast_ne_zero.mpr hN.1.ne' ),
          show
              ( ⌊Int.fract ( ( k : ℝ ) * α ) * N⌋ : ℝ ) =
                ⌊Int.fract ( ( l : ℝ ) * α ) * N⌋ by
            exact_mod_cast h]
    -- Let $n = l - k$ and $m = \lfloor l \alpha \rfloor - \lfloor k \alpha \rfloor$.
    -- Then $n \alpha - m$ is between $0$ and $1/N$.
    set n := l - k
    set m := ⌊l * α⌋ - ⌊k * α⌋
    have hnm :
        0 < n * α - m ∧ n * α - m < 1 / (N : ℝ) ∨
          0 < m - n * α ∧ m - n * α < 1 / (N : ℝ) := by
      simp +zetaDelta at *
      rw [ Nat.cast_sub hkl.le ];
      cases lt_or_gt_of_ne
          ( show
              ( l - k : ℝ ) * α ≠
                ⌊ ( l : ℝ ) * α⌋ - ⌊ ( k : ℝ ) * α⌋ from
            fun h =>
              hα_irr <| ⟨
                ( ⌊ ( l : ℝ ) * α⌋ - ⌊ ( k : ℝ ) * α⌋ ) / ( l - k ),
                by
                  push_cast [ ← h ]
                  rw [ mul_div_cancel_left₀ _
                    ( sub_ne_zero_of_ne <| by
                      norm_cast
                      linarith ) ]⟩ ) <;>
        first
        | left
          constructor <;>
            linarith [
              abs_lt.mp h_sub.2.2,
              Int.fract_add_floor ( ( l : ℝ ) * α ),
              Int.fract_add_floor ( ( k : ℝ ) * α )]
        | right
          constructor <;>
            linarith [
              abs_lt.mp h_sub.2.2,
              Int.fract_add_floor ( ( l : ℝ ) * α ),
              Int.fract_add_floor ( ( k : ℝ ) * α )]
    rcases hnm with hnm | hnm
    · use n, m.natAbs;
      simp +zetaDelta at *
      exact ⟨
        by
          rw [ abs_of_nonneg ] <;>
            linarith [
              show ( ⌊ ( l : ℝ ) * α⌋ : ℝ ) ≥ ⌊ ( k : ℝ ) * α⌋ by
                exact_mod_cast Int.floor_mono <|
                  mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hkl.le ) hα_pos.le],
        by
          rw [ abs_of_nonneg ] <;>
            linarith [
              show ( ⌊ ( l : ℝ ) * α⌋ : ℝ ) ≥ ⌊ ( k : ℝ ) * α⌋ by
                exact_mod_cast Int.floor_mono <|
                  mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hkl.le ) hα_pos.le]⟩
    · -- Let $q$ be the largest integer such that $q(m - n\alpha) < \alpha$.
      obtain ⟨q, hq⟩ : ∃ q : ℕ, q * (m - n * α) < α ∧ (q + 1) * (m - n * α) ≥ α := by
        have hq : ∃ q : ℕ, q * (m - n * α) < α ∧ (q + 1) * (m - n * α) ≥ α := by
          have h_seq : ∃ q : ℕ, q * (m - n * α) ≥ α := by
            exact ⟨
              ⌈α / ( m - n * α )⌉₊,
              by
                nlinarith [
                  Nat.le_ceil ( α / ( m - n * α ) ),
                  mul_div_cancel₀ α hnm.1.ne']⟩
          contrapose! h_seq;
          exact fun x => Nat.recOn x ( by norm_num; linarith ) fun x ih => mod_cast h_seq x ih;
        exact hq;
      refine ⟨ q * n + 1, q * m.natAbs, ?_, ?_ ⟩ <;> norm_num at *
      · rw [ abs_of_nonneg ] <;>
          nlinarith [ show ( n : ℝ ) ≥ 1 by exact_mod_cast Nat.sub_pos_of_lt hkl ]
      · rw [ abs_of_nonneg ] <;> nlinarith [ show ( 0 : ℝ ) ≤ n * α by positivity ]

/-
If $u, v > 0$ and $u/v$ is irrational, then the set
$\{ b v - a u \mid a, b \in \mathbb{N} \}$ is dense in $\mathbb{R}$.
-/
lemma dense_diff_submonoid_of_irrational_ratio (u v : ℝ) (hu : 0 < u)
    (hv : 0 < v) (h_irr : Irrational (u / v)) :
  Dense { x | ∃ a b : ℕ, x = (b : ℝ) * v - (a : ℝ) * u } := by
    -- Let $\delta_+ = b v - a u$ with $0 < b v - a u < \epsilon$.
    have h_delta_pos :
        ∀ ϵ > 0,
          ∃ a b : ℕ,
            0 < (b : ℝ) * v - (a : ℝ) * u ∧
              (b : ℝ) * v - (a : ℝ) * u < ϵ := by
      intro ε hε_pos
      obtain ⟨a, b, h_pos, h_lt⟩ :
          ∃ a b : ℕ,
            0 < (b : ℝ) * (v / u) - (a : ℝ) ∧
              (b : ℝ) * (v / u) - (a : ℝ) < ε / u := by
        have := exists_nat_mul_sub_nat_small ( v / u ) ( by positivity )
          ( by simpa [ div_eq_mul_inv ] using h_irr.inv ) ( ε / u ) ( by positivity )
        aesop
      exact ⟨
        a,
        b,
        by nlinarith [ mul_div_cancel₀ v hu.ne' ],
        by nlinarith [ mul_div_cancel₀ v hu.ne', mul_div_cancel₀ ε hu.ne' ]⟩
    -- Let $\delta_- = b' v - a' u$ with $-\epsilon < b' v - a' u < 0$.
    have h_delta_neg :
        ∀ ϵ > 0,
          ∃ a' b' : ℕ,
            -ϵ < (b' : ℝ) * v - (a' : ℝ) * u ∧
              (b' : ℝ) * v - (a' : ℝ) * u < 0 := by
      intro ϵ hϵ_pos
      obtain ⟨a', b', ha', hb'⟩ :
          ∃ a' b' : ℕ,
            0 < (a' : ℝ) * u - (b' : ℝ) * v ∧
              (a' : ℝ) * u - (b' : ℝ) * v < ϵ := by
        obtain ⟨a', b', ha', hb'⟩ :
            ∃ a' b' : ℕ,
              0 < (a' : ℝ) * (u / v) - (b' : ℝ) ∧
                (a' : ℝ) * (u / v) - (b' : ℝ) < ϵ / v := by
          have := exists_nat_mul_sub_nat_small ( u / v ) ( by positivity ) h_irr
            ( ϵ / v ) ( by positivity )
          aesop
        exact ⟨
          a',
          b',
          by nlinarith [ mul_div_cancel₀ u hv.ne' ],
          by nlinarith [ mul_div_cancel₀ u hv.ne', mul_div_cancel₀ ϵ hv.ne' ]⟩
      exact ⟨ a', b', by linarith, by linarith ⟩
    -- For any real number $x$, we can find a sequence in $S$ converging to $x$.
    have h_seq :
        ∀ x : ℝ, ∀ ϵ > 0,
          ∃ s ∈ {x : ℝ | ∃ a b : ℕ, x = b * v - a * u}, |x - s| < ϵ := by
      intro x ϵ hϵ_pos
      obtain ⟨a, b, hδ_pos⟩ :
          ∃ a b : ℕ,
            0 < (b : ℝ) * v - (a : ℝ) * u ∧
              (b : ℝ) * v - (a : ℝ) * u < ϵ := h_delta_pos ϵ hϵ_pos
      obtain ⟨a', b', hδ_neg⟩ :
          ∃ a' b' : ℕ,
            -ϵ < (b' : ℝ) * v - (a' : ℝ) * u ∧
              (b' : ℝ) * v - (a' : ℝ) * u < 0 := h_delta_neg ϵ hϵ_pos
      -- Consider two cases: $x \geq 0$ and $x < 0$.
      by_cases hx_nonneg : 0 ≤ x;
      · -- Let $k = \lfloor x / \delta_+ \rfloor$.
        obtain ⟨k, hk⟩ :
            ∃ k : ℕ,
              0 ≤ x - k * ((b : ℝ) * v - (a : ℝ) * u) ∧
                x - k * ((b : ℝ) * v - (a : ℝ) * u) <
                  (b : ℝ) * v - (a : ℝ) * u := by
          exact ⟨
            ⌊x / ( b * v - a * u )⌋₊,
            by
              nlinarith [
                Nat.floor_le ( show 0 ≤ x / ( b * v - a * u ) by
                  exact div_nonneg hx_nonneg hδ_pos.1.le ),
                mul_div_cancel₀ x hδ_pos.1.ne'],
            by
              nlinarith [
                Nat.lt_floor_add_one ( x / ( b * v - a * u ) ),
                mul_div_cancel₀ x hδ_pos.1.ne']⟩
        exact ⟨
          k * ( b * v - a * u ),
          ⟨ k * a, k * b, by push_cast; ring ⟩,
          abs_lt.mpr ⟨ by linarith, by linarith ⟩⟩
      · -- Since $x < 0$, multiples of $b' * v - a' * u$ approximate $x$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, |x - k * (b' * v - a' * u)| < ϵ := by
          exact ⟨
            ⌊x / ( b' * v - a' * u )⌋₊,
            by
              rw [ abs_lt ]
              constructor <;>
                nlinarith [
                  Nat.floor_le ( show 0 ≤ x / ( b' * v - a' * u ) by
                    exact div_nonneg_of_nonpos ( le_of_not_ge hx_nonneg )
                      ( by linarith ) ),
                  Nat.lt_floor_add_one ( x / ( b' * v - a' * u ) ),
                  mul_div_cancel₀ x ( by linarith : ( b' * v - a' * u ) ≠ 0 )]⟩
        exact ⟨ _, ⟨ k * a', k * b', by push_cast; ring ⟩, hk ⟩
    exact fun x => Metric.mem_closure_iff.mpr fun ε hε => by
      obtain ⟨ s, hs₁, hs₂ ⟩ := h_seq x ε hε
      exact ⟨ s, hs₁, by simpa [ abs_sub_comm ] using hs₂ ⟩

/-
For any $\epsilon > 0$, there exists a finite set of indices
$B \subset \mathbb{N}$ such that the set
$\{ b v \pmod u \mid b \in B \}$ forms an $\epsilon$-net of $[0, u]$.
-/
lemma finite_net_mod_u (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h_irr : Irrational (u / v)) (ε : ℝ) (hε : 0 < ε) :
  ∃ B : Finset ℕ,
    ∀ y ∈ Set.Icc 0 u,
      ∃ b ∈ B, ∃ k : ℤ, |((b : ℝ) * v - (k : ℝ) * u) - y| < ε := by
    -- Lemma 2 gives a finite epsilon-net from the dense set.
    obtain ⟨F, hF⟩ :
        ∃ F : Finset ℝ,
          (∀ x ∈ F, ∃ b : ℕ, ∃ k : ℤ, x = b * v - k * u) ∧
            (∀ y ∈ Set.Icc 0 u, ∃ x ∈ F, |x - y| < ε) := by
      have h_dense : Dense { x : ℝ | ∃ b : ℕ, ∃ k : ℤ, x = b * v - k * u } := by
        have h_dense : Dense { x : ℝ | ∃ a b : ℕ, x = (b : ℝ) * v - (a : ℝ) * u } := by
          exact dense_diff_submonoid_of_irrational_ratio u v hu hv h_irr;
        rw [ Metric.dense_iff ] at *;
        intro x r hr
        rcases h_dense x r hr with ⟨ y, hy₁, ⟨ a, b, rfl ⟩ ⟩
        exact ⟨ _, hy₁, b, a, rfl ⟩
      have := @compact_approx_by_finite_subset
        { x : ℝ | ∃ b : ℕ, ∃ k : ℤ, x = b * v - k * u } ?_
        ( Set.Icc 0 u ) ?_ ε hε
      · exact ⟨ this.choose, fun x hx => this.choose_spec.1 hx, fun y hy => by
          obtain ⟨ x, hx₁, hx₂ ⟩ := this.choose_spec.2 y hy
          exact ⟨ x, hx₁, by rwa [ abs_sub_comm ] ⟩⟩
      · exact h_dense;
      · exact CompactIccSpace.isCompact_Icc;
    choose! b k h using hF.1;
    exact ⟨ Finset.image b F, fun y hy => by
      rcases hF.2 y hy with ⟨ x, hx, hx' ⟩
      exact ⟨
        b x,
        Finset.mem_image_of_mem _ hx,
        k x,
        by simpa only [ ← h x hx ] using hx'⟩⟩

/-
If $u, v > 0$ and $u/v$ is irrational, then for every $\epsilon > 0$, the
additive semigroup generated by $u, v$ is $\epsilon$-dense in
$[K, \infty)$ for some large $K$.
-/
set_option linter.flexible false in
lemma dense_semigroup_of_irrational_ratio (u v : ℝ) (hu : 0 < u)
    (hv : 0 < v) (h_irr : Irrational (u / v)) (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℝ, ∀ x ≥ K,
    ∃ a b : ℕ,
      x < (a : ℝ) * u + (b : ℝ) * v ∧
        (a : ℝ) * u + (b : ℝ) * v < x + ε := by
    have := finite_net_mod_u u v hu hv h_irr ( ε / 2 ) ( half_pos hε );
    -- Let $K = \max_{b \in B} (b v)$.
    obtain ⟨B, hB⟩ := this;
    set K := sSup (Set.image (fun b : ℕ => b * v) B) with hK_def;
    -- For any $x \geq K$, let $t = x \pmod u$.
    -- Some $(b v \pmod u)$ lies in $(t, t+\epsilon)$.
    use K + u + 1
    intro x hx
    obtain ⟨b, hbB, k, hk⟩ :
        ∃ b ∈ B, ∃ k : ℤ,
          b * v - k * u ∈
            Set.Ioo (x - ⌊x / u⌋ * u) (x - ⌊x / u⌋ * u + ε) := by
      obtain ⟨b, hbB, k, hk⟩ :
          ∃ b ∈ B, ∃ k : ℤ,
            |(b * v - k * u) - (x - ⌊x / u⌋ * u + ε / 2)| < ε / 2 := by
        norm_num +zetaDelta at *;
        contrapose! hB;
        use x - ⌊x / u⌋ * u + ε / 2 - ⌊(x - ⌊x / u⌋ * u + ε / 2) / u⌋ * u;
        refine ⟨ ?_, ?_, ?_ ⟩
        · nlinarith [
            Int.floor_le ( ( x - ⌊x / u⌋ * u + ε / 2 ) / u ),
            Int.lt_floor_add_one ( ( x - ⌊x / u⌋ * u + ε / 2 ) / u ),
            mul_div_cancel₀ ( x - ⌊x / u⌋ * u + ε / 2 ) hu.ne']
        · nlinarith [
            Int.lt_floor_add_one ( ( x - ⌊x / u⌋ * u + ε / 2 ) / u ),
            mul_div_cancel₀ ( x - ⌊x / u⌋ * u + ε / 2 ) hu.ne']
        · intro b hb k
          specialize hB b hb ( k - ⌊ ( x - ⌊x / u⌋ * u + ε / 2 ) / u⌋ )
          simp_all +decide [sub_mul]
          exact hB.trans_eq ( by ring_nf );
      exact ⟨ b, hbB, k, by linarith [ abs_lt.mp hk ], by linarith [ abs_lt.mp hk ] ⟩;
    -- Let $a = \lfloor x / u \rfloor - k$.
    use Int.toNat (⌊x / u⌋ - k), b;
    have h_ak : ⌊x / u⌋ - k ≥ 0 := by
      exact Int.le_of_lt_add_one ( by
        rw [ ← @Int.cast_lt ℝ ]
        push_cast
        nlinarith [
          Int.floor_le ( x / u ),
          Int.lt_floor_add_one ( x / u ),
          mul_div_cancel₀ x hu.ne',
          hk.1,
          hk.2,
          show ( b : ℝ ) * v ≤ K from
            le_csSup ( by exact Set.Finite.bddAbove <| Set.toFinite _ ) <|
              Set.mem_image_of_mem _ hbB] )
    rw [
      show ( ⌊x / u⌋ - k |> Int.toNat : ℝ ) = ⌊x / u⌋ - k from
        mod_cast Int.toNat_of_nonneg h_ak]
    constructor <;> linarith [ hk.1, hk.2 ]

/-
Let $p,q$ be distinct primes and $\epsilon>0$. There is a bound $K$ such that
for every integer $n \ge K$ divisible by both $p$ and $q$, there exists an
integer $m \in (n,(1+\epsilon)n]$ whose prime divisors are contained in
$\{p,q\}$.
-/
set_option linter.style.multiGoal false in
lemma lemma_3 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℕ, ∀ n : ℕ, K ≤ n → p ∣ n → q ∣ n →
    ∃ m : ℕ, n < m ∧ (m : ℝ) ≤ (1 + ε) * n ∧ m.primeFactors ⊆ {p, q} := by
      -- Use density for the logarithms of $p$ and $q$.
      obtain ⟨K_log, hK_log⟩ :
          ∃ K_log : ℝ, ∀ L ≥ K_log,
            ∃ a b : ℕ,
              L < a * Real.log p + b * Real.log q ∧
                a * Real.log p + b * Real.log q < L + Real.log (1 + ε) := by
        have := @dense_semigroup_of_irrational_ratio
          ( Real.log p ) ( Real.log q )
          ( Real.log_pos <| Nat.one_lt_cast.mpr hp.one_lt )
          ( Real.log_pos <| Nat.one_lt_cast.mpr hq.one_lt ) ?_
          ( Real.log ( 1 + ε ) ) ( Real.log_pos <| by linarith )
        aesop
        exact irrational_log_ratio p q hp hq hpq;
      use ⌈Real.exp K_log⌉₊ + 1;
      intro n hn hpq hnpq
      obtain ⟨a, b, hL⟩ :
          ∃ a b : ℕ,
            Real.log n < a * Real.log p + b * Real.log q ∧
              a * Real.log p + b * Real.log q <
                Real.log n + Real.log (1 + ε) := by
        exact hK_log _ ( by
          simpa using
            Real.log_le_log ( by positivity )
              ( Nat.le_of_ceil_le ( Nat.le_of_succ_le hn ) ) )
      refine ⟨ p ^ a * q ^ b, ?_, ?_, ?_ ⟩ <;>
        norm_num [ Nat.primeFactors_mul, hp.ne_zero, hq.ne_zero ];
      · rw [ ← @Nat.cast_lt ℝ ]
        push_cast
        rw [
          ← Real.log_lt_log_iff
            ( Nat.cast_pos.mpr <| by linarith )
            ( mul_pos
              ( pow_pos ( Nat.cast_pos.mpr hp.pos ) _ )
              ( pow_pos ( Nat.cast_pos.mpr hq.pos ) _ ) )]
        rw [
          Real.log_mul
            ( pow_ne_zero _ <| Nat.cast_ne_zero.mpr hp.ne_zero )
            ( pow_ne_zero _ <| Nat.cast_ne_zero.mpr hq.ne_zero ),
          Real.log_pow,
          Real.log_pow]
        linarith
      · rw [
          ← Real.log_le_log_iff ( by
            norm_cast
            exact mul_pos ( pow_pos hp.pos _ ) ( pow_pos hq.pos _ ) )]
        · rw [
            Real.log_mul
              ( by norm_cast; exact pow_ne_zero _ hp.ne_zero )
              ( by norm_cast; exact pow_ne_zero _ hq.ne_zero ),
            Real.log_mul ( by positivity ) ( by norm_cast; linarith )]
          norm_num
          linarith
        · exact mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by linarith ) );
      · cases a <;> cases b <;> simp_all +decide [ Nat.primeFactors_pow, Finset.subset_iff ]

/-
The sum of the reciprocals of prime numbers diverges to infinity.
-/
lemma sum_prime_recip_diverges :
  Filter.Tendsto
    (fun M => ∑ p ∈ (Finset.range M).filter Nat.Prime, (1 / (p : ℝ)))
    Filter.atTop Filter.atTop := by
    -- The sum of the reciprocals of the primes diverges.
    have h_sum_diverges : ¬ Summable (fun p : ℕ => if Nat.Prime p then (1 / (p : ℝ)) else 0) := by
      intro h;
      convert not_summable_one_div_on_primes ?_;
      convert h using 1;
      ext; aesop;
    convert
      not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1
        h_sum_diverges using 1
    norm_num [ Finset.sum_filter ]

/-
The quantity $\left(\prod_{p < M} (1 - 1/p)\right)
\left(1 + \sum_{p < M} \frac{1}{p-1}\right)$ tends to 0 as
$M \to \infty$.
-/
lemma density_bound_tends_to_zero :
  Filter.Tendsto
    (fun M =>
      (∏ p ∈ (Finset.range M).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
        (1 + ∑ p ∈ (Finset.range M).filter Nat.Prime, (1 / (p - 1 : ℝ))))
    Filter.atTop (nhds 0) := by
    -- Let $P_M = (Finset.range M).filter Nat.Prime$.
    set P := fun M => (Finset.range M).filter Nat.Prime;
    -- We have the inequality $1 - x \le e^{-x}$ for all $x$.
    have h_exp_bound :
        ∀ M : ℕ,
          (∏ p ∈ P M, (1 - 1 / (p : ℝ))) ≤
            Real.exp (-∑ p ∈ P M, (1 / (p : ℝ))) := by
      intro M
      rw [
        Real.exp_neg,
        ← Real.log_le_log_iff
          ( Finset.prod_pos fun p hp => by
            exact sub_pos.mpr <| by
              simpa using inv_lt_one_of_one_lt₀ <|
                Nat.one_lt_cast.mpr <|
                  Nat.Prime.one_lt (Finset.mem_filter.mp hp).2 )
          ( inv_pos.mpr <| Real.exp_pos _ ),
        Real.log_prod fun p hp => ne_of_gt <| sub_pos.mpr <| by
          simpa using inv_lt_one_of_one_lt₀ <|
            Nat.one_lt_cast.mpr <|
              Nat.Prime.one_lt (Finset.mem_filter.mp hp).2]
      norm_num
      rw [ ← Finset.sum_neg_distrib ]
      exact Finset.sum_le_sum fun x hx => by
        linarith [
          Real.log_le_sub_one_of_pos ( show 0 < 1 - ( x : ℝ ) ⁻¹ by
            exact sub_pos.mpr <| inv_lt_one_of_one_lt₀ <|
              Nat.one_lt_cast.mpr <|
                Nat.Prime.one_lt (Finset.mem_filter.mp hx).2 )]
    -- For $p \ge 2$, $p-1 \ge p/2$, so $\frac{1}{p-1} \le \frac{2}{p}$.
    have h_inv_bound :
        ∀ M : ℕ,
          (∑ p ∈ P M, (1 / (p - 1 : ℝ))) ≤
            2 * (∑ p ∈ P M, (1 / (p : ℝ))) := by
      exact fun M => by
        rw [ Finset.mul_sum _ _ _ ]
        exact Finset.sum_le_sum fun p hp => by
          rw [ div_le_iff₀ ] <;>
            nlinarith only [
              show ( p : ℝ ) ≥ 2 by
                exact_mod_cast Nat.Prime.two_le (Finset.mem_filter.mp hp).2,
              one_div_mul_cancel <| show ( p : ℝ ) ≠ 0 by
                exact_mod_cast Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2]
    -- Let $f(x) = e^{-x}(1+2x)$. We have $\lim_{x \to \infty} f(x) = 0$.
    have h_lim :
        Filter.Tendsto (fun x : ℝ => Real.exp (-x) * (1 + 2 * x))
          Filter.atTop (nhds 0) := by
      ring_nf;
      simpa using Filter.Tendsto.add
        ( Filter.Tendsto.mul
          ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) tendsto_const_nhds )
        ( Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot )
    -- Since $S_M \to \infty$, the composition tends to 0.
    have h_comp :
        Filter.Tendsto
          (fun M : ℕ =>
            Real.exp (-∑ p ∈ P M, (1 / (p : ℝ))) *
              (1 + 2 * ∑ p ∈ P M, (1 / (p : ℝ))))
          Filter.atTop (nhds 0) := by
      refine h_lim.comp ?_;
      convert sum_prime_recip_diverges using 1;
    refine squeeze_zero
      ( fun M =>
        mul_nonneg
          ( Finset.prod_nonneg fun _ _ =>
            sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by
              aesop )
          ( add_nonneg zero_le_one <|
            Finset.sum_nonneg fun _ _ =>
              one_div_nonneg.2 <| sub_nonneg.2 <| mod_cast Nat.Prime.pos <| by
                aesop ) )
      ( fun M =>
        mul_le_mul
          ( h_exp_bound M )
          ( show
              1 + ∑ p ∈ P M, (1 / (p - 1 : ℝ)) ≤
                1 + 2 * ∑ p ∈ P M, (1 / (p : ℝ)) from by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left ( h_inv_bound M ) 1 )
          ( add_nonneg zero_le_one <|
            Finset.sum_nonneg fun _ _ =>
              one_div_nonneg.2 <| sub_nonneg.2 <| mod_cast Nat.Prime.pos <| by
                aesop )
          ( by positivity ) )
      h_comp

/-
For every $\delta>0$ there exists $M$ such that the natural density of integers
$n$ divisible by at least two distinct primes $p,q < M$ is at least
$1-\delta/2$.
-/
lemma lemma_1 (δ : ℝ) (hδ : 0 < δ) :
  ∃ M : ℕ, ∃ d : ℝ,
    has_natural_density {n | (n.primeFactors.filter (fun p => p < M)).card ≥ 2} d ∧
      d ≥ 1 - δ / 2 := by
    -- Let $d_{bad}$ be the density of integers with at most one small prime factor.
    obtain ⟨M, d, hd⟩ :
        ∃ M : ℕ,
          (∃ d : ℝ,
            has_natural_density
              {n : ℕ | (n.primeFactors.filter (fun p => p < M)).card ≤ 1} d ∧
              d < δ / 2) := by
      obtain ⟨M, hM⟩ :
          ∃ M : ℕ,
            (∏ p ∈ (Finset.range M).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
              (1 + ∑ p ∈ (Finset.range M).filter Nat.Prime,
                (1 / (p - 1 : ℝ))) < δ / 2 := by
        have := density_bound_tends_to_zero.eventually ( gt_mem_nhds <| half_pos hδ ) ; aesop;
      refine ⟨
        M,
        (∏ p ∈ (Finset.range M).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
          (1 + ∑ p ∈ (Finset.range M).filter Nat.Prime, (1 / (p - 1 : ℝ))),
        ?_,
        hM⟩
      convert density_at_most_one_prime M using 1;
    -- The set with at least two small prime factors complements the set with at most one.
    have h_complement :
        {n : ℕ | (n.primeFactors.filter (fun p => p < M)).card ≥ 2} =
          Set.univ \
            {n : ℕ | (n.primeFactors.filter (fun p => p < M)).card ≤ 1} := by
      ext; aesop;
    -- The density of the complement is $1 - d_{bad}$.
    have h_complement_density :
        has_natural_density
          (Set.univ \ {n : ℕ |
            (n.primeFactors.filter (fun p => p < M)).card ≤ 1})
          (1 - d) := by
      have := hd.1;
      refine Filter.Tendsto.congr' ?_ ( this.const_sub 1 )
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn
      simp +decide
      ring_nf
      field_simp;
      rw [ sub_eq_iff_eq_add', ← Nat.cast_add, Finset.card_filter, Finset.card_filter ];
      rw [
        ← Finset.sum_add_distrib,
        Finset.sum_congr rfl fun x hx => by aesop,
        Finset.sum_const,
        Finset.card_range,
        nsmul_one]
      norm_cast
    exact ⟨ M, 1 - d, h_complement ▸ h_complement_density, by linarith ⟩

/-
For every $\epsilon, \delta > 0$, there exists $x_0$ such that for all
$x \ge x_0$ at least $(1 - \delta)x$ of the integers $n \le x$ satisfy
$f(n) < (1 + \epsilon)n$.
-/
set_option linter.flexible false in
theorem main_theorem (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
  ∃ x₀ : ℝ, ∀ x ≥ x₀,
    (Finset.filter (fun n => (f n : ℝ) < (1 + ε) * n)
      (Finset.range (⌊x⌋₊ + 1))).card ≥ (1 - δ) * x := by
      -- Let's choose $M$ from Lemma 1.
      obtain ⟨M, d, hd⟩ :
          ∃ M : ℕ, ∃ d : ℝ,
            has_natural_density
              {n : ℕ | (n.primeFactors.filter (fun p => p < M)).card ≥ 2} d ∧
              d ≥ 1 - δ / 4 := by
        convert lemma_1 ( δ / 2 ) ( half_pos hδ ) using 6 ; ring;
      -- Lemma 3 applies eventually for each fixed prime pair $p,q<M$.
      have h_ex_m :
          ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q → p < M → q < M →
            ∃ K : ℕ, ∀ n ≥ K, p ∣ n → q ∣ n →
              (f n : ℝ) < (1 + ε) * n := by
        intro p q hp hq hpq hpM hqM
        obtain ⟨K, hK⟩ := lemma_3 p q hp hq hpq (ε / 2) (half_pos hε);
        use K + 2;
        intro n hn hpq hq
        obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hK n ( by linarith ) hpq hq
        refine lt_of_le_of_lt
          ( Nat.cast_le.mpr <| show f n ≤ m from ?_ )
          ?_
        · unfold f;
          split_ifs <;> simp_all +decide;
          exact ⟨ m, le_rfl, hm₁, hm₃.trans <| by intro x hx; aesop ⟩;
        · nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ];
      -- Choose one threshold covering all prime pairs below $M$.
      obtain ⟨K, hK⟩ :
          ∃ K : ℕ, ∀ n ≥ K,
            (n.primeFactors.filter (fun p => p < M)).card ≥ 2 →
              (f n : ℝ) < (1 + ε) * n := by
        choose! K hK using h_ex_m;
        use
          Finset.sup (Finset.filter Nat.Prime (Finset.range M))
            (fun p =>
              Finset.sup (Finset.filter Nat.Prime (Finset.range M))
                (fun q => if p = q then 0 else K p q)) + 1;
        intros n hn hn_card
        obtain ⟨p, hp, q, hq, hpq⟩ :
            ∃ p q : ℕ,
              Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p < M ∧ q < M ∧
                p ∣ n ∧ q ∣ n := by
          obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.mp hn_card
          use p, q
          aesop
        exact hK p hp q hq hpq.1 hpq.2.1 hpq.2.2.1 n
          ( by
            linarith [
              show K p hp ≤
                  Finset.sup ( Finset.filter Nat.Prime ( Finset.range M ) )
                    ( fun p =>
                      Finset.sup ( Finset.filter Nat.Prime ( Finset.range M ) )
                        ( fun q => if p = q then 0 else K p q ) ) from
                Finset.le_sup_of_le
                  ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hpq.2.1, q ⟩ )
                  ( Finset.le_sup_of_le
                    ( Finset.mem_filter.mpr
                      ⟨ Finset.mem_range.mpr hpq.2.2.1, hq ⟩ )
                    ( by aesop ) )] )
          hpq.2.2.2.1
          hpq.2.2.2.2
      -- Lemma 1 gives a lower bound for the cardinality of $S_x$.
      obtain ⟨x₀, hx₀⟩ :
          ∃ x₀ : ℕ, ∀ x ≥ x₀,
            (Finset.filter
              (fun n => (n.primeFactors.filter (fun p => p < M)).card ≥ 2)
              (Finset.range (x + 1))).card ≥ (d - δ / 4) * x := by
        have h_card_Sx :
            Filter.Tendsto
              (fun x =>
                (Finset.filter
                  (fun n => (n.primeFactors.filter (fun p => p < M)).card ≥ 2)
                  (Finset.range (x + 1))).card / (x : ℝ))
              Filter.atTop (nhds d) := by
          have := hd.1;
          have := this.comp
            ( show Filter.Tendsto ( fun x : ℕ => x + 1 ) Filter.atTop Filter.atTop from
              Filter.tendsto_add_atTop_nat 1 )
          convert this.mul
              ( show
                  Filter.Tendsto ( fun x : ℕ => ( x + 1 : ℝ ) / x )
                    Filter.atTop ( nhds 1 ) from ?_ )
            using 2 <;> norm_num;
          · rw [ div_mul_div_cancel₀ ( by positivity ) ];
          · norm_num [ add_div ];
            simpa [one_div] using Filter.Tendsto.add
              (tendsto_const_nhds.congr' ( by
                filter_upwards [ Filter.eventually_ne_atTop 0 ] with x hx
                rw [ div_self ( Nat.cast_ne_zero.mpr hx ) ] ))
              (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
        have := h_card_Sx.eventually ( lt_mem_nhds <| show d > d - δ / 4 by linarith );
        rw [ Filter.eventually_atTop ] at this
        rcases this with ⟨ x₀, hx₀ ⟩
        exact ⟨ x₀ + 1, fun x hx => by
          have := hx₀ x ( by linarith )
          rw [ lt_div_iff₀ ( Nat.cast_pos.mpr <| by linarith ) ] at this
          linarith⟩
      -- Bound the part of $S_x$ below the finite threshold.
      obtain ⟨x₁, hx₁⟩ :
          ∃ x₁ : ℕ, ∀ x ≥ x₁,
            (Finset.filter
              (fun n => (n.primeFactors.filter (fun p => p < M)).card ≥ 2 ∧ n < K)
              (Finset.range (x + 1))).card ≤ δ / 4 * x := by
        use ⌈ ( K : ℝ ) / ( δ / 4 ) ⌉₊ + 1;
        intro x hx;
        have hδ4 : 0 < δ / 4 := by positivity;
        have hcard_le :
            ((Finset.filter
              (fun n => (n.primeFactors.filter (fun p => p < M)).card ≥ 2 ∧ n < K)
              (Finset.range (x + 1))).card : ℝ) ≤ K := by
          have hcard_le_nat :
              (Finset.filter
                (fun n =>
                  (n.primeFactors.filter (fun p => p < M)).card ≥ 2 ∧ n < K)
                (Finset.range (x + 1))).card ≤ K := by
            simpa [ge_iff_le] using
              Finset.card_le_card
                ( show
                    Finset.filter
                        ( fun n =>
                          2 ≤ Finset.card
                            ( Finset.filter ( fun p => p < M ) ( Nat.primeFactors n ) ) ∧
                            n < K )
                        ( Finset.range ( x + 1 ) ) ⊆ Finset.range K from
                  fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2.2 )
          exact_mod_cast hcard_le_nat;
        have hceil_le_x : ((⌈ (K : ℝ) / (δ / 4) ⌉₊ : ℕ) : ℝ) ≤ x := by
          exact_mod_cast (show ⌈ (K : ℝ) / (δ / 4) ⌉₊ ≤ x by omega);
        have hK_le : (K : ℝ) ≤ δ / 4 * x := by
          have hdiv_le_x : (K : ℝ) / (δ / 4) ≤ (x : ℝ) := (Nat.le_ceil _).trans hceil_le_x;
          have := (div_le_iff₀ hδ4).1 hdiv_le_x;
          nlinarith;
        exact hcard_le.trans hK_le;
      refine ⟨ x₀ + x₁ + ⌈δ⁻¹ * 4⌉₊ + 1, fun x hx => ?_ ⟩
      norm_num at *
      -- Applying the bounds from hx₀ and hx₁, we get:
      have h_card :
          (Finset.filter (fun n => (f n : ℝ) < (1 + ε) * n)
            (Finset.range (⌊x⌋₊ + 1))).card ≥
            (Finset.filter
              (fun n => (n.primeFactors.filter (fun p => p < M)).card ≥ 2)
              (Finset.range (⌊x⌋₊ + 1))).card -
              (Finset.filter
                (fun n =>
                  (n.primeFactors.filter (fun p => p < M)).card ≥ 2 ∧ n < K)
                (Finset.range (⌊x⌋₊ + 1))).card := by
        refine Nat.sub_le_of_le_add ?_
        rw [ ← Finset.card_union_add_card_inter ]
        refine le_trans ?_ ( Nat.le_add_right _ _ )
        refine Finset.card_mono ?_;
        intro n hn; by_cases h : n < K <;> aesop;
      have := hx₀ ⌊x⌋₊ ( Nat.le_floor <| by linarith )
      have := hx₁ ⌊x⌋₊ ( Nat.le_floor <| by linarith )
      norm_num at *
      nlinarith [
        Nat.le_ceil ( δ⁻¹ * 4 ),
        mul_inv_cancel₀ ( ne_of_gt hδ ),
        Nat.floor_le ( show 0 ≤ x by linarith ),
        Nat.lt_floor_add_one x,
        show
            ( Finset.card
              ( Finset.filter
                ( fun n : ℕ => 2 ≤ { p ∈ n.primeFactors | p < M }.card )
                ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) : ℝ ) ≤
              Finset.card
                ( Finset.filter
                  ( fun n : ℕ => ( f n : ℝ ) < ( 1 + ε ) * n )
                  ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) +
                Finset.card
                  ( Finset.filter
                    ( fun n : ℕ =>
                      2 ≤ { p ∈ n.primeFactors | p < M }.card ∧ n < K )
                    ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) by
          exact_mod_cast h_card]

#print axioms main_theorem
-- 'Erdos459.main_theorem' depends on axioms: [propext, choice, Quot.sound]

end Erdos459
