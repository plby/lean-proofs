import Mathlib


/-
f(u) is the smallest number v > u such that all prime factors of v are factors of u.
-/
def f (u : ℕ) : ℕ :=
  if h : u < 2 then 0
  else Nat.find (show ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors by
                  -- Let $p$ be a prime factor of $u$. Then $u \cdot p$ is divisible by all prime factors of $u$.
                  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
                    exact Nat.exists_prime_and_dvd ( by linarith );
                  -- Let $v = u \cdot p$. Then $v$ is divisible by all prime factors of $u$ and $v > u$.
                  use u * p;
                  exact ⟨ lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt, fun x hx => by rw [ Nat.primeFactors_mul ] at * <;> aesop ⟩)

/-
For u ≥ 2, u + 2 ≤ f(u) ≤ u^2.
-/
theorem f_bounds {u : ℕ} (hu : 2 ≤ u) : u + 2 ≤ f u ∧ f u ≤ u ^ 2 := by
  -- Let's first prove that $u + 2 \leq f(u)$.
  have h_lower_bound : u + 2 ≤ f u := by
    -- By definition of $f$, we know that $f(u)$ is the smallest number greater than $u$ such that all prime factors of $f(u)$ are factors of $u$.
    have hf_def : ∀ v, u < v → v.primeFactors ⊆ u.primeFactors → u + 2 ≤ v := by
      intro v hv₁ hv₂; rcases Nat.even_or_odd' v with ⟨ k, rfl | rfl ⟩ <;> rcases Nat.even_or_odd' u with ⟨ l, rfl | rfl ⟩ <;> simp_all +arith +decide
      · linarith [ show k > l by linarith ];
      · contrapose! hv₂;
        norm_num [ show k = l + 1 by linarith ];
        norm_num [ Finset.subset_iff, Nat.primeFactors_mul ];
      · by_contra h_contra₁ ; simp_all +arith +decide [ Finset.subset_iff ];
        norm_num [ show k = l by linarith ] at *;
        exact absurd ( hv₂ ( Nat.minFac_prime ( by linarith ) ) ( Nat.minFac_dvd _ ) ) ( by intro t; have := Nat.dvd_gcd t.1 ( Nat.minFac_dvd _ ) ; aesop );
      · grind;
    convert hf_def _ ( Nat.find_spec ( _ : ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors ) |>.1 ) ( Nat.find_spec ( _ : ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors ) |>.2 ) using 1;
    unfold f
    split
    next h => exact (False.elim ((Nat.not_lt_of_ge hu) h))
    next h => rfl
    -- Let $p$ be a prime factor of $u$. Then $u \cdot p$ is divisible by all prime factors of $u$ and $u \cdot p > u$.
    obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
      exact Nat.exists_prime_and_dvd ( by linarith );
    use u * p;
    exact ⟨ lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt, by rw [ Nat.primeFactors_mul ( by linarith ) ( by linarith [ hp.1.pos ] ) ] ; aesop_cat ⟩
  refine ⟨ h_lower_bound, ?_ ⟩;
  -- By definition of $f$, we know that $f(u)$ is the smallest integer greater than $u$ such that all prime factors of $f(u)$ are factors of $u$.
  have h_def : ∀ v > u, v.primeFactors ⊆ u.primeFactors → f u ≤ v := by
    unfold f; aesop;
  exact h_def _ ( by nlinarith ) ( by rw [ Nat.primeFactors_pow ] ; aesop )

/-
When p is prime, f(p) = p^2.
-/
theorem f_prime {p : ℕ} (hp : p.Prime) : f p = p ^ 2 := by
  refine' le_antisymm ( f_bounds hp.two_le |>.2 ) _;
  -- By definition of $f$, we know that $p^2$ is the smallest integer greater than $p$ whose prime factors are all factors of $p$.
  have h_fp_def : ∀ v, p < v ∧ v.primeFactors ⊆ {p} → p^2 ≤ v := by
    -- If $v$'s prime factors are all $p$, then $v$ must be $p^k$ for some $k$.
    intro v hv
    obtain ⟨k, hk⟩ : ∃ k, v = p^k := by
      rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : v ≠ 0 ) ] ; rw [ Finsupp.prod ] ; aesop;
    exact hk.symm ▸ Nat.pow_le_pow_right hp.pos ( show k ≥ 2 by contrapose! hv; interval_cases k <;> aesop );
  unfold f at *;
  split_ifs at * <;> simp_all +decide
  · interval_cases p <;> trivial;
  · grind

/-
If u is a non-zero even number, the prime factors of any power of 2 are a subset of the prime factors of u.
-/
theorem primeFactors_pow_two_subset_even {u k : ℕ} (hu : Even u) (hu0 : u ≠ 0) : (2 ^ k).primeFactors ⊆ u.primeFactors := by
  rcases k with ( _ | k ) <;> simp_all +decide [ Nat.primeFactors_pow ];
  exact even_iff_two_dvd.mp hu

/-
For n ≥ 1, n ≤ 2^(size(n-1)).
-/
theorem le_pow_size_sub_one {n : ℕ} (hn : 1 ≤ n) : n ≤ 2 ^ (n - 1).size := by
  -- Let $m = n - 1$. Then $n = m + 1$.
  set m : ℕ := n - 1;
  -- By definition of size, we know that $m < 2^{\text{size}(m)}$.
  have h_size : m < 2 ^ (Nat.size m) := by
    exact Nat.lt_size_self m;
  grind

/-
For any natural number u, u < 2^(u.size).
-/
theorem lt_pow_size (u : ℕ) : u < 2 ^ u.size := by
  exact Nat.lt_size_self u

/-
If u is even, then f(u) is at most the smallest power of 2 greater than u.
-/
theorem f_even_le_next_pow_two {u : ℕ} (hu_even : Even u) (hu_pos : 0 < u) : f u ≤ 2 ^ (Nat.log 2 u + 1) := by
  -- Since $u$ is even, $u$ has at least one factor of 2.
  have h_even_factor : u.primeFactors ⊇ {2} := by
    exact Finset.singleton_subset_iff.mpr ( Nat.mem_primeFactors.mpr ⟨ Nat.prime_two, even_iff_two_dvd.mp hu_even, by aesop ⟩ );
  -- Since $2^{Nat.log 2 u + 1}$ is greater than $u$ and all its prime factors are in $u$'s prime factors, it must be that $f(u) \leq 2^{Nat.log 2 u + 1}$.
  have h_f_le : ∀ v, u < v → v.primeFactors ⊆ u.primeFactors → f u ≤ v := by
    unfold f; aesop;
  exact h_f_le _ ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( by rw [ Nat.primeFactors_pow ] <;> norm_num ; aesop )

/-
For k ≥ 2, f(2^k - 2) = (2^k - 2) + 2.
-/
theorem f_eq_u_plus_two_of_u_eq_pow_two_sub_two {k : ℕ} (hk : 2 ≤ k) : f (2 ^ k - 2) = (2 ^ k - 2) + 2 := by
  refine' le_antisymm _ _;
  · -- For $k \geq 2$, $2^k - 2$ is even, so we can apply the theorem $f_even_le_next_pow_two$.
    have h_even : Even (2 ^ k - 2) := by
      exact even_iff_two_dvd.mpr ( Nat.dvd_sub ( dvd_pow_self _ ( by linarith ) ) ( by norm_num ) );
    convert f_even_le_next_pow_two h_even ( Nat.sub_pos_of_lt <| by linarith [ Nat.pow_le_pow_right two_pos hk ] ) using 1;
    rw [ Nat.sub_add_cancel ( show 2 ≤ 2 ^ k from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hk ) ) ];
    -- Since $2^k - 2$ is less than $2^k$, we have $\log_2(2^k - 2) = k - 1$.
    have h_log : Nat.log 2 (2 ^ k - 2) = k - 1 := by
      rw [ Nat.log_eq_iff ] <;> norm_num;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        exact le_tsub_of_add_le_left ( by linarith [ Nat.one_le_pow k 2 zero_lt_two ] );
      · exact Or.inl ( Nat.sub_ne_zero_of_lt hk );
    cases k <;> aesop;
  · have := f_bounds ( show 2 ≤ 2 ^ k - 2 from Nat.le_sub_of_add_le ( by linarith [ Nat.pow_le_pow_right two_pos hk ] ) ) ; aesop;

/-
There are infinitely many u such that f(u) = u + 2.
-/
theorem infinite_setOf_f_eq_self_add_two : Set.Infinite {u | f u = u + 2} := by
  -- By definition of $f$, we know that for any $k \geq 2$, $f(2^k - 2) = (2^k - 2) + 2$.
  have h_f_eq_add_two : ∀ k ≥ 2, f (2^k - 2) = (2^k - 2) + 2 := by
    exact fun k a => f_eq_u_plus_two_of_u_eq_pow_two_sub_two a;
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ _, h_f_eq_add_two ( n + 2 ) ( by linarith ), lt_tsub_iff_right.mpr ( by induction' n with n ih <;> norm_num [ Nat.pow_succ' ] at * ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ) ⟩

/-
There are infinitely many u such that f(u) = u^2.
-/
theorem infinite_setOf_f_eq_sq : Set.Infinite {u | f u = u ^ 2} := by
  exact Nat.infinite_setOf_prime.mono ( fun p hp ↦ by simpa [ hp.ne_zero ] using f_prime hp ) |> Set.Infinite.mono fun u hu ↦ by aesop;
