/-

This is a Lean formalization of a solution to Erdős Problem 205.
https://www.erdosproblems.com/forum/thread/205

Please see the thread above for the history.

Roughly speaking, Wouter van Doorn suggested an approach, ChatGPT made
it into a full proof informally, and Aristotle formalized it.

Later, Terence Tao suggested that the log log m could be replaced with
>>sqrt(log m / log log m), which was independently verified.  This
file is a formal proof of THAT bound, produced with ChatGPT and
Aristotle.

We assume a statement of the Prime Number Theorem taken from the
PrimeNumberTheoremAnd project, but admitted as an axiom:
nth_prime_asymp.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos205

open Real Filter Asymptotics

/-
We assume we have the Prime Number Theorem in the (asymptotic) form
  nth_prime n ~ n * log n  as n → ∞.
-/
noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

axiom nth_prime_asymp :
    (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ))

/-
Let Omega(m) be the number of prime factors of m counted with multiplicity.
-/
def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-
A “PNT-scale” rate:  sqrt( (log n) / (log log n) ).
(Defined for all `n` using Mathlib's total `Real.log`, `Real.sqrt`.)
-/
noncomputable def pntRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))

/-
From `nth_prime_asymp` one can extract a Big-O / “exists a constant” upper bound for the
n-th prime:
  ∃ C > 0, ∀ᶠ n, nth_prime(n) ≤ C * n * log n.
-/
theorem nth_prime_le_const_mul_log_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ n in atTop, ((nth_prime n) : ℝ) ≤ C * (n : ℝ) * Real.log (n : ℝ)) := by
  -- Since the ratio (nth_prime n : ℝ) / (n * log n) tends to 1, there exists some N such that for all n ≥ N, the ratio is less than 2.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (nth_prime n : ℝ) / (n * Real.log n) < 2 := by
    have h_ratio : Filter.Tendsto (fun n : ℕ => (nth_prime n : ℝ) / (n * Real.log n)) Filter.atTop (nhds 1) := by
      have := nth_prime_asymp;
      rw [ Asymptotics.IsEquivalent ] at this;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
      · simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Pi.sub_apply, sub_div, div_self <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hx ) <| Real.log_pos <| Nat.one_lt_cast.mpr hx ] ; ring );
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn h using absurd h <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn;
    simpa using h_ratio.eventually ( gt_mem_nhds one_lt_two );
  refine' ⟨ 2, zero_lt_two, _ ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 1 ] with n hn hn' using by have := hN n hn; rw [ div_lt_iff₀ ( mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hn' ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn' ) ] at this; linarith;

/-
Select E^2 distinct odd primes, none equal to 3; for definiteness, take the first E^2 odd primes >= 5
and label them as p_{k,j}. Define Q_k as the product of p_{k,j} for j from 1 to E.
-/
noncomputable def p_kj (E k j : ℕ) : ℕ := Nat.nth Nat.Prime (k * E + (j - 1) + 2)

noncomputable def Q_k (E k : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 E, p_kj E k j

/-
Define M := 2^E * 3 * product_{k=0}^{E-1} Q_k.
-/
noncomputable def M (E : ℕ) : ℕ := 2^E * 3 * ∏ k ∈ Finset.range E, Q_k E k

/-
n is a solution if n = 0 mod 2^E, n = 0 mod 3, and n = 2^k mod Q_k for all k < E.
-/
def is_solution (E n : ℕ) : Prop :=
  n ≡ 0 [MOD 2^E] ∧
  n ≡ 0 [MOD 3] ∧
  ∀ k < E, n ≡ 2^k [MOD Q_k E k]

/-
p_{k,j} >= 5 for all valid indices.
-/
theorem p_kj_ge_5 (E k j : ℕ) : p_kj E k j ≥ 5 := by
  refine' le_trans _ ( Nat.nth_monotone _ <| Nat.le_add_left _ _ );
  · bound;
  · exact Nat.infinite_setOf_prime

/-
The primes p_{k,j} are distinct for distinct indices (k,j).
-/
theorem p_kj_injective (E : ℕ) :
  ∀ k1 < E, ∀ j1 ∈ Finset.Icc 1 E,
  ∀ k2 < E, ∀ j2 ∈ Finset.Icc 1 E,
  p_kj E k1 j1 = p_kj E k2 j2 → k1 = k2 ∧ j1 = j2 := by
    intros k1 hk1 j1 hj1 k2 hk2 j2 hj2 h_eq;
    -- Since the sequence of primes is strictly increasing, p_{k1, j1} = p_{k2, j2} implies the indices are equal.
    have h_inj : k1 * E + (j1 - 1) + 2 = k2 * E + (j2 - 1) + 2 := by
      apply Nat.nth_injective ( Nat.infinite_setOf_prime ) h_eq;
    have h_inj : k1 = k2 := by
      nlinarith [ Nat.sub_add_cancel ( Finset.mem_Icc.mp hj1 |>.1 ), Nat.sub_add_cancel ( Finset.mem_Icc.mp hj2 |>.1 ), Finset.mem_Icc.mp hj1 |>.2, Finset.mem_Icc.mp hj2 |>.2 ];
    cases j1 <;> cases j2 <;> aesop

/-
Q_k is squarefree and Omega(Q_k) = E.
-/
theorem Q_k_props (E k : ℕ) (hk : k < E) :
  Squarefree (Q_k E k) ∧ Omega (Q_k E k) = E := by
    -- Now consider the product of primes $Q_k$, which is squarefree since it consists of distinct primes.
    have h_sqfree : Squarefree (∏ j ∈ Finset.Icc 1 E, p_kj E k j) := by
      -- Since the primes p_{k,j} are distinct, their product is squarefree.
      have h_distinct : ∀ j1 j2 : ℕ, j1 ∈ Finset.Icc 1 E → j2 ∈ Finset.Icc 1 E → j1 ≠ j2 → p_kj E k j1 ≠ p_kj E k j2 := by
        intros j1 j2 hj1 hj2 hne;
        have := p_kj_injective E k hk j1 hj1 k hk j2 hj2; aesop;
      -- Since the primes p_{k,j} are distinct, their product is squarefree by definition.
      have h_squarefree : ∀ {s : Finset ℕ}, (∀ j ∈ s, Nat.Prime (p_kj E k j)) → (∀ j1 ∈ s, ∀ j2 ∈ s, j1 ≠ j2 → p_kj E k j1 ≠ p_kj E k j2) → Squarefree (∏ j ∈ s, p_kj E k j) := by
        intros s hs_prime hs_distinct; induction s using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
        exact ⟨ Nat.Coprime.prod_right fun x hx => hs_prime.1.coprime_iff_not_dvd.mpr fun h => hs_distinct.1 x hx ( by aesop ) <| Nat.prime_dvd_prime_iff_eq hs_prime.1 ( hs_prime.2 x hx ) |>.1 h, hs_prime.1.squarefree ⟩;
      exact h_squarefree ( fun j hj => Nat.prime_nth_prime _ ) ( fun j1 hj1 j2 hj2 hij => h_distinct j1 j2 hj1 hj2 hij );
    -- Each p_{k,j} is prime and there are E such primes.
    have h_prime_factors : (Q_k E k).primeFactorsList.length = E := by
      have h_prime : ∀ j ∈ Finset.Icc 1 E, Nat.Prime (p_kj E k j) := by
        exact fun j hj => Nat.prime_nth_prime _
      -- Since the primes are distinct, the length of the list of prime factors is equal to the number of primes.
      have h_prime_factors_length : (Q_k E k).primeFactorsList.length = Finset.card (Finset.image (fun j => p_kj E k j) (Finset.Icc 1 E)) := by
        have h_prime_factors_length : (Q_k E k).primeFactorsList.toFinset = Finset.image (fun j => p_kj E k j) (Finset.Icc 1 E) := by
          ext; simp [Q_k];
          constructor;
          · intro h; have := h.2.1; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ] ;
            obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := this; have := Nat.coprime_primes h.1 ( h_prime x hx₁ hx₂ ) ; aesop;
          · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ h_prime a ( Finset.mem_Icc.mpr ⟨ ha₁, ha₂ ⟩ ), Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ ha₁, ha₂ ⟩ ), Finset.prod_ne_zero_iff.mpr fun x hx => Nat.Prime.ne_zero ( h_prime x hx ) ⟩;
        rw [ ← h_prime_factors_length, List.toFinset_card_of_nodup ];
        exact Squarefree.nodup_primeFactorsList h_sqfree;
      rw [ h_prime_factors_length, Finset.card_image_of_injOn fun i hi j hj hij => ?_, Nat.card_Icc ] ; aesop;
      have := p_kj_injective E k ( by aesop ) i hi k ( by aesop ) j hj; aesop;
    exact ⟨ h_sqfree, h_prime_factors ⟩

/-
The moduli Q_k are coprime to 2, 3, and each other.
-/
theorem moduli_properties (E : ℕ) :
  (∀ k < E, Nat.Coprime (Q_k E k) 2) ∧
  (∀ k < E, Nat.Coprime (Q_k E k) 3) ∧
  (∀ k1 < E, ∀ k2 < E, k1 ≠ k2 → Nat.Coprime (Q_k E k1) (Q_k E k2)) := by
    refine' ⟨ _, _, _ ⟩;
    · intro k hk
      have h_odd : ∀ j ∈ Finset.Icc 1 E, Odd (p_kj E k j) := by
        intro j hj; exact Nat.Prime.odd_of_ne_two ( Nat.prime_nth_prime _ ) ( by linarith [ p_kj_ge_5 E k j ] ) ;
      exact Nat.Coprime.prod_left fun j hj => Nat.Coprime.symm ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using h_odd j hj );
    · intro k hk;
      refine' Nat.Coprime.prod_left fun i hi => _;
      -- Since $p_{k,i}$ is a prime number greater than or equal to 5, it is coprime with 3.
      have h_coprime : Nat.Prime (p_kj E k i) ∧ p_kj E k i ≥ 5 := by
        exact ⟨ Nat.prime_nth_prime _, p_kj_ge_5 E k i ⟩;
      exact h_coprime.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( by decide ) h; linarith;
    · intro k1 hk1 k2 hk2 hne;
      -- Since the primes in $Q_{k1}$ and $Q_{k2}$ are distinct, their product is coprime.
      have h_coprime_primes : ∀ j1 ∈ Finset.Icc 1 E, ∀ j2 ∈ Finset.Icc 1 E, p_kj E k1 j1 ≠ p_kj E k2 j2 := by
        intros j1 hj1 j2 hj2 h_eq;
        have := p_kj_injective E k1 hk1 j1 hj1 k2 hk2 j2 hj2 h_eq; aesop;
      exact Nat.Coprime.prod_left fun i hi => Nat.Coprime.prod_right fun j hj => by have := Nat.coprime_primes ( show Nat.Prime ( p_kj E k1 i ) from by exact Nat.prime_nth_prime _ ) ( show Nat.Prime ( p_kj E k2 j ) from by exact Nat.prime_nth_prime _ ) ; aesop;

/-
Define the modulus and remainder maps for the CRT system.
Index 0 corresponds to modulus 2^E and remainder 0.
Index 1 corresponds to modulus 3 and remainder 0.
Index k+2 corresponds to modulus Q_k and remainder 2^k.
-/
noncomputable def modulus_map (E : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 2^E
  else if i = 1 then 3
  else Q_k E (i - 2)

def remainder_map (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if i = 1 then 0
  else 2^(i - 2)

def indices (E : ℕ) : List ℕ := List.range (E + 2)

/-
The list of moduli consists of pairwise coprime integers.
-/
noncomputable def moduli_list (E : ℕ) : List ℕ := (indices E).map (modulus_map E)

def remainders_list (E : ℕ) : List ℕ := (indices E).map (remainder_map)

theorem moduli_pairwise_coprime (E : ℕ) (hE : E ≥ 10) :
  (moduli_list E).Pairwise Nat.Coprime := by
    -- By definition of moduli_list, it consists of 2^E, 3, and the Q_k's.
    simp [moduli_list];
    unfold indices modulus_map;
    -- Since $2^E$, $3$, and each $Q_k$ are pairwise coprime, the entire list is pairwise coprime.
    have h_coprime : Nat.Coprime (2^E) 3 ∧ ∀ k < E, Nat.Coprime (2^E) (Q_k E k) ∧ Nat.Coprime 3 (Q_k E k) ∧ ∀ k1 < E, ∀ k2 < E, k1 ≠ k2 → Nat.Coprime (Q_k E k1) (Q_k E k2) := by
      have := moduli_properties E;
      exact ⟨ by exact Nat.Coprime.pow_left _ ( by decide ), fun k hk => ⟨ Nat.Coprime.pow_left _ ( this.1 k hk |> Nat.Coprime.symm ), this.2.1 k hk |> Nat.Coprime.symm, this.2.2 ⟩ ⟩;
    rw [ List.pairwise_iff_get ];
    grind

/-
n_E satisfies the system of congruences.
-/
noncomputable def n_E (E : ℕ) (hE : E ≥ 10) : ℕ :=
  (Nat.chineseRemainderOfList (remainder_map) (modulus_map E) (indices E) (by
    have h := moduli_pairwise_coprime E hE
    rw [moduli_list] at h
    rw [List.pairwise_map] at h
    exact h
  )).val

theorem n_E_is_solution (E : ℕ) (hE : E ≥ 10) : is_solution E (n_E E hE) := by
  -- By definition of $n_E$, it satisfies the system of congruences.
  have h_cong : ∀ i ∈ indices E, n_E E hE ≡ remainder_map i [MOD modulus_map E i] := by
    unfold n_E;
    grind;
  refine' ⟨ _, _, _ ⟩;
  · exact h_cong 0 ( by simp +decide [ indices ] );
  · convert h_cong 1 _ using 1 ; norm_num [ indices ];
  · intro k hk;
    convert h_cong ( k + 2 ) _ using 1;
    exact List.mem_range.mpr ( by linarith )

/-
If a divides b and b is not zero, then Omega(a) <= Omega(b).
-/
theorem Omega_dvd_le {a b : ℕ} (h_dvd : a ∣ b) (hb : b ≠ 0) : Omega a ≤ Omega b := by
  obtain ⟨ c, rfl ⟩ := h_dvd;
  -- If $p$ divides $a$ and $c$, then $\Omega(p^i) \leq \Omega(p^i \cdot p^j)$ for any $i, j \geq 0$.
  have h_prime_factors (p : ℕ) (hp : Nat.Prime p) (a c : ℕ) (ha : a ≠ 0) (hc : c ≠ 0) : (Nat.factorization a p) + (Nat.factorization c p) = (Nat.factorization (a * c) p) := by
    rw [ Nat.factorization_mul ] <;> aesop;
  -- By definition of Omega, we have Omega(a) = ∑ p ∈ Nat.primeFactors a, Nat.factorization a p and Omega(a * c) = ∑ p ∈ Nat.primeFactors (a * c), Nat.factorization (a * c) p.
  have h_omega_def : Omega a = ∑ p ∈ Nat.primeFactors a, Nat.factorization a p ∧ Omega (a * c) = ∑ p ∈ Nat.primeFactors (a * c), Nat.factorization (a * c) p := by
    have h_omega_def : ∀ n : ℕ, n ≠ 0 → (Nat.primeFactorsList n).length = ∑ p ∈ Nat.primeFactors n, Nat.factorization n p := by
      intro n hn; rw [ ← Multiset.coe_card ] ; rw [ ← Multiset.toFinset_sum_count_eq ] ; aesop;
    exact ⟨ h_omega_def a ( by aesop ), h_omega_def ( a * c ) hb ⟩;
  rw [ h_omega_def.1, h_omega_def.2 ];
  exact Finset.sum_le_sum_of_subset ( Nat.primeFactors_mono ( dvd_mul_right _ _ ) ( by aesop ) ) |> le_trans ( Finset.sum_le_sum fun p hp => h_prime_factors p ( Nat.prime_of_mem_primeFactors hp ) a c ( by aesop ) ( by aesop ) ▸ Nat.le_add_right _ _ )

/-
Omega(2^E) = E.
-/
theorem Omega_pow_two (E : ℕ) : Omega (2^E) = E := by
  -- Omega(p^k) = k for any prime p. Since 2 is prime, Omega(2^E) = E.
  have h_prime_power : ∀ p k : ℕ, Nat.Prime p → Omega (p ^ k) = k := by
    intros p k hp
    have h_prime_factors : (p ^ k).primeFactorsList = List.replicate k p := by
      exact Nat.Prime.primeFactorsList_pow hp k;
    unfold Omega; aesop;
  exact h_prime_power 2 E Nat.prime_two

/-
n_E is not a power of 2.
-/
theorem n_E_not_pow_two (E : ℕ) (hE : E ≥ 10) : ∀ k, n_E E hE ≠ 2^k := by
  -- By definition of $n_E$, we know that $n_E \equiv 0 \pmod{3}$.
  have h_mod_3 : n_E E hE ≡ 0 [MOD 3] := by
    exact n_E_is_solution E hE |>.2.1;
  exact fun k hk => by have := Nat.dvd_of_mod_eq_zero h_mod_3; norm_num [ hk, Nat.Prime.dvd_iff_one_le_factorization ] at this;

/-
If k < E, then Omega(n(E) - 2^k) >= E.
-/
theorem Omega_lower_bound_case1 (E : ℕ) (hE : E ≥ 10) (k : ℕ) (hk : k < E) (h_le : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    -- Since $Q_k$ divides $n_E - 2^k$ and $Q_k$ is squarefree with $\Omega(Q_k) = E$, we have $\Omega(n_E - 2^k) \geq \Omega(Q_k) = E$ by the properties of the prime factors.
    have h_Qk_div : Q_k E k ∣ n_E E hE - 2 ^ k := by
      have h_mod : n_E E hE ≡ 2^k [MOD Q_k E k] := by
        convert n_E_is_solution E hE |>.2.2 k hk;
      rw [ ← Nat.modEq_zero_iff_dvd ];
      cases le_iff_exists_add'.mp h_le ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    by_cases h : n_E E hE - 2 ^ k = 0;
    · rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := n_E_not_pow_two E hE k; aesop;
      · exact h_le;
    · exact le_trans ( by erw [ Q_k_props E k hk |>.2 ] ) ( Omega_dvd_le h_Qk_div h )

/-
If k >= E, then Omega(n(E) - 2^k) >= E.
-/
theorem Omega_lower_bound_case2 (E : ℕ) (hE : E ≥ 10) (k : ℕ) (hk : k ≥ E) (h_le : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    -- Since $2^E$ divides $n_E$, we have $2^E \mid (n_E - 2^k)$.
    have h_div : 2^E ∣ (n_E E (by linarith) - 2^k) := by
      -- By definition of $n_E$, we know that $n_E$ is a solution to the system of congruences.
      have h_n_E_sol : n_E E hE ≡ 0 [MOD 2^E] := by
        exact n_E_is_solution E hE |>.1;
      exact Nat.dvd_sub ( Nat.dvd_of_mod_eq_zero h_n_E_sol ) ( pow_dvd_pow _ hk );
    by_cases h : n_E E ( by linarith ) - 2 ^ k = 0 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    · rw [ Nat.sub_eq_iff_eq_add ] at h <;> try linarith;
      exact absurd ( n_E_not_pow_two E ( by linarith ) k ) ( by aesop );
    · have h_omega_ge_E : Omega (2^E) ≤ Omega (n_E E hE - 2^k) := by
        exact Omega_dvd_le ( Nat.dvd_of_mod_eq_zero h_div ) h;
      exact le_trans ( by rw [ Omega_pow_two ] ) h_omega_ge_E

/-
Omega(n(E) - 2^k) >= E for all valid k.
-/
theorem Omega_lower_bound (E : ℕ) (hE : E ≥ 10) (k : ℕ) (hk : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    by_cases hk : k < E;
    · (expose_names; exact Omega_lower_bound_case1 E hE k hk hk_1);
    · exact Omega_lower_bound_case2 E hE k ( le_of_not_gt hk ) ‹_›

/-
A PNT-quality bound for p_{k,j}, stated in the “∃ constant, for all sufficiently large E” form.

This is the kind of statement you can actually extract from `nth_prime_asymp` without
choosing explicit numerical constants:
  p_{k,j} ≤ C * E^2 * log E  (eventually in E).
-/
theorem p_kj_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ k < E, ∀ j ∈ Finset.Icc 1 E,
          ((p_kj E k j) : ℝ) ≤ C * (E : ℝ)^2 * Real.log (E : ℝ)) := by
  -- Apply `nth_prime_asymp` to get a constant C such that `nth_prime(n) ≤ C * n * log n` for all n.
  obtain ⟨C, hC_pos, hC_eventually⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop, nth_prime n ≤ C * (n : ℝ) * Real.log (n : ℝ) := by
    exact nth_prime_le_const_mul_log_eventually;
  -- Since $p_{k,j}$ is the $(kE + j + 1)$-th prime, we can use the fact that $p_n \leq C n \log n$ for large $n$ to bound $p_{k,j}$.
  have h_prime_bound : ∀ᶠ E in Filter.atTop, ∀ k < E, ∀ j ∈ Finset.Icc 1 E, p_kj E k j ≤ C * (E^2 + E + 1) * Real.log (E^2 + E + 1) := by
    have h_prime_bound : ∀ᶠ E in Filter.atTop, ∀ k < E, ∀ j ∈ Finset.Icc 1 E, p_kj E k j ≤ nth_prime (E^2 + E + 1) := by
      refine Filter.Eventually.of_forall fun E k hk j hj => ?_;
      refine' Nat.nth_monotone _ _;
      · exact Nat.infinite_setOf_prime;
      · nlinarith [ Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith [ Finset.mem_Icc.mp hj ] : 1 ≤ j ) ];
    filter_upwards [ h_prime_bound, hC_eventually.filter_mono <| show Filter.Tendsto ( fun E : ℕ => E^2 + E + 1 ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_mono ( fun E => by nlinarith ) tendsto_natCast_atTop_atTop ] with E hE₁ hE₂ using fun k hk j hj => le_trans ( Nat.cast_le.mpr <| hE₁ k hk j hj ) <| mod_cast hE₂;
  -- We can simplify the expression $C * (E^2 + E + 1) * \log(E^2 + E + 1)$ to $C * E^2 * \log(E^2 + E + 1)$ since $E^2 + E + 1 \sim E^2$ for large $E$.
  have h_simplified_bound : ∀ᶠ E in Filter.atTop, ∀ k < E, ∀ j ∈ Finset.Icc 1 E, p_kj E k j ≤ C * (E^2) * Real.log (E^2 + E + 1) * 2 := by
    filter_upwards [ h_prime_bound, Filter.eventually_gt_atTop 1 ] with E hE₁ hE₂;
    intro k hk j hj; specialize hE₁ k hk j hj; nlinarith [ show 0 < C * Real.log ( E ^ 2 + E + 1 ) by exact mul_pos hC_pos ( Real.log_pos <| by norm_cast; nlinarith ), show ( E : ℝ ) ≥ 2 by norm_cast ] ;
  -- We can further simplify the expression $C * E^2 * \log(E^2 + E + 1) * 2$ to $C * E^2 * \log(E) * 4$ since $\log(E^2 + E + 1) \sim \log(E^2) = 2 \log(E)$ for large $E$.
  have h_final_bound : ∀ᶠ E in Filter.atTop, ∀ k < E, ∀ j ∈ Finset.Icc 1 E, p_kj E k j ≤ C * (E^2) * Real.log (E) * 8 := by
    have h_log_bound : ∀ᶠ E in Filter.atTop, Real.log (E^2 + E + 1) ≤ 4 * Real.log E := by
      filter_upwards [ Filter.eventually_gt_atTop 2 ] with E hE using by erw [ ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( by nlinarith [ sq_nonneg ( E - 2 ) ] ) ;
    filter_upwards [ h_simplified_bound, h_log_bound.natCast_atTop ] with E hE₁ hE₂ using fun k hk j hj => le_trans ( hE₁ k hk j hj ) ( by nlinarith [ show 0 ≤ C * ( E : ℝ ) ^ 2 by positivity, hE₂ ] );
  exact ⟨ C * 8, by positivity, h_final_bound.mono fun E hE k hk j hj => by linarith [ hE k hk j hj ] ⟩

/-
A corresponding PNT-quality bound for Q_k (product of E such primes):
  log Q_k ≤ C * E * log E  (eventually in E).
We state it directly at the log level since that is the natural scale.
-/
theorem log_Q_k_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ k < E,
          Real.log ((Q_k E k : ℕ) : ℝ) ≤ C * (E : ℝ) * Real.log (E : ℝ)) := by
  -- Applying the bound for p_{k,j} to Q_k, we get log Q_k ≤ E * log (C * E^2 * log E).
  have h_log_Q_upper_bound : ∃ C > 0, ∀ᶠ E in Filter.atTop, ∀ k < E, Real.log (Q_k E k) ≤ E * Real.log (C * (E : ℝ)^2 * Real.log (E : ℝ)) := by
    have h_log_Q_upper_bound : ∃ C > 0, ∀ᶠ E in Filter.atTop, ∀ k < E, ∀ j ∈ Finset.Icc 1 E, Real.log (p_kj E k j) ≤ Real.log (C * (E : ℝ)^2 * Real.log (E : ℝ)) := by
      obtain ⟨ C, hC₀, hC ⟩ := p_kj_bound_eventually;
      exact ⟨ C, hC₀, hC.mono fun E hE k hk j hj => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by { unfold p_kj; aesop } ) <| hE k hk j hj ⟩;
    obtain ⟨ C, hC₀, hC ⟩ := h_log_Q_upper_bound; use C, hC₀; filter_upwards [ hC ] with E hE; intro k hk; specialize hE k hk; simp_all +decide [ Q_k ] ;
    rw [ Real.log_prod _ _ fun i hi => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by unfold p_kj; aesop ] ; exact le_trans ( Finset.sum_le_sum fun i hi => hE i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ) ( by norm_num ) ;
  -- We can simplify the expression inside the logarithm: $\log (C * E^2 * \log E) = \log C + 2 \log E + \log \log E$.
  obtain ⟨C, hC_pos, hC_bound⟩ := h_log_Q_upper_bound
  have h_log_simplified : ∀ᶠ E in Filter.atTop, ∀ k < E, Real.log (Q_k E k) ≤ E * (Real.log C + 2 * Real.log E + Real.log (Real.log E)) := by
    filter_upwards [ hC_bound, Filter.eventually_gt_atTop 1 ] with E hE₁ hE₂;
    intro k hk; convert hE₁ k hk using 1; rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hE₂ ), Real.log_mul ( by positivity ) ( by positivity ) ] ; rw [ Real.log_pow ] ; ring;
  -- We can bound $\log C + 2 \log E + \log \log E$ by $C' \log E$ for some constant $C'$.
  obtain ⟨C', hC'_pos, hC'_bound⟩ : ∃ C' > 0, ∀ᶠ E in Filter.atTop, Real.log C + 2 * Real.log E + Real.log (Real.log E) ≤ C' * Real.log E := by
    -- We can bound $\log C + 2 \log E + \log \log E$ by $C' \log E$ for some constant $C'$ using the fact that $\log \log E$ grows slower than $\log E$.
    have h_log_log_bound : ∀ᶠ E in Filter.atTop, Real.log (Real.log E) ≤ Real.log E := by
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with E hE using Real.log_le_log ( Real.log_pos hE ) ( le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by linarith ) );
    exact ⟨ 4 + |Real.log C|, by positivity, by filter_upwards [ h_log_log_bound, Filter.eventually_gt_atTop ( Real.exp ( |Real.log C| + 1 ) ) ] with E hE₁ hE₂ using by cases abs_cases ( Real.log C ) <;> nlinarith [ Real.log_exp ( |Real.log C| + 1 ), Real.log_le_log ( by positivity ) hE₂.le ] ⟩;
  exact ⟨ C', hC'_pos, by filter_upwards [ h_log_simplified, hC'_bound.natCast_atTop ] with E hE₁ hE₂ using fun k hk => by nlinarith [ hE₁ k hk, hE₂ ] ⟩

/-
A PNT-quality bound for M(E), again at the log level:
  log M(E) ≤ C * E^2 * log E  (eventually in E).
This is the key input for the inversion to the sqrt(log n / log log n) scale.
-/
theorem log_M_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        Real.log ((M E : ℕ) : ℝ) ≤ C * (E : ℝ)^2 * Real.log (E : ℝ)) := by
  -- We'll use the bound for `log_Q_k_bound_eventually` to bound the logarithm of `M_E`.
  obtain ⟨C, hC_pos, hC_bound⟩ := log_Q_k_bound_eventually;
  use (C + 4 : ℝ); (
  -- We'll use the bound for `log_Q_k_bound_eventually` to bound the logarithm of `M_E`. Recall that $M_E = 2^E \cdot 3 \cdot \prod_{k=0}^{E-1} Q_k$.
  have hM_log : ∀ E ≥ 10, Real.log (M E) ≤ Real.log (2^E) + Real.log 3 + ∑ k ∈ Finset.range E, Real.log (Q_k E k) := by
    intro E hE; rw [ show ( M E : ℕ ) = 2 ^ E * 3 * ∏ k ∈ Finset.range E, Q_k E k from rfl ] ; rw [ Nat.cast_mul, Nat.cast_mul, Nat.cast_pow ] ; rw [ Real.log_mul, Real.log_mul ] <;> norm_cast <;> norm_num [ Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ] ;
    · rw [ Real.log_prod _ _ fun i hi => Nat.cast_ne_zero.mpr <| by exact Finset.prod_ne_zero_iff.mpr fun j hj => Nat.Prime.ne_zero <| Nat.prime_nth_prime _ ];
    · exact fun k hk => Finset.prod_ne_zero_iff.mpr fun j hj => Nat.Prime.ne_zero <| Nat.prime_nth_prime _;
  -- Using the bound for `log_Q_k_bound_eventually`, we can bound the sum $\sum_{k=0}^{E-1} \log(Q_k)$.
  have h_sum_bound : ∀ᶠ E in Filter.atTop, ∑ k ∈ Finset.range E, Real.log (Q_k E k) ≤ C * E^2 * Real.log E := by
    filter_upwards [ hC_bound, Filter.eventually_ge_atTop 10 ] with E hE hE' using le_trans ( Finset.sum_le_sum fun k hk => hE k <| Finset.mem_range.mp hk ) <| by norm_num; nlinarith;
  simp +zetaDelta at *;
  refine' ⟨ by positivity, _ ⟩;
  obtain ⟨ a, ha ⟩ := h_sum_bound; use Max.max a 10; intro b hb; specialize hM_log b ( le_trans ( le_max_right _ _ ) hb ) ; specialize ha b ( le_trans ( le_max_left _ _ ) hb ) ; nlinarith [ show ( b : ℝ ) ≥ 10 by exact_mod_cast le_trans ( le_max_right _ _ ) hb, show ( Real.log 2 : ℝ ) ≤ 1 by exact Real.log_two_lt_d9.le.trans ( by norm_num ), show ( Real.log 3 : ℝ ) ≤ 2 by exact le_trans ( Real.log_le_sub_one_of_pos ( by norm_num ) ) ( by norm_num ), show ( Real.log b : ℝ ) ≥ 1 by exact Real.le_log_iff_exp_le ( by norm_cast; linarith [ le_max_right a 10 ] ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( b : ℝ ) ≥ 10 by exact_mod_cast le_trans ( le_max_right _ _ ) hb ], pow_two_nonneg ( b - 10 : ℝ ) ] ;)

/-
n(E) < M(E).
-/
theorem n_E_lt_M (E : ℕ) (hE : E ≥ 10) : n_E E hE < M E := by
  -- Since $n_E$ is the solution to the system of congruences modulo $M$, it must be less than $M$.
  have h_n_E_lt_M : n_E E hE < Finset.prod (Finset.range (E + 2)) (fun i => modulus_map E i) := by
    apply Nat.chineseRemainderOfList_lt_prod; norm_num [ indices ];
    -- By definition of modulus_map, for any i < E + 2, modulus_map E i is either 2^E, 3, or a product of primes, all of which are positive.
    intros i hi
    simp [modulus_map];
    split_ifs <;> norm_num [ Nat.Prime.ne_zero ];
    exact Finset.prod_ne_zero_iff.mpr fun j hj => Nat.Prime.ne_zero <| Nat.prime_nth_prime _;
  convert h_n_E_lt_M using 1;
  unfold modulus_map M; simp +decide [ Finset.prod_range_succ' ] ;
  ring

/-
The “inversion step” expressed in the most natural way for your goal:

From the PNT-quality upper bound log n_E ≤ C E^2 log E, one gets
  pntRate(n_E) ≤ C' * E
eventually in E.

We state exactly that, with existential constants and eventual quantification.
-/
theorem pntRate_n_E_le_const_mul_E_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ hE : E ≥ 10,
          pntRate (n_E E hE) ≤ C * (E : ℝ)) := by
  -- Using the bound log n_E ≤ C E² log E, we get pntRate(n_E) ≤ sqrt((C E² log E) / log log n_E).
  obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ E in Filter.atTop, ∀ (hE : E ≥ 10), Real.log (n_E E hE) ≤ C * (E : ℝ)^2 * Real.log (E : ℝ) := by
    obtain ⟨ C, hC₀, hC ⟩ := log_M_bound_eventually;
    exact ⟨ C, hC₀, hC.mono fun E hE hE' => le_trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
      intro h; have := n_E_is_solution E hE'; simp_all
      have := this.2.2 0 ( by linarith ) ; norm_num [ Nat.modEq_iff_dvd ] at this;
      norm_cast at this; have := Nat.le_of_dvd ( by norm_num ) this; simp_all +decide [ Q_k ] ;
      exact absurd ( ‹∀ i : ℕ, 1 ≤ i → i ≤ E → p_kj E 0 i = 1› 1 ( by norm_num ) ( by linarith ) ) ( by exact ne_of_gt ( Nat.Prime.one_lt ( Nat.prime_nth_prime _ ) ) ) ) <| Nat.cast_le.mpr <| n_E_lt_M E hE' |> le_of_lt ) hE ⟩;
  refine' ⟨ Real.sqrt ( C * 2 ), _, _ ⟩ <;> norm_num [ Real.sqrt_lt', hC_pos ];
  -- Since $\log \log n_E \geq \log E$ for sufficiently large $E$, we can further simplify the bound.
  have h_log_log_bound : ∀ᶠ E in Filter.atTop, ∀ (hE : E ≥ 10), Real.log (Real.log (n_E E hE)) ≥ Real.log (E : ℝ) / 2 := by
    -- Since $n_E \geq 2^E$, we have $\log n_E \geq E \log 2$.
    have h_log_n_E_ge_E_log_2 : ∀ᶠ E in Filter.atTop, ∀ (hE : E ≥ 10), Real.log (n_E E hE) ≥ E * Real.log 2 := by
      -- Since $n_E \geq 2^E$, we have $\log n_E \geq \log (2^E) = E \log 2$.
      have h_log_n_E_ge_E_log_2 : ∀ᶠ E in Filter.atTop, ∀ (hE : E ≥ 10), n_E E hE ≥ 2^E := by
        filter_upwards [ Filter.eventually_gt_atTop 10 ] with E hE hE' using Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by
          intro h; have := n_E_is_solution E hE'; simp_all
          have := this.2.2 0 ( by linarith ) ; simp_all [ Nat.modEq_iff_dvd' ] ;
          unfold Q_k at this; simp_all
          exact absurd ( this 1 ( by norm_num ) ( by linarith ) ) ( Nat.Prime.ne_one ( Nat.prime_nth_prime _ ) ) ) ) ( Nat.dvd_of_mod_eq_zero ( by
          exact Nat.mod_eq_zero_of_dvd <| Nat.dvd_of_mod_eq_zero <| by have := n_E_is_solution E hE'; exact this.1; ) );
      filter_upwards [ h_log_n_E_ge_E_log_2 ] with E hE hE' using by simpa using Real.log_le_log ( by positivity ) ( Nat.cast_le.mpr ( hE hE' ) ) ;
    field_simp;
    filter_upwards [ h_log_n_E_ge_E_log_2, Filter.eventually_gt_atTop 10 ] with E hE₁ hE₂ hE₃ ; rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> try positivity;
    · refine' le_trans _ ( pow_le_pow_left₀ ( by positivity ) ( hE₁ hE₃ ) 2 );
      have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ show ( E : ℝ ) ≥ 10 by norm_cast, pow_two_nonneg ( Real.log 2 - 1 ), mul_le_mul_of_nonneg_left ( show ( E : ℝ ) ≥ 10 by norm_cast ) ( Real.log_nonneg one_le_two ) ];
    · exact sq_pos_of_pos ( lt_of_lt_of_le ( by positivity ) ( hE₁ hE₃ ) );
    · exact lt_of_lt_of_le ( by positivity ) ( hE₁ hE₃ );
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hC_bound.and h_log_log_bound );
  refine' ⟨ N + 10, fun b hb hE => Real.sqrt_le_iff.mpr ⟨ _, _ ⟩ ⟩;
  · positivity;
  · rw [ div_le_iff₀ ] <;> norm_num [ mul_pow ];
    · rw [ Real.sq_sqrt hC_pos.le ] ; nlinarith [ hN b ( by linarith ) |>.1 hE, hN b ( by linarith ) |>.2 hE, Real.log_nonneg ( show ( b : ℝ ) ≥ 1 by norm_cast; linarith ), Real.log_le_sub_one_of_pos ( show ( b : ℝ ) > 0 by norm_cast; linarith ), mul_le_mul_of_nonneg_left ( hN b ( by linarith ) |>.2 hE ) ( show ( 0 : ℝ ) ≤ b ^ 2 by positivity ) ] ;
    · exact lt_of_lt_of_le ( by exact div_pos ( Real.log_pos ( by norm_cast; linarith ) ) zero_lt_two ) ( hN b ( by linarith ) |>.2 hE )

/-
Main inequality in the “sqrt(log n / log log n) with a constant” form:

There exists an absolute constant c > 0 such that for all sufficiently large E,
for every k with 2^k ≤ n_E, we have
  Omega(n_E - 2^k) ≥ c * sqrt(log n_E / log log n_E).
-/
theorem main_inequality_eventually :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ E in atTop,
        ∀ hE : E ≥ 10,
          ∀ k, 2^k ≤ n_E E hE →
            (Omega (n_E E hE - 2^k) : ℝ) ≥ c * pntRate (n_E E hE)) := by
  simp +zetaDelta at *;
  obtain ⟨ C, hC₀, hC ⟩ := pntRate_n_E_le_const_mul_E_eventually;
  refine' ⟨ 1 / C, by positivity, _ ⟩;
  obtain ⟨ a, ha ⟩ := Filter.eventually_atTop.mp hC;
  field_simp;
  exact ⟨ a + 10, fun b hb hE k hk => le_trans ( ha b ( by linarith ) hE ) ( mul_le_mul_of_nonneg_left ( mod_cast by linarith [ show Omega ( n_E b hE - 2 ^ k ) ≥ b from by exact_mod_cast Omega_lower_bound b hE k hk ] ) hC₀.le ) ⟩
/-
The counterexample property, parameterized by the constant `c`.
-/
def is_counterexample (c : ℝ) (n : ℕ) : Prop :=
  ∀ k, 2^k ≤ n → (Omega (n - 2^k) : ℝ) ≥ c * pntRate n

/-
Infinitely many counterexamples, in the PNT-scale form:

∃ c > 0, there are infinitely many n such that
  ∀ k with 2^k ≤ n, Omega(n - 2^k) ≥ c * sqrt(log n / log log n).
-/
theorem infinitely_many_counterexamples :
    ∃ c : ℝ, 0 < c ∧ {n : ℕ | is_counterexample c n}.Infinite := by
  -- By the main_inequality_eventually theorem, there exists a constant c > 0 such that for sufficiently large E, the n_E values satisfy the counterexample property.
  obtain ⟨c, hc_pos, hc⟩ : ∃ c : ℝ, 0 < c ∧ (∀ᶠ E in Filter.atTop, ∀ hE : E ≥ 10, is_counterexample c (n_E E hE)) := by
    exact main_inequality_eventually;
  use c, hc_pos;
  rw [ Filter.eventually_atTop ] at hc;
  obtain ⟨ a, ha ⟩ := hc;
  refine Set.infinite_of_forall_exists_gt ?_;
  intro n;
  -- Choose $b$ such that $b \geq \max(a, 10, n + 1)$.
  use n_E (max a (max 10 (n + 1))) (by
  norm_num)
  generalize_proofs at *;
  refine' ⟨ ha _ ( le_max_left _ _ ) _, _ ⟩;
  -- By definition of $n_E$, we know that $n_E (max a (max 10 (n + 1)))$ is a solution to the system of congruences.
  have h_sol : n_E (max a (max 10 (n + 1))) (by
  assumption) ≡ 0 [MOD 2^(max a (max 10 (n + 1)))] ∧ n_E (max a (max 10 (n + 1))) (by
  assumption) ≡ 0 [MOD 3] ∧ ∀ k < max a (max 10 (n + 1)), n_E (max a (max 10 (n + 1))) (by
  assumption) ≡ 2^k [MOD Q_k (max a (max 10 (n + 1))) k] := by
    exact n_E_is_solution _ _
  generalize_proofs at *;
  -- Since $n_E (max a (max 10 (n + 1)))$ is a solution to the system of congruences, it must be divisible by $2^{max a (max 10 (n + 1))}$.
  have h_div : 2^(max a (max 10 (n + 1))) ∣ n_E (max a (max 10 (n + 1))) (by
  (expose_names; exact pf)) := by
    exact Nat.dvd_of_mod_eq_zero h_sol.1
  generalize_proofs at *;
  refine' lt_of_lt_of_le _ ( Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) h_div );
  · exact lt_of_lt_of_le ( Nat.lt_of_succ_le ( le_max_right _ _ ) ) ( le_max_right _ _ ) |> lt_of_lt_of_le <| Nat.le_of_lt <| Nat.recOn ( Max.max a ( Max.max 10 ( n + 1 ) ) ) ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ;
  · intro H; specialize ha ( Max.max a ( Max.max 10 ( n + 1 ) ) ) ( by aesop ) ( by aesop ) ; simp_all +decide [ Nat.ModEq ] ;
    specialize h_sol 0 ; norm_num at h_sol;
    unfold Q_k at h_sol; simp_all
    exact absurd ( h_sol 1 ( by norm_num ) ( by norm_num ) ) ( Nat.Prime.ne_one ( Nat.prime_nth_prime _ ) )

#print axioms infinitely_many_counterexamples
-- 'infinitely_many_counterexamples' depends on axioms: [nth_prime_asymp, propext, Classical.choice, Quot.sound]
