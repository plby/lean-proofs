/-

This is a Lean formalization of a solution to Erdős Problem 648.
https://www.erdosproblems.com/forum/thread/648

The original proof was found by: Stijn Cambie

[Ca25b] S. Cambie, On Erdős problem #648. arXiv:2503.22691 (2025).


Cambie's paper was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized the main result of the paper "On Erdős problem # 648" by Stijn Cambie.
This is achieved by proving the upper bound `g_upper_bound_asymptotic` and the lower bound `g_lower_bound_asymptotic` separately.
The bounds use the PNT.
-/

import Mathlib

open Asymptotics Filter Nat Real

/-
P(n) is the largest prime factor of n, or 1 if n has no prime factors.
-/
def P (n : ℕ) : ℕ := (n.primeFactors.max).getD 1

/-
g(n) is the length of the longest sequence of integers bounded by n for which the smaller integers have a larger largest prime divisor.
-/
def is_valid_seq (n : ℕ) (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ (∀ m ∈ l, m ∈ Set.Ioc 0 n) ∧ (l.map P).IsChain (· > ·)

noncomputable def g (n : ℕ) : ℕ :=
  sSup { k | ∃ l, is_valid_seq n l ∧ l.length = k }

/-
Define q(n) = n / P(n).
-/
def q (n : ℕ) : ℕ := n / P n

/-
P(n) > 0 for all n.
-/
lemma P_pos {n : ℕ} : 0 < P n := by
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ P ];
  rcases x : Finset.max ( n + 2 |> Nat.primeFactors ) with ( _ | _ | p ) <;> simp_all +arith +decide
  exact absurd ( Finset.mem_of_max x ) ( by norm_num )

/-
q(n) > 0 for n != 0.
-/
lemma q_pos {n : ℕ} (hn : n ≠ 0) : 0 < q n := by
  -- Since $n$ is not zero, $q(n)$ is well-defined and positive because it is the division of a positive integer by a positive integer.
  have hq_pos : 0 < n / P n := by
    have h_num_pos : 0 < n := by
      grind
    have h_denom_pos : 0 < P n := by
      exact P_pos
    refine' Nat.div_pos _ h_denom_pos;
    convert Nat.le_of_dvd h_num_pos _;
    unfold P;
    cases h : n.primeFactors.max <;> simp_all +decide
    exact Nat.dvd_of_mem_primeFactors <| Finset.mem_of_max h;
  exact hq_pos

/-
P(n) divides n.
-/
lemma P_dvd_n {n : ℕ} : P n ∣ n := by
  -- If $n$ has no prime factors, then $P(n) = 1$, which divides any $n$.
  by_cases h_prime_factors : n.primeFactors = ∅;
  · unfold P; aesop;
  · -- Since $n$ has prime factors, the maximum prime factor of $n$ is indeed a prime factor of $n$.
    have h_max_prime_factor : n.primeFactors.max.getD 1 ∈ n.primeFactors := by
      have h_max_prime_factor : ∃ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≤ p := by
        exact ⟨ Finset.max' _ <| Finset.nonempty_of_ne_empty h_prime_factors, Finset.max'_mem _ _, fun q hq => Finset.le_max' _ _ hq ⟩;
      obtain ⟨p, hp_mem, hp_max⟩ : ∃ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≤ p := h_max_prime_factor;
      have h_max_prime_factor : Finset.max n.primeFactors = some p := by
        exact le_antisymm ( Finset.sup_le fun q hq => WithBot.coe_le_coe.mpr ( hp_max q hq ) ) ( Finset.le_sup ( f := WithBot.some ) hp_mem );
      grind;
    exact Nat.dvd_of_mem_primeFactors h_max_prime_factor

/-
n = q(n) * P(n) for n != 0.
-/
lemma n_eq_q_mul_P {n : ℕ} : n = q n * P n := by
  exact Eq.symm ( Nat.div_mul_cancel ( P_dvd_n ) )

/-
If a < b and P(b) < P(a), then q(a) < q(b).
-/
lemma q_lt_q_of_lt_of_P_gt {a b : ℕ} (ha : 0 < a) (h_lt : a < b) (h_P : P b < P a) : q a < q b := by
  -- By definition of $q$, we have $q(a) = a / P(a)$ and $q(b) = b / P(b)$.
  have h_q_eq : q a = a / P a ∧ q b = b / P b := by
    exact ⟨ rfl, rfl ⟩
  rw [h_q_eq.left, h_q_eq.right] at *; (
  exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_mul_cancel ( P_dvd_n : P a ∣ a ), Nat.div_mul_cancel ( P_dvd_n : P b ∣ b ) ] ;);

/-
If l is a valid sequence, then q(l) is strictly increasing.
-/
lemma q_strict_mono {n : ℕ} {l : List ℕ} (h : is_valid_seq n l) : (l.map q).IsChain (· < ·) := by
  refine' List.isChain_iff_get.mpr _;
  intro i hi; have := h.1; simp_all +decide
  have := h.2.2; simp_all +decide
  have := List.isChain_iff_get.mp this;
  convert q_lt_q_of_lt_of_P_gt _ _ _ using 1;
  · exact h.2.1 _ ( List.getElem_mem _ ) |>.1;
  · have := List.isChain_iff_get.mp ‹List.IsChain ( fun x1 x2 => x1 < x2 ) l›; aesop;
  · grind

/-
If l is a valid sequence, then P(l) has no duplicates.
-/
lemma P_nodup {n : ℕ} {l : List ℕ} (h : is_valid_seq n l) : (l.map P).Nodup := by
  -- Since $P(l)$ is strictly decreasing, it must have no duplicates.
  have h_P_decreasing : (l.map P).IsChain (· > ·) := by
    exact h.2.2;
  exact List.isChain_iff_pairwise.mp h_P_decreasing |> fun h => h.nodup

/-
The length of l is at most the sum of the lengths of the filtered lists.
-/
lemma length_le_card_q_union_card_P {n : ℕ} {l : List ℕ} (h : is_valid_seq n l) (hn : 2 ≤ n) :
  l.length ≤ (l.filter (fun m => (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n))).length +
             (l.filter (fun m => (P m : ℝ) ≤ Real.sqrt (n * Real.log n / 2))).length := by
               induction' l with m l ih <;> simp +arith +decide [ * ] at *;
               have := h.2.1 m; simp_all +decide [ is_valid_seq ] ;
               by_cases h : ( P m : ℝ ) ≤ Real.sqrt n * Real.sqrt ( Real.log n ) / Real.sqrt 2 <;> by_cases h' : ( q m : ℝ ) ≤ Real.sqrt 2 * Real.sqrt n / Real.sqrt ( Real.log n ) <;> simp_all +decide
               · linarith [ ih ( by exact List.isChain_cons'.mp ( by tauto ) |>.2 ) ( by exact List.isChain_cons'.mp ( by tauto ) |>.2 ) ];
               · convert Nat.succ_le_succ ( ih _ _ ) using 1;
                 · exact
                   Nat.succ_add
                     (List.filter (fun m => decide (↑(P m) ≤ √↑n * √(Real.log ↑n) / √2)) l).length
                     (List.filter (fun m => decide (↑(q m) ≤ √2 * √↑n / √(Real.log ↑n))) l).length;
                 · exact List.isChain_cons'.mp ( by tauto ) |>.2;
                 · exact List.isChain_cons'.mp ( by tauto ) |>.2;
               · specialize ih ( by
                   exact List.isChain_cons'.mp ( by tauto ) |>.2 ) ( by
                   exact List.isChain_cons'.mp ( by tauto ) |>.2 ) ;
                 linarith;
               · contrapose! h';
                 -- Since $m = q m * P m$ and $m \leq n$, we have $q m \leq n / P m$.
                 have h_q_le_n_div_P : (q m : ℝ) ≤ n / P m := by
                   rw [ le_div_iff₀ ] <;> norm_cast;
                   · rw [ ← n_eq_q_mul_P ] ; linarith [ ‹List.IsChain ( fun x1 x2 => x1 < x2 ) ( m :: l ) ∧ ( ( 0 < m ∧ m ≤ n ) ∧ ∀ a ∈ l, 0 < a ∧ a ≤ n ) ∧ List.IsChain ( fun x1 x2 => x2 < x1 ) ( P m :: List.map P l ) ›.2.1.1.2 ];
                   · exact P_pos;
                 refine le_trans h_q_le_n_div_P ?_;
                 rw [ div_le_div_iff₀ ];
                 · rw [ div_lt_iff₀ ] at h <;> first | positivity | nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg n, Real.sqrt_nonneg ( Real.log n ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ ( n : ℝ ) by positivity ), Real.mul_self_sqrt ( show 0 ≤ Real.log n by exact Real.log_nonneg ( by norm_cast; linarith ) ) ] ;
                 · exact lt_of_le_of_lt ( by positivity ) h;
                 · exact Real.sqrt_pos.mpr ( Real.log_pos ( by norm_cast ) )

/-
The number of elements in l with q(m) <= sqrt(2n/log n) is at most floor(sqrt(2n/log n)).
-/
lemma card_q_le {n : ℕ} {l : List ℕ} (h : is_valid_seq n l) :
  (l.filter (fun m => (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n))).length ≤ Nat.floor (Real.sqrt (2 * n / Real.log n)) := by
    -- Since these are the only elements in the list with $q(m) \leq \sqrt{2n / \log n}$, the length of this list is at most the number of integers in this range.
    have h_card_q : (l.filter (fun m => (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n))).toFinset.card ≤ Nat.floor (Real.sqrt (2 * n / Real.log n)) := by
      -- Since $q(m)$ is a natural number and $q(m) \leq \sqrt{2n / \log n}$, the values of $q(m)$ are bounded above by $\sqrt{2n / \log n}$.
      have h_q_le : ∀ m ∈ l, (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n) → q m ≤ Nat.floor (Real.sqrt (2 * n / Real.log n)) := by
        exact fun m hm h => Nat.le_floor <| mod_cast h;
      -- Since $q(m)$ is a natural number and $q(m) \leq \sqrt{2n / \log n}$, the values of $q(m)$ are bounded above by $\sqrt{2n / \log n}$. Therefore, the number of such elements is at most the number of integers in this range.
      have h_q_le_card : (l.filter (fun m => (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n))).toFinset.card ≤ Finset.card (Finset.image (fun m => q m) (l.filter (fun m => (q m : ℝ) ≤ Real.sqrt (2 * n / Real.log n))).toFinset) := by
        rw [ Finset.card_image_of_injOn ];
        intros m hm m' hm' h_eq;
        have h_q_eq : (l.map q).IsChain (· < ·) := by
          exact q_strict_mono h;
        have h_q_eq : List.Nodup (List.map q l) := by
          exact List.isChain_iff_pairwise.mp h_q_eq |> fun h => h.nodup;
        rw [ List.nodup_map_iff_inj_on ] at h_q_eq;
        · exact h_q_eq m ( List.mem_toFinset.mp hm |> fun x => List.mem_of_mem_filter x ) m' ( List.mem_toFinset.mp hm' |> fun x => List.mem_of_mem_filter x ) h_eq;
        · exact List.Nodup.of_map q h_q_eq;
      refine le_trans h_q_le_card ?_;
      exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| q_pos <| by
        have := h.2.1 x; aesop;, h_q_le x ( by
        aesop ) <| by
        aesop ⟩ ) ( by simp );
    rwa [ List.toFinset_card_of_nodup ] at h_card_q;
    exact List.Nodup.filter _ ( List.isChain_iff_pairwise.mp h.1 |> fun h => h.nodup )

/-
If n is not 1 and not 0, then P(n) is prime.
-/
lemma P_prime_of_ne_one {n : ℕ} (hn : n ≠ 1) (hn0 : n ≠ 0) : Nat.Prime (P n) := by
  unfold P;
  -- Since n is not 1 and not 0, it must have at least one prime factor. The maximum of the prime factors of n is the largest prime that divides n. So, that maximum must be a prime number because it's a prime factor of n. Therefore, the maximum of the prime factors of n is indeed a prime.
  have h_prime_factor : ∃ p, p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q ≤ p := by
    exact ⟨ Finset.max' _ ⟨ Nat.minFac n, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime hn, Nat.minFac_dvd n, hn0 ⟩ ⟩, Finset.max'_mem _ _, fun q hq => Finset.le_max' _ _ hq ⟩;
  -- Obtain such a p from h_prime_factor.
  obtain ⟨p, hp_prime, hp_max⟩ := h_prime_factor;
  have h_max_prime : Finset.max (Nat.primeFactors n) = some p := by
    exact le_antisymm ( Finset.sup_le fun q hq => WithBot.coe_le_coe.mpr ( hp_max q hq ) ) ( Finset.le_sup ( f := WithBot.some ) hp_prime );
  aesop

/-
The number of elements in l with P(m) <= sqrt(n log n / 2) is at most pi(floor(sqrt(n log n / 2))) + 1.
-/
lemma card_P_le_plus_one {n : ℕ} {l : List ℕ} (h : is_valid_seq n l) :
  (l.filter (fun m => (P m : ℝ) ≤ Real.sqrt (n * Real.log n / 2))).length ≤ Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) + 1 := by
    -- Apply the lemma that states the length of a list of distinct primes ≤ B is at most pi(B).
    have h_card_P : (l.filter (fun m => (P m : ℝ) ≤ Real.sqrt (n * Real.log n / 2))).length ≤ Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) + 1 := by
      have h_distinct_primes : (l.filter (fun m => (P m : ℝ) ≤ Real.sqrt (n * Real.log n / 2))).map P |>.Nodup := by
        have := P_nodup h;
        grind
      have h_card_P : (List.map P (l.filter (fun m => (P m : ℝ) ≤ Real.sqrt (n * Real.log n / 2)))).toFinset ⊆ Finset.image (fun p => p) (Finset.filter Nat.Prime (Finset.Icc 1 (Nat.floor (Real.sqrt (n * Real.log n / 2))))) ∪ {1} := by
        intro p hp;
        norm_num +zetaDelta at *;
        rcases hp with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; by_cases ha₃ : a = 1 <;> by_cases ha₄ : a = 0 <;> simp_all +decide [ P_prime_of_ne_one ] ;
        · exact Or.inl <| by unfold P; aesop;
        · exact absurd ( h.2.1 0 ha₁ ) ( by norm_num );
        · exact Or.inr ⟨ Nat.pos_of_dvd_of_pos ( P_dvd_n ) ( Nat.pos_of_ne_zero ha₄ ), Nat.le_floor ha₂ ⟩;
      have := Finset.card_mono h_card_P; simp_all +decide [ Nat.primeCounting ] ;
      convert this using 1;
      · rw [ List.toFinset_card_of_nodup ];
        · norm_num [ le_div_iff₀, Real.sqrt_nonneg ];
        · convert h_distinct_primes using 1;
      · rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        congr 2 with ( _ | x ) <;> simp +arith +decide;
        exact fun _ => ⟨ fun h => Nat.succ_le_of_lt h, fun h => Nat.lt_of_succ_le h ⟩;
    exact h_card_P

/-
g(n) is bounded by the sum of the bounds for q and P.
-/
lemma g_le_card_sum {n : ℕ} (hn : 2 ≤ n) :
  g n ≤ Nat.floor (Real.sqrt (2 * n / Real.log n)) + Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) + 1 := by
    refine' csSup_le _ _;
    · -- The empty list is a valid sequence, so the set is nonempty.
      use 0
      simp [is_valid_seq];
    · rintro k ⟨ l, hl, rfl ⟩;
      convert length_le_card_q_union_card_P hl hn |> le_trans <| Nat.add_le_add ( card_q_le hl ) ( card_P_le_plus_one hl ) using 1

/-
log(primorial n) is the sum of log p for primes p <= n.
-/
lemma log_primorial_eq_sum_log {n : ℕ} : Real.log (primorial n) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Real.log p := by
  -- By definition of primorial, we can write it as the product of primes up to n.
  have h_primorial : primorial n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p := by
    induction n <;> simp_all +decide [ primorial ];
  rw [ h_primorial, Nat.cast_prod, Real.log_prod ] ; aesop

/-
The sum of log p for p <= n is at most n * log 4.
-/
lemma theta_le_n_log_4 {n : ℕ} : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Real.log p) ≤ n * Real.log 4 := by
  rw [← log_primorial_eq_sum_log]
  have h : (primorial n : ℝ) ≤ (4 ^ n : ℝ) := by
    norm_cast
    exact primorial_le_4_pow n
  have h_pos : 0 < (primorial n : ℝ) := by
    norm_cast
    exact primorial_pos n
  rw [← Real.log_pow]
  refine Real.log_le_log h_pos h

/-
The sum of log p for p <= x is at least (pi(x) - pi(sqrt(x))) * log(sqrt(x)).
-/
lemma sum_log_primes_ge_pi_sub_pi_sqrt_mul_log_sqrt {x : ℕ} (hx : 2 ≤ x) :
  (∑ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), Real.log p) ≥ (Nat.primeCounting x - Nat.primeCounting (Nat.sqrt x)) * Real.log (Real.sqrt x) := by
    -- We'll use that $\sum_{p \leq x} \log p \geq \sum_{\sqrt{x} < p \leq x} \log p$.
    have h_sum_log_ge : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.sqrt x + 1) x), Real.log p ≥ ((Nat.primeCounting x) - (Nat.primeCounting (Nat.sqrt x))) * Real.log (Real.sqrt x) := by
      have h_sum_log_ge : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.sqrt x + 1) x), Real.log p) ≥ (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (Nat.sqrt x + 1) x), Real.log (Real.sqrt x)) := by
        exact Finset.sum_le_sum fun p hp => Real.log_le_log ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| pos_of_gt hx ) <| Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hp |>.1, Nat.lt_succ_sqrt x ] ⟩;
      simp_all +decide [ Nat.primeCounting ];
      convert h_sum_log_ge using 2 ; erw [ Nat.primeCounting', Nat.count_eq_card_filter_range ] ; erw [ Nat.count_eq_card_filter_range ] ; ring_nf;
      norm_num [ add_comm, Finset.subset_iff ];
      rw [ show ( Finset.filter Nat.Prime ( Finset.Icc ( x.sqrt + 1 ) x ) ) = Finset.filter Nat.Prime ( Finset.range ( x + 1 ) ) \ Finset.filter Nat.Prime ( Finset.range ( x.sqrt + 1 ) ) from ?_, Finset.card_sdiff ];
      · rw [ Nat.cast_sub ];
        · rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ <| Nat.sqrt_le_self _ ) ];
          rfl;
        · exact Finset.card_mono fun p hp => by aesop;
      · -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro p
        simp [Finset.mem_sdiff, Finset.mem_filter];
        grind
    refine le_trans h_sum_log_ge ?_;
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop;
    exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ), Finset.mem_filter.mp hp |>.2 ⟩

/-
pi(x) <= 2 * theta(x) / log(x) + sqrt(x).
-/
lemma pi_le_theta_div_log_plus_sqrt {x : ℕ} (hx : 2 ≤ x) :
  (Nat.primeCounting x : ℝ) ≤ 2 * (∑ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), Real.log p) / Real.log x + Real.sqrt x := by
    -- Applying the inequality $\sum_{p \leq x} \log p \geq (\pi(x) - \pi(\sqrt{x})) \log(\sqrt{x})$.
    have h_ineq : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), Real.log p) ≥ (Nat.primeCounting x - Nat.primeCounting (Nat.sqrt x)) * Real.log (Real.sqrt x) := by
      convert sum_log_primes_ge_pi_sub_pi_sqrt_mul_log_sqrt hx using 1;
    -- Applying the inequality $\pi(\sqrt{x}) \leq \sqrt{x}$.
    have h_pi_sqrt : (Nat.primeCounting (Nat.sqrt x) : ℝ) ≤ Real.sqrt x := by
      rw [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      refine' le_trans _ ( Real.sqrt_le_sqrt <| Nat.cast_le.mpr <| Nat.sqrt_le' x );
      norm_num [ Real.sqrt_sq ( Nat.cast_nonneg _ ) ];
      exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range ( x.sqrt + 1 ) ) ⊆ Finset.Ico 2 ( x.sqrt + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩ ) ) ( by simp +arith +decide );
    rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] at *;
    rw [ div_add', le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( x : ℝ ) > 1 by norm_cast ), Real.log_le_sub_one_of_pos ( show ( x : ℝ ) > 0 by positivity ) ]

/-
pi(x) <= 2 * x * log 4 / log x + sqrt(x).
-/
lemma pi_le_x_log_4_div_log_plus_sqrt {x : ℕ} (hx : 2 ≤ x) :
  (Nat.primeCounting x : ℝ) ≤ 2 * x * Real.log 4 / Real.log x + Real.sqrt x := by
    refine le_trans ( pi_le_theta_div_log_plus_sqrt hx ) ?_;
    -- Substitute the upper bound of the sum of log p for primes up to x.
    have h_subst : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), Real.log p) ≤ x * Real.log 4 := by
      convert theta_le_n_log_4 using 1;
    exact add_le_add_right ( by rw [ div_le_div_iff_of_pos_right ( Real.log_pos ( by norm_cast ) ) ] ; linarith ) _

/-
term1 is O(sqrt(n / log n)).
-/
noncomputable def term1 (n : ℕ) : ℝ := Nat.floor (Real.sqrt (2 * (n : ℝ) / Real.log (n : ℝ)))

lemma term1_isBigO : term1 =O[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
  refine' Asymptotics.isBigO_iff.mpr _;
  use 2;
  norm_num [ term1 ];
  refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; ring_nf;
  nlinarith [ Nat.floor_le ( show 0 ≤ Real.sqrt 2 * Real.sqrt n * ( Real.sqrt ( Real.log n ) ) ⁻¹ by positivity ), show ( Real.sqrt 2 : ℝ ) ≤ 2 by norm_num [ Real.sqrt_le_iff ], show ( Real.sqrt n : ℝ ) * ( Real.sqrt ( Real.log n ) ) ⁻¹ ≥ 0 by positivity ]

/-
primeCounting(n) is O(n / log n).
-/
lemma primeCounting_isBigO : (fun n => (Nat.primeCounting n : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.log n) := by
  -- Apply the bound from `pi_le_x_log_4_div_log_plus_sqrt`.
  have h_pi_bound : ∀ x : ℕ, 2 ≤ x → (Nat.primeCounting x : ℝ) ≤ 2 * x * Real.log 4 / Real.log x + Real.sqrt x := by
    exact fun x a => pi_le_x_log_4_div_log_plus_sqrt a;
  -- The second term $\sqrt{x}$ is $o(x / \log x)$ because $\sqrt{x} \cdot \log x / x = \log x / \sqrt{x} \to 0$.
  have h_sqrt : (fun x : ℕ => Real.sqrt x) =o[atTop] (fun x : ℕ => x / Real.log x) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
    · -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun x : ℕ => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) by
        convert h_simplify using 2 ; norm_num [ div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm, Real.sqrt_div_self ];
        rw [ ← Real.sqrt_div_self ] ; ring;
      -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
      suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => 2 * Real.log y / y) Filter.atTop (nhds 0) by
        have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun x : ℕ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by simpa using Nat.ceil_le.mp hn ⟩ );
        exact this.congr fun x => by rw [ Function.comp_apply ] ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring;
      -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
      suffices h_log_sqrt_z : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_sqrt_z.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
      norm_num +zetaDelta at *;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
    · exact ⟨ 2, by rintro b hb ( rfl | rfl | hb ) <;> norm_cast at hb ⟩;
  -- The first term $2 * x * \log 4 / \log x$ is $O(x / \log x)$ because $\log 4$ is a constant.
  have h_first_term : (fun x : ℕ => 2 * x * Real.log 4 / Real.log x) =O[atTop] (fun x : ℕ => x / Real.log x) := by
    norm_num [ Asymptotics.isBigO_iff ];
    exact ⟨ 2 * |Real.log 4|, 2, fun n hn => by ring_nf; norm_num ⟩;
  refine' Asymptotics.IsBigO.trans _ ( h_first_term.add h_sqrt.isBigO );
  rw [ Asymptotics.isBigO_iff ];
  exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 2, fun x hx => by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( add_nonneg ( div_nonneg ( by positivity ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( Real.sqrt_nonneg _ ) ) ] ; linarith [ h_pi_bound x hx ] ⟩ ⟩

/-
xn tends to infinity.
-/
noncomputable def xn_real (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2)

noncomputable def xn (n : ℕ) : ℕ := Nat.floor (xn_real n)

lemma xn_tendsto_atTop : Filter.Tendsto xn Filter.atTop Filter.atTop := by
  -- We'll use that $xn_real$ tends to infinity as $n$ tends to infinity.
  have h_xn_real_inf : Filter.Tendsto (fun n => Real.sqrt (n * Real.log n / 2)) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_atTop.2 fun x => ⟨ Real.exp ( x ^ 2 * 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Real.add_one_le_exp ( x ^ 2 * 2 ), Real.log_exp ( x ^ 2 * 2 ), Real.log_le_log ( by positivity ) hn ] ⟩;
  rw [ Filter.tendsto_atTop_atTop ] at *;
  exact fun b => by obtain ⟨ i, hi ⟩ := h_xn_real_inf b; exact ⟨ ⌈i⌉₊, fun n hn => Nat.le_floor <| hi n <| Nat.le_of_ceil_le hn ⟩ ;

/-
term2 is O(xn / log xn).
-/
noncomputable def term2 (n : ℕ) : ℝ := Nat.primeCounting (xn n)

lemma term2_isBigO_xn : term2 =O[atTop] (fun n => (xn n : ℝ) / Real.log (xn n)) := by
  exact primeCounting_isBigO.comp_tendsto xn_tendsto_atTop

/-
xn / log xn is O(sqrt(n / log n)).
-/
lemma xn_div_log_xn_isBigO : (fun n => (xn n : ℝ) / Real.log (xn n)) =O[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
  -- We'll use the fact that $xn n \sim \sqrt{\frac{n \log n}{2}}$ and $\log(xn n) \sim \frac{1}{2} \log n$.
  have h_xn_log : Filter.Tendsto (fun n => (xn n : ℝ) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2)) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun n => Real.log (xn n) / (1 / 2 * Real.log (n : ℝ))) Filter.atTop (nhds 1) := by
    have h_xn_log : Filter.Tendsto (fun n => (xn n : ℝ) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2)) Filter.atTop (nhds 1) := by
      -- We'll use the fact that $xn n \sim \sqrt{\frac{n \log n}{2}}$.
      have h_xn_sqrt : Filter.Tendsto (fun n => (Nat.floor (Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2)) : ℝ) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2)) Filter.atTop (nhds 1) := by
        have : Filter.Tendsto (fun x : ℝ => (Nat.floor x : ℝ) / x) Filter.atTop (nhds 1) := by
          rw [ Metric.tendsto_nhds ];
          intro ε hε; filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( ε⁻¹ + 1 ) ] with x hx₁ hx₂ using abs_lt.mpr ⟨ by nlinarith [ Nat.floor_le ( show 0 ≤ x by linarith ), Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) ( show x ≠ 0 by linarith ) ], by nlinarith [ Nat.floor_le ( show 0 ≤ x by linarith ), Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) ( show x ≠ 0 by linarith ) ] ⟩ ;
        refine' this.comp _;
        exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 * 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Real.add_one_le_exp ( x ^ 2 * 2 ), Real.log_exp ( x ^ 2 * 2 ), Real.log_le_log ( by positivity ) hn ] ⟩;
      exact h_xn_sqrt.comp tendsto_natCast_atTop_atTop;
    have h_log_xn : Filter.Tendsto (fun n => Real.log (xn n) / (1 / 2 * Real.log (n : ℝ))) Filter.atTop (nhds 1) := by
      -- We'll use the fact that $\log(xn n) \sim \frac{1}{2} \log n$.
      have h_log_xn : Filter.Tendsto (fun n => Real.log (xn n) / (Real.log (n : ℝ)) - 1 / 2) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\log(xn n) = \log(\sqrt{n \log n / 2}) + \log(1 + o(1))$.
        have h_log_xn : Filter.Tendsto (fun n => Real.log (xn n) - (1 / 2) * Real.log (n * Real.log n / 2)) Filter.atTop (nhds 0) := by
          have h_log_xn : Filter.Tendsto (fun n => Real.log (xn n / Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 2))) Filter.atTop (nhds 0) := by
            simpa using Filter.Tendsto.log h_xn_log;
          refine h_log_xn.congr' ?_;
          filter_upwards [ h_xn_log.eventually ( lt_mem_nhds one_pos ) ] with n hn using by rw [ Real.log_div ( by aesop ) ( by aesop ), Real.log_sqrt ( by positivity ) ] ; ring;
        -- We'll use the fact that $\log(n \log n / 2) = \log n + \log \log n - \log 2$.
        have h_log_split : Filter.Tendsto (fun n => (1 / 2) * (Real.log n + Real.log (Real.log n) - Real.log 2) / Real.log n - 1 / 2) Filter.atTop (nhds 0) := by
          -- We'll use the fact that $\frac{\log \log n}{\log n} \to 0$ as $n \to \infty$.
          have h_log_log : Filter.Tendsto (fun n => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
            -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
            suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
            suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          ring_nf;
          exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.add ( Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) tendsto_const_nhds ) ) ( h_log_log.mul_const _ ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) tendsto_const_nhds ) ) ( by norm_num );
        have h_log_split : Filter.Tendsto (fun n => (1 / 2) * Real.log (n * Real.log n / 2) / Real.log n - 1 / 2) Filter.atTop (nhds 0) := by
          refine h_log_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ Real.log_div ( by exact ne_of_gt ( mul_pos ( by positivity ) ( Real.log_pos hn ) ) ) ( by positivity ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.log_pos hn ) ) ] );
        have := h_log_xn.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        convert this.add ( h_log_split.comp tendsto_natCast_atTop_atTop ) using 2 <;> norm_num ; ring;
      convert h_log_xn.const_mul 2 |> Filter.Tendsto.add_const 1 using 2 <;> ring
    exact ⟨h_xn_log, h_log_xn⟩;
  have h_xn_log : Filter.Tendsto (fun n => (xn n : ℝ) / Real.log (xn n) / Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) Filter.atTop (nhds (Real.sqrt 2)) := by
    convert h_xn_log.1.mul ( h_xn_log.2.inv₀ one_ne_zero ) |> Filter.Tendsto.mul_const ( Real.sqrt 2 ) using 2 <;> norm_num ; ring_nf;
    grind;
  rw [ Asymptotics.isBigO_iff ];
  have := h_xn_log.bddAbove_range;
  obtain ⟨ c, hc ⟩ := this;
  exact ⟨ c, Filter.eventually_atTop.mpr ⟨ 2, fun n hn => by rw [ Real.norm_of_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Real.log_natCast_nonneg _ ) ), Real.norm_of_nonneg ( Real.sqrt_nonneg _ ) ] ; have := hc ⟨ n, rfl ⟩ ; rw [ div_le_iff₀ ( Real.sqrt_pos.mpr <| div_pos ( Nat.cast_pos.mpr <| by linarith ) <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ] at *; linarith ⟩ ⟩

/-
term2 is O(sqrt(n / log n)).
-/
lemma term2_isBigO : term2 =O[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
  exact term2_isBigO_xn.trans xn_div_log_xn_isBigO

/-
The upper bound function is O(sqrt(n / log n)).
-/
noncomputable def upper_bound_func (n : ℕ) : ℝ := term1 n + term2 n + 1

theorem upper_bound_asymptotic :
  upper_bound_func =O[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
    refine' Asymptotics.IsBigO.add _ _;
    · exact Asymptotics.IsBigO.add ( term1_isBigO ) ( term2_isBigO );
    · refine' Asymptotics.isBigO_iff.mpr _;
      use 1;
      filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( Real.sqrt_nonneg _ ), Real.norm_of_nonneg ( by positivity ) ] ; exact one_le_mul_of_one_le_of_one_le ( by norm_num ) ( Real.le_sqrt_of_sq_le <| by rw [ le_div_iff₀ <| Real.log_pos <| by norm_cast; linarith ] ; nlinarith [ Real.log_le_sub_one_of_pos <| show 0 < ( x : ℝ ) by positivity, show ( x : ℝ ) ≥ 3 by norm_cast ] ) ;

/-
Definition of the sequence construction. next_a(prev_a, p) is the smallest multiple of p strictly greater than prev_a. construct_seq constructs the sequence recursively.
-/
def next_a (prev_a : ℕ) (p : ℕ) : ℕ := (prev_a / p + 1) * p

def construct_seq_aux : List ℕ → ℕ → List ℕ
| [], _ => []
| (p :: ps), prev_a => let a := next_a prev_a p; a :: construct_seq_aux ps a

def construct_seq (primes : List ℕ) : List ℕ := construct_seq_aux primes 0

/-
The length of the constructed sequence is equal to the number of primes used to construct it.
-/
lemma construct_seq_length (primes : List ℕ) : (construct_seq primes).length = primes.length := by
  have h_len : ∀ (primes : List ℕ) (prev_a : ℕ), (construct_seq_aux primes prev_a).length = primes.length := by
    intros primes prev_a
    induction' primes with p ps ih generalizing prev_a
    · simp [construct_seq_aux]
    · simp [construct_seq_aux]
      exact ih _;
  exact h_len _ _

/-
`next_a` produces a value strictly greater than `prev_a`.
-/
lemma next_a_gt (prev_a p : ℕ) (hp : 0 < p) : prev_a < next_a prev_a p := by
  exact show prev_a < ( prev_a / p + 1 ) * p from by nlinarith [ Nat.div_add_mod prev_a p, Nat.mod_lt prev_a hp ] ;

/-
The constructed sequence is strictly increasing.
-/
lemma construct_seq_increasing (primes : List ℕ) (h_primes_pos : ∀ p ∈ primes, 0 < p) :
  (construct_seq primes).IsChain (· < ·) := by
    -- By induction on the list of primes, we can show that the constructed sequence is strictly increasing.
    have h_ind : ∀ (primes : List ℕ) (prev_a : ℕ), (∀ p ∈ primes, 0 < p) → List.IsChain (· < ·) (construct_seq_aux primes prev_a) := by
      intros primes prev_a h_primes_pos; induction' primes with p primes ih generalizing prev_a <;> simp_all +decide
      · exact List.isChain_nil;
      · -- By definition of `construct_seq_aux`, we have `construct_seq_aux (p :: primes) prev_a = next_a prev_a p :: construct_seq_aux primes (next_a prev_a p)`.
        have h_def : construct_seq_aux (p :: primes) prev_a = next_a prev_a p :: construct_seq_aux primes (next_a prev_a p) := by
          rfl;
        rw [ List.isChain_iff_get ] at *;
        intro i hi; rcases i with ( _ | i ) <;> simp_all +decide
        · rcases primes <;> simp_all +decide [ List.isChain_iff_get ];
          · exact (StrictAnti.lt_iff_gt fun ⦃a b⦄ a => hi).mp hi;
          · exact next_a_gt _ _ h_primes_pos.2.1;
        · have := ih ( next_a prev_a p ) ; rw [ List.isChain_iff_get ] at this; aesop;
    exact h_ind _ _ h_primes_pos

/-
`next_a` produces a value at most `prev_a + p`.
-/
lemma next_a_le_add (prev_a p : ℕ) : next_a prev_a p ≤ prev_a + p := by
  exact Nat.le_of_lt_succ <| by nlinarith! [ Nat.div_mul_le_self prev_a p, show next_a prev_a p = ( prev_a / p + 1 ) * p from rfl ] ;

/-
Every element in the constructed sequence is bounded by the sum of the primes plus the initial value.
-/
lemma construct_seq_bound_aux (primes : List ℕ) (prev_a : ℕ) (h_primes_pos : ∀ p ∈ primes, 0 < p) :
  ∀ a ∈ construct_seq_aux primes prev_a, a ≤ prev_a + primes.sum := by
    -- We proceed by induction on the list `primes`.
    induction' primes with p primes ih generalizing prev_a;
    · tauto;
    · simp +zetaDelta at *;
      intro a ha;
      -- By definition of `construct_seq_aux`, we know that `a` is either `next_a prev_a p` or an element from `construct_seq_aux primes (next_a prev_a p)`.
      by_cases ha_case : a = next_a prev_a p;
      · exact ha_case.symm ▸ by linarith [ next_a_le_add prev_a p, Nat.zero_le ( List.sum primes ) ] ;
      · exact le_trans ( ih ( next_a prev_a p ) h_primes_pos.2 a <| by unfold construct_seq_aux at ha; aesop ) <| by linarith [ next_a_le_add prev_a p ] ;

/-
Every element in the constructed sequence is bounded by the sum of the primes.
-/
lemma construct_seq_bound (primes : List ℕ) (h_primes_pos : ∀ p ∈ primes, 0 < p) :
  ∀ a ∈ construct_seq primes, a ≤ primes.sum := by
    have := @construct_seq_bound_aux primes 0 h_primes_pos;
    grind

/-
All elements in the constructed sequence are positive.
-/
lemma construct_seq_pos (primes : List ℕ) (h_primes_pos : ∀ p ∈ primes, 0 < p) :
  ∀ a ∈ construct_seq primes, 0 < a := by
    -- By induction on the list of primes, we can show that every element in the constructed sequence is positive.
    have h_ind : ∀ (primes : List ℕ) (prev_a : ℕ), (∀ p ∈ primes, 0 < p) → (∀ a ∈ construct_seq_aux primes prev_a, 0 < a) := by
      intro primes prev_a h_primes_pos a ha
      induction' primes with p primes ih generalizing prev_a a;
      · cases ha;
      · simp_all +decide [ construct_seq_aux ];
        exact ha.elim ( fun ha => ha.symm ▸ Nat.mul_pos ( Nat.succ_pos _ ) h_primes_pos.1 ) fun ha => ih _ _ ha;
    exact h_ind primes 0 h_primes_pos

/-
The sum of primes up to x.
-/
noncomputable def sum_primes_upto (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, (p : ℝ)

/-
If $q < p$ and $p$ is prime, then $P(q p) = p$.
-/
lemma P_eq_of_mul_lt (q p : ℕ) (h_prime : Nat.Prime p) (h_lt : q < p) (h_pos : 0 < q) : P (q * p) = p := by
  -- Since $p$ is prime and $q < p$, all prime factors of $q$ are $\le q < p$. Therefore, $p$ is the largest prime factor of $q * p$.
  have h_max_prime_factor : ∀ f ∈ Nat.primeFactors (q * p), f ≤ p := by
    norm_num [ Nat.primeFactors_mul, h_prime.ne_zero, h_pos.ne' ];
    rintro f ( ⟨ hf₁, hf₂ ⟩ | ⟨ hf₁, hf₂ ⟩ ) <;> [ exact le_trans ( Nat.le_of_dvd h_pos hf₂ ) h_lt.le; exact Nat.le_of_dvd h_prime.pos hf₂ ];
  -- Since $p$ is a prime factor of $q * p$ and $p$ is the largest prime factor, we have $P(q * p) = p$.
  have h_max_prime_factor_eq : (Nat.primeFactors (q * p)).max = p := by
    refine' le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr ( h_max_prime_factor x hx ) ) _;
    exact Finset.le_max ( Nat.mem_primeFactors.mpr ⟨ h_prime, by aesop ⟩ );
  unfold P; aesop;

/-
If the sum of primes is at most n, then every element in the constructed sequence is at most n.
-/
lemma construct_seq_le_n (primes : List ℕ) (n : ℕ) (h_bound : primes.sum ≤ n) (h_primes_pos : ∀ p ∈ primes, 0 < p) :
  ∀ a ∈ construct_seq primes, a ≤ n := by
    exact fun a ha => le_trans ( construct_seq_bound primes h_primes_pos a ha ) h_bound

/-
The largest prime factor of `next_a prev_a p` is `p` under the given conditions.
-/
lemma P_next_a_eq (n prev_a p : ℕ) (h_prime : Nat.Prime p) (h_bound : prev_a + p ≤ n)
  (h_min : Nat.floor (Real.sqrt n) < p) : P (next_a prev_a p) = p := by
    convert P_eq_of_mul_lt ( prev_a / p + 1 ) p h_prime _ _ using 1;
    · -- Since $p$ is a prime number greater than $\sqrt{n}$, we have $p^2 > n$.
      have h_p_sq_gt_n : p^2 > n := by
        exact_mod_cast ( by nlinarith only [ Nat.lt_floor_add_one ( Real.sqrt n ), Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, show ( p :ℝ ) ≥ ⌊Real.sqrt n⌋₊ + 1 by exact_mod_cast h_min ] : ( p :ℝ ) ^ 2 > n );
      nlinarith [ Nat.div_mul_le_self prev_a p ];
    · positivity

/-
Helper lemma: The bound condition for the recursive step holds.
-/
lemma construct_seq_aux_bound_condition (ps : List ℕ) (prev_a n p : ℕ)
  (h_bound : (p :: ps).sum + prev_a ≤ n) (hp : 0 < p) :
  ps.sum + next_a prev_a p ≤ n := by
    -- By definition of `next_a`, we know that `next_a prev_a p ≤ prev_a + p`.
    have h_next_a_le : next_a prev_a p ≤ prev_a + p := by
      exact next_a_le_add prev_a p;
    grind

/-
Helper lemma: The constructed sequence auxiliary function maps P to the primes.
-/
lemma construct_seq_aux_P_eq (primes : List ℕ) (n : ℕ) (prev_a : ℕ)
  (h_primes_min : ∀ p ∈ primes, Nat.floor (Real.sqrt n) < p)
  (h_primes_pos : ∀ p ∈ primes, 0 < p)
  (h_primes_prime : ∀ p ∈ primes, Nat.Prime p)
  (h_bound : primes.sum + prev_a ≤ n) :
  (construct_seq_aux primes prev_a).map P = primes := by
    -- By induction on the list primes.
    induction' primes with p primes ih generalizing prev_a n;
    · rfl;
    · convert congr_arg ( fun l => p :: l ) ( ih n ( next_a prev_a p ) ( fun q hq => ?_ ) ( fun q hq => ?_ ) ( fun q hq => ?_ ) ( ?_ ) ) using 1;
      · rw [ show construct_seq_aux ( p :: primes ) prev_a = next_a prev_a p :: construct_seq_aux primes ( next_a prev_a p ) from rfl, List.map_cons ];
        rw [ P_next_a_eq ];
        exact n;
        · exact h_primes_prime p ( by simp +decide );
        · grind;
        · aesop;
      · exact h_primes_min q ( List.mem_cons_of_mem _ hq );
      · exact h_primes_pos q ( List.mem_cons_of_mem _ hq );
      · exact h_primes_prime q ( List.mem_cons_of_mem _ hq );
      · convert construct_seq_aux_bound_condition primes prev_a n p _ _ using 1 <;> aesop

/-
Helper lemma: The constructed sequence auxiliary function maps P to the primes.
-/
lemma construct_seq_aux_P_eq_new (primes : List ℕ) (n : ℕ) (prev_a : ℕ)
  (h_primes_min : ∀ p ∈ primes, Nat.floor (Real.sqrt n) < p)
  (h_primes_pos : ∀ p ∈ primes, 0 < p)
  (h_primes_prime : ∀ p ∈ primes, Nat.Prime p)
  (h_bound : primes.sum + prev_a ≤ n) :
  (construct_seq_aux primes prev_a).map P = primes := by
    convert construct_seq_aux_P_eq primes n prev_a h_primes_min h_primes_pos h_primes_prime h_bound using 1

/-
If the primes are sorted, large enough, and their sum is small enough, the constructed sequence is valid.
-/
lemma construct_seq_is_valid (primes : List ℕ) (n : ℕ)
  (h_sorted : primes.IsChain (· > ·))
  (h_primes_prime : ∀ p ∈ primes, Nat.Prime p)
  (h_primes_min : ∀ p ∈ primes, Nat.floor (Real.sqrt n) < p)
  (h_sum : primes.sum ≤ n) :
  is_valid_seq n (construct_seq primes) := by
    refine' ⟨ _, _, _ ⟩;
    · convert construct_seq_increasing primes _;
      exact fun p hp => Nat.Prime.pos ( h_primes_prime p hp );
    · exact fun m hm => ⟨ construct_seq_pos primes ( fun p hp => Nat.Prime.pos ( h_primes_prime p hp ) ) m hm, construct_seq_le_n primes n h_sum ( fun p hp => Nat.Prime.pos ( h_primes_prime p hp ) ) m hm ⟩;
    · -- By definition of `construct_seq`, the largest prime factor of each element in the constructed sequence is exactly the prime used to construct it.
      have h_map_P : (construct_seq primes).map P = primes := by
        convert construct_seq_aux_P_eq_new primes n 0 _ _ _ _ using 1;
        · assumption;
        · exact fun p hp => Nat.Prime.pos ( h_primes_prime p hp );
        · assumption;
        · linarith;
      grind

/-
The function g(n) is O(sqrt(n / log n)).
-/
theorem g_upper_bound_asymptotic :
  (fun n => (g n : ℝ)) =O[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
    have h_g_le_upper_bound : ∀ᶠ n in atTop, (g n : ℝ) ≤ upper_bound_func n := by
      -- For n ≥ 2, we have g(n) ≤ upper_bound_func(n) by definition.
      have h_g_le_upper_bound : ∀ n ≥ 2, (g n : ℝ) ≤ upper_bound_func n := by
        -- By definition of $g$, we know that $g(n) \leq \text{upper\_bound\_func}(n)$ for all $n \geq 2$.
        intros n hn
        have h_g_le_upper_bound : (g n : ℝ) ≤ Nat.floor (Real.sqrt (2 * n / Real.log n)) + Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) + 1 := by
          exact_mod_cast g_le_card_sum hn;
        convert h_g_le_upper_bound using 1;
      exact Filter.eventually_atTop.mpr ⟨ 2, h_g_le_upper_bound ⟩;
    refine' Asymptotics.IsBigO.trans _ ( upper_bound_asymptotic );
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ 1, by filter_upwards [ h_g_le_upper_bound ] with n hn; rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by exact le_trans ( by positivity ) hn ) ] ; linarith ⟩

axiom pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x

lemma pi_asymp_lemma : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ)) ~[atTop] (fun x => x / Real.log x) := by
  have := pi_alt;
  obtain ⟨ c, hc₁, hc₂ ⟩ := this; simp_all +decide [ Asymptotics.isEquivalent_iff_exists_eq_mul ] ;
  exact ⟨ fun x => 1 + c x, by simpa using hc₁.const_add 1, by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by simp +decide [ mul_div_assoc ] ⟩

lemma sum_primes_eq_integral (x : ℝ) (hx : 2 ≤ x) :
  sum_primes_upto x = (Nat.primeCounting (Nat.floor x) : ℝ) * x - ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ) := by
    -- By definition of sum_primes_upto, we can write it as a sum of terms involving prime numbers.
    have h_sum_primes_upto : sum_primes_upto x = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1)), (p : ℝ) := by
      exact rfl;
    -- Using summation by parts for sums, we can rewrite the sum as follows:
    have h_sum_parts : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1)), (p : ℝ) = (Nat.primeCounting (Nat.floor x) : ℝ) * (Nat.floor x) - ∑ k ∈ Finset.range (Nat.floor x), (Nat.primeCounting k : ℝ) := by
      have h_sum_parts : ∀ n : ℕ, ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (p : ℝ) = (Nat.primeCounting n : ℝ) * n - ∑ k ∈ Finset.range n, (Nat.primeCounting k : ℝ) := by
        intro n;
        induction n <;> simp_all +decide [ Finset.sum_range_succ, Nat.primeCounting ];
        · norm_num [ Finset.sum_filter ];
        · simp_all +decide [ Finset.sum_range_succ, Finset.sum_filter, Nat.primeCounting' ];
          split_ifs <;> simp_all +decide [ Nat.count_succ ] ; ring;
          ring;
      apply h_sum_parts;
    -- We'll use the fact that $\int_2^x \pi(t) dt = \sum_{k=2}^{\lfloor x \rfloor - 1} \pi(k)$.
    have h_integral_sum : ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ) = ∑ k ∈ Finset.range (Nat.floor x), (Nat.primeCounting k : ℝ) - ∑ k ∈ Finset.range 2, (Nat.primeCounting k : ℝ) + (Nat.primeCounting (Nat.floor x) : ℝ) * (x - Nat.floor x) := by
      -- We'll use the fact that the integral of a step function can be computed as the sum of the values of the function at the jump points multiplied by the length of the interval.
      have h_integral_step : ∀ n : ℕ, 2 ≤ n → ∫ t in (2 : ℝ)..n, (Nat.primeCounting (Nat.floor t) : ℝ) = ∑ k ∈ Finset.range n, (Nat.primeCounting k : ℝ) - ∑ k ∈ Finset.range 2, (Nat.primeCounting k : ℝ) := by
        intro n hn
        induction' n, hn using Nat.le_induction with n hn ih;
        · norm_num;
        · -- For the induction step, we can split the integral at $n$.
          have h_split : ∫ t in (2 : ℝ)..(n + 1), (Nat.primeCounting (Nat.floor t) : ℝ) = (∫ t in (2 : ℝ)..n, (Nat.primeCounting (Nat.floor t) : ℝ)) + (∫ t in (n : ℝ)..(n + 1), (Nat.primeCounting (Nat.floor t) : ℝ)) := by
            rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MonotoneOn.intervalIntegrable ];
            · exact fun x hx y hy hxy => Nat.cast_le.mpr <| Nat.monotone_primeCounting <| Nat.floor_mono hxy;
            · exact fun x hx y hy hxy => Nat.cast_le.mpr <| Nat.monotone_primeCounting <| Nat.floor_mono hxy;
          -- For the second integral, we can use the fact that $\pi(t)$ is constant on the interval $[n, n+1)$.
          have h_const : ∫ t in (n : ℝ)..(n + 1), (Nat.primeCounting (Nat.floor t) : ℝ) = (Nat.primeCounting n : ℝ) := by
            rw [ intervalIntegral.integral_of_le ] <;> norm_num;
            rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo ];
            rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [ show ⌊t⌋₊ = n by exact Nat.floor_eq_iff ( by linarith [ ht.1 ] ) |>.2 ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ] ] ; norm_num;
          norm_num [ Finset.sum_range_succ ] at * ; linarith;
      convert congr_arg ( fun y : ℝ => y + ( Nat.primeCounting ⌊x⌋₊ : ℝ ) * ( x - ⌊x⌋₊ ) ) ( h_integral_step ⌊x⌋₊ ( Nat.le_floor hx ) ) using 1;
      rw [ ← intervalIntegral.integral_add_adjacent_intervals ];
      congr! 1;
      · rw [ intervalIntegral.integral_of_le ( Nat.floor_le ( by positivity ) ) ];
        rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun y hy => by rw [ show ⌊y⌋₊ = ⌊x⌋₊ from Nat.floor_eq_iff ( by linarith [ hy.1 ] ) |>.2 ⟨ by linarith [ hy.1, Nat.floor_le ( by linarith : 0 ≤ x ) ], by linarith [ hy.2, Nat.lt_floor_add_one x ] ⟩ ] ] ; norm_num [ mul_comm ];
        rw [ max_eq_left ( sub_nonneg.mpr <| Nat.floor_le <| by positivity ), mul_comm ];
      · apply_rules [ Monotone.intervalIntegrable ];
        exact fun a b hab => Nat.cast_le.mpr <| Nat.monotone_primeCounting <| Nat.floor_mono hab;
      · apply_rules [ MonotoneOn.intervalIntegrable ];
        exact fun a ha b hb hab => Nat.cast_le.mpr <| Nat.monotone_primeCounting <| Nat.floor_mono hab;
    norm_num [ Finset.sum_range_succ ] at * ; linarith

lemma integral_t_div_log_t_asymp : (fun x => ∫ t in (2 : ℝ)..x, t / Real.log t) ~[atTop] (fun x => x^2 / (2 * Real.log x)) := by
  -- By integration by parts, we have $\int_2^x \frac{t}{\log t} dt = \frac{x^2}{2 \log x} + \int_2^x \frac{t}{2 (\log t)^2} dt$.
  have h_int_parts : ∀ x : ℝ, 2 ≤ x → ∫ t in (2 : ℝ)..x, t / Real.log t = x^2 / (2 * Real.log x) - 2^2 / (2 * Real.log 2) + ∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2) := by
    intros x hx
    have h_parts : ∀ a b : ℝ, 2 ≤ a → a ≤ b → ∫ t in a..b, t / Real.log t = (b^2 / (2 * Real.log b)) - (a^2 / (2 * Real.log a)) + ∫ t in a..b, t / (2 * (Real.log t)^2) := by
      intros a b _ _; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => x^2 / ( 2 * Real.log x ) + ∫ t in ( 2 : ℝ )..x, t / ( 2 * Real.log t ^ 2 );
      · rw [ ← intervalIntegral.integral_add_adjacent_intervals ] <;> ring_nf <;> apply_rules [ ContinuousOn.intervalIntegrable ] <;> norm_num [ Real.log_pos ] at *;
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.mul ( ContinuousAt.mul continuousAt_id <| ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> linarith ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith ) continuousAt_const;
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.mul ( ContinuousAt.mul continuousAt_id <| ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> linarith ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith ) continuousAt_const;
      · intro x hx
        have h_int_deriv : HasDerivAt (fun x => ∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) (x / (2 * (Real.log x)^2)) x := by
          apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hy <;> linarith [ Set.mem_Icc.mp <| by simpa [ * ] using hx ] ) _ ) <| ne_of_gt <| mul_pos zero_lt_two <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hy <;> linarith [ Set.mem_Icc.mp <| by simpa [ * ] using hx ];
          · exact Measurable.stronglyMeasurable ( by exact Measurable.mul ( measurable_id' ) ( Measurable.inv ( measurable_const.mul ( Real.measurable_log.pow_const 2 ) ) ) ) |> fun h => h.stronglyMeasurableAtFilter;
          · exact ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) _ ) ) ( mul_ne_zero two_ne_zero ( pow_ne_zero 2 ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ) );
        convert HasDerivAt.add ( HasDerivAt.div ( hasDerivAt_pow 2 x ) ( HasDerivAt.const_mul 2 ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ( show ( 2 * Real.log x ) ≠ 0 by exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith ) ) h_int_deriv using 1 ; ring_nf;
        grind;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) );
    exact h_parts _ _ le_rfl hx;
  -- We'll use the fact that $\int_2^x \frac{t}{2 (\log t)^2} dt = o(\frac{x^2}{\log x})$.
  have h_integral_small : Filter.Tendsto (fun x => (∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) / (x^2 / (2 * Real.log x))) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\int_2^x \frac{t}{2 (\log t)^2} dt \leq \int_2^{\sqrt{x}} \frac{t}{2 (\log t)^2} dt + \int_{\sqrt{x}}^x \frac{t}{2 (\log t)^2} dt$.
    have h_integral_split : ∀ x : ℝ, 4 ≤ x → (∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) ≤ (∫ t in (2 : ℝ)..Real.sqrt x, t / (2 * (Real.log t)^2)) + (∫ t in (Real.sqrt x : ℝ)..x, t / (2 * (Real.log t)^2)) := by
      intros x hx
      have h_split : ∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2) = (∫ t in (2 : ℝ)..Real.sqrt x, t / (2 * (Real.log t)^2)) + (∫ t in (Real.sqrt x : ℝ)..x, t / (2 * (Real.log t)^2)) := by
        rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ] ) _ ) <| ne_of_gt <| mul_pos zero_lt_two <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ];
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ] ) _ ) <| ne_of_gt <| mul_pos zero_lt_two <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ];
      rw [h_split];
    -- For the first part, $\int_2^{\sqrt{x}} \frac{t}{2 (\log t)^2} dt \leq \frac{\sqrt{x}^2}{2 (\log 2)^2} = \frac{x}{2 (\log 2)^2}$.
    have h_integral_first_part : ∀ x : ℝ, 4 ≤ x → (∫ t in (2 : ℝ)..Real.sqrt x, t / (2 * (Real.log t)^2)) ≤ x / (2 * (Real.log 2)^2) := by
      intros x hx
      have h_integral_first_part_le : ∫ t in (2 : ℝ)..Real.sqrt x, t / (2 * (Real.log t)^2) ≤ ∫ t in (2 : ℝ)..Real.sqrt x, t / (2 * (Real.log 2)^2) := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · exact Real.le_sqrt_of_sq_le ( by linarith );
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ] ) _ ) <| ne_of_gt <| mul_pos zero_lt_two <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ];
        · bound;
      norm_num [ div_eq_mul_inv ] at *;
      exact h_integral_first_part_le.trans ( by rw [ Real.sq_sqrt ( by positivity ) ] ; nlinarith [ inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos one_lt_two ) ) ] );
    -- For the second part, $\int_{\sqrt{x}}^x \frac{t}{2 (\log t)^2} dt \leq \frac{x^2}{2 (\log \sqrt{x})^2} = \frac{2x^2}{(\log x)^2}$.
    have h_integral_second_part : ∀ x : ℝ, 4 ≤ x → (∫ t in (Real.sqrt x : ℝ)..x, t / (2 * (Real.log t)^2)) ≤ 2 * x^2 / (Real.log x)^2 := by
      intros x hx
      have h_integral_second_part_bound : ∫ t in (Real.sqrt x : ℝ)..x, t / (2 * (Real.log t)^2) ≤ ∫ t in (Real.sqrt x : ℝ)..x, t / (2 * (Real.log (Real.sqrt x))^2) := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · rw [ Real.sqrt_le_left ] <;> nlinarith;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( ContinuousAt.mul continuousAt_const <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ] ) _ ) <| ne_of_gt <| mul_pos zero_lt_two <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith ] ;
        · intro t ht₁ ht₂; gcongr;
          · linarith [ Real.sqrt_nonneg x ];
          · exact mul_pos zero_lt_two ( sq_pos_of_pos ( Real.log_pos ( Real.lt_sqrt_of_sq_lt ( by linarith ) ) ) );
          · exact Real.log_nonneg <| Real.le_sqrt_of_sq_le <| by linarith;
      refine le_trans h_integral_second_part_bound ?_;
      norm_num [ Real.log_sqrt ( show 0 ≤ x by linarith ) ] ; ring_nf ; norm_num;
      exact le_add_of_le_of_nonneg ( le_mul_of_one_le_right ( by positivity ) ( by norm_num ) ) ( by positivity );
    -- Combining the bounds for the two parts, we get $\int_2^x \frac{t}{2 (\log t)^2} dt \leq \frac{x}{2 (\log 2)^2} + \frac{2x^2}{(\log x)^2}$.
    have h_integral_combined : ∀ x : ℝ, 4 ≤ x → (∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) ≤ x / (2 * (Real.log 2)^2) + 2 * x^2 / (Real.log x)^2 := by
      exact fun x hx => le_trans ( h_integral_split x hx ) ( add_le_add ( h_integral_first_part x hx ) ( h_integral_second_part x hx ) );
    -- We'll use the fact that $\frac{x}{2 (\log 2)^2} / \frac{x^2}{2 \log x} = \frac{\log x}{x (\log 2)^2}$ and $\frac{2x^2}{(\log x)^2} / \frac{x^2}{2 \log x} = \frac{4 \log x}{(\log x)^2} = \frac{4}{\log x}$.
    have h_ratio_simplified : ∀ x : ℝ, 4 ≤ x → (∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) / (x^2 / (2 * Real.log x)) ≤ (Real.log x / (x * (Real.log 2)^2)) + (4 / Real.log x) := by
      intro x hx; convert div_le_div_of_nonneg_right ( h_integral_combined x hx ) ( show 0 ≤ x ^ 2 / ( 2 * Real.log x ) from div_nonneg ( sq_nonneg _ ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by linarith ) ) ) ) using 1 ; ring_nf;
      by_cases hx' : x = 0 <;> simp +decide [ sq, mul_assoc, hx' ] ; ring_nf;
      by_cases h : Real.log x = 0 <;> simp +decide [ sq, mul_assoc, h ];
    -- We'll use the fact that $\frac{\log x}{x (\log 2)^2}$ and $\frac{4}{\log x}$ tend to $0$ as $x \to \infty$.
    have h_tendsto_zero : Filter.Tendsto (fun x : ℝ => Real.log x / (x * (Real.log 2)^2)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => 4 / Real.log x) Filter.atTop (nhds 0) := by
      constructor;
      · -- We can use the fact that $\frac{\log x}{x}$ tends to $0$ as $x$ tends to infinity.
        have h_log_x_over_x : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
          suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        simpa [ div_mul_eq_div_div ] using h_log_x_over_x.div_const ( Real.log 2 ^ 2 );
      · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop );
    refine' squeeze_zero_norm' _ ( by simpa using h_tendsto_zero.1.add h_tendsto_zero.2 );
    filter_upwards [ Filter.eventually_ge_atTop 4 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( intervalIntegral.integral_nonneg ( by linarith ) fun t ht => div_nonneg ( by linarith [ ht.1 ] ) ( by positivity ) ) ( by exact div_nonneg ( sq_nonneg _ ) ( by exact mul_nonneg zero_le_two ( Real.log_nonneg ( by linarith ) ) ) ) ) ] ; exact h_ratio_simplified x hx;
  -- Using the fact that subtraction and addition are continuous operations, we can combine the results.
  have h_combined : Filter.Tendsto (fun x => ((x^2 / (2 * Real.log x) - 2^2 / (2 * Real.log 2) + ∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) / (x^2 / (2 * Real.log x)))) Filter.atTop (nhds 1) := by
    -- We can simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun x => 1 - (2^2 / (2 * Real.log 2)) / (x^2 / (2 * Real.log x)) + (∫ t in (2 : ℝ)..x, t / (2 * (Real.log t)^2)) / (x^2 / (2 * Real.log x))) Filter.atTop (nhds 1) by
      refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using by rw [ add_div, sub_div, div_self <| ne_of_gt <| div_pos ( sq_pos_of_pos <| by linarith ) <| mul_pos zero_lt_two <| Real.log_pos <| by linarith ] );
    -- We'll use the fact that $2^2 / (2 * \log 2) / (x^2 / (2 * \log x))$ tends to $0$ as $x$ tends to infinity.
    have h_const : Filter.Tendsto (fun x => (2^2 / (2 * Real.log 2)) / (x^2 / (2 * Real.log x))) Filter.atTop (nhds 0) := by
      field_simp;
      -- We can factor out $x^{-2}$ and use the fact that $\log x / x^2 \to 0$ as $x \to \infty$.
      have h_log_x_over_x2 : Filter.Tendsto (fun x => Real.log x / x^2) Filter.atTop (nhds 0) := by
        refine' squeeze_zero_norm' _ _;
        exacts [ fun x => 1 / x, Filter.eventually_atTop.mpr ⟨ 2, fun x hx => by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( sq_nonneg x ) ) ] ; rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < x ) ] ⟩, tendsto_const_nhds.div_atTop Filter.tendsto_id ];
      convert h_log_x_over_x2.const_mul ( 2 ^ 2 / Real.log 2 ) using 2 <;> ring;
    simpa using Filter.Tendsto.add ( tendsto_const_nhds.sub h_const ) h_integral_small;
  rw [ Asymptotics.isEquivalent_iff_exists_eq_mul ];
  exact ⟨ _, h_combined, by filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Pi.mul_apply, div_mul_cancel₀ _ ( ne_of_gt <| div_pos ( sq_pos_of_pos <| by linarith ) <| mul_pos two_pos <| Real.log_pos <| by linarith ) ] ; rw [ h_int_parts x hx ] ⟩

lemma integral_pi_asymp : (fun x => ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) ~[atTop] (fun x => x^2 / (2 * Real.log x)) := by
  have h_integral : (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) ~[atTop] (fun x : ℝ => ∫ t in (2 : ℝ)..x, (t / Real.log t)) := by
    -- Using the fact that the difference between the integral of π(t) and the integral of t / log t is bounded, we can apply the asymptotic equivalence.
    have h_diff : ∀ ε > 0, ∃ T : ℝ, ∀ x ≥ T, |(∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) - (∫ t in (2 : ℝ)..x, t / Real.log t)| ≤ ε * (∫ t in (2 : ℝ)..x, t / Real.log t) + (∫ t in (2 : ℝ)..T, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t|) := by
      intro ε ε_pos
      obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ t ≥ T, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t| ≤ ε * (t / Real.log t) := by
        have h_pi_approx : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ)) ~[atTop] (fun x : ℝ => x / Real.log x) := by
          exact pi_asymp_lemma;
        rw [ Asymptotics.IsEquivalent ] at h_pi_approx;
        rw [ Asymptotics.isLittleO_iff ] at h_pi_approx;
        norm_num +zetaDelta at *;
        exact Exists.elim ( h_pi_approx ε_pos ) fun T hT => ⟨ Max.max T 2, fun t ht => by simpa only [ abs_of_nonneg ( show 0 ≤ t by linarith [ le_max_right T 2 ] ), abs_of_nonneg ( show 0 ≤ Real.log t by exact Real.log_nonneg ( by linarith [ le_max_right T 2 ] ) ) ] using hT t ( le_trans ( le_max_left T 2 ) ht ) ⟩;
      use Max.max T 2;
      intro x hx
      have h_integral_split : ∫ t in (2 : ℝ)..x, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t| ≤ (∫ t in (2 : ℝ)..(Max.max T 2), |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t|) + (∫ t in (Max.max T 2)..x, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t|) := by
        rw [ intervalIntegral.integral_add_adjacent_intervals ];
        · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
          refine' MeasureTheory.Integrable.abs _;
          refine' MeasureTheory.Integrable.sub _ _;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun t => ( Nat.primeCounting ( Nat.floor t ) : ℝ );
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun t => ( Nat.primeCounting ( Nat.floor ( Max.max T 2 ) ) : ℝ );
              · exact Continuous.integrableOn_Icc ( by continuity );
              · fun_prop;
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht;
                norm_num +zetaDelta at *;
                exact Nat.monotone_primeCounting <| Nat.floor_mono <| by cases ht.2 <;> linarith [ le_max_left T 2, le_max_right T 2 ] ;
            · fun_prop;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ;
          · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) ) );
        · rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ( by linarith [ le_max_left T 2, le_max_right T 2 ] ) ];
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun t => ε * ( t / Real.log t );
          · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul continuousOn_const <| ContinuousOn.div continuousOn_id ( Real.continuousOn_log.mono <| by intro t ht; exact ne_of_gt <| lt_of_lt_of_le ( by positivity ) ht.1 ) fun t ht => ne_of_gt <| Real.log_pos <| lt_of_lt_of_le ( by norm_num ) ht.1 ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
          · refine' Measurable.aestronglyMeasurable _;
            fun_prop (disch := norm_num);
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by simpa using hT t ( le_trans ( le_max_left _ _ ) ht.1.le ) ;
      have h_integral_bound : ∫ t in (Max.max T 2)..x, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t| ≤ ε * (∫ t in (Max.max T 2)..x, t / Real.log t) := by
        rw [ intervalIntegral.integral_of_le ( by linarith [ le_max_left T 2, le_max_right T 2 ] ), intervalIntegral.integral_of_le ( by linarith [ le_max_left T 2, le_max_right T 2 ] ) ];
        rw [ ← MeasureTheory.integral_const_mul ];
        refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
        · exact Filter.Eventually.of_forall fun t => abs_nonneg _;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul continuousOn_const <| ContinuousOn.div continuousOn_id ( Real.continuousOn_log.mono <| by intro t ht; exact ne_of_gt <| lt_of_lt_of_le ( by positivity ) ht.1 ) fun t ht => ne_of_gt <| Real.log_pos <| by linarith [ ht.1, le_max_right T 2 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using hT t ( le_trans ( le_max_left _ _ ) ht.1.le );
      have h_integral_bound : |(∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) - (∫ t in (2 : ℝ)..x, t / Real.log t)| ≤ ∫ t in (2 : ℝ)..x, |(Nat.primeCounting (Nat.floor t) : ℝ) - t / Real.log t| := by
        rw [ ← intervalIntegral.integral_sub ];
        · apply_rules [ intervalIntegral.abs_integral_le_integral_abs, le_rfl ];
          linarith [ le_max_right T 2 ];
        · apply_rules [ Monotone.intervalIntegrable ];
          intro a b hab; exact (by
          simp +zetaDelta at *;
          exact Nat.monotone_primeCounting <| Nat.floor_mono hab);
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) );
      have h_integral_bound : ∫ t in (Max.max T 2)..x, t / Real.log t ≤ ∫ t in (2 : ℝ)..x, t / Real.log t := by
        apply_rules [ intervalIntegral.integral_mono_interval ];
        · norm_num;
        · norm_num;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using div_nonneg ( by linarith [ ht.1 ] ) ( Real.log_nonneg ( by linarith [ ht.1 ] ) );
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ le_max_right T 2 ] ) ) );
      nlinarith [ show 0 ≤ ∫ t in ( 2 : ℝ )..x, t / Real.log t from intervalIntegral.integral_nonneg ( by linarith [ le_max_right T 2 ] ) fun t ht => div_nonneg ( by linarith [ ht.1 ] ) ( Real.log_nonneg ( by linarith [ ht.1 ] ) ) ];
    -- Using the fact that the integral of t / log t grows to infinity, we can show that the difference divided by the integral of t / log t tends to zero.
    have h_div_zero : Filter.Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, t / Real.log t)) Filter.atTop Filter.atTop := by
      have h_integral_growth : Filter.Tendsto (fun x : ℝ => ∫ t in (2 : ℝ)..x, t / Real.log t) Filter.atTop Filter.atTop := by
        have h_integral_bound : ∀ x : ℝ, 2 ≤ x → ∫ t in (2 : ℝ)..x, t / Real.log t ≥ ∫ t in (2 : ℝ)..x, t / Real.log x := by
          intro x hx; refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
          · exact hx;
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) );
          · bound
        have h_integral_bound : Filter.Tendsto (fun x : ℝ => (x^2 - 4) / (2 * Real.log x)) Filter.atTop Filter.atTop := by
          have h_integral_bound : Filter.Tendsto (fun x : ℝ => x^2 / (2 * Real.log x)) Filter.atTop Filter.atTop := by
            have h_integral_bound : Filter.Tendsto (fun x : ℝ => x^2 / Real.log x) Filter.atTop Filter.atTop := by
              have : Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
                -- We can use the change of variables $u = \log x$ to transform the limit expression.
                suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
                  have := h_log.comp Real.tendsto_log_atTop;
                  exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
                simpa using Real.tendsto_exp_div_pow_atTop 1
              have : Filter.Tendsto (fun x : ℝ => x * (x / Real.log x)) Filter.atTop Filter.atTop := by
                exact Filter.Tendsto.atTop_mul_atTop₀ Filter.tendsto_id this;
              exact this.congr fun x => by ring;
            convert h_integral_bound.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 2 by norm_num ) using 2 ; ring;
          have h_integral_bound : Filter.Tendsto (fun x : ℝ => x^2 / (2 * Real.log x) - 4 / (2 * Real.log x)) Filter.atTop Filter.atTop := by
            exact Filter.Tendsto.atTop_add h_integral_bound ( Filter.Tendsto.neg ( tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop zero_lt_two ( Real.tendsto_log_atTop ) ) ) );
          exact h_integral_bound.congr fun x => by ring;
        refine' Filter.tendsto_atTop_mono' _ _ h_integral_bound;
        filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using le_trans ( by norm_num [ div_eq_mul_inv ] ; ring_nf; norm_num ) ( ‹∀ x : ℝ, 2 ≤ x → ∫ t in ( 2 : ℝ )..x, t / Real.log t ≥ ∫ t in ( 2 : ℝ )..x, t / Real.log x› x hx );
      convert h_integral_growth using 1;
    rw [ Asymptotics.IsEquivalent ];
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · rw [ Metric.tendsto_nhds ];
      intro ε hε; rcases h_diff ( ε / 2 ) ( half_pos hε ) with ⟨ T, hT ⟩ ; filter_upwards [ h_div_zero.eventually_gt_atTop ( 2 * ( ∫ t in ( 2 : ℝ )..T, |( Nat.primeCounting ⌊t⌋₊ : ℝ ) - t / Real.log t| ) / ( ε / 2 ) ), Filter.eventually_ge_atTop T ] with x hx₁ hx₂; rw [ dist_eq_norm ] ; norm_num;
      rw [ div_lt_iff₀ ] <;> cases abs_cases ( ∫ t in ( 2 : ℝ )..x, t / Real.log t ) <;> nlinarith [ hT x hx₂, abs_le.mp ( hT x hx₂ ), mul_div_cancel₀ ( 2 * ∫ t in ( 2 : ℝ )..T, |( ⌊t⌋₊.primeCounting : ℝ ) - t / Real.log t| ) ( ne_of_gt ( half_pos hε ) ) ];
    · filter_upwards [ h_div_zero.eventually_gt_atTop 0 ] with x hx hx' using False.elim <| hx.ne' hx';
  exact h_integral.trans ( by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using integral_t_div_log_t_asymp )

lemma sum_primes_asymp_lemma : sum_primes_upto ~[atTop] (fun x => x ^ 2 / (2 * Real.log x)) := by
  -- By combining the results from the previous steps, we can conclude that sum_primes_upto is asymptotically equivalent to x^2 / (2 * log x).
  have h_combined : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * x - ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) ~[atTop] (fun x : ℝ => x^2 / (2 * Real.log x)) := by
    -- We'll use the fact that $\pi(x) \sim \frac{x}{\log x}$ and $\int_2^x \pi(t) \, dt \sim \frac{x^2}{2 \log x}$ to show the desired result.
    have h_pi : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ)) ~[atTop] (fun x => x / Real.log x) := by
      convert pi_asymp_lemma using 1
    have h_integral : (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) ~[atTop] (fun x => x^2 / (2 * Real.log x)) := by
      convert integral_pi_asymp using 1;
    have h_combined : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * x) ~[atTop] (fun x : ℝ => x^2 / Real.log x) := by
      have h_combined : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * x) ~[atTop] (fun x : ℝ => (x / Real.log x) * x) := by
        apply_rules [ Asymptotics.IsEquivalent.mul, h_pi ];
        rfl;
      exact h_combined.trans ( by refine' Filter.EventuallyEq.isEquivalent _ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by ring );
    have h_combined : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * x - ∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) ~[atTop] (fun x : ℝ => x^2 / Real.log x - x^2 / (2 * Real.log x)) := by
      rw [ Asymptotics.IsEquivalent ] at *;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
      · have h_combined : Filter.Tendsto (fun x : ℝ => (((Nat.primeCounting (Nat.floor x) : ℝ) * x - x^2 / Real.log x) / (x^2 / Real.log x)) * (1 / (1 - 1 / 2)) - (((∫ t in (2 : ℝ)..x, (Nat.primeCounting (Nat.floor t) : ℝ)) - x^2 / (2 * Real.log x)) / (x^2 / (2 * Real.log x))) * (1 / (2 - 1))) Filter.atTop (nhds 0) := by
          convert Filter.Tendsto.sub ( h_combined.mul_const ( 1 / ( 1 - 1 / 2 ) ) ) ( h_integral.mul_const ( 1 / ( 2 - 1 ) ) ) using 2 ; ring;
        refine h_combined.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
        grind;
      · exact ⟨ 2, by rintro x hx ( rfl | rfl | rfl ) <;> norm_num at hx ⟩;
      · exact ⟨ 2, by rintro x hx ( rfl | rfl | rfl ) <;> norm_num at hx ⟩;
      · exact ⟨ 2, fun x hx hx' => by rcases hx' with ( rfl | rfl | rfl ) <;> norm_num at * ⟩;
      · exact ⟨ 3, fun x hx hx' => absurd hx' <| by ring_nf; nlinarith [ inv_pos.mpr <| Real.log_pos <| show 1 < x by linarith, Real.log_pos <| show 1 < x by linarith, mul_inv_cancel₀ <| ne_of_gt <| Real.log_pos <| show 1 < x by linarith ] ⟩;
    convert h_combined using 2 ; ring;
  refine' h_combined.congr' _ _;
  · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx;
    have := sum_primes_eq_integral x hx.le;
    aesop;
  · rfl

noncomputable def safe_primes (n : ℕ) : List ℕ :=
  let A := Nat.floor (Real.sqrt n)
  let B := Nat.floor (Real.sqrt (n * Real.log n / 2))
  let primes := (Finset.Ioc A B).filter Nat.Prime
  (primes.sort (· ≤ ·)).reverse

lemma safe_primes_sum_le_n : ∀ᶠ n in atTop, (safe_primes n).sum ≤ n := by
  -- By definition of `safe_primes`, we know that its sum is less than or equal to `n`.
  have h_sum_le_n : ∀ᶠ n in Filter.atTop, (safe_primes n).sum ≤ n := by
    have h_sum_primes_asymp : sum_primes_upto ~[atTop] (fun x => x ^ 2 / (2 * Real.log x)) := by
      convert sum_primes_asymp_lemma using 1
    -- Using the asymptotic equivalence of the sum of primes, we can show that the sum of the primes in the interval is eventually less than n.
    have h_sum_primes_lt_n : ∀ᶠ n in Filter.atTop, sum_primes_upto (Real.sqrt (n * Real.log n / 2)) < n := by
      -- Using the asymptotic equivalence of the sum of primes, we can show that the sum of the primes in the interval is eventually less than n by choosing a sufficiently large N.
      have h_sum_primes_lt_n : ∀ᶠ n in Filter.atTop, sum_primes_upto (Real.sqrt (n * Real.log n / 2)) ≤ (1 + 1 / 4) * (Real.sqrt (n * Real.log n / 2)) ^ 2 / (2 * Real.log (Real.sqrt (n * Real.log n / 2))) := by
        have h_sum_primes_lt_n : ∀ᶠ x in Filter.atTop, sum_primes_upto x ≤ (1 + 1 / 4) * x ^ 2 / (2 * Real.log x) := by
          have := h_sum_primes_asymp.def ( show 0 < 1 / 4 by norm_num );
          filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
          norm_num [ abs_of_nonneg, Real.log_nonneg hx₂.le ] at *;
          ring_nf at *; linarith [ abs_le.mp hx₁ ] ;
        have h_subst : Filter.Tendsto (fun n => Real.sqrt (n * Real.log n / 2)) Filter.atTop Filter.atTop := by
          exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Real.exp ( x ^ 2 * 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Real.add_one_le_exp ( x ^ 2 * 2 ), Real.log_exp ( x ^ 2 * 2 ), Real.log_le_log ( by positivity ) hn ] ⟩;
        exact h_sum_primes_lt_n.filter_mono h_subst;
      filter_upwards [ h_sum_primes_lt_n, Filter.eventually_gt_atTop 4, Filter.eventually_gt_atTop ( Real.exp 4 ) ] with n hn hn' hn'';
      refine lt_of_le_of_lt hn ?_;
      rw [ Real.sq_sqrt ( by nlinarith [ Real.log_pos ( by linarith : 1 < n ) ] ), Real.log_sqrt ( by nlinarith [ Real.log_pos ( by linarith : 1 < n ) ] ) ];
      rw [ div_lt_iff₀ ] <;> ring_nf;
      · field_simp;
        rw [ show n * Real.log n / 2 = n * ( Real.log n / 2 ) by ring, Real.log_mul ( by linarith ) ( by linarith [ Real.log_pos ( by linarith : 1 < n ) ] ) ];
        nlinarith [ Real.log_exp 4, Real.log_lt_log ( by positivity ) hn'', Real.log_pos ( show 1 < Real.log n / 2 by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith [ Real.log_exp 4, Real.log_lt_log ( by positivity ) hn'' ] ) ];
      · exact Real.log_pos ( by nlinarith [ Real.add_one_le_exp 4, Real.log_exp 4, Real.log_le_log ( by positivity ) hn''.le ] );
    have h_sum_primes_lt_n_nat : ∀ᶠ n in Filter.atTop, (safe_primes n).sum ≤ sum_primes_upto (Real.sqrt (n * Real.log n / 2)) := by
      refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn => _ ⟩ ; unfold safe_primes ; norm_num [ sum_primes_upto ];
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      rotate_left;
      exact Finset.filter Nat.Prime ( Finset.Ioc n.sqrt ⌊Real.sqrt n * Real.sqrt ( Real.log n ) / Real.sqrt 2⌋₊ );
      · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ), Finset.mem_filter.mp hx |>.2 ⟩;
      · exact fun _ _ _ => Nat.cast_nonneg _;
      · -- Since the sorted list is a permutation of the original list, their sums are equal.
        have h_perm : List.Perm (Finset.sort (· ≤ ·) (Finset.filter Nat.Prime (Finset.Ioc n.sqrt ⌊Real.sqrt n * Real.sqrt (Real.log n) / Real.sqrt 2⌋₊))) (Finset.filter Nat.Prime (Finset.Ioc n.sqrt ⌊Real.sqrt n * Real.sqrt (Real.log n) / Real.sqrt 2⌋₊)).toList := by
          rw [ ← Multiset.coe_eq_coe ] ; aesop;
        simpa using h_perm.map ( fun x : ℕ => ( x : ℝ ) ) |> List.Perm.sum_eq |> le_of_eq;
    filter_upwards [ h_sum_primes_lt_n_nat, h_sum_primes_lt_n.natCast_atTop ] with n hn hn' using by exact_mod_cast hn.trans hn'.le;
  convert h_sum_le_n using 1

lemma pi_B_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) : ℝ)) ~[atTop] (fun n => Real.sqrt 2 * Real.sqrt (n / Real.log n)) := by
  have h_pi_asymp : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ)) ~[atTop] (fun x => x / Real.log x) := by
    convert pi_asymp_lemma using 1;
  have h_subst : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2)) : ℕ) : ℝ)) ~[Filter.atTop] (fun n : ℕ => Real.sqrt (n * Real.log n / 2) / Real.log (Real.sqrt (n * Real.log n / 2))) := by
    refine' h_pi_asymp.comp_tendsto _;
    exact Filter.tendsto_atTop_atTop.mpr fun x => ⟨ ⌈x ^ 2 * 2⌉₊ + 2, fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Nat.le_ceil ( x ^ 2 * 2 ), show ( n : ℝ ) ≥ ⌈x ^ 2 * 2⌉₊ + 2 by exact_mod_cast hn, Real.log_inv n ▸ Real.log_le_sub_one_of_pos ( inv_pos.mpr <| show ( n : ℝ ) > 0 by norm_cast; linarith ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ] ⟩;
  refine' h_subst.trans _;
  have h_simplify : (fun n : ℕ => Real.sqrt (n * Real.log n / 2) / Real.log (Real.sqrt (n * Real.log n / 2))) ~[Filter.atTop] (fun n : ℕ => Real.sqrt (n * Real.log n / 2) / (Real.log n / 2)) := by
    have h_log_simplify : Filter.Tendsto (fun n : ℕ => Real.log (Real.sqrt (n * Real.log n / 2)) / (Real.log n / 2)) Filter.atTop (nhds 1) := by
      have h_log_simplify : Filter.Tendsto (fun n : ℕ => (Real.log (n * Real.log n / 2)) / Real.log n) Filter.atTop (nhds 1) := by
        -- We can use the fact that $\log(n \log n / 2) = \log n + \log \log n - \log 2$.
        suffices h_log_simplify : Filter.Tendsto (fun n : ℕ => (Real.log n + Real.log (Real.log n) - Real.log 2) / Real.log n) Filter.atTop (nhds 1) by
          refine h_log_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ Real.log_div ( by exact ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ( by positivity ), Real.log_mul ( by exact ne_of_gt <| Nat.cast_pos.mpr <| pos_of_gt hn ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] );
        -- We can use the fact that $\frac{\log \log n}{\log n}$ tends to $0$ as $n$ tends to infinity.
        have h_log_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
          -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
          suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
            exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
          suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
            exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num +zetaDelta at *;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        ring_nf;
        simpa using Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hx ) ) ) ] ) ) ( Filter.Tendsto.sub h_log_log ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) );
      refine h_log_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ Real.log_sqrt ( by exact div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hn.le ) ) ) zero_le_two ) ] ; ring );
    rw [ Asymptotics.isEquivalent_iff_exists_eq_mul ];
    refine' ⟨ fun n => ( Real.log ( Real.sqrt ( n * Real.log n / 2 ) ) / ( Real.log n / 2 ) ) ⁻¹, _, _ ⟩ <;> norm_num [ div_eq_mul_inv ] at *;
    · simpa using h_log_simplify.inv₀ ( by norm_num ) |> Filter.Tendsto.congr ( by intros; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] );
    · filter_upwards [ h_log_simplify.eventually_ne one_ne_zero ] with n hn using by by_cases h : Real.log n = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  convert h_simplify using 2 ; norm_num ; ring_nf;
  grind

lemma pi_A_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ)) ~[atTop] (fun n => 2 * Real.sqrt n / Real.log n) := by
  -- By the asymptotic equivalence, we can replace `Nat.floor (Real.sqrt n)` with `Real.sqrt n`.
  have h_floor_sqrt : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt n) : ℕ) : ℝ)) ~[Filter.atTop] (fun n : ℕ => Real.sqrt n / Real.log (Real.sqrt n)) := by
    have h_pi_sqrt : (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ)) ~[atTop] (fun x : ℝ => x / Real.log x) := by
      exact pi_asymp_lemma
    generalize_proofs at *; (
    exact h_pi_sqrt.comp_tendsto ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun n hn => Real.le_sqrt_of_sq_le <| Nat.le_of_ceil_le hn ⟩ ));
  convert h_floor_sqrt using 2 ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring

set_option maxHeartbeats 0 in
lemma safe_primes_length_asymp : (fun n => ((safe_primes n).length : ℝ)) =Θ[atTop] (fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
  -- By definition of $safe_primes$, we know that its length is $\pi(B_n) - \pi(A_n)$ where $A_n = \lfloor \sqrt{n} \rfloor$ and $B_n = \lfloor \sqrt{n \log n / 2} \rfloor$.
  have h_length : ∀ᶠ n in Filter.atTop, (safe_primes n).length = (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) : ℝ) - (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ) := by
    have h_length : ∀ᶠ n in Filter.atTop, (safe_primes n).length = (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) : ℝ) - (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ) := by
      have h_eventually : ∀ᶠ n in Filter.atTop, Nat.floor (Real.sqrt n) < Nat.floor (Real.sqrt (n * Real.log n / 2)) := by
        -- We'll use that $Real.sqrt (n * Real.log n / 2) > Real.sqrt n$ for sufficiently large $n$.
        have h_sqrt_ineq : ∀ᶠ n in Filter.atTop, Real.sqrt (n * Real.log n / 2) > Real.sqrt n + 1 := by
          -- We'll use that $Real.sqrt (n * Real.log n / 2) > Real.sqrt n + 1$ for sufficiently large $n$. Squaring both sides, we get $n * Real.log n / 2 > n + 2 * Real.sqrt n + 1$.
          have h_sqrt_ineq : ∀ᶠ n in Filter.atTop, n * Real.log n / 2 > n + 2 * Real.sqrt n + 1 := by
            -- We'll use that $Real.log n$ grows faster than $2 + 4 / Real.sqrt n + 2 / n$.
            have h_log_growth : Filter.Tendsto (fun n : ℝ => Real.log n - (2 + 4 / Real.sqrt n + 2 / n)) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.atTop_add ( Real.tendsto_log_atTop ) ( Filter.Tendsto.neg ( Filter.Tendsto.add ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2 + 1, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ ) ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) );
            filter_upwards [ h_log_growth.eventually_gt_atTop 0, Filter.eventually_gt_atTop 0 ] with n hn hn';
            ring_nf at hn ⊢;
            nlinarith [ inv_pos.2 hn', inv_pos.2 ( Real.sqrt_pos.2 hn' ), mul_inv_cancel₀ ( ne_of_gt hn' ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.2 hn' ) ), Real.sqrt_nonneg n, Real.sq_sqrt hn'.le, mul_pos hn' ( Real.sqrt_pos.2 hn' ), mul_pos hn' ( inv_pos.2 ( Real.sqrt_pos.2 hn' ) ), mul_pos ( Real.sqrt_pos.2 hn' ) ( inv_pos.2 hn' ) ];
          filter_upwards [ h_sqrt_ineq, Filter.eventually_gt_atTop 0 ] with n hn hn' using Real.lt_sqrt_of_sq_lt <| by nlinarith [ Real.mul_self_sqrt hn'.le ] ;
        filter_upwards [ h_sqrt_ineq, Filter.eventually_gt_atTop 1 ] with n hn hn' using Nat.le_floor <| by push_cast; linarith [ Nat.floor_le <| Real.sqrt_nonneg n ] ;
      have h_length : ∀ᶠ n in Filter.atTop, (safe_primes n).length = Finset.card (Finset.filter Nat.Prime (Finset.Ioc (Nat.floor (Real.sqrt n)) (Nat.floor (Real.sqrt (n * Real.log n / 2)))) ) := by
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; unfold safe_primes ; aesop;
      have h_card_eq : ∀ {a b : ℕ}, a ≤ b → (Finset.filter Nat.Prime (Finset.Ioc a b)).card = (Nat.primeCounting b : ℝ) - (Nat.primeCounting a : ℝ) := by
        intros a b hab
        simp [Nat.primeCounting];
        simp +decide [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        rw [ show ( Finset.filter Nat.Prime ( Finset.Ioc a b ) ) = Finset.filter Nat.Prime ( Finset.range ( b + 1 ) ) \ Finset.filter Nat.Prime ( Finset.range ( a + 1 ) ) from ?_, Finset.card_sdiff ];
        · rw [ Nat.cast_sub ] <;> norm_num [ Finset.inter_eq_left.mpr ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ hab ) ];
          · rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ hab ) ];
          · exact Finset.card_mono <| Finset.inter_subset_right;
        · ext; simp [Finset.mem_Ioc, Finset.mem_range, Finset.mem_sdiff];
          grind +ring;
      filter_upwards [ h_length, h_eventually.natCast_atTop ] with n hn hn' using by rw [ hn, h_card_eq hn'.le ] ;
    convert h_length using 1;
  have h_length_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) : ℝ) - (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ)) ~[Filter.atTop] (fun n : ℕ => Real.sqrt 2 * Real.sqrt (n / Real.log n)) := by
    have h_length_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt (n * Real.log n / 2))) : ℝ)) ~[Filter.atTop] (fun n : ℕ => Real.sqrt 2 * Real.sqrt (n / Real.log n)) := by
      convert pi_B_asymp using 1;
    have h_length_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ)) =o[Filter.atTop] (fun n : ℕ => Real.sqrt 2 * Real.sqrt (n / Real.log n)) := by
      have h_pi_A_asymp : (fun n : ℕ => (Nat.primeCounting (Nat.floor (Real.sqrt n)) : ℝ)) ~[Filter.atTop] (fun n : ℕ => 2 * Real.sqrt n / Real.log n) := by
        convert pi_A_asymp using 1;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
      · have h_pi_A_asymp : Filter.Tendsto (fun n : ℕ => (2 * Real.sqrt n / Real.log n) / (Real.sqrt 2 * Real.sqrt (n / Real.log n))) Filter.atTop (nhds 0) := by
          -- Simplify the expression inside the limit.
          suffices h_simplify : Filter.Tendsto (fun n : ℕ => (2 / Real.sqrt 2) * (Real.sqrt (Real.log n))⁻¹) Filter.atTop (nhds 0) by
            refine h_simplify.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
            field_simp [mul_comm, mul_assoc, mul_left_comm];
            rw [ Real.sqrt_div ( by positivity ), div_eq_div_iff ] <;> ring_nf <;> norm_num [ ne_of_gt, Real.log_pos, hn ];
            · rw [ mul_right_comm, ← div_eq_mul_inv, Real.div_sqrt ];
              ring;
            · exact ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos <| Nat.one_lt_cast.mpr hn;
            · exact ⟨ ⟨ ⟨ by positivity, by linarith ⟩, by positivity ⟩, ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos <| Nat.one_lt_cast.mpr hn ⟩;
          exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( Real.exp ( x ^ 2 ) ), fun n hn => Real.le_sqrt_of_sq_le <| by simpa using Real.log_le_log ( by positivity ) <| Nat.ceil_le.mp hn ⟩ );
        rw [ Asymptotics.IsEquivalent ] at *;
        rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
        · convert h_pi_A_asymp.add ( ‹Filter.Tendsto ( fun x : ℕ => ( ( x.sqrt.primeCounting : ℝ ) - 2 * Real.sqrt x / Real.log x ) / ( 2 * Real.sqrt x / Real.log x ) ) Filter.atTop ( nhds 0 ) ›.mul ( show Filter.Tendsto ( fun x : ℕ => ( 2 * Real.sqrt x / Real.log x ) / ( Real.sqrt 2 * ( Real.sqrt x / Real.sqrt ( Real.log x ) ) ) ) Filter.atTop ( nhds 0 ) from h_pi_A_asymp ) ) using 2 <;> ring_nf;
          grind;
        · exact ⟨ 2, fun n hn hn' => by rcases hn' with ( rfl | hn' ) <;> norm_num at * ; linarith [ Real.sqrt_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ) ) ] ⟩;
        · exact ⟨ 2, by rintro n hn ( rfl | rfl | hn ) <;> norm_cast at * ⟩;
      · exact ⟨ 2, fun n hn hn' => by rcases hn' with ( rfl | hn' ) <;> norm_num at * ; exact absurd hn' <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ⟩;
    convert Asymptotics.IsEquivalent.sub_isLittleO ‹_› h_length_asymp using 1;
  have h_length_asymp : (fun n : ℕ => (safe_primes n).length : ℕ → ℝ) ~[Filter.atTop] (fun n : ℕ => Real.sqrt 2 * Real.sqrt (n / Real.log n)) := by
    exact h_length_asymp.congr' ( by filter_upwards [ h_length ] with n hn; aesop ) ( by filter_upwards [ h_length ] with n hn; aesop );
  refine' ⟨ _, _ ⟩;
  · rw [ Asymptotics.isBigO_iff ];
    rw [ Asymptotics.IsEquivalent ] at h_length_asymp;
    rw [ Asymptotics.isLittleO_iff ] at h_length_asymp;
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( h_length_asymp one_half_pos ) ; use 2 * Real.sqrt 2; filter_upwards [ Filter.eventually_ge_atTop N ] with n hn; specialize hN n hn; norm_num at *;
    rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] at * ; nlinarith [ abs_le.mp hN, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show 0 ≤ Real.sqrt n / Real.sqrt ( Real.log n ) by positivity ];
  · rw [ Asymptotics.IsEquivalent ] at h_length_asymp;
    rw [ Asymptotics.isLittleO_iff ] at h_length_asymp;
    rw [ Asymptotics.isBigO_iff ];
    obtain ⟨ c, hc ⟩ := Filter.eventually_atTop.mp ( h_length_asymp ( show 0 < 1 / 2 by norm_num ) );
    refine' ⟨ 2 * Real.sqrt 2, Filter.eventually_atTop.mpr ⟨ c + 2, fun n hn => _ ⟩ ⟩ ; specialize hc n ( by linarith ) ; norm_num [ abs_of_nonneg, Real.sqrt_nonneg ] at *;
    nlinarith [ abs_le.mp hc, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( 0 : ℝ ) ≤ Real.sqrt n / Real.sqrt ( Real.log n ) by positivity ]

lemma safe_primes_is_valid : ∀ᶠ n in atTop, is_valid_seq n (construct_seq (safe_primes n)) := by
  -- By combining the results from the previous lemmas, we can conclude the proof.
  apply Filter.eventually_atTop.mpr;
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (safe_primes n).sum ≤ n := by
    exact Filter.eventually_atTop.mp ( safe_primes_sum_le_n ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => hN n hn ⟩;
  use N + 2; intro n hn; refine' construct_seq_is_valid _ _ _ _ _ _ <;> norm_num at *;
  · -- Since the primes are distinct and sorted in descending order, the list is strictly decreasing.
    have h_sorted : List.Sorted (fun x y => x > y) (safe_primes n) := by
      convert List.pairwise_reverse.mpr _;
      exact Finset.sort_sorted_lt _;
    exact List.isChain_iff_pairwise.mpr h_sorted;
  · unfold safe_primes; aesop;
  · unfold safe_primes; aesop;
  · exact hN n ( by linarith )

theorem erdos_648 :
  (fun (n : ℕ) => (g n : ℝ)) =Θ[atTop] (fun (n : ℕ) => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
    by_contra hTheta;
    have h_pnt_ineq : ∀ᶠ n in atTop, (safe_primes n).sum ≤ n := by
      convert safe_primes_sum_le_n using 1;
    apply hTheta;
    refine' ⟨ _, _ ⟩;
    · exact g_upper_bound_asymptotic;
    · have h_g_lower_bound : ∀ᶠ n in atTop, (safe_primes n).length ≤ (g n : ℝ) := by
        filter_upwards [ h_pnt_ineq, safe_primes_is_valid ] with n hn hn';
        refine' mod_cast le_csSup _ _;
        · use n + 1;
          rintro k ⟨ l, hl, rfl ⟩;
          have := hl.1;
          have := List.isChain_iff_pairwise.mp this;
          have := List.toFinset_card_of_nodup ( List.Pairwise.nodup this ) ▸ Finset.card_le_card ( show l.toFinset ⊆ Finset.Icc 0 n from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.zero_le _, by linarith [ hl.2.1 x ( List.mem_toFinset.mp hx ) |>.2 ] ⟩ ) ; aesop;
        · exact ⟨ _, hn', construct_seq_length _ ⟩;
      have h_g_lower_bound : (fun n : ℕ => (safe_primes n).length : ℕ → ℝ) =Θ[atTop] (fun n : ℕ => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))) := by
        exact safe_primes_length_asymp;
      refine' h_g_lower_bound.symm.trans_isBigO _;
      rw [ Asymptotics.isBigO_iff ];
      exact ⟨ 1, by filter_upwards [ ‹∀ᶠ n in Filter.atTop, ( safe_primes n |> List.length : ℝ ) ≤ g n› ] with n hn; rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; linarith ⟩

#print axioms erdos_648
-- 'erdos_648' depends on axioms: [pi_alt, propext, Classical.choice, Quot.sound]
