/-
Below you can find a formalization of (a version of) Mertens third theorem,
which is used in the conditional Lean proofs of Erdős Problems #237
(https://www.erdosproblems.com/237) and #1141
(https://www.erdosproblems.com/1141) that you can find here:

https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean

https://github.com/yuta0x89/ErdosProblems/blob/9eebc7a51466e6ad1b57318302cdc821d30df4ff/Erdos1141.lean

The formalization of Mertens third theorem was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

import Mathlib

set_option linter.style.longLine false
set_option linter.style.refine false

open Finset ArithmeticFunction Real
open scoped BigOperators

set_option maxRecDepth 4000

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
noncomputable def sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
noncomputable def sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
noncomputable def prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-! # Lemma: Central Binomial Coefficient Bounds -/

lemma centralBinom_le_four_pow (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) r ≤ 4 ^ r := by
  rw [show 4 ^ r = (2 : ℕ) ^ (2 * r) by norm_num [pow_mul]]
  rw [← Nat.sum_range_choose]
  exact Finset.single_le_sum (fun x _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by linarith))

lemma choose_odd_le_four_pow (r : ℕ) (_hr : 1 ≤ r) :
    Nat.choose (2 * r + 1) r ≤ 4 ^ r := by
  exact Nat.choose_middle_le_pow r

/-! # LCM helpers -/

lemma lcmRange_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < lcmRange n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma lcmRange_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ lcmRange n := by
  exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hm, hmn ⟩ )

/-! # LCM Divisibility Lemmas -/

set_option linter.flexible false in
lemma lcmRange_dvd_even (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r) ∣ lcmRange r * Nat.choose (2 * r) r := by
  -- By definition of lcmRange, we need to show that for every prime power $p^a$ dividing $m \in (1, 2r]$, $p^a$ divides $lcmRange(r) * \binom{2r}{r}$.
  have h_div : ∀ m ∈ Finset.Icc 1 (2 * r), ∀ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm p hp
    by_cases hpa : p ^ Nat.factorization m p ≤ r;
    · exact dvd_mul_of_dvd_left ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), hpa ⟩ ) ) _;
    · -- Since $p^a > r$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p ^ (Nat.factorization m p - 1) ≤ r := by
        rcases k : Nat.factorization m p with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.1.two_le, Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show m ≥ p ^ ( Nat.factorization m p ) from Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show p ^ ( Nat.factorization m p ) = p * p ^ ‹_› from by rw [ ← pow_succ', k ] ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r)$.
      have hpa_minus_one_div : p ^ (Nat.factorization m p - 1) ∣ lcmRange r := by
        exact lcmRange_dvd_of_le ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hpa_minus_one;
      -- Since $p^a > r$, we have $p \mid \binom{2r}{r}$.
      have hpa_div_choose : p ∣ Nat.choose (2 * r) r := by
        have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p ≥ 1 := by
          have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * r) + 1), (Nat.floor ((2 * r) / p ^ k) - 2 * Nat.floor (r / p ^ k))) := by
            haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine' Finset.sum_congr rfl fun x hx => _;
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine' le_trans _ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from _ ) ) ⟩ ) );
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      convert Finset.lcm_dvd fun p hp => h_div m hm p hp using 1;
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
    rwa [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

set_option linter.flexible false in
lemma lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · refine' dvd_mul_of_dvd_left _ _;
      exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩ );
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          haveI := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine' Finset.card_pos.mpr ⟨ a, _ ⟩ ; norm_num;
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt ha ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        have hpa_div_choose : p ∣ Nat.choose (2 * r + 1) r := by
          contrapose! hpa_div_choose; simp_all +decide ;
        rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ', mul_dvd_mul ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r+1)$.
      have hpa_minus_one_div_lcm : p^(a-1) ∣ lcmRange (r + 1) := by
        have hpa_minus_one_div_lcm : p^(a-1) ∈ Finset.Icc 1 (r + 1) := by
          exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, by linarith ⟩;
        exact Finset.dvd_lcm hpa_minus_one_div_lcm;
      exact dvd_trans hpa_div_choose ( by rw [ mul_comm ] ; exact mul_dvd_mul hpa_minus_one_div_lcm dvd_rfl );
  -- By definition of lcmRange, lcmRange (2 * r + 1) divides the product of all numbers in the range 1 to 2r+1.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r + 1), m ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro m hm; rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ m <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      have := h_prime_power p ( Nat.factorization m p ) hp ( Nat.le_trans ( Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd _ _ ) ) hm.2 ) ; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> simp_all +decide ;
      exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
    · linarith [ Finset.mem_Icc.mp hm ];
    · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
  exact Finset.lcm_dvd fun x hx => h_lcm_div x hx

/-! # LCM Bound: L_n ≤ 4^n -/

lemma lcmRange_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmRange n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine' le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) _;
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine' le_trans ( Nat.le_of_dvd _ h_div ) _;
      · exact mul_pos ( lcmRange_pos _ ( by linarith ) ) ( Nat.choose_pos ( by linarith ) );
      · exact le_trans ( Nat.mul_le_mul ( ih _ ( by linarith ) ( by linarith ) ) h_choose ) ( by ring_nf; norm_num )

/-! # Chebyshev ψ bound -/

set_option linter.flexible false in
lemma chebyshevPsi_eq_log_lcmRange (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n = Real.log (lcmRange n) := by
  -- By definition of ψ, we know that ψ(n) = Σ_{m=0}^n Λ(m)
  have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.log p n * Real.log p := by
    have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p) := by
      unfold chebyshevPsi;
      have h_sum_floor : ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p ^ k)) := by
        have h_sum_floor : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.range (n + 1)) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
          ext m;
          simp [ArithmeticFunction.vonMangoldt];
          constructor;
          · intro hm;
            obtain ⟨ p, k, hp, hk, rfl ⟩ := hm.2.1;
            exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm.1 ⟩, rfl ⟩;
          · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
            exact ⟨ Nat.pow_le_of_le_log ( by linarith ) hk₂, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
        rw [ ← Finset.sum_filter_ne_zero, h_sum_floor, Finset.sum_biUnion ];
        · exact Finset.sum_congr rfl fun p hp => Finset.sum_image <| fun a ha b hb h => Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) h;
        · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
          intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      convert h_sum_floor using 3;
      rw [ ArithmeticFunction.vonMangoldt_apply ];
      rw [ if_pos ];
      · rw [ Nat.Prime.pow_minFac ] <;> aesop;
      · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] );
    aesop;
  -- By definition of $lcmRange$, we know that $lcmRange n = \prod_{p \leq n} p^{e_p(n)}$ where $e_p(n) = \lfloor \log_p n \rfloor$.
  have h_lcm_def : lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
    clear h_psi_def;
    -- By definition of lcmRange, we know that lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n).
    have h_lcmRange_def : ∀ m ∈ Finset.Icc 1 n, m ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
      intro m hm; rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine' Nat.dvd_antisymm _ _;
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      convert Finset.lcm_dvd h_lcmRange_div using 1;
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
  rw [ h_psi_def, h_lcm_def, Nat.cast_prod, Real.log_prod ] <;> aesop

lemma chebyshevPsi_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_log : Real.log (lcmRange n) ≤ Real.log (4 ^ n) := by
    gcongr;
    · exact_mod_cast lcmRange_pos n hn;
    · exact_mod_cast lcmRange_le_four_pow n hn;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, pow_right_comm ] at h_log ; norm_num at *;
  rw [ chebyshevPsi_eq_log_lcmRange n hn ] ; linarith

/-! # S(n) Upper Bound -/

/-
S(n) ≤ (log(n!) + ψ(n)) / n
-/
set_option linter.flexible false in
lemma sumS_le_basic (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≤ (Real.log (n.factorial) + chebyshevPsi n) / n := by
  -- By the properties of logarithms and the definition of S(n), we can rewrite the inequality.
  have h_rewrite : ∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n ≤ Real.log (Nat.factorial n) + ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    -- We'll use that $\sum_{m=1}^n \Lambda(m) \left\lfloor \frac{n}{m} \right\rfloor = \log(n!)$.
    have h_log_factorial : ∑ m ∈ Finset.Icc 1 n, (vonMangoldt m : ℝ) * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
      -- By definition of von Mangoldt function, we know that $\sum_{d \mid m} \Lambda(d) = \log m$.
      have h_von_mangoldt : ∀ m : ℕ, 1 ≤ m → ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = Real.log m := by
        exact fun m a => vonMangoldt_sum;
      -- Applying the definition of von Mangoldt function to the sum.
      have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * Nat.floor (n / d) := by
        have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * (if d ∣ m then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          simp +zetaDelta at *;
          intro x hx₁ hx₂; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.mem_divisors ] ;
          exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hx₁, Nat.le_trans ( Nat.le_of_dvd hx₁ h.1 ) hx₂ ⟩, h.1 ⟩, fun h => ⟨ h.2, by linarith ⟩ ⟩;
        simp_all +decide [ Finset.sum_ite ];
        refine' Finset.sum_congr rfl fun x hx => _;
        rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 n ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( n / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
        · norm_num;
        · ext y; simp [Finset.mem_image];
          exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self n x ] ⟩, by simp +decide ⟩ ⟩;
      rw [ ← h_sum_von_mangoldt, Finset.sum_congr rfl fun m hm => h_von_mangoldt m <| Finset.mem_Icc.mp hm |>.1 ];
      erw [ ← Real.log_prod ] <;> norm_cast <;> norm_num;
      · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
      · grind;
    -- Applying the inequality $\frac{n}{m} \leq \left\lfloor \frac{n}{m} \right\rfloor + 1$ to each term in the sum, we get:
    have h_ineq : ∀ m ∈ Finset.Icc 2 n, (vonMangoldt m : ℝ) * (n / m) ≤ (vonMangoldt m : ℝ) * Nat.floor (n / m) + (vonMangoldt m : ℝ) := by
      intros m hm
      have h_floor : (n / m : ℝ) ≤ Nat.floor (n / m) + 1 := by
        rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n m, Nat.mod_lt n ( by linarith [ Finset.mem_Icc.mp hm ] : 0 < m ), Nat.lt_floor_add_one ( n / m ) ];
      simpa only [ mul_add, mul_one ] using mul_le_mul_of_nonneg_left h_floor <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ;
    refine le_trans ( Finset.sum_le_sum fun m hm => by convert h_ineq m hm using 1 ; ring ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    exact add_le_add ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => mul_nonneg ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg );
  convert div_le_div_of_nonneg_right h_rewrite ( Nat.cast_nonneg n ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ;
  · unfold chebyshevPsi;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num

/-
log(n!) ≤ n*log(n) - n + 1 + log(n)
-/
set_option linter.flexible false in
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_comm ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
  rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

lemma sumS_le_logn_plus (n : ℕ) (hn : 200 ≤ n) :
    sumS n ≤ Real.log n + 0.418 := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : Real.log (n.factorial) + chebyshevPsi n ≤ n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n := by
    linarith [ log_factorial_le n ( by linarith ), chebyshevPsi_le n ( by linarith ) ];
  -- Divide both sides by $n$ and simplify the expression.
  have h_div : sumS n ≤ Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
    convert sumS_le_basic n ( by linarith ) |> le_trans <| div_le_div_of_nonneg_right ( h_final ) ( Nat.cast_nonneg _ ) using 1 ; ring_nf;
    simpa [ show n ≠ 0 by linarith ] using by ring;
  -- We'll use that $Real.log n + 1 \leq Real.log 200 + 1$ for $n \geq 200$.
  have h_log_bound : (Real.log n + 1) / n ≤ (Real.log 200 + 1) / 200 := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) / 200 );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ ( by norm_cast : ( 200 :ℝ ) ≤ n ), Real.le_log_iff_exp_le ( by positivity : ( 0 :ℝ ) < 200 ) |>.2 <| show ( Real.exp 1 :ℝ ) ≤ 200 by exact le_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ];
  -- We'll use that $Real.log 200 < 5.3$.
  have h_log_200 : Real.log 200 < 5.3 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to remove the fraction.
    suffices h_exp : (200 : ℝ) ^ 10 < Real.exp 53 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 53 = ( Real.exp 1 ) ^ 53 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-! # Tail bound -/

/-
-log P(n) ≤ T(n) + 1/10 via log series truncation
-/
set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- The generated tail-bound proof uses large `norm_num` and summability terms.
lemma neg_log_prodP_le_sumT_plus (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) ≤ sumT n + 1/10 := by
  -- Let's rewrite the sum in terms of the prime number theorem and the bound we have.
  have h_sum_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ 1 / 10 := by
    -- For each prime $p$, the tail $\sum_{k > \lfloor \log_p n \rfloor} \frac{1}{k p^k}$ is bounded by $\frac{1}{(K+1)(p-1)p^K}$ where $K = \lfloor \log_p n \rfloor$.
    have h_tail_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
      intro p hp
      have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) := by
        have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) = ∑' k : ℕ, 1 / ((k + 1) * (p : ℝ) ^ (k + 1)) := by
          have := @Real.hasSum_pow_div_log_of_abs_lt_one ( 1 / ( p : ℝ ) ) ?_ <;> norm_num at *;
          · exact this.tsum_eq.symm ▸ rfl;
          · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.2.one_lt;
        erw [ h_tail_bound, ← Summable.sum_add_tsum_nat_add ( Nat.log p n ) ];
        · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          norm_num [ Finset.sum_range_succ' ];
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.2 hp.2.one_lt;
      -- We'll use the fact that $\sum_{k=K+1}^{\infty} \frac{1}{k p^k} \leq \frac{1}{(K+1)p^K} \sum_{k=0}^{\infty} \frac{1}{p^k}$.
      have h_sum_bound : ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) ≤ 1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) * ∑' k : ℕ, (1 / (p : ℝ)) ^ k := by
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hp.2.one_lt ) |> Summable.comp_injective <| by intros a b; aesop;
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      convert h_tail_bound.trans h_sum_bound using 1;
      rw [ tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
      rw [ ← mul_inv ] ; congr ; nlinarith only [ inv_mul_cancel_left₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ( p ^ Nat.log p n ), inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ), show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ;
    -- Split the sum into two parts: one for primes $p \leq 13$ and one for primes $p > 13$.
    have h_split_sum : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ) ^ 1)) := by
      refine le_trans ( Finset.sum_le_sum h_tail_bound ) ?_;
      have h_split_sum : Finset.filter Nat.Prime (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range 14) ∪ Finset.filter Nat.Prime (Finset.Icc 17 n) := by
        simp +decide [ Finset.subset_iff ];
        exact fun p hp₁ hp₂ => if h : p < 14 then Or.inl ⟨ h, hp₂ ⟩ else Or.inr ⟨ ⟨ not_lt.mp fun h' => by interval_cases p <;> trivial, hp₁ ⟩, hp₂ ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split_sum ?_ ) ?_;
      · exact fun _ _ _ => one_div_nonneg.mpr ( mul_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by positivity ) );
      · rw [ Finset.sum_union ];
        · gcongr;
          all_goals norm_num at *;
          any_goals linarith [ Nat.Prime.one_lt ( by tauto ) ];
          · exact mul_pos ( mul_pos two_pos ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_pos.mpr ( by linarith ) );
          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( mod_cast Nat.Prime.pos ( by tauto ) ) );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- For primes $p \leq 13$, we can bound the sum individually.
    have h_small_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) ≤ 1 / 50 := by
      norm_num [ Finset.sum_filter, Finset.sum_range_succ ];
      -- Since $n \geq 200$, we have $\log_2 n \geq 7$, $\log_3 n \geq 4$, $\log_5 n \geq 3$, $\log_7 n \geq 2$, $\log_{11} n \geq 2$, and $\log_{13} n \geq 2$.
      have h_log_bounds : Nat.log 2 n ≥ 7 ∧ Nat.log 3 n ≥ 4 ∧ Nat.log 5 n ≥ 3 ∧ Nat.log 7 n ≥ 2 ∧ Nat.log 11 n ≥ 2 ∧ Nat.log 13 n ≥ 2 := by
        exact ⟨ Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ⟩;
      refine' le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) _ ; norm_num;
      exact le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.1 ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.2 ) ) ( by positivity ) ) ) ( by norm_num );
    -- For primes $p > 13$, we can bound the sum using the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
    have h_large_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ)) ≤ 1 / 32 := by
      -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
      have h_large_primes_bound : ∑ p ∈ Finset.Icc 17 n, (1 / ((p - 1) * (p : ℝ))) ≤ 1 / 16 := by
        -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)}$ is a telescoping series.
        have h_telescoping : ∀ m : ℕ, 17 ≤ m → ∑ p ∈ Finset.Icc 17 m, (1 / ((p - 1) * (p : ℝ))) = 1 / 16 - 1 / (m : ℝ) := by
          intro m hm; induction hm <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 16 _, _ = _› ] ; norm_num;
          -- Combine and simplify the terms on the left-hand side.
          field_simp
          ring;
        exact h_telescoping n ( by linarith ) ▸ sub_le_self _ ( by positivity );
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith [ Finset.mem_Icc.1 ‹_› ] ) ) ) ) ) ( by norm_num ) ) ( by linarith );
    norm_num at * ; linarith;
  convert add_le_add_left h_sum_bound ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ), ∑ k ∈ Finset.Icc 1 ( Nat.log p n ), 1 / ( k * ( p : ℝ ) ^ k ) ) using 1;
  · unfold prodP; rw [ Real.log_prod ] <;> norm_num;
    exact fun p hp hp' => sub_ne_zero_of_ne <| by aesop;
  · rw [ add_comm, sumT ];
    -- Let's rewrite the sum $\sum_{m=2}^n \frac{\Lambda(m)}{m \log m}$ using the definition of $\Lambda$.
    have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p^k) : ℝ) / (p^k * Real.log (p^k)) := by
      have h_sum_eq : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p n))) := by
        ext m; simp [ArithmeticFunction.vonMangoldt];
        constructor;
        · rintro ⟨ ⟨ hm₁, hm₂ ⟩, hm₃, hm₄, hm₅, hm₆ ⟩;
          obtain ⟨ p, k, hp, hk, rfl ⟩ := hm₃;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm₂ ⟩, rfl ⟩;
        · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
          exact ⟨ ⟨ one_lt_pow₀ hp₂.one_lt ( by linarith ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
      have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ m ∈ Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n), (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      rw [ h_sum_eq, ‹ { m ∈ Icc 2 n | Λ m ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    rw [ h_sum_eq ];
    refine' congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => _ );
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.pow_minFac ] <;> norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
      · rw [ Nat.Prime.minFac_eq ( Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ), one_mul ];
      · grind;
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hk ] )

/-! ### Helper lemmas for sumT_sub_199_bound -/

set_option linter.flexible false in
private lemma log_factorial_ge' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≥ n * Real.log n - n + 1 := by
  induction hn <;> simp_all +decide [ Nat.factorial ]
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm; rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ]
    nlinarith [ Real.add_one_le_exp ( 1 / ( m : ℝ ) ), one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ]
  have := h_log _ ‹_›; norm_num at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ]

set_option linter.flexible false in
private lemma sumS_ge_log_sub_one (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≥ Real.log n - 1 := by
  have h_sum_floor : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
    have h_sum_floor : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log (Nat.factorial n) := by
      have h_sum_floor : ∀ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log k := by
        exact fun _ _ => vonMangoldt_sum
      rw [ Finset.sum_congr rfl h_sum_floor ]
      exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; linarith
    have h_interchange : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, vonMangoldt d * (if d ∣ k then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      simp +contextual [ Finset.sum_ite ]
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 n ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ <| Nat.dvd_of_mem_divisors hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop
    have h_inner : ∀ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then 1 else 0) = Nat.floor (n / d) := by
      intros d hd
      have h_divisors : Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n) = Finset.image (fun k => d * k) (Finset.Icc 1 (n / d)) := by
        ext k; simp [Finset.mem_image]
        exact ⟨ fun h => ⟨ k / d, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hd |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hd |>.1 ], by nlinarith [ Finset.mem_Icc.mp hd |>.2, Nat.div_mul_le_self n d ] ⟩, by norm_num ⟩ ⟩
      simp_all +decide [ Finset.sum_ite ]
      rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop
    simp_all +decide [ Finset.sum_ite ]
    exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; ring ) h_sum_floor
  have h_floor_le : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) ≤ n * ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := by
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_le_sum fun x hx => _ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]

private lemma sumS_mono {a b : ℕ} (h : a ≤ b) : sumS a ≤ sumS b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right h ) fun _ _ _ ↦ div_nonneg ( by
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( by norm_cast; linarith [ Finset.mem_Icc.mp ‹_› ] )

private lemma div_sub_le_log_sub' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h_mul : b - a ≤ b * (Real.log b - Real.log a) := by
    have := Real.log_le_sub_one_of_pos ( div_pos ha ( show 0 < b by linarith ) )
    rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ a ( by linarith : b ≠ 0 ) ]
  rwa [ div_le_iff₀' ( by linarith ) ]

set_option linter.flexible false in
private lemma sum_log_ratio_le_log_log' (a n : ℕ) (ha : 3 ≤ a) (hn : a ≤ n) :
    ∑ m ∈ Finset.Ico a n,
      (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1) ≤
    Real.log (Real.log n) - Real.log (Real.log a) := by
  have h_term : ∀ m ∈ Finset.Ico a n, (Real.log (m + 1) - Real.log m) / Real.log (m + 1) ≤ Real.log (Real.log (m + 1)) - Real.log (Real.log m) := by
    intro m hm
    rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ]
    convert Real.one_sub_inv_le_log_of_pos _ using 1
    · rw [ inv_div, sub_div, div_self <| ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ]
    · exact div_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) )
  convert Finset.sum_le_sum h_term ; induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top ]
  rename_i k hk ih; linarith [ ih fun m hm₁ hm₂ => h_term m hm₁ ( by linarith ) ]

private lemma log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

set_option linter.flexible false in
private lemma abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction hn with
  | refl =>
    simp [sumS]
    rw [ show ( Finset.Icc 2 200 : Finset ℕ ) = Finset.Icc 2 199 ∪ { 200 } by decide, Finset.sum_union ] <;> norm_num ; ring
  | step hk ih =>
    rename_i k
    simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
    rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 199 k, _ = _› ]
    rw [ Finset.sum_Ico_succ_top ( by linarith ), show sumS ( k + 1 ) = sumS k + Λ ( k + 1 ) / ( k + 1 : ℝ ) from ?_ ]
    · norm_num [ div_eq_mul_inv ] ; ring
    · exact_mod_cast Finset.sum_Ioc_succ_top ( by linarith ) _

/-
T(n) - T(199) ≤ log(log n) - log(log 199) + 27/100, using Abel summation and S(m) ≤ log m + 0.418
-/
lemma sumT_sub_199_bound (n : ℕ) (hn : 200 ≤ n) :
    sumT n ≤ sumT 199 + Real.log (Real.log ↑n) - Real.log (Real.log 199) + 27/100 := by
  -- Step 1: Split sumT
  have h_split : sumT n = sumT 199 + ∑ m ∈ Finset.Icc 200 n, vonMangoldt m / (m * Real.log m) := by
    unfold sumT; erw [ Finset.sum_Ico_consecutive ] <;> norm_cast ; linarith
  rw [h_split]
  -- Step 2: Abel summation identity
  have h_identity := abel_identity_sumT n hn
  -- Step 3: Bound the Abel sum terms
  have h_bound : (∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1))) ≤ (∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1)))) := by
    refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ ?_ <;> norm_num at *
    · have := sumS_le_logn_plus m ( by linarith ) ; ( have := sumS_ge_log_sub_one 199 ( by norm_num ) ; ( norm_num at * ; linarith ) )
    · exact inv_anti₀ ( Real.log_pos <| by norm_cast; linarith ) ( Real.log_le_log ( by norm_cast; linarith ) <| by linarith )
  -- Step 4: Expand and telescope the sum
  have h_expand : ∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log 200 - 1 / Real.log n) := by
    have h_expand : ∀ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
      intro m hm; ring_nf
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ) ] ; ring
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_add_distrib ]
    norm_num [ Finset.sum_Ico_eq_sum_range ]
    rw [ ← Finset.mul_sum _ _ _ ]
    exact congrArg _ ( by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast [ Nat.cast_sub hn ] <;> ring_nf )
  -- Step 5: Apply log ratio telescoping bound
  have h_log_ratio : ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) ≤ Real.log (Real.log n) - Real.log (Real.log 200) := by
    convert sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn using 1
  -- Step 6: Bound the boundary term
  have h_sumS_le : (sumS n - sumS 199) / Real.log n ≤ (Real.log n + 0.418 - (Real.log 199 - 1)) / Real.log n := by
    gcongr
    · exact sumS_le_logn_plus n hn
    · exact sumS_ge_log_sub_one 199 ( by norm_num )
  -- Step 7: Numerical bound
  have h_num : 1 + (1.418 - Real.log 199) / Real.log 200 + Real.log (Real.log 199) - Real.log (Real.log 200) ≤ 27 / 100 := by
    have h_log_diff : Real.log (Real.log 200) - Real.log (Real.log 199) ≥ (Real.log 200 - Real.log 199) / Real.log 200 := by
      exact div_sub_le_log_sub' ( show 0 < Real.log 199 by positivity ) ( show Real.log 199 ≤ Real.log 200 by gcongr ; norm_num )
    ring_nf at *
    nlinarith [ inv_mul_cancel₀ ( show Real.log 200 ≠ 0 by positivity ), Real.log_pos ( show 199 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 200 > 199 by norm_num ), show Real.log 200 ≥ 1418 / 270 from log_200_ge' ]
  -- Step 8: Combine all bounds
  ring_nf at *
  nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), inv_pos.mpr ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ) ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ]

/-
Computational upper bound on T(199)
-/
set_option linter.flexible false in
lemma sumT_199_lt : sumT 199 < 23/10 := by
  -- By definition of sumT, we can rewrite the sum as a sum over prime powers.
  have h_sum_prime_powers : ∀ n : ℕ, sumT n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (1 / (p^k * k : ℝ)) := by
    intro n
    have h_sumT_prime_powers : ∀ m ∈ Finset.Icc 2 n, vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0) := by
      intro m hm
      by_cases hm_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ m = p^k ∧ p^k ≤ n;
      · obtain ⟨ p, k, hp, hk, rfl, hk' ⟩ := hm_prime_power; simp +decide [Finset.sum_ite] ;
        rw [ Finset.sum_eq_single p ];
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num [ hp, hk ];
          · grind +suggestions;
          · exact ⟨ k, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk, Nat.le_log_of_pow_le hp.one_lt hk' ⟩, rfl ⟩, fun x hx => Nat.pow_right_injective hp.one_lt <| Finset.mem_filter.mp hx |>.2.symm ⟩ ⟩;
        · intro q hq hqp; simp_all +decide [ Finset.ext_iff ] ;
          exact Or.inl fun a ha₁ ha₂ ha₃ => hqp <| by have := congr_arg ( ·.factorization ( q : ℕ ) ) ha₃; norm_num at this; have := congr_arg ( ·.factorization ( p : ℕ ) ) ha₃; norm_num at this; aesop;
        · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.two_le, by linarith [ pow_le_pow_right₀ hp.one_lt.le hk ] ⟩, hp ⟩;
      · rw [ ArithmeticFunction.vonMangoldt_apply ];
        rw [ if_neg ];
        · exact Eq.symm ( Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun k hk => if_neg fun h => hm_prime_power ⟨ p, k, Finset.mem_filter.mp hp |>.2, Finset.mem_Icc.mp hk |>.1, h, by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk |>.2, Nat.pow_log_le_self p ( show m ≠ 0 by linarith [ Finset.mem_Icc.mp hm ] ) ] ⟩ );
        · contrapose! hm_prime_power;
          rw [ isPrimePow_nat_iff ] at hm_prime_power ; aesop;
    -- By interchanging the order of summation, we can rewrite the sum.
    have h_interchange : ∑ m ∈ Finset.Icc 2 n, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0)) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (Real.log p) / (p^k * Real.log (p^k)) := by
      simp +decide only [Finset.sum_div _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv ] ;
      exact Finset.sum_congr rfl fun x hx => if_pos ⟨ le_trans ( Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Icc.mp hx ] ) _ ), Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩;
    convert h_interchange using 2;
    · exact Finset.sum_congr rfl fun x hx => h_sumT_prime_powers x hx ▸ rfl;
    · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by aesop ) ) ) ) ) ] ; ring;
  rw [ h_sum_prime_powers ];
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rw [ show ( Finset.filter Nat.Prime ( Finset.Ioc 1 199 ) ) = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199 } by decide ] ; simp +decide ;
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *

/-
Lower bound on log(log 199)
-/
lemma log_log_199_gt : Real.log (Real.log 199) > 163/100 := by
  -- We'll use that $Real.log 199 > 5.11$.
  have h_log_199 : Real.log 199 > 5.11 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 100 to remove the fraction.
    suffices h_exp : Real.exp 511 < 199 ^ 100 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 100 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We can raise both sides to the power of 511 to remove the fraction.
    have : Real.exp 511 ≤ (2.7182818286 : ℝ) ^ 511 := by
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) this _ );
    grind;
  refine' lt_of_lt_of_le _ ( Real.log_le_log ( by positivity ) h_log_199.le );
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 163 = ( Real.exp 1 ) ^ 163 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma neg_log_prodP_bound (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) < Real.log (Real.log n) + 1.095 := by
  have h1 := neg_log_prodP_le_sumT_plus n hn
  have h2 := sumT_sub_199_bound n hn
  have h3 := sumT_199_lt
  have h4 := log_log_199_gt
  -- -log P(n) ≤ T(n) + 1/10
  --           ≤ T(199) + log(log n) - log(log 199) + 27/100 + 1/10
  --           < 23/10 + log(log n) - 163/100 + 27/100 + 1/10
  --           = log(log n) + (2300 + 270 + 100 - 1630)/1000
  --           = log(log n) + 1040/1000 = log(log n) + 1.04
  --           < log(log n) + 1.095
  linarith

/-! # Finite Check -/

lemma prodP_le_of_le {m n : ℕ} (h : m ≤ n) : prodP n ≤ prodP m := by
  unfold prodP;
  rw [ ← Finset.prod_sdiff ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ h ) ];
  exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;

lemma mertens_finite_check (n : ℕ) (hn3 : 3 ≤ n) (hn199 : n ≤ 199) :
    1 / (3 * Real.log n) ≤ prodP n := by
  by_cases hn : n ≤ 10;
  · interval_cases n <;> norm_num [ Finset.prod_filter, Finset.prod_range_succ, prodP ];
    any_goals rw [ inv_mul_le_iff₀ ( by positivity ) ];
    any_goals rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals rw [ ← div_le_iff₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals positivity;
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 5 : ℝ ) / 4 = 1 + 1 / 4 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 1 / 4 ), Real.exp_neg ( 1 / 4 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 4 ) ) ), Real.add_one_le_exp ( 1 / 4 ), Real.add_one_le_exp ( - ( 1 / 4 ) ) ];
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 35 / 24 : ℝ ) = 1 + 11 / 24 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 11 / 24 ), Real.exp_neg ( 11 / 24 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 11 / 24 ) ) ), Real.add_one_le_exp ( 11 / 24 ), Real.add_one_le_exp ( - ( 11 / 24 ) ) ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
    · exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  · by_cases hn : n ≤ 30;
    · -- For $11 \leq n \leq 30$, we use the fact that $prodP(n) \geq prodP(30)$ and $prodP(30) \geq 1/7$.
      have h_prod_bound : prodP n ≥ prodP 30 := by
        exact prodP_le_of_le hn
      have h_prod_30 : prodP 30 ≥ 1 / 7 := by
        unfold prodP; norm_num [ Finset.prod_filter, Finset.prod_range_succ ] ;
      have h_log_bound : 7 ≤ 3 * Real.log 11 := by
        norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ] at *;
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
      have h_final : 1 / (3 * Real.log n) ≤ 1 / 7 := by
        exact one_div_le_one_div_of_le ( by positivity ) ( by linarith [ Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 11 by norm_cast; linarith ) ] )
      exact le_trans h_final (le_trans h_prod_30 h_prod_bound);
    · have h_prodP_199 : prodP 199 ≥ 1 / 10 := by
        unfold prodP; norm_num;
        norm_num [ Finset.prod_filter, Finset.prod_range_succ ];
      have h_log_bound : Real.log n ≥ 10 / 3 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_cast <;> try linarith;
        · exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr ( Nat.pow_le_pow_left ( show n ≥ 31 by linarith ) 3 ) );
        · positivity;
      exact le_trans ( by rw [ div_le_iff₀ ] <;> linarith ) ( h_prodP_199.trans ( prodP_le_of_le ( by linarith ) ) )

/-! # Main Theorem -/

theorem mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  by_cases hn2 : n ≥ 200;
  · have := neg_log_prodP_bound n hn2;
    -- Exponentiating both sides, we get $prodP n > \frac{1}{3 \log n}$.
    have h_exp : prodP n > 1 / (3 * Real.log n) := by
      have h_exp : Real.log (prodP n) > -Real.log (3 * Real.log n) := by
        rw [ Real.log_mul ] <;> norm_num;
        · have h_log3 : Real.log 3 > 1.095 := by
            norm_num [ Real.log_lt_log ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 219 = ( Real.exp 1 ) ^ 219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
          linarith;
        · grind;
      rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] at h_exp;
      · simpa [ Real.exp_neg, Real.exp_log ( show 0 < 3 * Real.log n by exact mul_pos zero_lt_three ( Real.log_pos ( by norm_cast; linarith ) ) ) ] using h_exp;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_filter.mp hp, Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    exact h_exp.le;
  · -- Apply the finite check lemma to conclude the proof.
    apply mertens_finite_check n hn (by linarith)

#print axioms mertens_third_theorem
