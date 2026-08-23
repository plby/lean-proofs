/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 418.
https://www.erdosproblems.com/forum/thread/418

Formalization status:
- Conditional on: computation_lemma_check._native.native_decide.ax_1_1

Informal authors:
- Jerzy Browkin
- Andrzej Schinzel
- ChatGPT 5.1 Pro

Statement authors:
- Formal Conjectures authors
- Salvatore Mercuri

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos418.md
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos418


def IsCototient (m : ℕ) : Prop := ∃ n, m = n - n.totient

def IsNoncototient (m : ℕ) : Prop := ¬ IsCototient m

def m_BS : ℕ := 509203

def Composite (n : ℕ) : Prop := ∃ a b, 1 < a ∧ 1 < b ∧ n = a * b

lemma prime_of_no_small_divisors {n : ℕ}
    (hn : 2 ≤ n)
    (h : ∀ d, 2 ≤ d → d ≤ Nat.sqrt n → ¬ d ∣ n) :
    Nat.Prime n :=
  Nat.prime_def_le_sqrt.mpr ⟨hn, h⟩

set_option maxHeartbeats 5000000 in
-- Exhaustive divisor certificate for the prime 509203.
@[local simp] lemma prime_509203 : Nat.Prime 509203 :=
  prime_of_no_small_divisors (by norm_num) (by
    intro d hd hds
    interval_cases d <;> norm_num)

set_option maxHeartbeats 5000000 in
-- Exhaustive divisor certificate for the prime 127301.
@[local simp] lemma prime_127301 : Nat.Prime 127301 :=
  prime_of_no_small_divisors (by norm_num) (by
    intro d hd hds
    interval_cases d <;> norm_num)

private lemma riesel_covering_congruence (k : ℕ) (_hk : 1 ≤ k) :
    ∃ q ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 2 ^ k * m_BS ≡ 1 [MOD q] := by
  rw [← Nat.mod_add_div k 24]
  norm_num [Nat.ModEq, Nat.mul_mod, Nat.pow_add, Nat.pow_mul, Nat.pow_mod, m_BS]
  have hkmod := Nat.mod_lt k (by norm_num : 0 < 24)
  interval_cases k % 24 <;> norm_num [Nat.ModEq, Nat.mul_mod, Nat.pow_mod, m_BS]

private lemma m_BS_gt_241 : 241 < m_BS := by
  norm_num [m_BS]

theorem riesel_number (k : ℕ) (hk : 1 ≤ k) : Composite (2^k * m_BS - 1) := by
  -- By definition of $m_BS$, we know that $2^k * m_BS - 1$ is divisible
  -- by at least one prime from the set {3, 5, 7, 13, 17, 241}.
  have h_div :
      ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ (2^k * m_BS - 1) := by
    -- For each prime q in the set {3, 5, 7, 13, 17, 241}, we find an
    -- integer a such that 509203 ≡ 2^a (mod q).
    have h_cong :
        ∀ k ≥ 1,
          (∃ q ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ),
            2 ^ k * m_BS ≡ 1 [MOD q]) :=
      riesel_covering_congruence
    obtain ⟨ q, hq₁, hq₂ ⟩ := h_cong k hk
    refine ⟨q, hq₁, ?_⟩
    rw [← Nat.modEq_zero_iff_dvd]
    have hle : 1 ≤ 2 ^ k * m_BS := by
      exact Nat.succ_le_of_lt
        (mul_pos (pow_pos (by decide : 0 < 2) _) (by norm_num [m_BS]))
    simpa using hq₂.sub hle (by norm_num) (Nat.ModEq.refl 1)
  -- Since $p$ is a prime and $p \leq 241$, it follows that $2^k * m_BS - 1$ is composite.
  obtain ⟨p, hp_prime, hp_div⟩ := h_div
  have h_gt : 1 < 2^k * m_BS - 1 := by
    exact lt_tsub_iff_left.mpr ( by
      nlinarith [ Nat.pow_le_pow_right two_pos hk, show m_BS > 1 from by decide ] );
  -- Since $p$ divides $2^k * m_BS - 1$ and $2^k * m_BS - 1 > p$,
  -- it follows that $2^k * m_BS - 1$ is composite.
  have h_composite : p < 2^k * m_BS - 1 := by
    exact lt_of_le_of_lt
      ( Finset.mem_insert.mp hp_prime |> fun x => by aesop_cat )
      ( show 241 < 2 ^ k * m_BS - 1 from lt_tsub_iff_left.mpr <| by
        nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) hk, m_BS_gt_241 ] );
  exact ⟨ p, ( 2 ^ k * m_BS - 1 ) / p, by aesop,
    by nlinarith [ Nat.div_mul_cancel hp_div ],
    by rw [ Nat.mul_div_cancel' hp_div ] ⟩


lemma lemma_half_n (n : ℕ) (h : 4 ∣ n) : (n / 2).totient = n.totient / 2 := by
  rcases h with ⟨ k, rfl ⟩;
  -- Apply the property of the totient function for even numbers: φ(2n) = 2φ(n) if n is even.
  have h_totient_even : Nat.totient (2 * (2 * k)) = 2 * Nat.totient (2 * k) := by
    -- Since $2$ is prime and divides $2k$, we can apply the lemma Nat.totient_mul_of_prime_of_dvd.
    have h_prime_div : Nat.Prime 2 ∧ 2 ∣ 2 * k := by
      norm_num;
    rw [ Nat.totient_mul_of_prime_of_dvd ] <;> tauto;
  grind


lemma phi_mod_4_eq_2_iff_of_even (n : ℕ) (h_even : Even n) (h_gt : 4 < n) :
  n.totient % 4 = 2 ↔ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ n = 2 * p^k := by
    -- Let's consider the prime factorization of $n$. Since $n$ is even, it
    -- must have at least one factor of $2$. Write $n$ as $2^a \cdot m$,
    -- where $m$ is odd.
    obtain ⟨a, m, ha, hm⟩ : ∃ a m, n = 2^a * m ∧ Odd m := by
      -- By definition of prime factorization, every integer can be expressed
      -- as $2^a \cdot m$ where $m$ is odd.
      use Nat.factorization n 2, n / 2^Nat.factorization n 2;
      exact ⟨ Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ),
        Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h₃ =>
          absurd ( Nat.dvd_of_mod_eq_zero h₃ )
            ( Nat.not_dvd_ordCompl ( by norm_num ) ( by linarith ) ) ) ⟩;
    subst ha
    simp_all only [exists_and_left]
    apply Iff.intro
    · intro a_1
      rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.totient_mul, Nat.totient_prime_pow ];
      · -- Since $m$ is both even and odd, this is a contradiction.
        exfalso; exact absurd h_even (by simpa using hm);
      · -- Since $m$ is odd and its totient is $2 \mod 4$, $m$ must have
        -- exactly one prime factor $p$.
        obtain ⟨p, k, hp, hk⟩ : ∃ p k : ℕ, Nat.Prime p ∧ m = p^k := by
          -- If $m$ has more than one prime factor, then $\phi(m)$ would be
          -- divisible by 4, contradicting $\phi(m) \equiv 2 \pmod{4}$.
          by_contra h_contra
          have h_div4 : 4 ∣ Nat.totient m := by
            -- If $m$ has more than one prime factor, then $\phi(m)$ would be
            -- divisible by 4, contradicting $\phi(m) \equiv 2 \pmod{4}$.
            -- Hence, $m$ must have exactly one prime factor.
            have h_prime_factors : (Nat.primeFactors m).card ≥ 2 := by
              by_cases h_prime_factors : (Nat.primeFactors m).card = 1;
              · rw [ Finset.card_eq_one ] at h_prime_factors
                obtain ⟨w, h⟩ := h_prime_factors
                exact False.elim <| h_contra ⟨w, Nat.factorization m w,
                  Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_singleton_self _ ),
                  by
                    nth_rw 1 [ ← Nat.prod_factorization_pow_eq_self hm.pos.ne' ]
                    rw [ Finsupp.prod ]
                    aesop⟩;
              · exact Nat.lt_of_le_of_ne
                  ( Finset.card_pos.mpr ⟨ Nat.minFac m,
                    Nat.mem_primeFactors.mpr
                      ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd m,
                        by linarith ⟩ ⟩ )
                  ( Ne.symm h_prime_factors );
            have h_div4 : ∀ p : ℕ, Nat.Prime p → p ∣ m → ¬m = 0 → 2 ∣ Nat.totient p := by
              intro p hp_prime hp_dvd _hm_ne
              rw [Nat.totient_prime hp_prime]
              exact even_iff_two_dvd.mp (hp_prime.even_sub_one <| by
                rintro rfl
                exact absurd (hm.of_dvd_nat hp_dvd) (by norm_num))
            have h_div4 : 2 ^ (Nat.primeFactors m).card ∣ Nat.totient m := by
              rw [Nat.totient_eq_prod_factorization hm.pos.ne', Finsupp.prod_mul]
              exact dvd_mul_of_dvd_right ( by
                simpa [ Finsupp.prod ] using Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
                  show 2 ∣ p - 1 from by
                    rw [← Nat.totient_prime (Nat.prime_of_mem_primeFactors hp)]
                    exact h_div4 p (Nat.prime_of_mem_primeFactors hp)
                      (Nat.dvd_of_mem_primeFactors hp) hm.pos.ne' ) _;
            exact dvd_trans ( pow_dvd_pow _ h_prime_factors ) h_div4;
          omega;
        rcases k with ( _ | k ) <;> simp_all +decide [ Nat.totient_prime_pow ];
        rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
        · exact absurd hm ( by norm_num [ Nat.even_pow ] );
        · rcases Nat.even_or_odd' c with ⟨ d, rfl | rfl ⟩ <;> ring_nf at * <;>
            norm_num [ Nat.add_mod, Nat.mul_mod ] at *;
          exact ⟨ 3 + d * 4, hp, by norm_num [ Nat.add_mod, Nat.mul_mod ], k + 1, by ring ⟩;
      · rcases a with ( _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
        -- Since $m$ is odd and greater than 1, we have $\phi(m) \equiv 0 \pmod{2}$.
        have h_phi_m_even : 2 ∣ Nat.totient m := by
          exact even_iff_two_dvd.mp ( Nat.totient_even <| Nat.le_of_not_lt fun contra => by
            interval_cases m
            contradiction );
        grind;
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      obtain ⟨w_1, h⟩ := right
      simp_all only [even_two, Even.mul_right]
      -- Since $m$ is odd and $2^a * m = 2 * w^{w_1}$, we must have $a = 1$.
      have ha_one : a = 1 := by
        rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        · exact absurd hm ( by norm_num );
        · have := congr_arg ( · % 2 ) h
          norm_num [ Nat.mul_mod, Nat.pow_mod,
            left.eq_two_or_odd.resolve_left ( by aesop_cat ) ] at this;
      simp_all +decide [ Nat.totient_mul ];
      rw [ Nat.totient_prime_pow left ];
      · rw [ ← Nat.mod_add_div w 4, left_1 ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;
        rcases Nat.even_or_odd' ( w_1 - 1 ) with ⟨ k, hk | hk ⟩ <;>
          norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hk ];
      · contrapose! h_gt; aesop


lemma m_BS_prime : m_BS.Prime := by
  simp [m_BS]

private lemma two_pow_ne_m_BS_plus_one_of_lt_23 (k : ℕ) (hk : k < 23) :
    2 ^ k ≠ m_BS + 1 := by
  interval_cases k <;> norm_num [m_BS]

lemma m_BS_plus_one_not_power_of_two (k : ℕ) : 2 ^ k ≠ m_BS + 1 := by
  intro h;
  exact absurd ( h.symm ▸ pow_dvd_pow _ ( show k ≥ 23 by
    contrapose! h
    exact two_pow_ne_m_BS_plus_one_of_lt_23 k h ) ) ( by decide )

lemma composite_implies_not_prime {n : ℕ} (h : Composite n) : ¬ n.Prime := by
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h; exact Nat.not_prime_mul ( by linarith ) ( by linarith ) ;


lemma inductive_step
    (k : ℕ) (hk : 2 ≤ k) (h_ind : IsNoncototient (2 ^ (k - 1) * m_BS)) :
    IsNoncototient (2 ^ k * m_BS) := by
  -- Assume for contradiction that $2^k * m_BS$ is a cototient.
  by_contra h_contra
  obtain ⟨n, hn⟩ : ∃ n, 2^k * m_BS = n - n.totient := by
    -- By definition of noncototient, if 2^k * m_BS is not a noncototient,
    -- then it must be a cototient.
    unfold IsNoncototient at h_contra; aesop;
  -- Since $k \geq 2$, $2^k * m_BS$ is divisible by 4. So $n - \phi(n)$ is divisible by 4.
  have h_div4 : 4 ∣ n - n.totient := by
    exact hn ▸ dvd_mul_of_dvd_left ( pow_dvd_pow _ hk ) _;
  -- Consider two cases: when $\phi(n)$ is divisible by 4 and when it is not.
  by_cases h_phi_div4 : 4 ∣ n.totient;
  · -- By lemma_half_n, we have $\phi(n/2) = \phi(n)/2$.
    have h_phi_half : n.totient / 2 = (n / 2).totient := by
      rw [ ← lemma_half_n ];
      rw [ eq_tsub_iff_add_eq_of_le ] at hn;
      · exact hn ▸ dvd_add
          ( dvd_mul_of_dvd_left ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk ) ) _ )
          h_phi_div4;
      · exact Nat.totient_le n;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc ];
    exact h_ind ⟨ n / 2, by omega ⟩;
  · -- Since $\phi(n)$ is not divisible by 4 and $n > 4$, we have
    -- $\phi(n) = 2 \mod 4$. By the lemma, this implies $n = 2 * p^a$
    -- where $p$ is a prime congruent to $3 \mod 4$.
    obtain ⟨p, a, hp_prime, hp_mod, hn_eq⟩ :
        ∃ p a, Nat.Prime p ∧ p % 4 = 3 ∧ n = 2 * p^a := by
      have h_phi_mod4 : n.totient % 4 = 2 := by
        -- Since $\phi(n)$ is even and not divisible by 4, we have $\phi(n) \equiv 2 \mod 4$.
        have h_phi_even : Even n.totient := by
          rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.totient_prime ];
          exact Nat.totient_even <| by linarith;
        rw [ Nat.even_iff ] at h_phi_even; omega;
      apply phi_mod_4_eq_2_iff_of_even n (by
      rw [ Nat.even_iff ]
      replace hn := congr_arg Even hn
      simp_all +decide
        [ Nat.even_sub ( show n.totient ≤ n from Nat.totient_le n ), parity_simps ] ;
      cases k <;> simp_all +decide [ Nat.even_iff ];
      omega) (by
      rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp +arith +decide at *) |>.1 h_phi_mod4;
    -- Substitute $n = 2 * p^a$ into the equation $2^k * m_BS = n - n.totient$ and simplify.
    have h_eq : 2 ^ k * m_BS = p ^ (a - 1) * (p + 1) := by
      rcases a with ( _ | a ) <;> simp_all +decide;
      rw [ Nat.totient_mul, Nat.totient_prime_pow ] <;> norm_num [ hp_prime ];
      · exact Nat.sub_eq_of_eq_add <| by cases p <;> norm_num [ pow_succ' ] at * ; linarith;
      · exact hp_prime.odd_of_ne_two <| by aesop_cat;
    -- Consider two subcases: $a = 1$ and $a > 1$.
    by_cases ha : a = 1;
    · -- Substitute $a = 1$ into the equation $2^k * m_BS = p^(a-1) * (p + 1)$ and simplify.
      subst ha
      have h_eq_simplified : 2^k * m_BS = p + 1 := by
        simpa using h_eq;
      -- By the lemma, $2^k * m_BS - 1$ is composite.
      have h_composite : ¬Nat.Prime (2^k * m_BS - 1) := by
        apply composite_implies_not_prime;
        convert riesel_number k ( by linarith ) using 1;
      exact h_composite ( by simpa [ h_eq_simplified ] using hp_prime );
    · -- Since $a > 1$, we have $p \mid 2^k * m_BS$. Since $p$ is odd, $p \mid m_BS$.
      have hp_div_m_BS : p ∣ m_BS := by
        have hp_div_m_BS : p ∣ 2^k * m_BS := by
          exact h_eq.symm ▸ dvd_mul_of_dvd_left
            ( dvd_pow_self _ ( Nat.sub_ne_zero_of_lt
              ( lt_of_le_of_ne
                ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) )
                ( Ne.symm ha ) ) ) ) _;
        exact Or.resolve_left ( hp_prime.dvd_mul.mp hp_div_m_BS ) ( by
          intro t
          have := Nat.Prime.dvd_of_dvd_pow hp_prime t
          simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] );
      -- Since $p$ is prime and $p \mid m_BS$, we have $p = m_BS$.
      have hp_eq_m_BS : p = m_BS := by
        have := Nat.prime_dvd_prime_iff_eq hp_prime m_BS_prime ; aesop;
      -- Substitute $p = m_BS$ into the equation
      -- $2^k * m_BS = p^(a-1) * (p + 1)$ and simplify.
      have h_eq_simplified : 2^k = m_BS^(a-2) * (m_BS + 1) := by
        -- Substitute $p = m_BS$ into the equation and simplify by dividing
        -- both sides by $m_BS$.
        rw [hp_eq_m_BS] at h_eq;
        rcases a with ( _ | _ | a ) <;> simp +decide [ pow_succ' ] at *;
        · grind;
        · nlinarith [ Nat.Prime.pos m_BS_prime ];
      -- Since $m_BS$ is prime and $m_BS + 1$ is not a power of 2, we have a contradiction.
      have h_contradiction : ¬∃ k, m_BS + 1 = 2^k := by
        exact fun ⟨ k, hk ⟩ => by have := m_BS_plus_one_not_power_of_two k; aesop;
      have h_contradiction : m_BS + 1 ∣ 2^k := by
        exact h_eq_simplified.symm ▸ dvd_mul_left _ _;
      rw [ Nat.dvd_prime_pow ] at h_contradiction <;> norm_num at * ; aesop


lemma totient_le_half_of_even (n : ℕ) (h_even : Even n) (h_pos : 0 < n) : n.totient ≤ n / 2 := by
  -- Since $n$ is even, we can write $n = 2k$ for some integer $k$.
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := even_iff_two_dvd.mp h_even;
  -- Since $k$ is even, the set of numbers coprime with $2k$ is a subset of
  -- the odd numbers up to $2k$.
  have h_subset :
      Finset.filter (fun a => Nat.Coprime (2 * k) a) (Finset.range (2 * k)) ⊆
        Finset.image (fun a => 2 * a + 1) (Finset.range k) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_image]
    exact ⟨ a / 2,
      by
        exact Finset.mem_range.mpr <|
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 (by
            simpa [mul_comm] using ha.1),
      by
        have hmod : a % 2 = 1 := Nat.mod_two_ne_zero.mp fun h => by
            have := Nat.dvd_gcd ( dvd_mul_right 2 k ) ( Nat.dvd_of_mod_eq_zero h )
            aesop
        linarith [Nat.mod_add_div a 2, hmod] ⟩;
  exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( by norm_num ) )

lemma n_le_four_m (n : ℕ) (h : n - n.totient = 2 * m_BS) : n ≤ 4 * m_BS := by
  -- Assume n is odd. Then φ(n) is even (for n > 2), so n - φ(n) is odd - even = odd.
  by_cases h_odd : Odd n;
  · -- If n is odd, then φ(n) is even (for n > 2), so n - φ(n) is odd - even = odd.
    have h_phi_even : Even (Nat.totient n) := by
      rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.totient_even ];
    rw [ Nat.sub_eq_iff_eq_add ] at h;
    · obtain ⟨ k, hk ⟩ := h_phi_even
      replace h := congr_arg Even h
      simp_all +decide [ parity_simps ] ;
      exact absurd h ( by simpa using h_odd );
    · exact Nat.totient_le n;
  · -- If n is even, then φ(n) ≤ n / 2.
    have h_phi_even : n.totient ≤ n / 2 := by
      -- Since n is even, the numbers coprime to n are exactly the odd numbers
      -- less than n. There are n/2 such numbers.
      have h_odd_count :
          Finset.card (Finset.filter (fun x => Nat.gcd x n = 1) (Finset.range n)) ≤
            Finset.card (Finset.filter (fun x => x % 2 = 1) (Finset.range n)) := by
        exact Finset.card_mono fun x hx => Finset.mem_filter.mpr
          ⟨ Finset.mem_filter.mp hx |>.1,
            Nat.mod_two_ne_zero.mp fun contra => by
              have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero contra )
                ( even_iff_two_dvd.mp ( by simpa using h_odd ) )
              aesop ⟩;
      -- The set of odd numbers less than n has cardinality n / 2.
      have h_odd_card :
          Finset.card (Finset.filter (fun x => x % 2 = 1) (Finset.range n)) =
            n / 2 := by
        rw [ Finset.card_eq_of_bijective ];
        focus
          use fun i hi => 2 * i + 1
        · intro a ha
          rw [Finset.mem_filter] at ha
          rw [Finset.mem_range] at ha
          exact ⟨ a / 2,
            by
              linarith [ Nat.mod_add_div a 2,
                Nat.div_mul_cancel ( even_iff_two_dvd.mp (by simpa using h_odd) ) ],
            by linarith [ Nat.mod_add_div a 2 ] ⟩;
        · exact fun i hi => Finset.mem_filter.mpr
            ⟨ Finset.mem_range.mpr ( by linarith [ Nat.div_mul_le_self n 2 ] ),
              by norm_num [ Nat.add_mod ] ⟩;
        · -- If $2i + 1 = 2j + 1$, then subtracting 1 from both sides gives
          -- $2i = 2j$, and dividing by 2 gives $i = j$.
          intros i j hi hj h_eq
          linarith
      simpa [Nat.totient_eq_card_coprime, Nat.Coprime, Nat.gcd_comm] using
        h_odd_count.trans h_odd_card.le
    omega

private lemma not_four_dvd_two_mul_m_BS : ¬ 4 ∣ 2 * m_BS := by
  norm_num [m_BS]

lemma not_dvd_four (n : ℕ) (h : n - n.totient = 2 * m_BS) : ¬ 4 ∣ n := by
  -- Assume for contradiction that 4 divides n.
  by_contra h_div4
  have h_even : Even n := by
    -- If 4 divides n, then n is even because 4 is even.
    exact even_iff_two_dvd.mpr ( dvd_trans ( by decide ) h_div4 );
  have h_phi_div4 : 4 ∣ n.totient := by
    -- Since $n$ is divisible by 4, we can write $n = 4k$ for some integer $k$.
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := h_div4;
    -- Since $4k$ is divisible by 4, we have
    -- $\phi(4k) = \phi(4) \cdot \phi(k) = 2 \cdot \phi(k)$.
    have h_phi_4k : Nat.totient (4 * k) = 2 * Nat.totient (2 * k) := by
      rw [ show 4 * k = 2 * ( 2 * k ) by ring,
        Nat.totient_mul_of_prime_of_dvd ] <;> norm_num;
    rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
    exact mul_dvd_mul_left 2
      ( even_iff_two_dvd.mp ( Nat.totient_even <| by linarith ) );
  -- Since $4 \mid n$ and $4 \mid n.totient$, their difference
  -- $n - n.totient$ must also be divisible by 4.
  have h_diff_div4 : 4 ∣ (n - n.totient) := by
    exact Nat.dvd_sub h_div4 h_phi_div4;
  exact not_four_dvd_two_mul_m_BS (h ▸ h_diff_div4)


lemma base_case_reduction : IsCototient (2 * m_BS) ↔ ∃ m, Odd m ∧ 2 * m - m.totient = 2 * m_BS := by
  -- Assume 2 * m_BS is a cototient. Then there exists an n such that 2 * m_BS = n - phi(n).
  apply Iff.intro
  · intro h_cototient
    obtain ⟨n, hn⟩ := h_cototient
    have hn_even : Even n := by
      -- Since $2 * m_BS$ is even, $n - n.totient$ must also be even. If $n$
      -- were odd, then $n.totient$ would be even, making $n - n.totient$ odd,
      -- which contradicts $2 * m_BS$ being even. Hence, $n$ must be even.
      have h_even : Even (n - n.totient) := by
        exact hn ▸ even_two_mul _;
      cases le_total n ( n.totient ) <;> simp_all +decide [ parity_simps ];
      by_contra h_odd;
      exact h_odd <| Nat.totient_even <| Nat.le_of_not_lt fun h => by
        interval_cases n <;> contradiction;
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
      exact even_iff_two_dvd.mp hn_even
    have hm_odd : Odd m := by
      -- Since $2 * m - 2 * m_BS$ is even and $2 * m_BS$ is even, $2 * m$
      -- must be even. Therefore, $m$ must be odd.
      by_contra hm_even
      have h_div_four : 4 ∣ 2 * m := by
        exact mul_dvd_mul_left 2 ( even_iff_two_dvd.mp ( by simpa using hm_even ) );
      exact not_dvd_four ( 2 * m ) ( by omega ) h_div_four
    use m
    constructor
    · exact hm_odd
    · rw [ Nat.totient_mul ] at hn
      · norm_num [ hm_odd ] at hn
        omega
      · exact hm_odd.coprime_two_left
  · rintro ⟨m, hm_odd, hm⟩
    -- Let $n = 2m$. Then, $\phi(n) = \phi(2m) = \phi(2) \cdot \phi(m)$,
    -- which equals $\phi(m)$.
    use 2 * m
    rw [ ← hm, Nat.totient_mul ]
    · norm_num
    · exact hm_odd.coprime_two_left


lemma m_BS_is_prime : Nat.Prime m_BS := by
  simp [m_BS]

lemma m_BS_plus_one_div_four : (m_BS + 1) / 4 = 127301 := by decide

lemma p_127301_prime : Nat.Prime 127301 := by
  exact prime_127301

def IsSolution (m : ℕ) : Prop := Odd m ∧ 2 * m - m.totient = 2 * m_BS

lemma solution_bounds (m : ℕ) (h : IsSolution m) : m_BS < m ∧ m < 2 * m_BS := by
  cases h;
  -- Since $m$ is odd and greater than 1, we have $\varphi(m) \geq 1$.
  have h_phi_ge_one : 1 ≤ m.totient := by
    -- Since $m$ is a positive integer, the totient function $\phi(m)$ is always at least 1.
    apply Nat.pos_of_ne_zero
    intro h_zero
    aesop;
  -- Since $m$ is odd and greater than 1, we have $\varphi(m) < m$.
  have h_phi_lt_m : m.totient < m := by
    -- Since $m$ is odd and greater than 1, we can apply the lemma that states
    -- $\varphi(m) < m$ for any $m > 1$.
    have h_phi_lt_m : 1 < m → m.totient < m := by
      exact fun h => Nat.totient_lt m h;
    rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
  omega


lemma solution_squarefree (m : ℕ) (h : IsSolution m) : Squarefree m := by
  -- Assume m is not squarefree. Then there exists a prime p such that p² divides m.
  by_contra h_not_squarefree
  obtain ⟨p, hp_prime, hp_sq⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ m := by
    simpa only [ pow_two ] using by rw [ Nat.squarefree_iff_prime_squarefree ] at *; aesop;
  -- Since $p$ is odd and $p^2 \mid m$, we have $p \mid m$ and $p \mid \phi(m)$.
  have hp_div_m : p ∣ m := by
    exact dvd_of_mul_left_dvd hp_sq
  have hp_div_phi : p ∣ m.totient := by
    refine Nat.dvd_trans ?_ ( Nat.totient_dvd_of_dvd hp_sq );
    norm_num [ Nat.totient_prime_pow hp_prime (by norm_num : 0 < 2) ];
  -- Since $p$ divides $2 * m_BS$ and $m_BS$ is prime, $p$ must be either $2$
  -- or $m_BS$. However, $m$ is odd, so $p$ cannot be $2$. Thus, $p = m_BS$.
  have hp_eq_m_BS : p = m_BS := by
    -- Since $p$ divides $2 * m_BS$ and $p$ is prime, $p$ must divide either
    -- $2$ or $m_BS$. Since $m$ is odd, $p$ cannot be $2$.
    have hp_div_m_BS : p ∣ m_BS := by
      have hp_div_2m_BS : p ∣ 2 * m_BS := by
        -- Since $p \mid m$ and $p \mid \phi(m)$, we have
        -- $p \mid 2m - \phi(m) = 2m_BS$ by divisibility.
        have hp_div_2m_BS : p ∣ 2 * m - m.totient := by
          exact Nat.dvd_sub ( dvd_mul_of_dvd_right hp_div_m _ ) hp_div_phi
        simpa [h.2] using hp_div_2m_BS
      -- Since $p$ is odd and $p \mid 2 * m_BS$, it must divide $m_BS$
      -- because $p$ cannot divide $2$.
      have hp_div_m_BS : p ∣ 2 * m_BS → p ≠ 2 → p ∣ m_BS := by
        -- Since $p$ is a prime and $p \neq 2$, it must divide $m_BS$.
        intros hp_div_2m_BS hp_ne_2
        have hp_div_m_BS : p ∣ 2 * m_BS → p ≠ 2 → p ∣ m_BS := by
          intro hp_div_2m_BS hp_ne_2
          have hp_div_factor : p ∣ 2 ∨ p ∣ m_BS := by
            exact hp_prime.dvd_mul.mp hp_div_2m_BS
          exact hp_div_factor.resolve_left fun h => hp_ne_2 <| by
            have := Nat.le_of_dvd ( by decide ) h
            interval_cases p <;> trivial;
        -- Apply the lemma that if p divides 2*m_BS and p is not 2, then p divides m_BS.
        exact hp_div_m_BS hp_div_2m_BS hp_ne_2
      exact hp_div_m_BS hp_div_2m_BS ( by
        rintro rfl
        exact absurd (h.1.of_dvd_nat hp_div_m) (by norm_num))
    have := Nat.prime_dvd_prime_iff_eq hp_prime m_BS_prime; aesop;
  -- Since $m_BS^2 \mid m$, we have $m \geq m_BS^2$.
  have hm_ge_m_BS_sq : m ≥ m_BS^2 := by
    exact Nat.le_of_dvd
      ( Nat.pos_of_ne_zero ( by rintro rfl; cases h; aesop ) )
      ( hp_eq_m_BS ▸ hp_sq );
  exact not_lt_of_ge hm_ge_m_BS_sq ( by nlinarith only [ solution_bounds m h ] )


lemma totient_mod_3_of_squarefree_not_dvd_3
    (n : ℕ) (h_sq : Squarefree n) (h_nd : ¬ 3 ∣ n) :
    n.totient % 3 ≠ 2 := by
  -- Since $n$ is squarefree and not divisible by 3, each prime factor $p$ of
  -- $n$ is either 1 or 2 modulo 3.
  have h_prime_factors : ∀ p ∈ Nat.primeFactors n, p % 3 = 1 ∨ p % 3 = 2 := by
    intro p hp
    have := Nat.mod_lt p three_pos
    interval_cases _ : p % 3 <;>
      simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq ] ;
  -- Since $n$ is squarefree and not divisible by 3, each prime factor $p$ is
  -- either 1 or 2 modulo 3. Therefore, $\phi(n)$ is the product of $(p-1)$.
  have h_phi_factors : n.totient = ∏ p ∈ Nat.primeFactors n, (p - 1) := by
    rw [ Nat.totient_eq_prod_factorization ];
    · exact Finset.prod_congr rfl fun p hp => by
        rw [ Nat.factorization_eq_one_of_squarefree ] <;> aesop;
    · aesop_cat;
  -- Since each term (p-1) is either 0 or 1 modulo 3, the product of these
  -- terms can only be 0 or 1 modulo 3.
  have h_prod_mod : ∀ p ∈ Nat.primeFactors n, (p - 1) % 3 = 0 ∨ (p - 1) % 3 = 1 := by
    intro p hp; specialize h_prime_factors p hp; omega;
  -- If there exists a prime factor $p$ such that $(p - 1) \equiv 0 \pmod{3}$,
  -- then the product is $0 \pmod{3}$.
  by_cases h_zero : ∃ p ∈ Nat.primeFactors n, (p - 1) % 3 = 0;
  · obtain ⟨ p, hp₁, hp₂ ⟩ := h_zero
    rw [ h_phi_factors, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hp₁ ]
    norm_num [ Nat.mul_mod, hp₂ ] ;
  · rw [ h_phi_factors, Finset.prod_nat_mod ];
    rw [ Finset.prod_congr rfl fun x hx =>
      Or.resolve_left ( h_prod_mod x hx ) fun hx' => h_zero ⟨ x, hx, hx' ⟩ ]
    norm_num


lemma n_not_div_3 (m : ℕ) (h : IsSolution m) : ¬ 3 ∣ 2 * m := by
  -- Since $m$ is not divisible by 3, $2m$ cannot be divisible by 3 either.
  have h_not_div_3 : ¬(3 ∣ m) := by
    -- Suppose for contradiction that 3 divides m. Then m = 3k for some integer k.
    by_contra h_div_3
    obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := h_div_3;
    -- Since m is squarefree, k is not divisible by 3.
    have h_k_not_div_3 : ¬(3 ∣ k) := by
      have hsq := solution_squarefree (3 * k) h
      rw [Nat.squarefree_mul_iff] at hsq
      exact fun h3k => by
        have hdiv : 3 ∣ Nat.gcd 3 k := Nat.dvd_gcd (by decide : 3 ∣ 3) h3k
        rw [hsq.1] at hdiv
        norm_num at hdiv
    -- Since $m$ is squarefree, $k$ is not divisible by 3, and thus $\phi(k) \neq 2 \mod 3$.
    have h_phi_k_ne_2_mod_3 : (Nat.totient k) % 3 ≠ 2 := by
      -- Since $k$ is squarefree and not divisible by 3, we can apply
      -- totient_mod_3_of_squarefree_not_dvd_3.
      have h_k_squarefree : Squarefree k := by
        have hsq := solution_squarefree (3 * k) h
        rw [Nat.squarefree_mul_iff] at hsq
        exact hsq.2.2
      exact totient_mod_3_of_squarefree_not_dvd_3 k h_k_squarefree h_k_not_div_3;
    unfold IsSolution at h;
    rw [ Nat.totient_mul ] at h <;> simp_all +arith +decide [ Nat.totient_prime ];
    · unfold m_BS at h; omega;
    · exact Nat.prime_three.coprime_iff_not_dvd.mpr h_k_not_div_3;
  -- Since 3 is prime, if it divides 2m, it must divide either 2 or m. It
  -- does not divide 2, and `h_not_div_3` says it does not divide m.
  exact fun h_div =>
    h_not_div_3 (Nat.prime_three.dvd_mul.mp h_div |> Or.resolve_left <| by norm_num)

lemma n_mod_12_eq_2 (m : ℕ) (h : IsSolution m) : 2 * m % 12 = 2 := by
  -- Assume 3 | 2m. Since m is odd, 3 | m.
  by_cases h3 : 3 ∣ m;
  · -- Since m is squarefree (by solution_squarefree), m = 3k with gcd(3,k)=1.
    obtain ⟨k, hk⟩ : ∃ k, m = 3 * k ∧ Nat.gcd 3 k = 1 := by
      obtain ⟨ k, rfl ⟩ := h3;
      have := solution_squarefree ( 3 * k ) h; simp_all +decide [ Nat.squarefree_mul_iff ] ;
    -- Since $k$ is not divisible by 3, $\phi(k)$ is even. Therefore,
    -- $3k - \phi(k) \equiv 1 \mod 3$ implies
    -- $\phi(k) \equiv 2 \mod 3$, a contradiction.
    have h_contra : Nat.totient k % 3 = 2 := by
      have h_contra : 3 * k - Nat.totient k = m_BS := by
        have h_eq : 2 * (3 * k) - Nat.totient (3 * k) = 2 * m_BS := by
          simpa [hk.1] using h.2
        rw [Nat.totient_mul (by simpa [Nat.Coprime] using hk.2)] at h_eq
        norm_num [Nat.totient_prime] at h_eq
        omega
      rw [ Nat.sub_eq_iff_eq_add ] at h_contra;
      · have := congr_arg ( · % 3 ) h_contra
        norm_num [ Nat.add_mod, Nat.mul_mod ] at this
        have := Nat.mod_lt ( Nat.totient k ) zero_lt_three
        interval_cases Nat.totient k % 3 <;> trivial;
      · exact le_trans ( Nat.totient_le _ ) ( by linarith );
    exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 k ( by
      have hsq_m := solution_squarefree m h
      exact hsq_m.squarefree_of_dvd (by
        rw [hk.1]
        exact dvd_mul_left _ _) ) ( by
      exact fun h => by
        have := Nat.dvd_gcd ( by decide : 3 ∣ 3 ) h
        simp_all +decide ; ) ) ( by aesop );
  · -- Since m is odd and not divisible by 3, m % 3 must be 1 or 2. But if
    -- m % 3 = 2, then 2m % 6 = 4, contradicting 2m % 12 = 2. Therefore,
    -- m % 3 must be 1.
    have h_mod3 : m % 3 = 1 := by
      unfold IsSolution at h;
      rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := congr_arg ( · % 3 ) h.2
        norm_num [ Nat.add_mod, Nat.mul_mod ] at this
        ( have := Nat.mod_lt m zero_lt_three
          interval_cases _ : m % 3 <;>
            simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ; );
        -- Since $m$ is odd and $m \equiv 2 \pmod{3}$, we have $\phi(m) \equiv 2 \pmod{3}$.
        have h_phi_mod3 : m.totient % 3 = 2 := by
          norm_num [ Nat.add_mod, Nat.mul_mod ] at this
          have := Nat.mod_lt ( Nat.totient m ) three_pos
          interval_cases Nat.totient m % 3 <;> trivial;
        have h_squarefree : Squarefree m := by
          have h_solution : IsSolution m := by
            exact ⟨ h.1, by omega ⟩
          exact solution_squarefree m h_solution;
        exact absurd
          ( totient_mod_3_of_squarefree_not_dvd_3 m h_squarefree ( by omega ) )
          ( by norm_num [ h_phi_mod3 ] );
      · exact le_trans ( Nat.totient_le m ) ( by linarith );
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf at *;
    · exact absurd ( h.1 ) ( by norm_num [ Nat.even_iff ] );
    · omega

lemma m_mod_6_eq_1 (m : ℕ) (h : IsSolution m) : m % 6 = 1 := by
  -- Assume 3 | 2m. Since m is odd, 3 | m.
  by_cases h3 : 3 ∣ m;
  · -- Since m is squarefree (by solution_squarefree), m = 3k with gcd(3,k)=1.
    obtain ⟨k, hk⟩ : ∃ k, m = 3 * k ∧ Nat.gcd 3 k = 1 := by
      obtain ⟨ k, rfl ⟩ := h3;
      have := solution_squarefree ( 3 * k ) h; simp_all +decide [ Nat.squarefree_mul_iff ] ;
    -- Since $k$ is not divisible by 3, $\phi(k)$ is even. Therefore,
    -- $3k - \phi(k) \equiv 1 \mod 3$ implies
    -- $\phi(k) \equiv 2 \mod 3$, a contradiction.
    have h_contra : Nat.totient k % 3 = 2 := by
      have h_contra : 3 * k - Nat.totient k = m_BS := by
        have h_eq : 2 * (3 * k) - Nat.totient (3 * k) = 2 * m_BS := by
          simpa [hk.1] using h.2
        rw [Nat.totient_mul (by simpa [Nat.Coprime] using hk.2)] at h_eq
        norm_num [Nat.totient_prime] at h_eq
        omega
      rw [ Nat.sub_eq_iff_eq_add ] at h_contra;
      · have := congr_arg ( · % 3 ) h_contra
        norm_num [ Nat.add_mod, Nat.mul_mod ] at this
        have := Nat.mod_lt ( Nat.totient k ) zero_lt_three
        interval_cases Nat.totient k % 3 <;> trivial;
      · exact le_trans ( Nat.totient_le _ ) ( by linarith );
    exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 k ( by
      have hsq_m := solution_squarefree m h
      exact hsq_m.squarefree_of_dvd (by
        rw [hk.1]
        exact dvd_mul_left _ _) ) ( by
      exact fun h => by
        have := Nat.dvd_gcd ( by decide : 3 ∣ 3 ) h
        simp_all +decide ; ) ) ( by aesop );
  · -- Since m is odd and not divisible by 3, m % 3 must be 1 or 2. But if
    -- m % 3 = 2, then 2m % 6 = 4, contradicting 2m % 12 = 2. Therefore,
    -- m % 3 must be 1.
    have h_mod3 : m % 3 = 1 := by
      unfold IsSolution at h;
      rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := congr_arg ( · % 3 ) h.2
        norm_num [ Nat.add_mod, Nat.mul_mod ] at this
        ( have := Nat.mod_lt m zero_lt_three
          interval_cases _ : m % 3 <;>
            simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ; );
        -- Since $m$ is odd and $m \equiv 2 \pmod{3}$, we have $\phi(m) \equiv 2 \pmod{3}$.
        have h_phi_mod3 : m.totient % 3 = 2 := by
          norm_num [ Nat.add_mod, Nat.mul_mod ] at this
          have := Nat.mod_lt ( Nat.totient m ) three_pos
          interval_cases Nat.totient m % 3 <;> trivial;
        have h_squarefree : Squarefree m := by
          have h_solution : IsSolution m := by
            exact ⟨ h.1, by omega ⟩
          exact solution_squarefree m h_solution;
        exact absurd
          ( totient_mod_3_of_squarefree_not_dvd_3 m h_squarefree ( by omega ) )
          ( by norm_num [ h_phi_mod3 ] );
      · exact le_trans ( Nat.totient_le m ) ( by linarith );
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf at *;
    · exact absurd ( h.1 ) ( by norm_num [ Nat.even_iff ] );
    · omega


lemma m_BS_mod_3 : m_BS % 3 = 1 := by decide

lemma phi_k_mod_3_contra
    (k : ℕ) (h_sq : Squarefree k) (h_nd : ¬ 3 ∣ k)
    (h_eq : 3 * k - k.totient = m_BS) :
    False := by
  have h_mod3 : k.totient % 3 = 2 := by
    rw [ Nat.sub_eq_iff_eq_add ] at h_eq;
    · have := congr_arg ( · % 3 ) h_eq
      norm_num [ Nat.add_mod, Nat.mul_mod ] at this ⊢
      have := Nat.mod_lt k.totient zero_lt_three
      interval_cases k.totient % 3 <;> trivial;
    · exact le_trans ( Nat.totient_le _ ) ( by linarith );
  exact absurd h_mod3 ( by
    have := totient_mod_3_of_squarefree_not_dvd_3 k h_sq h_nd
    aesop )

private lemma computation_lemma_check_prime (p : ℕ) (hp : p.Prime) :
    2 * p - p * (∏ q ∈ Nat.primeFactors p, (1 - 1 / q : ℚ)) ≠ 2 * m_BS := by
  intro h
  simp [hp.primeFactors, m_BS] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprod : (p : ℚ) * (1 - (p : ℚ)⁻¹) = p - 1 := by
    field_simp [hp0]
  rw [hprod] at h
  have hp_cast : (p : ℚ) = 1018405 := by
    norm_num [m_BS] at h ⊢
    linarith
  have hp_eq : p = 1018405 := by exact_mod_cast hp_cast
  subst p
  norm_num at hp

private lemma computation_lemma_check_two_primes
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    2 * (p * q) - (p * q) *
        (∏ r ∈ Nat.primeFactors (p * q), (1 - 1 / r : ℚ)) ≠ 2 * m_BS := by
  intro h
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors] at h
  simp [hpq] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hprod :
      (p : ℚ) * q * ((1 - (p : ℚ)⁻¹) * (1 - (q : ℚ)⁻¹)) = (p - 1) * (q - 1) := by
    field_simp [hp0, hq0]
  rw [hprod] at h
  have hfactor_cast : ((p + 1 : ℕ) : ℚ) * (q + 1) = 1018408 := by
    norm_num [m_BS] at h ⊢
    nlinarith
  have hfactor : (p + 1) * (q + 1) = 1018408 := by exact_mod_cast hfactor_cast
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hq_odd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
  have hp_bound : p + 1 < 2 * 127301 := by
    have hmul := Nat.mul_le_mul_left (p + 1) (show 6 ≤ q + 1 by omega)
    rw [hfactor] at hmul
    omega
  have hq_bound : q + 1 < 2 * 127301 := by
    have hmul := Nat.mul_le_mul_right (q + 1) (show 6 ≤ p + 1 by omega)
    rw [hfactor] at hmul
    omega
  have hr_dvd : 127301 ∣ (p + 1) * (q + 1) := by
    rw [hfactor]
    norm_num
  rcases prime_127301.dvd_mul.mp hr_dvd with hp_dvd | hq_dvd
  · have hp_eq : p + 1 = 127301 :=
      Nat.eq_of_dvd_of_lt_two_mul (Nat.succ_ne_zero p) hp_dvd hp_bound
    have hp_parity := congrArg (fun n : ℕ ↦ n % 2) hp_eq
    norm_num [Nat.add_mod, hp_odd] at hp_parity
  · have hq_eq : q + 1 = 127301 :=
      Nat.eq_of_dvd_of_lt_two_mul (Nat.succ_ne_zero q) hq_dvd hq_bound
    have hq_parity := congrArg (fun n : ℕ ↦ n % 2) hq_eq
    norm_num [Nat.add_mod, hq_odd] at hq_parity

private def primes5to100 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
    71, 73, 79, 83, 89, 97]

private def primes5to451 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
    71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
    151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
    317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449]

private lemma prime_five_le_le_100_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp100 : p ≤ 100) : p ∈ primes5to100 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to100]

private lemma prime_five_le_le_451_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp451 : p ≤ 451) : p ∈ primes5to451 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to451]

set_option maxRecDepth 100000 in
private lemma three_prime_arithmetic_check :
    ∀ p ∈ primes5to100, ∀ q ∈ primes5to451, p < q →
      let c := (p - 1) * (q - 1)
      let d := p * q + p + q - 1
      c ≤ 1018406 → (1018406 - c) % d = 0 → q < (1018406 - c) / d →
        ¬Nat.Prime ((1018406 - c) / d) := by
  decide

private def primes5to31 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31]

private def primes5to58 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private def primes5to170 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
    71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
    151, 157, 163, 167]

private def primes5to15 : List ℕ := [5, 7, 11, 13]

private def primes5to21 : List ℕ := [5, 7, 11, 13, 17, 19]

private def primes5to30 : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29]

private def primes5to51 : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

private lemma prime_five_le_le_31_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp31 : p ≤ 31) : p ∈ primes5to31 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to31]

private lemma prime_five_le_le_58_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp58 : p ≤ 58) : p ∈ primes5to58 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to58]

private lemma prime_five_le_le_170_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp170 : p ≤ 170) : p ∈ primes5to170 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to170]

private lemma prime_five_le_le_15_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp15 : p ≤ 15) : p ∈ primes5to15 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to15]

private lemma prime_five_le_le_21_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp21 : p ≤ 21) : p ∈ primes5to21 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to21]

private lemma prime_five_le_le_30_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp30 : p ≤ 30) : p ∈ primes5to30 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to30]

private lemma prime_five_le_le_51_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp51 : p ≤ 51) : p ∈ primes5to51 := by
  interval_cases p <;> norm_num at hp <;> simp [primes5to51]

set_option maxRecDepth 100000 in
private lemma four_prime_arithmetic_check :
    ∀ p ∈ primes5to31, ∀ q ∈ primes5to58, ∀ r ∈ primes5to170,
      p < q → q < r →
      let c := (p - 1) * (q - 1) * (r - 1)
      let d := 2 * (p * q * r) - c
      c ≤ 1018406 → (1018406 - c) % d = 0 → r < (1018406 - c) / d →
        ¬Nat.Prime ((1018406 - c) / d) := by
  decide

private def FivePrimeArithmeticForPair (p q : ℕ) : Prop :=
  ∀ r ∈ primes5to30, ∀ s ∈ primes5to51, q < r → r < s →
    let c := (p - 1) * (q - 1) * (r - 1) * (s - 1)
    let d := 2 * (p * q * r * s) - c
    c ≤ 1018406 → (1018406 - c) % d = 0 → s < (1018406 - c) / d →
      ¬Nat.Prime ((1018406 - c) / d)

private lemma five_prime_arithmetic_check_5_7 : FivePrimeArithmeticForPair 5 7 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_5_11 : FivePrimeArithmeticForPair 5 11 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_5_13 : FivePrimeArithmeticForPair 5 13 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_5_17 : FivePrimeArithmeticForPair 5 17 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_5_19 : FivePrimeArithmeticForPair 5 19 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_7_11 : FivePrimeArithmeticForPair 7 11 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_7_13 : FivePrimeArithmeticForPair 7 13 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_7_17 : FivePrimeArithmeticForPair 7 17 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_7_19 : FivePrimeArithmeticForPair 7 19 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_11_13 : FivePrimeArithmeticForPair 11 13 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_11_17 : FivePrimeArithmeticForPair 11 17 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_11_19 : FivePrimeArithmeticForPair 11 19 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_13_17 : FivePrimeArithmeticForPair 13 17 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private lemma five_prime_arithmetic_check_13_19 : FivePrimeArithmeticForPair 13 19 := by
  norm_num [FivePrimeArithmeticForPair, primes5to30, primes5to51]

private def FivePrimeArithmeticFor (p : ℕ) : Prop :=
  ∀ q ∈ primes5to21, p < q → FivePrimeArithmeticForPair p q

private lemma five_prime_arithmetic_check (p : ℕ) (hp : p ∈ primes5to15) :
    FivePrimeArithmeticFor p := by
  simp only [primes5to15, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl)
  all_goals
    intro q hq hpq
    simp only [primes5to21, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | omega
    | exact five_prime_arithmetic_check_5_7
    | exact five_prime_arithmetic_check_5_11
    | exact five_prime_arithmetic_check_5_13
    | exact five_prime_arithmetic_check_5_17
    | exact five_prime_arithmetic_check_5_19
    | exact five_prime_arithmetic_check_7_11
    | exact five_prime_arithmetic_check_7_13
    | exact five_prime_arithmetic_check_7_17
    | exact five_prime_arithmetic_check_7_19
    | exact five_prime_arithmetic_check_11_13
    | exact five_prime_arithmetic_check_11_17
    | exact five_prime_arithmetic_check_11_19
    | exact five_prime_arithmetic_check_13_17
    | exact five_prime_arithmetic_check_13_19

set_option maxHeartbeats 1000000 in
-- The finite prime-factor case split below exceeds the default heartbeat budget.
private lemma computation_lemma_check_three_primes
    (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hp5 : 5 ≤ p)
    (hm_lt : p * q * r < 2 * m_BS) :
    2 * (p * q * r) - (p * q * r) *
        (∏ x ∈ Nat.primeFactors (p * q * r), (1 - 1 / x : ℚ)) ≠ 2 * m_BS := by
  intro h
  rw [Nat.primeFactors_mul (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero,
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    hr.primeFactors] at h
  simp [hpq.ne, (hpq.trans hqr).ne, hqr.ne] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hprod :
      (p : ℚ) * q * r * ((1 - (p : ℚ)⁻¹) * ((1 - (q : ℚ)⁻¹) *
        (1 - (r : ℚ)⁻¹))) = (p - 1) * (q - 1) * (r - 1) := by
    field_simp [hp0, hq0, hr0]
  rw [hprod] at h
  norm_num [m_BS] at h hm_lt
  have hp_cube : p ^ 3 < p * q * r := by
    calc
      p ^ 3 = p * p * p := by ring
      _ < p * q * r := by
        simpa only [mul_assoc] using Nat.mul_lt_mul_of_pos_left
          (mul_lt_mul hpq (show p ≤ r by omega) hp.pos (Nat.zero_le q)) hp.pos
  have hp100 : p ≤ 100 := by
    by_contra hp_bound
    have hp_ge : 101 ≤ p := by omega
    have hp_pow := Nat.pow_le_pow_left hp_ge 3
    norm_num at hp_pow
    omega
  have hq_square : 5 * q ^ 2 < p * q * r := by
    calc
      5 * q ^ 2 = 5 * q * q := by ring
      _ ≤ p * q * q := by gcongr
      _ < p * q * r := Nat.mul_lt_mul_of_pos_left hqr (mul_pos hp.pos hq.pos)
  have hq451 : q ≤ 451 := by
    by_contra hq_bound
    have hq_ge : 452 ≤ q := by omega
    have hq_pow := Nat.pow_le_pow_left hq_ge 2
    have hq_mul := Nat.mul_le_mul_left 5 hq_pow
    norm_num at hq_mul
    omega
  have hlinear :
      (p * q + p + q - 1) * r + (p - 1) * (q - 1) = 1018406 := by
    have hcoef : 1 ≤ p * q + p + q := by omega
    apply Nat.cast_injective (R := ℚ)
    push_cast [Nat.cast_sub hcoef, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le]
    nlinarith [h]
  have hp_mem := prime_five_le_le_100_mem p hp hp5 hp100
  have hq5 : 5 ≤ q := by omega
  have hq_mem := prime_five_le_le_451_mem q hq hq5 hq451
  let c := (p - 1) * (q - 1)
  let d := p * q + p + q - 1
  have hd_pos : 0 < d := by dsimp [d]; omega
  have hc_le : c ≤ 1018406 := by dsimp [c, d] at *; omega
  have hnum : 1018406 - c = d * r := by dsimp [c, d] at *; omega
  have hmod : (1018406 - c) % d = 0 := by
    rw [hnum]
    exact Nat.mul_mod_right d r
  have hquot : (1018406 - c) / d = r := by
    rw [hnum]
    exact Nat.mul_div_cancel_left r hd_pos
  have hnot_prime := three_prime_arithmetic_check p hp_mem q hq_mem hpq hc_le hmod
    (by rw [hquot]; exact hqr)
  exact hnot_prime (hquot.symm ▸ hr)

private lemma computation_lemma_check_four_primes
    (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (hp5 : 5 ≤ p)
    (hm_lt : p * q * r * s < 2 * m_BS) :
    2 * (p * q * r * s) - (p * q * r * s) *
        (∏ x ∈ Nat.primeFactors (p * q * r * s), (1 - 1 / x : ℚ)) ≠ 2 * m_BS := by
  intro h
  rw [Nat.primeFactors_mul (mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
      hs.ne_zero,
    Nat.primeFactors_mul (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero,
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    hr.primeFactors, hs.primeFactors] at h
  simp [hpq.ne, (hpq.trans hqr).ne, (hpq.trans (hqr.trans hrs)).ne, hqr.ne,
    (hqr.trans hrs).ne, hrs.ne] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne_zero
  have hprod :
      (p : ℚ) * q * r * s * ((1 - (p : ℚ)⁻¹) * ((1 - (q : ℚ)⁻¹) *
        ((1 - (r : ℚ)⁻¹) * (1 - (s : ℚ)⁻¹)))) =
        (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
    field_simp [hp0, hq0, hr0, hs0]
  rw [hprod] at h
  norm_num [m_BS] at h hm_lt
  have hp_pow : p ^ 4 < p * q * r * s := by
    calc
      p ^ 4 = p * p * p * p := by ring
      _ < p * q * r * s := by gcongr <;> omega
  have hp31 : p ≤ 31 := by
    by_contra hp_bound
    have hp_ge : 32 ≤ p := by omega
    have hp_power := Nat.pow_le_pow_left hp_ge 4
    norm_num at hp_power
    omega
  have hq_pow : 5 * q ^ 3 < p * q * r * s := by
    have hqq : q * q < r * s :=
      mul_lt_mul hqr (by omega) hq.pos (Nat.zero_le r)
    calc
      5 * q ^ 3 = (5 * q) * (q * q) := by ring
      _ ≤ (p * q) * (q * q) := Nat.mul_le_mul_right (q * q) (by gcongr)
      _ < (p * q) * (r * s) :=
        Nat.mul_lt_mul_of_pos_left hqq (mul_pos hp.pos hq.pos)
      _ = p * q * r * s := by ring
  have hq58 : q ≤ 58 := by
    by_contra hq_bound
    have hq_ge : 59 ≤ q := by omega
    have hq_power := Nat.pow_le_pow_left hq_ge 3
    have hq_mul := Nat.mul_le_mul_left 5 hq_power
    norm_num at hq_mul
    omega
  have hr_pow : 5 * 7 * r ^ 2 < p * q * r * s := by
    have hq7 : 7 ≤ q := by
      by_contra hq_bound
      have hq6 : q ≤ 6 := by omega
      interval_cases q <;> norm_num at hq <;> omega
    have hcoef : 5 * 7 ≤ p * q := mul_le_mul hp5 hq7 (by omega) (by omega)
    calc
      5 * 7 * r ^ 2 = (5 * 7) * (r * r) := by ring
      _ ≤ (p * q) * (r * r) := Nat.mul_le_mul_right (r * r) hcoef
      _ < (p * q) * (r * s) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_left hrs hr.pos) (mul_pos hp.pos hq.pos)
      _ = p * q * r * s := by ring
  have hr170 : r ≤ 170 := by
    by_contra hr_bound
    have hr_ge : 171 ≤ r := by omega
    have hr_power := Nat.pow_le_pow_left hr_ge 2
    have hr_mul := Nat.mul_le_mul_left 35 hr_power
    norm_num at hr_mul
    omega
  let c := (p - 1) * (q - 1) * (r - 1)
  let d := 2 * (p * q * r) - c
  have hc_base : c ≤ p * q * r := by dsimp [c]; gcongr <;> omega
  have hc_double : c ≤ 2 * (p * q * r) := hc_base.trans (by omega)
  have hn_pos : 0 < p * q * r := mul_pos (mul_pos hp.pos hq.pos) hr.pos
  have hd_pos : 0 < d := by dsimp [d]; omega
  have hlinear : d * s + c = 1018406 := by
    have hc_cast : (c : ℚ) = (p - 1) * (q - 1) * (r - 1) := by
      dsimp [c]
      push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_sub hr.one_le]
      rfl
    apply Nat.cast_injective (R := ℚ)
    dsimp [d]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hc_double]
    rw [hc_cast]
    push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_sub hr.one_le]
    nlinarith [h]
  have hc_le : c ≤ 1018406 := by omega
  have hnum : 1018406 - c = d * s := by omega
  have hmod : (1018406 - c) % d = 0 := by
    rw [hnum]
    exact Nat.mul_mod_right d s
  have hquot : (1018406 - c) / d = s := by
    rw [hnum]
    exact Nat.mul_div_cancel_left s hd_pos
  have hp_mem := prime_five_le_le_31_mem p hp hp5 hp31
  have hq_mem := prime_five_le_le_58_mem q hq (by omega) hq58
  have hr_mem := prime_five_le_le_170_mem r hr (by omega) hr170
  have hnot_prime :=
    four_prime_arithmetic_check p hp_mem q hq_mem r hr_mem hpq hqr hc_le hmod
      (by rw [hquot]; exact hrs)
  exact hnot_prime (hquot.symm ▸ hs)

private lemma computation_lemma_check_five_primes
    (p q r s t : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (ht : t.Prime) (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hst : s < t) (hp5 : 5 ≤ p) (hm_lt : p * q * r * s * t < 2 * m_BS) :
    2 * (p * q * r * s * t) - (p * q * r * s * t) *
        (∏ x ∈ Nat.primeFactors (p * q * r * s * t), (1 - 1 / x : ℚ)) ≠
      2 * m_BS := by
  intro h
  rw [Nat.primeFactors_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero) hs.ne_zero)
      ht.ne_zero,
    Nat.primeFactors_mul (mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
      hs.ne_zero,
    Nat.primeFactors_mul (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero,
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    hr.primeFactors, hs.primeFactors, ht.primeFactors] at h
  simp [hpq.ne, (hpq.trans hqr).ne, (hpq.trans (hqr.trans hrs)).ne,
    (hpq.trans (hqr.trans (hrs.trans hst))).ne, hqr.ne, (hqr.trans hrs).ne,
    (hqr.trans (hrs.trans hst)).ne, hrs.ne, (hrs.trans hst).ne, hst.ne] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne_zero
  have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne_zero
  have hprod :
      (p : ℚ) * q * r * s * t * ((1 - (p : ℚ)⁻¹) * ((1 - (q : ℚ)⁻¹) *
        ((1 - (r : ℚ)⁻¹) * ((1 - (s : ℚ)⁻¹) * (1 - (t : ℚ)⁻¹))))) =
        (p - 1) * (q - 1) * (r - 1) * (s - 1) * (t - 1) := by
    field_simp [hp0, hq0, hr0, hs0, ht0]
  rw [hprod] at h
  norm_num [m_BS] at h hm_lt
  have hp_pow : p ^ 5 < p * q * r * s * t := by
    calc
      p ^ 5 = p * p * p * p * p := by ring
      _ < p * q * r * s * t := by gcongr <;> omega
  have hp15 : p ≤ 15 := by
    by_contra hp_bound
    have hp_ge : 16 ≤ p := by omega
    have hp_power := Nat.pow_le_pow_left hp_ge 5
    norm_num at hp_power
    omega
  have hq_pow : 5 * q ^ 4 < p * q * r * s * t := by
    have hqq : q * q < r * s :=
      mul_lt_mul hqr (by omega) hq.pos (Nat.zero_le r)
    have hq3 : q ^ 3 < r * s * t := by
      rw [show q ^ 3 = (q * q) * q by ring]
      exact mul_lt_mul hqq (by omega) hq.pos (Nat.zero_le (r * s))
    calc
      5 * q ^ 4 = (5 * q) * q ^ 3 := by ring
      _ ≤ (p * q) * q ^ 3 := Nat.mul_le_mul_right (q ^ 3) (by gcongr)
      _ < (p * q) * (r * s * t) :=
        Nat.mul_lt_mul_of_pos_left hq3 (mul_pos hp.pos hq.pos)
      _ = p * q * r * s * t := by ring
  have hq21 : q ≤ 21 := by
    by_contra hq_bound
    have hq_ge : 22 ≤ q := by omega
    have hq_power := Nat.pow_le_pow_left hq_ge 4
    have hq_mul := Nat.mul_le_mul_left 5 hq_power
    norm_num at hq_mul
    omega
  have hq7 : 7 ≤ q := by
    by_contra hq_bound
    have hq6 : q ≤ 6 := by omega
    interval_cases q <;> norm_num at hq <;> omega
  have hr_pow : 5 * 7 * r ^ 3 < p * q * r * s * t := by
    have hrr : r * r < s * t :=
      mul_lt_mul hrs (by omega) hr.pos (Nat.zero_le s)
    have hcoef : 5 * 7 ≤ p * q := mul_le_mul hp5 hq7 (by omega) (by omega)
    calc
      5 * 7 * r ^ 3 = (5 * 7) * r * (r * r) := by ring
      _ ≤ (p * q) * r * (r * r) := by
        simpa only [mul_assoc] using Nat.mul_le_mul_right (r * (r * r)) hcoef
      _ < (p * q) * r * (s * t) :=
        Nat.mul_lt_mul_of_pos_left hrr (mul_pos (mul_pos hp.pos hq.pos) hr.pos)
      _ = p * q * r * s * t := by ring
  have hr30 : r ≤ 30 := by
    by_contra hr_bound
    have hr_ge : 31 ≤ r := by omega
    have hr_power := Nat.pow_le_pow_left hr_ge 3
    have hr_mul := Nat.mul_le_mul_left 35 hr_power
    norm_num at hr_mul
    omega
  have hr11 : 11 ≤ r := by
    by_contra hr_bound
    have hr10 : r ≤ 10 := by omega
    interval_cases r <;> norm_num at hr <;> omega
  have hs_pow : 5 * 7 * 11 * s ^ 2 < p * q * r * s * t := by
    have hpq_lower : 5 * 7 ≤ p * q := mul_le_mul hp5 hq7 (by omega) (by omega)
    have hcoef : 5 * 7 * 11 ≤ p * q * r :=
      mul_le_mul hpq_lower hr11 (by omega) (by omega)
    calc
      5 * 7 * 11 * s ^ 2 = (5 * 7 * 11) * (s * s) := by ring
      _ ≤ (p * q * r) * (s * s) := Nat.mul_le_mul_right (s * s) hcoef
      _ < (p * q * r) * (s * t) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_left hst hs.pos)
          (mul_pos (mul_pos hp.pos hq.pos) hr.pos)
      _ = p * q * r * s * t := by ring
  have hs51 : s ≤ 51 := by
    by_contra hs_bound
    have hs_ge : 52 ≤ s := by omega
    have hs_power := Nat.pow_le_pow_left hs_ge 2
    have hs_mul := Nat.mul_le_mul_left 385 hs_power
    norm_num at hs_mul
    omega
  let c := (p - 1) * (q - 1) * (r - 1) * (s - 1)
  let d := 2 * (p * q * r * s) - c
  have hc_base : c ≤ p * q * r * s := by dsimp [c]; gcongr <;> omega
  have hc_double : c ≤ 2 * (p * q * r * s) := hc_base.trans (by omega)
  have hn_pos : 0 < p * q * r * s :=
    mul_pos (mul_pos (mul_pos hp.pos hq.pos) hr.pos) hs.pos
  have hd_pos : 0 < d := by dsimp [d]; omega
  have hlinear : d * t + c = 1018406 := by
    have hc_cast : (c : ℚ) = (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
      dsimp [c]
      push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_sub hr.one_le,
        Nat.cast_sub hs.one_le]
      rfl
    apply Nat.cast_injective (R := ℚ)
    dsimp [d]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hc_double]
    rw [hc_cast]
    push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_sub hr.one_le,
      Nat.cast_sub hs.one_le]
    nlinarith [h]
  have hc_le : c ≤ 1018406 := by omega
  have hnum : 1018406 - c = d * t := by omega
  have hmod : (1018406 - c) % d = 0 := by
    rw [hnum]
    exact Nat.mul_mod_right d t
  have hquot : (1018406 - c) / d = t := by
    rw [hnum]
    exact Nat.mul_div_cancel_left t hd_pos
  have hp_mem := prime_five_le_le_15_mem p hp hp5 hp15
  have hq_mem := prime_five_le_le_21_mem q hq (by omega) hq21
  have hr_mem := prime_five_le_le_30_mem r hr (by omega) hr30
  have hs_mem := prime_five_le_le_51_mem s hs (by omega) hs51
  have hnot_prime := five_prime_arithmetic_check p hp_mem q hq_mem hpq r hr_mem s hs_mem
    hqr hrs hc_le hmod (by rw [hquot]; exact hst)
  exact hnot_prime (hquot.symm ▸ ht)



private lemma six_large_primes_le_list_prod
    (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hlower : ∀ p ∈ l, 5 ≤ p)
    (hchain : l.IsChain (· ≤ ·)) (hnodup : l.Nodup) (hlen : 6 ≤ l.length) :
    1616615 ≤ l.prod := by
  match l with
  | a :: b :: c :: d :: e :: f :: rest =>
      have ha : a.Prime := hprime a (by simp)
      have hb : b.Prime := hprime b (by simp)
      have hc : c.Prime := hprime c (by simp)
      have hd : d.Prime := hprime d (by simp)
      have he : e.Prime := hprime e (by simp)
      have hf : f.Prime := hprime f (by simp)
      have hab_le : a ≤ b := (List.isChain_cons_cons.mp hchain).1
      have hchain_b := (List.isChain_cons_cons.mp hchain).2
      have hbc_le : b ≤ c := (List.isChain_cons_cons.mp hchain_b).1
      have hchain_c := (List.isChain_cons_cons.mp hchain_b).2
      have hcd_le : c ≤ d := (List.isChain_cons_cons.mp hchain_c).1
      have hchain_d := (List.isChain_cons_cons.mp hchain_c).2
      have hde_le : d ≤ e := (List.isChain_cons_cons.mp hchain_d).1
      have hchain_e := (List.isChain_cons_cons.mp hchain_d).2
      have hef_le : e ≤ f := (List.isChain_cons_cons.mp hchain_e).1
      have hab_ne : a ≠ b := by
        intro h
        subst b
        exact (List.nodup_cons.mp hnodup).1 (by simp)
      have hnodup_b := (List.nodup_cons.mp hnodup).2
      have hbc_ne : b ≠ c := by
        intro h
        subst c
        exact (List.nodup_cons.mp hnodup_b).1 (by simp)
      have hnodup_c := (List.nodup_cons.mp hnodup_b).2
      have hcd_ne : c ≠ d := by
        intro h
        subst d
        exact (List.nodup_cons.mp hnodup_c).1 (by simp)
      have hnodup_d := (List.nodup_cons.mp hnodup_c).2
      have hde_ne : d ≠ e := by
        intro h
        subst e
        exact (List.nodup_cons.mp hnodup_d).1 (by simp)
      have hnodup_e := (List.nodup_cons.mp hnodup_d).2
      have hef_ne : e ≠ f := by
        intro h
        subst f
        exact (List.nodup_cons.mp hnodup_e).1 (by simp)
      have hab : a < b := by omega
      have hbc : b < c := by omega
      have hcd : c < d := by omega
      have hde : d < e := by omega
      have hef : e < f := by omega
      have ha5 : 5 ≤ a := hlower a (by simp)
      have hb7 : 7 ≤ b := by
        by_contra h
        have hb_le : b ≤ 6 := by omega
        interval_cases b <;> norm_num at hb <;> omega
      have hc11 : 11 ≤ c := by
        by_contra h
        have hc_le : c ≤ 10 := by omega
        interval_cases c <;> norm_num at hc <;> omega
      have hd13 : 13 ≤ d := by
        by_contra h
        have hd_le : d ≤ 12 := by omega
        interval_cases d <;> norm_num at hd <;> omega
      have he17 : 17 ≤ e := by
        by_contra h
        have he_le : e ≤ 16 := by omega
        interval_cases e <;> norm_num at he <;> omega
      have hf19 : 19 ≤ f := by
        by_contra h
        have hf_le : f ≤ 18 := by omega
        interval_cases f <;> norm_num at hf <;> omega
      have hfirst : 1616615 ≤ a * b * c * d * e * f := by
        calc
          1616615 = 5 * 7 * 11 * 13 * 17 * 19 := by norm_num
          _ ≤ a * b * c * d * e * f := by gcongr
      have hrest : 0 < rest.prod := List.prod_pos fun p hp ↦ (hprime p (by simp [hp])).pos
      simpa only [List.prod_cons, mul_assoc] using
        hfirst.trans (Nat.le_mul_of_pos_right _ hrest)
  | [] => simp at hlen
  | [_] => simp at hlen
  | [_, _] => simp at hlen
  | [_, _, _] => simp at hlen
  | [_, _, _, _] => simp at hlen
  | [_, _, _, _, _] => simp at hlen

private lemma primeFactors_card_le_five
    (m : ℕ) (hm_lt : m < 2 * m_BS) (hm_odd : Odd m) (hm_sq : Squarefree m)
    (hm_not_div3 : ¬3 ∣ m) :
    m.primeFactors.card ≤ 5 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm_odd
  have hnodup := hm_sq.nodup_primeFactorsList
  have hcard_eq : m.primeFactors.card = m.primeFactorsList.length := by
    change m.primeFactorsList.toFinset.card = m.primeFactorsList.length
    exact List.toFinset_card_of_nodup hnodup
  by_contra hcard
  have hlen : 6 ≤ m.primeFactorsList.length := by omega
  have hprime : ∀ p ∈ m.primeFactorsList, p.Prime := by
    exact fun p hp ↦ Nat.prime_of_mem_primeFactorsList hp
  have hlower : ∀ p ∈ m.primeFactorsList, 5 ≤ p := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactorsList hp
    have hp_dvd : p ∣ m := (Nat.mem_primeFactorsList hm0).mp hp |>.2
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat hp_dvd) (by norm_num)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hm_not_div3 hp_dvd
    exact hp_prime.five_le_of_ne_two_of_ne_three hp2 hp3
  have hlarge := six_large_primes_le_list_prod m.primeFactorsList hprime hlower
    (Nat.isChain_primeFactorsList m) hnodup hlen
  rw [Nat.prod_primeFactorsList hm0] at hlarge
  norm_num [m_BS] at hm_lt
  omega

private lemma squarefree_three_primeFactors
    (m : ℕ) (hm_sq : Squarefree m) (hcard : m.primeFactors.card = 3) :
    ∃ p q r, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ m = p * q * r := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hcard
  have hnodup := hm_sq.nodup_primeFactorsList
  have hcard_eq : m.primeFactors.card = m.primeFactorsList.length := by
    change m.primeFactorsList.toFinset.card = m.primeFactorsList.length
    exact List.toFinset_card_of_nodup hnodup
  have hlen : m.primeFactorsList.length = 3 := by omega
  obtain ⟨p, q, r, hlist⟩ := List.length_eq_three.mp hlen
  have hp_mem : p ∈ m.primeFactorsList := by rw [hlist]; simp
  have hq_mem : q ∈ m.primeFactorsList := by rw [hlist]; simp
  have hr_mem : r ∈ m.primeFactorsList := by rw [hlist]; simp
  have hp := Nat.prime_of_mem_primeFactorsList hp_mem
  have hq := Nat.prime_of_mem_primeFactorsList hq_mem
  have hr := Nat.prime_of_mem_primeFactorsList hr_mem
  have hchain := Nat.isChain_primeFactorsList m
  rw [hlist] at hchain
  simp only [List.isChain_cons_cons, List.isChain_singleton] at hchain
  have hpq_ne : p ≠ q := by
    intro hpq
    subst q
    rw [hlist] at hnodup
    simp at hnodup
  have hqr_ne : q ≠ r := by
    intro hqr
    subst r
    rw [hlist] at hnodup
    simp at hnodup
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hm_eq : m = p * q * r := by
    rw [← Nat.prod_primeFactorsList hm0, hlist]
    simp [mul_assoc]
  exact ⟨p, q, r, hp, hq, hr, hpq, hqr, hm_eq⟩

private lemma squarefree_four_primeFactors
    (m : ℕ) (hm_sq : Squarefree m) (hcard : m.primeFactors.card = 4) :
    ∃ p q r s, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      p < q ∧ q < r ∧ r < s ∧ m = p * q * r * s := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hcard
  have hnodup := hm_sq.nodup_primeFactorsList
  have hcard_eq : m.primeFactors.card = m.primeFactorsList.length := by
    change m.primeFactorsList.toFinset.card = m.primeFactorsList.length
    exact List.toFinset_card_of_nodup hnodup
  have hlen : m.primeFactorsList.length = 4 := by omega
  obtain ⟨p, q, r, s, hlist⟩ := List.length_eq_four.mp hlen
  have hp := Nat.prime_of_mem_primeFactorsList
    (show p ∈ m.primeFactorsList by rw [hlist]; simp)
  have hq := Nat.prime_of_mem_primeFactorsList
    (show q ∈ m.primeFactorsList by rw [hlist]; simp)
  have hr := Nat.prime_of_mem_primeFactorsList
    (show r ∈ m.primeFactorsList by rw [hlist]; simp)
  have hs := Nat.prime_of_mem_primeFactorsList
    (show s ∈ m.primeFactorsList by rw [hlist]; simp)
  have hchain := Nat.isChain_primeFactorsList m
  rw [hlist] at hchain
  simp only [List.isChain_cons_cons, List.isChain_singleton] at hchain
  rw [hlist] at hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnodup
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hrs : r < s := by omega
  have hm_eq : m = p * q * r * s := by
    rw [← Nat.prod_primeFactorsList hm0, hlist]
    simp [mul_assoc]
  exact ⟨p, q, r, s, hp, hq, hr, hs, hpq, hqr, hrs, hm_eq⟩

private lemma list_length_eq_five {α : Type*} {l : List α} :
    l.length = 5 ↔ ∃ a b c d e, l = [a, b, c, d, e] :=
  ⟨fun _ => let [a, b, c, d, e] := l; ⟨a, b, c, d, e, rfl⟩,
    fun ⟨_, _, _, _, _, h⟩ => h ▸ rfl⟩

private lemma squarefree_five_primeFactors
    (m : ℕ) (hm_sq : Squarefree m) (hcard : m.primeFactors.card = 5) :
    ∃ p q r s t, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ t.Prime ∧
      p < q ∧ q < r ∧ r < s ∧ s < t ∧ m = p * q * r * s * t := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hcard
  have hnodup := hm_sq.nodup_primeFactorsList
  have hcard_eq : m.primeFactors.card = m.primeFactorsList.length := by
    change m.primeFactorsList.toFinset.card = m.primeFactorsList.length
    exact List.toFinset_card_of_nodup hnodup
  have hlen : m.primeFactorsList.length = 5 := by omega
  obtain ⟨p, q, r, s, t, hlist⟩ := list_length_eq_five.mp hlen
  have hp := Nat.prime_of_mem_primeFactorsList
    (show p ∈ m.primeFactorsList by rw [hlist]; simp)
  have hq := Nat.prime_of_mem_primeFactorsList
    (show q ∈ m.primeFactorsList by rw [hlist]; simp)
  have hr := Nat.prime_of_mem_primeFactorsList
    (show r ∈ m.primeFactorsList by rw [hlist]; simp)
  have hs := Nat.prime_of_mem_primeFactorsList
    (show s ∈ m.primeFactorsList by rw [hlist]; simp)
  have ht := Nat.prime_of_mem_primeFactorsList
    (show t ∈ m.primeFactorsList by rw [hlist]; simp)
  have hchain := Nat.isChain_primeFactorsList m
  rw [hlist] at hchain
  simp only [List.isChain_cons_cons, List.isChain_singleton] at hchain
  rw [hlist] at hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnodup
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hrs : r < s := by omega
  have hst : s < t := by omega
  have hm_eq : m = p * q * r * s * t := by
    rw [← Nat.prod_primeFactorsList hm0, hlist]
    simp [mul_assoc]
  exact ⟨p, q, r, s, t, hp, hq, hr, hs, ht, hpq, hqr, hrs, hst, hm_eq⟩

private lemma computation_lemma_check :
    ∀ m ∈ Finset.Ico (m_BS + 1) (2 * m_BS), Odd m → Squarefree m → ¬(3 ∣ m) →
      2 * m - m * (∏ p ∈ Nat.primeFactors m, (1 - 1 / p : ℚ)) ≠ 2 * m_BS := by
  intro m hm hm_odd hm_sq hm_not_div3
  by_cases hcard_zero : m.primeFactors.card = 0
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at hcard_zero
    have hm_bounds := Finset.mem_Ico.mp hm
    omega
  by_cases hcard_one : m.primeFactors.card = 1
  · have hm_prime : m.Prime := by
      rw [← Nat.squarefree_and_prime_pow_iff_prime]
      exact ⟨hm_sq, isPrimePow_iff_card_primeFactors_eq_one.mpr hcard_one⟩
    exact computation_lemma_check_prime m hm_prime
  by_cases hcard_two : m.primeFactors.card = 2
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcard_two
    have hp_mem : p ∈ m.primeFactors := by simp [hset]
    have hq_mem : q ∈ m.primeFactors := by simp [hset]
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hm_eq : m = p * q := by
      rw [← Nat.prod_primeFactors_of_squarefree hm_sq, hset]
      simp [hpq]
    subst m
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat (dvd_mul_right 2 q)) (by norm_num)
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat (dvd_mul_left 2 p)) (by norm_num)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hm_not_div3 (dvd_mul_right 3 q)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hm_not_div3 (dvd_mul_left 3 p)
    simpa only [Nat.cast_mul] using
      computation_lemma_check_two_primes p q hp hq hpq hp2 hq2 hp3 hq3
  have hcard_le :=
    primeFactors_card_le_five m (Finset.mem_Ico.mp hm).2 hm_odd hm_sq hm_not_div3
  have hcard_cases : m.primeFactors.card = 3 ∨ m.primeFactors.card = 4 ∨
      m.primeFactors.card = 5 := by omega
  rcases hcard_cases with hcard_three | hcard_four | hcard_five
  · obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hm_eq⟩ :=
      squarefree_three_primeFactors m hm_sq hcard_three
    have hp_dvd : p ∣ m := by rw [hm_eq]; simp [mul_assoc]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat hp_dvd) (by norm_num)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hm_not_div3 hp_dvd
    have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    subst m
    simpa only [Nat.cast_mul] using computation_lemma_check_three_primes p q r hp hq hr
      hpq hqr hp5 (Finset.mem_Ico.mp hm).2
  · obtain ⟨p, q, r, s, hp, hq, hr, hs, hpq, hqr, hrs, hm_eq⟩ :=
      squarefree_four_primeFactors m hm_sq hcard_four
    have hp_dvd : p ∣ m := by rw [hm_eq]; simp [mul_assoc]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat hp_dvd) (by norm_num)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hm_not_div3 hp_dvd
    have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    subst m
    simpa only [Nat.cast_mul] using computation_lemma_check_four_primes p q r s hp hq hr hs
      hpq hqr hrs hp5 (Finset.mem_Ico.mp hm).2
  · obtain ⟨p, q, r, s, t, hp, hq, hr, hs, ht, hpq, hqr, hrs, hst, hm_eq⟩ :=
      squarefree_five_primeFactors m hm_sq hcard_five
    have hp_dvd : p ∣ m := by rw [hm_eq]; simp [mul_assoc]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (hm_odd.of_dvd_nat hp_dvd) (by norm_num)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hm_not_div3 hp_dvd
    have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    subst m
    simpa only [Nat.cast_mul] using computation_lemma_check_five_primes p q r s t hp hq hr
      hs ht hpq hqr hrs hst hp5 (Finset.mem_Ico.mp hm).2


lemma computation_lemma : ¬ ∃ m, IsSolution m := by
  -- We'll use the fact that if the conditions hold, then m must be in the
  -- range (509203, 1018406) and satisfy the equation.
  have h_check :
      ∀ m ∈ Finset.Ico (m_BS + 1) (2 * m_BS), Odd m → Squarefree m →
        ¬(3 ∣ m) → 2 * m - Nat.totient m ≠ 2 * m_BS := by
    -- We can check each m in this range to verify that
    -- 2m - φ(m) ≠ 2m_BS.
    have h_check :
        ∀ m ∈ Finset.Ico (m_BS + 1) (2 * m_BS), Odd m → Squarefree m →
          ¬(3 ∣ m) → 2 * m - Nat.totient m ≠ 2 * m_BS := by
      intro m hm hm_odd hm_sq hm_not_div3
      have h_phi : Nat.totient m = m * (∏ p ∈ Nat.primeFactors m, (1 - 1 / p : ℚ)) := by
        have := @Nat.totient_eq_mul_prod_factors m; aesop;
      have h_check := computation_lemma_check m hm hm_odd hm_sq hm_not_div3
      intro h_eq
      apply h_check
      have h_eq_cast : ((2 * m - m.totient : ℕ) : ℚ) = 2 * (m_BS : ℚ) := by
        exact_mod_cast h_eq
      rw [← h_phi, ← h_eq_cast]
      rw [Nat.cast_sub]
      · norm_num
      · exact le_trans (Nat.totient_le m) (by omega)
    assumption;
  contrapose! h_check;
  exact ⟨ h_check.choose,
    Finset.mem_Ico.mpr ⟨
      by linarith [ solution_bounds h_check.choose h_check.choose_spec ],
      by linarith [ solution_bounds h_check.choose h_check.choose_spec ] ⟩,
    h_check.choose_spec.1,
    solution_squarefree h_check.choose h_check.choose_spec,
    by
      have := n_not_div_3 h_check.choose h_check.choose_spec
      omega,
    h_check.choose_spec.2 ⟩


lemma base_case : IsNoncototient (2 * m_BS) := by
  -- We have proven that 2 * m_BS is a cototient iff there exists a solution
  -- m, and that there is no solution m.
  have h_base : IsCototient (2 * m_BS) ↔ ∃ m, IsSolution m := by
    -- Apply the base_case_reduction lemma to conclude the equivalence.
    apply base_case_reduction;
  exact fun h => computation_lemma.elim <| h_base.mp h


theorem browkin_schinzel (k : ℕ) (hk : 1 ≤ k) : IsNoncototient (2^k * m_BS) := by
  -- We proceed by induction on $k$.
  induction hk with
  | refl =>
    -- Apply the base_case lemma to conclude the proof for the base case.
    apply base_case
  | step hb ih =>
    rename_i k
    -- Apply the inductive step to $k+1$.
    apply inductive_step (k + 1) (by linarith [Nat.succ_le_iff.mp hb]) ih

/--
Are there infinitely many integers not of the form $n - \phi(n)$?

This is true, as shown by Browkin and Schinzel [BrSc95].

[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_.
Colloq. Math. (1995), 55-58.
-/
theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  -- Since the set {2^k * m_BS | k ≥ 1} is infinite, the set of noncototients
  -- must also be infinite.
  have h_infinite : Set.Infinite {x : ℕ | ∃ k ≥ 1, x = 2^k * m_BS} := by
    -- To prove the set is infinite, we show that the function
    -- $k \mapsto 2^k \cdot m_BS$ is injective.
    have h_inj : Function.Injective (fun k : ℕ => 2^k * m_BS) := by
      -- To prove injectivity, assume $2^a * m_BS = 2^b * m_BS$. Since
      -- $m_BS$ is non-zero, we can divide both sides by $m_BS$, yielding
      -- $2^a = 2^b$. The exponential function with base 2 is injective.
      intro a b hab
      have h_exp : 2^a = 2^b := by
        exact mul_right_cancel₀ ( show m_BS ≠ 0 by decide ) hab;
      -- Since the exponential function with base 2 is injective, if $2^a = 2^b$, then $a = b$.
      apply Nat.pow_right_injective (by norm_num) h_exp;
    exact Set.infinite_of_injective_forall_mem
      ( fun a b h => by simpa using h_inj h )
      fun k => ⟨ k + 1, by linarith, rfl ⟩;
  -- By Lemma~\ref{lem:browkin_schinzel}, each element of this set is a noncototient.
  have h_noncototient : ∀ k ≥ 1, IsNoncototient (2^k * m_BS) := by
    -- Apply browkin_schinzel to conclude that 2^k * m_BS is a noncototient.
    intros k hk
    apply browkin_schinzel k hk;
  exact h_infinite.mono fun x hx => by
    obtain ⟨ k, hk, rfl ⟩ := hx
    exact fun h => h_noncototient k hk <| by
      obtain ⟨ n, hn ⟩ := h
      exact ⟨ n, hn.symm ⟩ ;

#print axioms erdos_418
-- 'Erdos418.erdos_418' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos418
