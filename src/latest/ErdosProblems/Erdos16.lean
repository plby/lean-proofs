/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 16.
https://www.erdosproblems.com/forum/thread/16

Informal authors:
- Yong-Gao Chen

Formal authors:
- Gemini 3.1 Pro
- Antigravity
- Daniel Chin

URLs:
- https://github.com/danielchin/proofs/blob/main/Proofs/ErdosProblems/Erdos16.lean
- https://www.erdosproblems.com/forum/thread/16#post-4464
-/
import Mathlib

namespace Erdos16

open scoped Nat
open scoped Pointwise

set_option linter.style.setOption false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option linter.style.openClassical false
set_option linter.style.longLine false

open Classical

/-- The set of positive odd integers that cannot be represented as the sum of a prime and a power of two. -/
def U : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p + 2^k }

/-- A set has asymptotic density zero if it does not contain any infinite arithmetic progression. -/
def density_zero (S : Set ℕ) : Prop :=
  ∀ m a : ℕ, m > 0 → ¬ {x | ∃ k, x = m * k + a} ⊆ S

lemma density_zero_of_subset {S T : Set ℕ} (h : S ⊆ T) (hT : density_zero T) : density_zero S := by
  intro m a hm h_sub
  exact hT m a hm (Set.Subset.trans h_sub h)

lemma not_in_ap_mod (m_0 a_0 x : ℕ) (h : x % m_0 ≠ a_0 % m_0) : ¬ ∃ h', x = m_0 * h' + a_0 := by
  rintro ⟨h', rfl⟩
  have eq1 : (m_0 * h' + a_0) % m_0 = a_0 % m_0 := by
    rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  exact h eq1

lemma ap_sub_mod (m m_0 h_1 a k : ℕ) :
  (m * m_0 * k + (m * h_1 + a)) % m_0 = (m * h_1 + a) % m_0 := by
  have H : m * m_0 * k = m_0 * (m * k) := by ring
  rw [H, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
lemma dvd_of_add_mod_eq_mod (a c m : ℕ) (h : (c + a) % m = a % m) : m ∣ c := by
  -- Let (c + a) / m = q1 and a / m = q2
  -- Then c + a = q1 * m + r and a = q2 * m + r
  -- So c = (q1 - q2) * m
  have h_div_1 : c + a = m * ((c + a) / m) + (c + a) % m := (Nat.div_add_mod (c + a) m).symm
  have h_div_2 : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
  have h1 : c + a = ((c + a) / m) * m + a % m := by
    calc
      c + a = m * ((c + a) / m) + (c + a) % m := h_div_1
      _ = ((c + a) / m) * m + (c + a) % m := by rw [Nat.mul_comm]
      _ = ((c + a) / m) * m + a % m := by rw [h]
  have h2 : a = (a / m) * m + a % m := by
    calc
      a = m * (a / m) + a % m := h_div_2
      _ = (a / m) * m + a % m := by rw [Nat.mul_comm]
  have h3 : c + ((a / m) * m + a % m) = ((c + a) / m) * m + a % m := by
    calc
      c + ((a / m) * m + a % m) = c + a := by rw [←h2]
      _ = ((c + a) / m) * m + a % m := h1
  have h3_assoc : (c + (a / m) * m) + a % m = ((c + a) / m) * m + a % m := by
    calc
      (c + (a / m) * m) + a % m = c + ((a / m) * m + a % m) := Nat.add_assoc c ((a / m) * m) (a % m)
      _ = ((c + a) / m) * m + a % m := h3
  have h4 : c + (a / m) * m = ((c + a) / m) * m := Nat.add_right_cancel h3_assoc
  -- so c = ((c+a)/m - a/m) * m
  have h5 : c = ((c + a) / m - a / m) * m := by
    calc
      c = c + (a / m) * m - (a / m) * m := (Nat.add_sub_cancel c ((a / m) * m)).symm
      _ = ((c + a) / m) * m - (a / m) * m := by rw [h4]
      _ = ((c + a) / m - a / m) * m := (Nat.mul_sub_right_distrib ((c + a) / m) (a / m) m).symm
  have h6 : c = m * ((c + a) / m - a / m) := by
    calc
      c = ((c + a) / m - a / m) * m := h5
      _ = m * ((c + a) / m - a / m) := Nat.mul_comm _ _
  exact ⟨(c + a) / m - a / m, h6⟩

lemma lemma1 {m a m_0 a_0 : ℕ} {W : Set ℕ}
  (hW : density_zero W)
  (hU : U = { x | ∃ h, x = m_0 * h + a_0 } ∪ W)
  (hm : m > 0) (hm0 : m_0 > 0)
  (hSub : {x | ∃ h, x = m * h + a} ⊆ U) :
  m_0 ∣ m ∧ a % m_0 = a_0 % m_0 := by
  have H_all : ∀ h_1, (m * h_1 + a) % m_0 = a_0 % m_0 := by
    intro h_1
    by_cases h_eq : (m * h_1 + a) % m_0 = a_0 % m_0
    · exact h_eq
    · exfalso
      -- Construct the contradiction
      have h_not : ∀ k, (m * m_0 * k + (m * h_1 + a)) % m_0 ≠ a_0 % m_0 := by
        intro k
        rw [ap_sub_mod]
        exact h_eq
      have h_subW : {x | ∃ k, x = (m * m_0) * k + (m * h_1 + a)} ⊆ W := by
        rintro x ⟨k, rfl⟩
        have hA : (m * m_0) * k + (m * h_1 + a) = m * (m_0 * k + h_1) + a := by ring
        have h_in_U : (m * m_0) * k + (m * h_1 + a) ∈ U := by
          apply Set.mem_of_subset_of_mem hSub
          use m_0 * k + h_1
        have h_in_UW : (m * m_0) * k + (m * h_1 + a) ∈ { x | ∃ h, x = m_0 * h + a_0 } ∪ W := by
          rw [←hU]
          exact h_in_U
        cases h_in_UW with
        | inl hLeft =>
          exfalso
          apply not_in_ap_mod m_0 a_0 ((m * m_0) * k + (m * h_1 + a)) (h_not k) hLeft
        | inr hRight => exact hRight
      have hmm0 : m * m_0 > 0 := Nat.mul_pos hm hm0
      exact hW (m * m_0) (m * h_1 + a) hmm0 h_subW
  have ha : a % m_0 = a_0 % m_0 := by
    have H0 := H_all 0
    rwa [Nat.mul_zero, zero_add] at H0
  have hm_div : m_0 ∣ m := by
    have H1 := H_all 1
    rw [Nat.mul_one] at H1
    have H2 : (m + a) % m_0 = a % m_0 := by rw [H1, ha]
    exact dvd_of_add_mod_eq_mod a m m_0 H2
  exact ⟨hm_div, ha⟩

def P : ℕ := 11184810
def primes_list : List ℕ := [3, 5, 17, 7, 13, 241]

lemma first_ap_cover : ∀ k ∈ List.range 24, ∃ p ∈ primes_list, 992077 % p = (2^k) % p := by decide
lemma first_ap_no_prime : ∀ p' ∈ primes_list, ∀ k ∈ List.range 24, ∃ q ∈ primes_list, (p' + 2^k) % q ≠ 992077 % q := by decide

lemma second_ap_cover : ∀ k ∈ List.range 24, ∃ p ∈ primes_list, 3292241 % p = (2^k) % p := by decide
lemma second_ap_no_prime : ∀ p' ∈ primes_list, ∀ k ∈ List.range 24, ∃ q ∈ primes_list, (p' + 2^k) % q ≠ 3292241 % q := by decide

lemma two_pow_twenty_four_mod (q : ℕ) (hq : q ∈ primes_list) : (2^24) % q = 1 := by
  revert q hq
  decide

lemma two_pow_mod_eq_helper (m r q : ℕ) (hq : q ∈ primes_list) : (2^(m * 24 + r)) % q = (2^r) % q := by
  induction m with
  | zero =>
    rw [Nat.zero_mul, zero_add]
  | succ m ih =>
    have h1 : (m + 1) * 24 + r = 24 + (m * 24 + r) := by ring
    rw [h1, Nat.pow_add, Nat.mul_mod, two_pow_twenty_four_mod q hq, Nat.one_mul, Nat.mod_mod, ih]

lemma two_pow_mod_eq (k q : ℕ) (hq : q ∈ primes_list) : (2^k) % q = (2^(k % 24)) % q := by
  have h_div : k = (k / 24) * 24 + k % 24 := by omega
  nth_rw 1 [h_div]
  exact two_pow_mod_eq_helper (k / 24) (k % 24) q hq

lemma P_mod_q_eq_zero (q : ℕ) (hq : q ∈ primes_list) : P % q = 0 := by
  revert q hq
  decide

lemma mod_q_eq_of_in_ap (s a q : ℕ) (hq : q ∈ primes_list) : (P * s + a) % q = a % q := by
  have h1 : P * s % q = 0 := by
    rw [Nat.mul_mod, P_mod_q_eq_zero q hq, Nat.zero_mul, Nat.zero_mod]
  rw [Nat.add_mod, h1, zero_add, Nat.mod_mod]

lemma q_prime (q : ℕ) (hq : q ∈ primes_list) : q.Prime := by
  revert q hq
  decide

lemma prime_eq_of_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : q ∣ p) : p = q := by
  have h1 : q = 1 ∨ q = p := hp.eq_one_or_self_of_dvd q h
  rcases h1 with rfl | rfl
  · exfalso
    exact Nat.Prime.ne_one hq rfl
  · rfl

lemma firstap : {x | ∃ s, x = 11184810 * s + 992077} ⊆ U := by
  rintro n ⟨s, rfl⟩
  have h_odd : Odd (11184810 * s + 992077) := by
    use 5592405 * s + 496038
    have hP : 11184810 = 2 * 5592405 := rfl
    have ha : 992077 = 2 * 496038 + 1 := rfl
    calc
      11184810 * s + 992077 = (2 * 5592405) * s + (2 * 496038 + 1) := by rw [hP, ha]
      _ = 2 * (5592405 * s + 496038) + 1 := by ring
  refine ⟨h_odd, ?_⟩
  rintro ⟨p', k, hp, hk, heq⟩
  let r := k % 24
  have hr : r ∈ List.range 24 := by
    apply List.mem_range.mpr
    exact Nat.mod_lt k (by decide)
  have h_cov := first_ap_cover r hr
  rcases h_cov with ⟨q, hq, hq_eq⟩
  have h1 : (P * s + 992077) % q = 992077 % q := mod_q_eq_of_in_ap s 992077 q hq
  have h_add : (p' + 2^k) % q = (p' + 992077) % q := by
    calc
      (p' + 2^k) % q = (p' % q + 2^k % q) % q := Nat.add_mod p' (2^k) q
      _ = (p' % q + 2^r % q) % q := by rw [two_pow_mod_eq k q hq]
      _ = (p' % q + 992077 % q) % q := by rw [←hq_eq]
      _ = (p' + 992077) % q := (Nat.add_mod p' 992077 q).symm
  have heqP : P * s + 992077 = p' + 2^k := heq
  rw [heqP] at h1
  rw [h_add] at h1
  have h_dvd : q ∣ p' := dvd_of_add_mod_eq_mod 992077 p' q h1
  have hq_prime : q.Prime := q_prime q hq
  have hp_eq_q : p' = q := prime_eq_of_dvd hp hq_prime h_dvd
  have hp_in : p' ∈ primes_list := hp_eq_q.symm ▸ hq
  have h_no_prime := first_ap_no_prime p' hp_in r hr
  rcases h_no_prime with ⟨q2, hq2, hq2_neq⟩
  have h2 : (P * s + 992077) % q2 = 992077 % q2 := mod_q_eq_of_in_ap s 992077 q2 hq2
  have h_add2 : (p' + 2^k) % q2 = (p' + 2^r) % q2 := by
    calc
      (p' + 2^k) % q2 = (p' % q2 + 2^k % q2) % q2 := Nat.add_mod p' (2^k) q2
      _ = (p' % q2 + 2^r % q2) % q2 := by rw [two_pow_mod_eq k q2 hq2]
      _ = (p' + 2^r) % q2 := (Nat.add_mod p' (2^r) q2).symm
  rw [heqP] at h2
  rw [h_add2] at h2
  exact hq2_neq h2

lemma secondap : {x | ∃ s, x = 11184810 * s + 3292241} ⊆ U := by
  rintro n ⟨s, rfl⟩
  have h_odd : Odd (11184810 * s + 3292241) := by
    use 5592405 * s + 1646120
    have hP : 11184810 = 2 * 5592405 := rfl
    have ha : 3292241 = 2 * 1646120 + 1 := rfl
    calc
      11184810 * s + 3292241 = (2 * 5592405) * s + (2 * 1646120 + 1) := by rw [hP, ha]
      _ = 2 * (5592405 * s + 1646120) + 1 := by ring
  refine ⟨h_odd, ?_⟩
  rintro ⟨p', k, hp, hk, heq⟩
  let r := k % 24
  have hr : r ∈ List.range 24 := by
    apply List.mem_range.mpr
    exact Nat.mod_lt k (by decide)
  have h_cov := second_ap_cover r hr
  rcases h_cov with ⟨q, hq, hq_eq⟩
  have h1 : (P * s + 3292241) % q = 3292241 % q := mod_q_eq_of_in_ap s 3292241 q hq
  have h_add : (p' + 2^k) % q = (p' + 3292241) % q := by
    calc
      (p' + 2^k) % q = (p' % q + 2^k % q) % q := Nat.add_mod p' (2^k) q
      _ = (p' % q + 2^r % q) % q := by rw [two_pow_mod_eq k q hq]
      _ = (p' % q + 3292241 % q) % q := by rw [←hq_eq]
      _ = (p' + 3292241) % q := (Nat.add_mod p' 3292241 q).symm
  have heqP : P * s + 3292241 = p' + 2^k := heq
  rw [heqP] at h1
  rw [h_add] at h1
  have h_dvd : q ∣ p' := dvd_of_add_mod_eq_mod 3292241 p' q h1
  have hq_prime : q.Prime := q_prime q hq
  have hp_eq_q : p' = q := prime_eq_of_dvd hp hq_prime h_dvd
  have hp_in : p' ∈ primes_list := hp_eq_q.symm ▸ hq
  have h_no_prime := second_ap_no_prime p' hp_in r hr
  rcases h_no_prime with ⟨q2, hq2, hq2_neq⟩
  have h2 : (P * s + 3292241) % q2 = 3292241 % q2 := mod_q_eq_of_in_ap s 3292241 q2 hq2
  have h_add2 : (p' + 2^k) % q2 = (p' + 2^r) % q2 := by
    calc
      (p' + 2^k) % q2 = (p' % q2 + 2^k % q2) % q2 := Nat.add_mod p' (2^k) q2
      _ = (p' % q2 + 2^r % q2) % q2 := by rw [two_pow_mod_eq k q2 hq2]
      _ = (p' + 2^r) % q2 := (Nat.add_mod p' (2^r) q2).symm
  rw [heqP] at h2
  rw [h_add2] at h2
  exact hq2_neq h2

lemma not_in_U_5 : 5 ∉ U := by
  intro h
  rcases h with ⟨h_odd, h_not⟩
  apply h_not
  use 3, 1
  refine ⟨by decide, by decide, by decide⟩

lemma not_in_U_2 : 2 ∉ U := by
  intro h
  rcases h with ⟨h_odd, _⟩
  contradiction


lemma n_lt_two_pow (n : ℕ) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 2^n ≥ n + 1 := ih
    have h2 : 2^n ≥ 1 := by omega
    have h3 : 2^n + 2^n ≥ n + 1 + 1 := by omega
    have h4 : 2^n + 2^n = 2^(n + 1) := by ring
    omega

theorem ErdosProblem16 : ¬ ∃ m_0 a_0 : ℕ, m_0 > 0 ∧ ∃ W : Set ℕ, density_zero W ∧ U = { x | ∃ h, x = m_0 * h + a_0 } ∪ W := by
  rintro ⟨m_0, a_0, hm0, W, hW, hU⟩
  have h1 := lemma1 hW hU (by decide) hm0 firstap
  have h2 := lemma1 hW hU (by decide) hm0 secondap
  have H : m_0 ∣ 11184810 ∧ m_0 ∣ 2300164 := by
    refine ⟨h1.1, ?_⟩
    have heq : 3292241 % m_0 = 992077 % m_0 := by
      rw [h2.2, h1.2]
    have h_mod_add : (2300164 + 992077) % m_0 = 992077 % m_0 := by
      have hst : 2300164 + 992077 = 3292241 := by decide
      rw [hst, heq]
    exact dvd_of_add_mod_eq_mod 992077 2300164 m_0 h_mod_add
  have H2 : m_0 ∣ gcd 11184810 2300164 := Nat.dvd_gcd H.1 H.2
  have H3 : gcd 11184810 2300164 = 2 := by decide
  rw [H3] at H2
  have hm0_le : m_0 ≤ 2 := Nat.le_of_dvd (by decide) H2
  have hA_sub_U : { x | ∃ h, x = m_0 * h + a_0 } ⊆ U := by
    intro x hx
    have h_in_UW : x ∈ { x | ∃ h, x = m_0 * h + a_0 } ∪ W := Set.mem_union_left W hx
    rw [←hU] at h_in_UW
    exact h_in_UW
  have h_m0_cases : m_0 = 1 ∨ m_0 = 2 := by omega
  rcases h_m0_cases with rfl | rfl
  · have h1_in : a_0 ∈ U := by
      apply hA_sub_U
      use 0
      ring
    have h2_in : a_0 + 1 ∈ U := by
      apply hA_sub_U
      use 1
      ring
    have h1_odd : Odd a_0 := h1_in.1
    have h2_odd : Odd (a_0 + 1) := h2_in.1
    rcases h1_odd with ⟨k1, hk1⟩
    rcases h2_odd with ⟨k2, hk2⟩
    omega
  · have h1_in : a_0 ∈ U := by
      apply hA_sub_U
      use 0
      ring
    have h1_odd : Odd a_0 := h1_in.1
    let x := 3 + 2^(a_0 + 1)
    have hx_odd : Odd x := by
      use 1 + 2^a_0
      calc
        x = 3 + 2^(a_0 + 1) := rfl
        _ = 3 + 2 * 2^a_0 := by ring
        _ = 2 * (1 + 2^a_0) + 1 := by ring
    rcases hx_odd with ⟨k1, hk1⟩
    rcases h1_odd with ⟨k2, hk2⟩
    have hx_ge : x ≥ a_0 := by
      have hlt : a_0 + 1 + 1 ≤ 2^(a_0 + 1) := n_lt_two_pow (a_0 + 1)
      have h1 : 3 + (a_0 + 2) ≥ a_0 := by omega
      calc
        x = 3 + 2^(a_0 + 1) := rfl
        _ ≥ 3 + (a_0 + 2) := Nat.add_le_add_left hlt 3
        _ ≥ a_0 := h1
    have hk12 : k1 ≥ k2 := by omega
    have hx_a : x = 2 * (k1 - k2) + a_0 := by omega
    have hx_in_A : x ∈ { x | ∃ h, x = 2 * h + a_0 } := by
      use k1 - k2
    have hx_in_U : x ∈ U := hA_sub_U hx_in_A
    have hx_not_in_U : x ∉ U := by
      intro h
      rcases h with ⟨-, h_not⟩
      apply h_not
      use 3, a_0 + 1
      refine ⟨by decide, by omega, rfl⟩
    exact hx_not_in_U hx_in_U

#print axioms ErdosProblem16
-- 'Erdos16.ErdosProblem16' depends on axioms: [propext, choice, Quot.sound]

end Erdos16
