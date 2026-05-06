import Mathlib
import Aesop
set_option linter.style.setOption false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open Filter


noncomputable def S (n : ℕ) : ℕ :=
  sSup {s | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^s ∣n.choose k}




namespace depth_0_lemma_1

lemma round1_h_q_ne_two (R : ℕ) (hR : R ≥ 1) (q : ℕ) (hq_prime : Nat.Prime q)
  (hq_dvd : q ∣ (2 ^ (2 * Nat.factorial R) + 1)) : q ≠ 2 := by
  intro h
  rw [h] at hq_dvd
  have h₅ : 2 ∣ (2 ^ (2 * Nat.factorial R) + 1) := hq_dvd
  have h₆ : 2 * Nat.factorial R ≠ 0 := by
    have h₇ : Nat.factorial R ≥ 1 := Nat.factorial_pos R
    omega
  have h₉ : (2 ^ (2 * Nat.factorial R)) % 2 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply dvd_pow_self 2 h₆
  have h₁₀ : (2 ^ (2 * Nat.factorial R) + 1) % 2 = 1 := by
    omega
  have h₁₁ : (2 ^ (2 * Nat.factorial R) + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h₅
  omega

lemma round1_h_coprime (q : ℕ) (hq_prime : Nat.Prime q) (h_q_ne_two : q ≠ 2) :
  Nat.Coprime 2 q := by
  have h₁ : Nat.Prime q := hq_prime
  have h₂ : q ≠ 2 := h_q_ne_two
  have h₃ : Nat.gcd 2 q ∣ 2 := Nat.gcd_dvd_left 2 q
  have h₄ : Nat.gcd 2 q = 1 ∨ Nat.gcd 2 q = 2 := by
    have h₅ : Nat.gcd 2 q ∣ 2 := h₃
    have h₆ : Nat.gcd 2 q ≤ 2 := Nat.le_of_dvd (by norm_num) h₅
    interval_cases h₇ : Nat.gcd 2 q <;> tauto
  cases h₄ with
  | inl h₄ =>
    exact h₄
  | inr h₄ =>
    have h₅ : Nat.gcd 2 q = 2 := h₄
    have h₆ : 2 ∣ q := by
      have h₇ : Nat.gcd 2 q ∣ q := Nat.gcd_dvd_right 2 q
      rw [h₅] at h₇
      exact h₇
    have h₇ : q = 2 := by
      have h₈ : Nat.Prime q := h₁
      have h₉ : 2 ∣ q := h₆
      have h₁₀ := Nat.Prime.eq_one_or_self_of_dvd h₈ 2 h₉
      omega
    contradiction

lemma round1_h_q_gt_R (R : ℕ) (hR : R ≥ 1) (q : ℕ) (hq_prime : Nat.Prime q)
  (hq_dvd : q ∣ (2 ^ (2 * Nat.factorial R) + 1)) (h_q_ne_two : q ≠ 2) : q > R := by
  by_contra h
  have h₅ : q ≤ R := by omega
  have h₆ : Nat.Prime q := hq_prime
  have h₇ : q > 1 := Nat.Prime.one_lt h₆
  have h₈ : q - 1 ∣ Nat.factorial R := by
    apply Nat.dvd_factorial
    <;> omega
  have h₉ : q - 1 ∣ 2 * Nat.factorial R := dvd_mul_of_dvd_right h₈ 2
  have h₁₀ : Nat.Coprime 2 q := round1_h_coprime q h₆ h_q_ne_two
  have h₁₁ : Nat.totient q = q - 1 := by
    rw [Nat.totient_prime h₆] <;> omega
  have h₁₂ : Nat.ModEq q (2 ^ (q - 1)) 1 := by
    have h₁₃ : Nat.ModEq q (2 ^ Nat.totient q) 1 := Nat.ModEq.pow_totient h₁₀
    rw [h₁₁] at h₁₃
    exact h₁₃
  rcases h₉ with ⟨k, hk⟩
  have h₁₃ : Nat.ModEq q (2 ^ (2 * Nat.factorial R)) 1 := by
    have h₁₄ : 2 * Nat.factorial R = (q - 1) * k := by linarith
    rw [h₁₄]
    simpa [pow_mul] using h₁₂.pow k
  have h₁₄ : Nat.ModEq q (2 ^ (2 * Nat.factorial R) + 1) 0 := by
    simpa [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] using hq_dvd
  have h₁₅ : Nat.ModEq q (2 ^ (2 * Nat.factorial R) + 1) (1 + 1) := by
    exact Nat.ModEq.add h₁₃ (Nat.ModEq.refl 1)
  have h₁₆ : Nat.ModEq q (1 + 1) 0 := h₁₅.symm.trans h₁₄
  have h₁₇ : q ∣ 2 := by
    simpa [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] using h₁₆
  have h₁₈ : q = 2 := by
    have h₁₉ : q ∣ 2 := h₁₇
    have h₂₀ : q ≤ 2 := Nat.le_of_dvd (by norm_num) h₁₉
    interval_cases q <;> tauto
  contradiction

lemma round1_h_main₁ (R : ℕ) (hR : R ≥ 1) :
  ∃ (q : ℕ), Nat.Prime q ∧ q ∣ (2 ^ (2 * Nat.factorial R) + 1) ∧ q > R ∧ q ≠ 2 := by
  let L₀ := 2 * Nat.factorial R
  let N := 2 ^ L₀ + 1
  have hN_gt_one : N ≠ 1 := by
    have h₁ : L₀ ≥ 2 := by
      have h₂ : Nat.factorial R ≥ 1 := Nat.factorial_pos R
      omega
    have h₃ : 2 ^ L₀ ≥ 4 := by
      have h₄ : L₀ ≥ 2 := h₁
      have h₅ : 2 ^ L₀ ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h₄
      omega
    have h₄ : N > 1 := by omega
    omega
  have h₁ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ N := Nat.exists_prime_and_dvd hN_gt_one
  rcases h₁ with ⟨q, hq_prime, hq_dvd_N⟩
  have h₂ : q ∣ 2 ^ L₀ + 1 := hq_dvd_N
  have h₃ : q ≠ 2 := round1_h_q_ne_two R hR q hq_prime h₂
  have h₄ : q > R := round1_h_q_gt_R R hR q hq_prime h₂ h₃
  exact ⟨q, hq_prime, h₂, h₄, h₃⟩

lemma round1_h_goal (q : ℕ) (hq_prime : Nat.Prime q) (hq_odd : q % 2 = 1)
  (t : ℕ) (ht_ge_one : t ≥ 1) (a : ℤ) :
  (q : ℤ) ^ (t + 1) ∣ ((a * (q : ℤ) ^ t - 1) ^ q + 1) := by
  let y : ℤ := (q : ℤ)
  have h₁ : (a * y ^ t - 1) = (-1 : ℤ) + (a * y ^ t) := by ring
  have h_main₁ : ((a * y ^ t - 1) ^ q)
    = ∑ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i := by
    rw [h₁]
    rw [add_comm]
    rw [add_pow]
    <;> simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring
  have h₂ : Finset.range (q + 1) = insert 0 (insert 1 (Finset.Ico 2 (q + 1))) := by
    ext x
    simp [Finset.mem_range, Finset.mem_Ico]
    <;> omega
  have h₃ : ∑ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i
    = (Nat.choose q 0 : ℤ) * ((-1 : ℤ) ^ (q - 0)) * (a * y ^ t) ^ 0
      + (Nat.choose q 1 : ℤ) * ((-1 : ℤ) ^ (q - 1)) * (a * y ^ t) ^ 1
      + ∑ i ∈ Finset.Ico 2 (q + 1), (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i := by
    rw [h₂]
    <;> simp [Finset.sum_insert, Finset.sum_Ico_succ_top]
    <;> ring
  have h₄ : (Nat.choose q 0 : ℤ) = 1 := by simp
  have h₅ : (Nat.choose q 1 : ℤ) = (q : ℤ) := by simp [Nat.choose_one_right]
  have h₆ : (q : ℤ) % 2 = 1 := by exact_mod_cast hq_odd
  have h₇ : (-1 : ℤ) ^ q = -1 := by
    have h₈ : ∃ k, q = 2 * k + 1 := by
      use q / 2
      omega
    rcases h₈ with ⟨k, hk⟩
    rw [hk]
    <;> simp [pow_add, pow_mul]
    <;> ring
  have h₉ : (-1 : ℤ) ^ (q - 1) = 1 := by
    have h₁₀ : ∃ k, q - 1 = 2 * k := by
      use (q - 1) / 2
      omega
    rcases h₁₀ with ⟨k, hk⟩
    rw [hk]
    <;> simp [pow_add, pow_mul]
    <;> ring
  set S := ∑ i ∈ Finset.Ico 2 (q + 1), (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i with hS
  have h_term0 : (Nat.choose q 0 : ℤ) * ((-1 : ℤ) ^ (q - 0)) * (a * y ^ t) ^ 0 = (-1 : ℤ) := by
    rw [h₄, pow_zero, mul_one]
    <;> simpa using h₇
  have h_term1 : (Nat.choose q 1 : ℤ) * ((-1 : ℤ) ^ (q - 1)) * (a * y ^ t) ^ 1 = a * y ^ (t + 1) := by
    rw [h₅, pow_one]
    <;> rw [h₉] <;> ring
  have h₁₀ : ∑ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i
    = (-1 : ℤ) + (a * y ^ (t + 1)) + S := by
    rw [h₃, h_term0, h_term1, hS] <;> ring
  have h₁₁ : ((a * y ^ t - 1) ^ q + 1) = a * y ^ (t + 1) + S := by
    linarith [h_main₁, h₁₀]
  have h₁₂ : ∀ i ∈ Finset.Ico 2 (q + 1), (y ^ (t + 1)) ∣ (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a * y ^ t) ^ i := by
    intro i hi
    have h₁₃ : 2 ≤ i := Finset.mem_Ico.mp hi |>.1
    have h₁₄ : (a * y ^ t) ^ i = a ^ i * (y ^ t) ^ i := by ring
    rw [h₁₄]
    have h₁₅ : (y ^ t) ^ i = y ^ (t * i) := by rw [← pow_mul] <;> ring
    rw [h₁₅]
    have h₁₆ : t + 1 ≤ t * i := by nlinarith
    have h₁₇ : y ^ (t + 1) ∣ y ^ (t * i) := by apply pow_dvd_pow <;> omega
    have h₁₈ : y ^ (t + 1) ∣ (Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a ^ i) * (y ^ (t * i)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_right h₁₇ ((Nat.choose q i : ℤ) * ((-1 : ℤ) ^ (q - i)) * (a ^ i))
    simpa [mul_assoc, mul_comm, mul_left_comm] using h₁₈
  have h₁₉ : (y ^ (t + 1)) ∣ S := by
    rw [hS]
    apply Finset.dvd_sum
    intro i hi
    exact h₁₂ i hi
  have h₂₀ : (y ^ (t + 1)) ∣ (a * y ^ (t + 1)) := by
    use a <;> ring
  have h₂₁ : (y ^ (t + 1)) ∣ (a * y ^ (t + 1) + S) := by
    apply dvd_add h₂₀ h₁₉
  rw [h₁₁]
  exact h₂₁

lemma round1_h_main_induction (q : ℕ) (hq_prime : Nat.Prime q) (hq_odd : q % 2 = 1)
  (d : ℕ) (hd_pos : d > 0) (h_div : q ∣ 2 ^ d + 1) :
  ∀ m : ℕ, q ^ (m + 1) ∣ 2 ^ (d * q ^ m) + 1 := by
  intro m
  induction m with
  | zero =>
    simpa using h_div
  | succ m ih =>
    have h₁ : q ^ (m + 1) ∣ 2 ^ (d * q ^ m) + 1 := ih
    have h₂ : ∃ (a : ℕ), (2 ^ (d * q ^ m) + 1) = a * q ^ (m + 1) := by
      exact exists_eq_mul_left_of_dvd ih
    rcases h₂ with ⟨a, ha⟩
    have h₃ : ((2 ^ (d * q ^ m) : ℤ) + 1) = (a : ℤ) * (q : ℤ) ^ (m + 1) := by
      exact_mod_cast ha
    have h₄ : (q : ℤ) ^ (m + 2) ∣ ((2 ^ (d * q ^ m) : ℤ) ^ q + 1) := by
      have h₅ : ((2 ^ (d * q ^ m) : ℤ) ^ q + 1) = (( (a : ℤ) * (q : ℤ) ^ (m + 1) - 1) ^ q + 1) := by
        have h₆ : (2 ^ (d * q ^ m) : ℤ) = (a : ℤ) * (q : ℤ) ^ (m + 1) - 1 := by linarith
        rw [h₆]
        <;> ring
      rw [h₅]
      exact round1_h_goal q hq_prime hq_odd (m + 1) (by omega) (a : ℤ)
    have h₅ : (2 ^ (d * q ^ (m + 1)) : ℤ) = ((2 ^ (d * q ^ m) : ℤ) ^ q) := by
      have h₆ : d * q ^ (m + 1) = d * q ^ m * q := by
        ring
      rw [h₆]
      <;> rw [pow_mul]
      <;> ring
    have h₆ : (q : ℤ) ^ (m + 2) ∣ (2 ^ (d * q ^ (m + 1)) : ℤ) + 1 := by
      rw [h₅] at *
      exact h₄
    exact_mod_cast h₆

lemma round1_h_sub_mul (k : ℕ) (hk : k ≥ 1) (n : ℕ) (hn : n > 0) :
  k * n - 1 = (k - 1) * n + (n - 1) := by
  cases k with
  | zero =>
    exfalso
    linarith
  | succ k' =>
    simp [Nat.mul_succ, Nat.add_assoc]
    <;> ring_nf at * <;> omega

lemma round2_h_mod_eq (k n : ℕ) (hk : k ≥ 1) (hn : n > 0) :
  (k * n - 1) % n = n - 1 := by
  have h1 : k * n - 1 = (k - 1) * n + (n - 1) := round1_h_sub_mul k hk n hn
  rw [h1]
  have h2 : (((k - 1) * n) % n) = 0 := by
    simp [Nat.mul_mod]
  rw [Nat.add_mod]
  rw [h2]
  have h3 : (0 + (n - 1) % n) % n = (n - 1) % n := by simp
  rw [h3]
  have h4 : (n - 1) % n = n - 1 := by
    apply Nat.mod_eq_of_lt
    omega
  rw [h4]

theorem dirichlet_type_lemma :
  ∀ (M : ℕ) (hM : M ≥ 1) (R : ℕ) (hR : R ≥ 1),
  ∃ (q L : ℕ), Nat.Prime q ∧ q > R ∧ L ≥ 1 ∧ (2 ^ L) % (q ^ M) = q ^ M - 1  := by
  intro M hM R hR
  have h_main₁ : ∃ (q : ℕ), Nat.Prime q ∧ q ∣ (2 ^ (2 * Nat.factorial R) + 1) ∧ q > R ∧ q ≠ 2 :=
    round1_h_main₁ R hR
  rcases h_main₁ with ⟨q, hq_prime, hq_div, hq_gt_R, hq_ne_two⟩
  have hq_pos : q > 0 := Nat.Prime.pos hq_prime
  have hq_odd : q % 2 = 1 := by
    have h₁ : Nat.Prime q := hq_prime
    have h₂ : q ≠ 2 := hq_ne_two
    have h₃ := Nat.Prime.eq_two_or_odd h₁
    omega
  set d := 2 * Nat.factorial R with hd
  have hd_pos : d > 0 := by
    have h₁ : Nat.factorial R ≥ 1 := Nat.factorial_pos R
    omega
  have h_div : q ∣ 2 ^ d + 1 := hq_div
  have h_main_induction : ∀ m : ℕ, q ^ (m + 1) ∣ 2 ^ (d * q ^ m) + 1 :=
    round1_h_main_induction q hq_prime hq_odd d hd_pos h_div
  have hM' : ∃ m : ℕ, M = m + 1 := by
    refine' ⟨M - 1, _⟩
    omega
  rcases hM' with ⟨m, rfl⟩
  have h₁ : q ^ (m + 1) ∣ 2 ^ (d * q ^ m) + 1 := h_main_induction m
  set L := d * q ^ m with hL
  have hq_pow_pos : q ^ m > 0 := by
    apply Nat.pow_pos hq_pos
  have hL_pos : L ≥ 1 := by
    have h₂ : d > 0 := hd_pos
    have h₃ : q ^ m > 0 := hq_pow_pos
    have h₄ : d * q ^ m > 0 := mul_pos h₂ h₃
    linarith
  have h₂ : q ^ (m + 1) ∣ 2 ^ L + 1 := h₁
  have h₃ : ∃ k : ℕ, 2 ^ L + 1 = k * q ^ (m + 1) := by
    exact exists_eq_mul_left_of_dvd (h_main_induction m)
  rcases h₃ with ⟨k, hk⟩
  have h₄ : q ^ (m + 1) > 0 := by
    apply Nat.pow_pos hq_pos
  have h₅ : 2 ^ L + 1 > 0 := by positivity
  have h₆ : k * q ^ (m + 1) > 0 := by
    linarith [hk]
  have h₇ : k > 0 := by
    by_contra h
    have h₈ : k = 0 := by omega
    rw [h₈] at hk
    <;> simp at hk <;> omega
  have h₉ : 2 ^ L = k * q ^ (m + 1) - 1 := by
    omega
  have h₁₀₁ : (2 ^ L) % (q ^ (m + 1)) = (k * q ^ (m + 1) - 1) % (q ^ (m + 1)) := by
    rw [h₉]
  have h₁₀₂ : (k * q ^ (m + 1) - 1) % (q ^ (m + 1)) = q ^ (m + 1) - 1 :=
    round2_h_mod_eq k (q ^ (m + 1)) h₇ h₄
  have h₁₀ : (2 ^ L) % (q ^ (m + 1)) = q ^ (m + 1) - 1 := by
    rw [h₁₀₁]
    exact h₁₀₂
  refine' ⟨q, L, hq_prime, hq_gt_R, hL_pos, _⟩
  simpa using h₁₀
end depth_0_lemma_1

namespace depth_0_lemma_2

lemma round1_h1 (q M D : ℕ) (hM1 : 1 ≤ M) (hq : Nat.Prime q)
  (hD_mod : D % (q ^ M) = q ^ M - 1) :
  ∀ (i : ℕ), 1 ≤ i → i ≤ M → D % (q ^ i) = q ^ i - 1 := by
  intro i hi1 hi2
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have h2 : q ^ i ∣ q ^ M := by
    apply pow_dvd_pow
    <;> linarith
  have h3 : D % (q ^ i) = (D % (q ^ M)) % (q ^ i) := by
    rw [← Nat.mod_mod_of_dvd D h2]
  rw [h3, hD_mod]
  have h4 : q ^ i > 0 := by positivity
  have h7 : ∃ t : ℕ, q ^ M = t * q ^ i := by
    exact exists_eq_mul_left_of_dvd h2
  rcases h7 with ⟨t, ht⟩
  have h8 : t > 0 := by
    by_contra h9
    have h10 : t = 0 := by omega
    rw [h10] at ht
    have h11 : q ^ M = 0 := by simpa using ht
    have h12 : q ^ M > 0 := by
      apply Nat.pow_pos hq_pos
    linarith
  have h9 : q ^ M - 1 = (t - 1) * q ^ i + (q ^ i - 1) := by
    rw [ht]
    <;> cases t <;> simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.add_mul] <;> ring_nf at * <;> omega
  have h10 : (q ^ M - 1) % (q ^ i) = q ^ i - 1 := by
    rw [h9]
    <;> simp [Nat.add_mod, Nat.mul_mod, h4]
    <;> omega
  exact h10

lemma subgoal1 (q i j : ℕ) (h1 : 0 < q ^ i) (h2 : 0 < j) (h3 : j < q ^ i) :
  j * (q ^ i - 1) % (q ^ i) = q ^ i - j := by
  have h4 : j * (q ^ i - 1) = (j - 1) * (q ^ i) + (q ^ i - j) := by
    cases j with
    | zero => omega
    | succ j' =>
      simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.add_mul] <;> ring_nf <;> omega
  rw [h4]
  have h5 : (( (j - 1) * (q ^ i) + (q ^ i - j) ) % (q ^ i)) = (q ^ i - j) := by
    have h6 : (( (j - 1) * (q ^ i) + (q ^ i - j) ) % (q ^ i)) = (((j - 1) * (q ^ i)) % (q ^ i) + (q ^ i - j) % (q ^ i)) % (q ^ i) := by
      simp [Nat.add_mod]
    rw [h6]
    have h7 : ((j - 1) * (q ^ i)) % (q ^ i) = 0 := by
      simp [Nat.mul_mod]
    rw [h7]
    have h8 : (0 + (q ^ i - j) % (q ^ i)) % (q ^ i) = (q ^ i - j) % (q ^ i) := by simp
    rw [h8]
    have h9 : q ^ i - j < q ^ i := by omega
    have h10 : (q ^ i - j) % (q ^ i) = q ^ i - j := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h10]
  exact h5

lemma subgoal2 (q i R j : ℕ) (h1 : 0 < q ^ i) (h2 : R > j) (h3 : R - j < q ^ i) :
  (R - j) * (q ^ i - 1) % (q ^ i) = q ^ i - (R - j) := by
  have h4 : 0 < R - j := by omega
  have h5 : (R - j) * (q ^ i - 1) % (q ^ i) = q ^ i - (R - j) := by
    exact subgoal1 q i (R - j) h1 h4 h3
  exact h5

lemma subgoal3 (q i R : ℕ) (hi1 : 1 ≤ i) (h_q_gt_R : q > R) (hR : R ≥ 1) :
  q ^ i > R := by
  have h4 : q ^ i ≥ q := by
    have h5 : i ≥ 1 := by linarith
    have h6 : q > 0 := by linarith
    have h7 : q ^ i ≥ q ^ 1 := by
      apply Nat.pow_le_pow_right
      · omega
      · exact h5
    simpa using h7
  linarith

lemma round1_h2 (q M R j D : ℕ) (hM1 : 1 ≤ M) (hq : Nat.Prime q) (hR : R ≥ 1) (hD : D ≥ 1)
  (h_j1 : 1 ≤ j) (h_j2 : j < R) (h_q_gt_R : q > R) (hD_mod : D % (q ^ M) = q ^ M - 1) :
  ∀ (i : ℕ), 1 ≤ i → i ≤ M → q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i)) := by
  have h1 := round1_h1 q M D hM1 hq hD_mod
  intro i hi1 hi2
  have h4 : 1 ≤ i := hi1
  have h5 : i ≤ M := hi2
  have h6 : D % (q ^ i) = q ^ i - 1 := h1 i h4 h5
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have hq_i_pos : 0 < q ^ i := by positivity
  have h7 : q ^ i > R := subgoal3 q i R h4 h_q_gt_R hR
  have h71 : j < q ^ i := by linarith
  have h72 : 0 < j := by linarith
  have h73 : (j * D) % (q ^ i) = (q ^ i - j) := by
    have h74 : (j * D) % (q ^ i) = (j * (D % (q ^ i))) % (q ^ i) := by
      simp [Nat.mul_mod]
    rw [h74, h6]
    <;> exact subgoal1 q i j hq_i_pos h72 h71
  have h81 : R - j > 0 := by omega
  have h82 : R - j < q ^ i := by omega
  have h84 : j ≤ R := by linarith
  have h85 : R * D = j * D + (R - j) * D := by
    have h86 : R = j + (R - j) := by omega
    rw [h86]
    <;> simp [mul_add, add_mul]
    <;> ring
  have h86 : R * D - j * D = (R - j) * D := by
    omega
  have h83 : ((R * D - j * D) % (q ^ i)) = (q ^ i - (R - j)) := by
    rw [h86]
    have h87 : ((R - j) * D) % (q ^ i) = ((R - j) * (D % (q ^ i))) % (q ^ i) := by
      simp [Nat.mul_mod]
    rw [h87, h6]
    <;> exact subgoal2 q i R j hq_i_pos (by omega) h82
  rw [h73, h83]
  <;> omega

theorem kummer_application_lemma :
  ∀ (q R D M : ℕ) (hq : Nat.Prime q) (hR : R ≥ 1) (hD : D ≥ 1) (hM : M ≥ 1) (h_q_gt_R : q > R)
  (hD_mod : D % (q ^ M) = q ^ M - 1),
  ∀ (j : ℕ), 1 ≤ j → j < R → q ^ M ∣ ((R * D).choose (j * D))  := by
  intro q R D M hq hR hD hM h_q_gt_R hD_mod j hj1 hj2
  have hM1 : 1 ≤ M := by linarith
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have hqM_pos : 0 < q ^ M := by
    apply Nat.pow_pos hq_pos
  have h_main2 : ∀ (i : ℕ), 1 ≤ i → i ≤ M → q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i)) :=
    round1_h2 q M R j D hM1 hq hR hD hj1 hj2 h_q_gt_R hD_mod
  have h_main3 : ∀ (i : ℕ), i ∈ Finset.Ico 1 (M + 1) → q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i)) := by
    intro i hi
    have h9 : 1 ≤ i ∧ i < M + 1 := Finset.mem_Ico.mp hi
    have h10 : 1 ≤ i := h9.1
    have h11 : i ≤ M := by linarith
    exact h_main2 i h10 h11
  have h_pos : 0 < R * D := by positivity
  have h14 : D % (q ^ M) = q ^ M - 1 := hD_mod
  have h15 : (D + 1) % (q ^ M) = 0 := by
    have h16 : (D + 1) % (q ^ M) = ((D % (q ^ M)) + 1) % (q ^ M) := by
      simp [Nat.add_mod]
    rw [h16, h14]
    have h17 : ((q ^ M - 1) + 1) % (q ^ M) = 0 := by
      have h18 : (q ^ M - 1) + 1 = q ^ M := by omega
      rw [h18]
      <;> simp [hqM_pos]
    exact h17
  have h17 : q ^ M ∣ D + 1 := Nat.dvd_of_mod_eq_zero h15
  have h18 : q ^ M ≤ D + 1 := Nat.le_of_dvd (by positivity) h17
  have h19 : q ^ M ≤ R * D := by nlinarith
  have h20 : M ≤ Nat.log q (R * D) := by
    apply Nat.le_log_of_pow_le (show 1 < q by linarith [Nat.Prime.one_lt hq]) h19
  let b := Nat.log q (R * D) + 1
  have hnb : Nat.log q (R * D) < b := by
    dsimp only [b] <;> omega
  have hkn : j * D ≤ R * D := by
    have h12 : j ≤ R := by linarith
    nlinarith
  have h_main4 : (Nat.choose (R * D) (j * D)).factorization q ≥ M := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    have h_eq : (Nat.choose (R * D) (j * D)).factorization q = (Finset.filter (fun i : ℕ => q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i))) (Finset.Ico 1 b)).card := by
      rw [Nat.factorization_choose hq hkn hnb] <;> rfl
    rw [h_eq]
    have h1b : 1 < b := by
      dsimp only [b] <;> omega
    have h5 : M + 1 ≤ b := by
      dsimp only [b] <;> omega
    have h6 : Finset.Ico 1 (M + 1) ⊆ Finset.Ico 1 b := by
      apply Finset.Ico_subset_Ico_right h5
    have h7 : Finset.Ico 1 (M + 1) ⊆ Finset.filter (fun i : ℕ => q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i))) (Finset.Ico 1 b) := by
      intro x hx
      simp only [Finset.mem_filter] at *
      <;> exact ⟨h6 hx, h_main3 x hx⟩
    have h9 : (Finset.Ico 1 (M + 1)).card ≤ (Finset.filter (fun i : ℕ => q ^ i ≤ (j * D) % (q ^ i) + ((R * D - j * D) % (q ^ i))) (Finset.Ico 1 b)).card := Finset.card_le_card h7
    have h10 : (Finset.Ico 1 (M + 1)).card = M := by
      simp [Finset.Ico_eq_empty_of_le, hM1]
      <;> omega
    rw [h10] at h9
    <;> omega
  have h_pos2 : 0 < Nat.choose (R * D) (j * D) := Nat.choose_pos hkn
  have h_ne_zero : Nat.choose (R * D) (j * D) ≠ 0 := by linarith
  have h12 : q ^ M ∣ Nat.choose (R * D) (j * D) := by
    have h13 : M ≤ (Nat.choose (R * D) (j * D)).factorization q := h_main4
    have h14 : q ^ M ∣ Nat.choose (R * D) (j * D) := (Nat.Prime.pow_dvd_iff_le_factorization hq h_ne_zero).mpr h13
    exact h14
  exact h12
end depth_0_lemma_2

namespace depth_0_lemma_3

lemma round1_h_main (M L n k : ℕ) (hL : L ≥ 1) (hk1 : 1 ≤ k) (hk3 : ¬(2 ^ L ∣ k)) :
  Nat.factorization k 2 ≤ L - 1 := by
  by_contra h
  have h' : Nat.factorization k 2 ≥ L := by omega
  have h1 : Nat.factorization k 2 = padicValNat 2 k := by
    rw [Nat.factorization_def k (by norm_num)]
  rw [h1] at h'
  have h2 : (2 ^ (padicValNat 2 k)) ∣ k := by
    exact pow_padicValNat_dvd
  have h3 : (2 ^ L) ∣ (2 ^ (padicValNat 2 k)) := by
    apply pow_dvd_pow
    <;> omega
  have h4 : (2 ^ L) ∣ k := dvd_trans h3 h2
  exact hk3 h4

theorem valuation_2_lemma :
  ∀ (M L n k : ℕ) (hM : M ≥ 1) (hL : L ≥ 1) (hn : n = 2 ^ (M + L - 1))
  (hk1 : 1 ≤ k) (hk2 : k < n) (hk3 : ¬(2 ^ L ∣ k)),
  2 ^ M ∣ (n.choose k)  := by
  intro M L n k hM hL hn hk1 hk2 hk3
  have h_k_pos : 0 < k := by linarith
  have h_k_ne_zero : k ≠ 0 := by linarith
  have h_j_lt_n : k - 1 < n := by omega
  have h_main1 : Nat.factorization k 2 ≤ L - 1 := round1_h_main M L n k hL hk1 hk3
  let N := M + L - 1
  have hN : n = 2 ^ N := hn
  have h1 : k - 1 < 2 ^ N := by
    rw [show (2 ^ N) = n from hN.symm]
    exact h_j_lt_n
  have h_eq1 : Nat.factorization k 2 = padicValNat 2 k := by
    rw [Nat.factorization_def k (by norm_num)]
  have h_eq2 : padicValNat 2 k = multiplicity 2 k := by
    have h : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact padicValNat_def (hn := h_k_ne_zero)
  have h_key : (2 ^ (N - Nat.factorization k 2)) ∣ ((2 ^ N).choose k) := by
    have h2 : ((k - 1) + 1) = k := by omega
    have h3 : ∀ (n j : ℕ), j < 2 ^ n → (2 ^ (n - multiplicity 2 (j + 1))) ∣ ((2 ^ n).choose (j + 1)) := by
      intro n j hj
      exact WittVector.map_frobeniusPoly.key₁ (p := 2) (n := n) (j := j) (hj)
    have h4 := h3 N (k - 1) h1
    have h5 : multiplicity 2 ((k - 1) + 1) = Nat.factorization ((k - 1) + 1) 2 := by
      have h6 : ((k - 1) + 1) ≠ 0 := by omega
      have h7 : Nat.factorization ((k - 1) + 1) 2 = padicValNat 2 ((k - 1) + 1) := by
        rw [Nat.factorization_def ((k - 1) + 1) (by norm_num)]
      have h8 : padicValNat 2 ((k - 1) + 1) = multiplicity 2 ((k - 1) + 1) := by
        have h9 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
        exact padicValNat_def (hn := h6)
      rw [h7, h8]
    rw [h5] at h4
    simpa [h2] using h4
  have h4 : (2 ^ N).choose k = n.choose k := by
    rw [hN]
  rw [h4] at h_key
  have h_ineq : N - Nat.factorization k 2 ≥ M := by omega
  have h_main2 : 2 ^ M ∣ 2 ^ (N - Nat.factorization k 2) := by
    apply pow_dvd_pow
    <;> omega
  exact dvd_trans h_main2 h_key
end depth_0_lemma_3

namespace depth_0_lemma_4
lemma round1_h1 : ∀ (x : ℕ), 2 ^ x > x := by
  intro x
  induction x with
  | zero => norm_num
  | succ x ih =>
    simp [pow_succ] at *
    <;> omega
theorem S_unbounded_from_lemmas
  (dirichlet_type_lemma : ∀ (M : ℕ) (hM : M ≥ 1) (R : ℕ) (hR : R ≥ 1),
    ∃ (q L : ℕ), Nat.Prime q ∧ q > R ∧ L ≥ 1 ∧ (2 ^ L) % (q ^ M) = q ^ M - 1)
  (kummer_application_lemma : ∀ (q R D M : ℕ) (hq : Nat.Prime q) (hR : R ≥ 1) (hD : D ≥ 1) (hM : M ≥ 1) (h_q_gt_R : q > R)
    (hD_mod : D % (q ^ M) = q ^ M - 1),
    ∀ (j : ℕ), 1 ≤ j → j < R → q ^ M ∣ ((R * D).choose (j * D)))
  (valuation_2_lemma : ∀ (M L n k : ℕ) (hM : M ≥ 1) (hL : L ≥ 1) (hn : n = 2 ^ (M + L - 1))
    (hk1 : 1 ≤ k) (hk2 : k < n) (hk3 : ¬(2 ^ L ∣ k)),
    2 ^ M ∣ (n.choose k)):
  ∀ (b : ℕ), ∃ (n : ℕ), S n ≥ b  := by
  have h1 : ∀ (x : ℕ), 2 ^ x > x := round1_h1
  intro b
  have h_main : ∃ (n : ℕ), S n ≥ b := by
    let M := b + 1
    have hM : M ≥ 1 := by omega
    have hM_pos : 0 < M := by omega
    let R := 2 ^ (M - 1)
    have hR : R ≥ 1 := by
      have h₁ : M - 1 ≥ 0 := by omega
      have h₂ : 2 ^ (M - 1) ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      simpa [R] using h₂
    have h₁ : ∃ (q L : ℕ), Nat.Prime q ∧ q > R ∧ L ≥ 1 ∧ (2 ^ L) % (q ^ M) = q ^ M - 1 :=
      dirichlet_type_lemma M hM R hR
    rcases h₁ with ⟨q, L, hq, hq_gt_R, hL, hmod⟩
    let D := 2 ^ L
    have hD : D ≥ 1 := by
      have hL' : L ≥ 1 := hL
      have h : 2 ^ L ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      simpa [D] using h
    let n := R * D
    have h_n_pos : 0 < n := by
      positivity
    have h_n_gt_one : 1 < n := by
      have h₁ : M + L - 1 ≥ 1 := by omega
      have h₂ : n = 2 ^ (M + L - 1) := by
        dsimp [n, R, D]
        have h₃ : (M - 1) + L = M + L - 1 := by omega
        rw [← h₃]
        <;> ring
      rw [h₂]
      <;> apply Nat.one_lt_pow
      <;> omega
    have h_n_def : n = 2 ^ (M + L - 1) := by
      dsimp [n, R, D]
      have h₃ : (M - 1) + L = M + L - 1 := by omega
      rw [← h₃]
      <;> ring
    have h₄ : ∀ (k : ℕ), k ∈ Finset.Ico 1 n → ∃ (p : ℕ), Nat.Prime p ∧ p ^ b ∣ n.choose k := by
      intro k hk
      have h₅ : 1 ≤ k ∧ k < n := by
        simp only [Finset.mem_Ico] at hk
        exact ⟨hk.1, hk.2⟩
      have h₅₁ : 1 ≤ k := h₅.1
      have h₅₂ : k < n := h₅.2
      by_cases h₆ : (2 ^ L ∣ k)
      ·
        have h₇ : ∃ (j : ℕ), k = j * D := by
          have h₈ : D = 2 ^ L := by simp [D]
          rw [h₈] at *
          exact exists_eq_mul_left_of_dvd h₆
        rcases h₇ with ⟨j, hj⟩
        have h₉ : 1 ≤ j := by
          by_contra h₁₀
          have h₁₁ : j = 0 := by omega
          rw [h₁₁] at hj
          omega
        have h₁₀ : j < R := by
          have h₁₁ : k < n := h₅₂
          have h₁₂ : k = j * D := hj
          have h₁₃ : n = R * D := by rfl
          rw [h₁₂, h₁₃] at h₁₁
          have h₁₄ : j * D < R * D := h₁₁
          have h₁₅ : D > 0 := by linarith
          nlinarith
        have h₁₁ : q ^ M ∣ n.choose k := by
          have h₁₂ := kummer_application_lemma q R D M hq hR hD hM hq_gt_R hmod
          simpa [hj] using h₁₂ j h₉ h₁₀
        have h₁₃ : q ^ b ∣ n.choose k := by
          have h₁₄ : b ≤ M := by omega
          have h₁₅ : q ^ b ∣ q ^ M := by
            apply pow_dvd_pow
            <;> omega
          exact dvd_trans h₁₅ h₁₁
        refine ⟨q, hq, h₁₃⟩
      ·
        have h₇ : ¬ (2 ^ L ∣ k) := h₆
        have h₈ : 2 ^ M ∣ n.choose k := valuation_2_lemma M L n k hM hL h_n_def h₅₁ h₅₂ h₇
        have h₉ : 2 ^ b ∣ n.choose k := by
          have h₁₀ : b ≤ M := by omega
          have h₁₁ : 2 ^ b ∣ 2 ^ M := by
            apply pow_dvd_pow
            <;> omega
          exact dvd_trans h₁₁ h₈
        refine ⟨2, by decide, h₉⟩
    have h₅ : b ∈ {s : ℕ | ∀ (k : ℕ), k ∈ Finset.Ico 1 n → ∃ (p : ℕ), Nat.Prime p ∧ p ^ s ∣ n.choose k } := by
      simpa using h₄
    refine ⟨n, ?_⟩
    let A := {s : ℕ | ∀ (k : ℕ), k ∈ Finset.Ico 1 n → ∃ (p : ℕ), Nat.Prime p ∧ p ^ s ∣ n.choose k }
    have h_bdd : BddAbove A := by
      use n.choose 1
      intro s hs
      have h₁ : ∀ (k : ℕ), k ∈ Finset.Ico 1 n → ∃ (p : ℕ), Nat.Prime p ∧ p ^ s ∣ n.choose k := hs
      have h₂ : 1 ∈ Finset.Ico 1 n := by
        simp [Finset.mem_Ico]
        <;> omega
      have h₃ : ∃ (p : ℕ), Nat.Prime p ∧ p ^ s ∣ n.choose 1 := h₁ 1 h₂
      rcases h₃ with ⟨p, hp_prime, hpdvd⟩
      have h₄₁ : 0 < n.choose 1 := by
        apply Nat.choose_pos
        <;> omega
      have h₄ : p ^ s ∣ n.choose 1 := hpdvd
      have h₅ : p ^ s ≤ n.choose 1 := Nat.le_of_dvd h₄₁ h₄
      by_contra h₆
      have h₇ : s > n.choose 1 := by omega
      have h₈ : p ≥ 2 := Nat.Prime.two_le hp_prime
      have h₉ : p ^ s ≥ 2 ^ s := Nat.pow_le_pow_left h₈ s
      have h₁₀ : s ≥ n.choose 1 + 1 := by omega
      have h₁₁ : 2 ^ s ≥ 2 ^ (n.choose 1 + 1) := Nat.pow_le_pow_right (by norm_num) h₁₀
      have h₁₂ : 2 ^ (n.choose 1 + 1) > n.choose 1 := by
        have h₁₃ : 2 ^ (n.choose 1 + 1) = 2 * 2 ^ (n.choose 1) := by
          simp [pow_succ]
          <;> ring
        rw [h₁₃]
        have h₁₄ : 2 ^ (n.choose 1) > n.choose 1 := h1 (n.choose 1)
        omega
      have h₁₃ : 2 ^ s > n.choose 1 := by linarith
      have h₁₄ : p ^ s > n.choose 1 := by linarith
      linarith
    have h₆ : b ≤ sSup A := le_csSup h_bdd h₅
    simpa [S, A] using h₆
  exact h_main
end depth_0_lemma_4

namespace depth_0_lemma_5

lemma round1_h8 (n₀ : ℕ) (g' : ℕ → Fin n₀) (n₁ : Fin n₀) (h7 : Set.Infinite (g' ⁻¹' {n₁})) :
  ∀ m : ℕ, ∃ k : ℕ, m ≤ k ∧ g' k = n₁ := by
  intro m
  have h10 : Set.Infinite (g' ⁻¹' {n₁}) := h7
  have h11 : ∃ k ∈ (g' ⁻¹' {n₁}), m ≤ k := by
    by_contra h12
    push Not at h12
    have h13 : (g' ⁻¹' {n₁}) ⊆ Finset.range m := by
      intro x hx
      have h14 : m > x := h12 x hx
      exact Finset.mem_range.mpr (by linarith)
    have h15 : Set.Finite (g' ⁻¹' {n₁}) := Set.Finite.subset (Finset.finite_toSet (Finset.range m)) h13
    exact Set.not_infinite.mpr h15 h10
  rcases h11 with ⟨k, hk1, hk2⟩
  refine ⟨k, hk2, ?_⟩
  simpa [Set.mem_preimage, Set.mem_singleton_iff] using hk1

lemma round1_h5 (f : ℕ → ℕ)
  (h_main : ∀ (n₀ : ℕ) (b : ℕ), ¬ (∀ i ≥ n₀, f i ≤ b)) :
  ∀ (n₀ : ℕ), sSup (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }) = ⊤ := by
  intro n₀
  by_contra h6
  have h7 : sSup (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }) ≠ ⊤ := h6
  have h8 : ∃ (b : ℕ), sSup (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }) = ((b : ℕ∞)) := by
    exact Option.ne_none_iff_exists'.mp h6
  rcases h8 with ⟨b, hb⟩
  have h9 : ∀ x ∈ (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }), x ≤ (b : ℕ∞) := by
    exact sSup_le_iff.mp (show sSup (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }) ≤ (b : ℕ∞) from by rw [hb])
  have h10 : ∀ i : ℕ, i ≥ n₀ → (f i : ℕ∞) ≤ (b : ℕ∞) := by
    intro i hi
    have h111 : i ∈ { i : ℕ | i ≥ n₀ } := by
      exact Set.mem_setOf.mpr hi
    have h11 : (f i : ℕ∞) ∈ (Set.image (fun i => (f i : ℕ∞)) { i : ℕ | i ≥ n₀ }) := by
      exact Set.mem_image_of_mem (fun i : ℕ => (f i : ℕ∞)) h111
    exact h9 (f i : ℕ∞) h11
  have h11 : ∀ i : ℕ, i ≥ n₀ → f i ≤ b := by
    intro i hi
    have h12 : (f i : ℕ∞) ≤ (b : ℕ∞) := h10 i hi
    exact_mod_cast h12
  exact h_main n₀ b h11

theorem limsup_from_unbounded_lemma (f : ℕ → ℕ)
  (h : ∀ (b : ℕ), ∃ (n : ℕ), f n ≥ b):
  atTop.limsup (fun n => (f n : ℕ∞)) = ⊤  := by
  have h_main : ∀ (n₀ : ℕ) (b : ℕ), ¬ (∀ i ≥ n₀, f i ≤ b) := by
    intro n₀ b h2
    have h3 : ∀ k : ℕ, k > b → ∃ n < n₀, f n ≥ k := by
      intro k hk
      have h4 : ∃ n : ℕ, f n ≥ k := h k
      rcases h4 with ⟨n, hn⟩
      by_cases h5 : n ≥ n₀
      ·
        have h6 : f n ≤ b := h2 n h5
        linarith
      ·
        refine ⟨n, by omega, hn⟩
    have h4 : ∀ k : ℕ, ∃ n < n₀, f n ≥ k + b + 1 := fun k => h3 (k + b + 1) (by linarith)
    choose g hg using h4
    have h5 : ∀ k : ℕ, g k < n₀ ∧ f (g k) ≥ k + b + 1 := by simpa [hg] using hg
    let g' : ℕ → Fin n₀ := fun k => ⟨g k, (h5 k).1⟩
    have h61 : ∃ (n₁ : Fin n₀), Set.Infinite (g' ⁻¹' {n₁}) := by
      rcases Finite.exists_infinite_fiber (g' : ℕ → Fin n₀) with ⟨n₁, h7⟩
      refine ⟨n₁, ?_⟩
      have h7' : (g' ⁻¹' {n₁}).Infinite := by
        exact Set.infinite_coe_iff.mp h7
      exact h7'
    rcases h61 with ⟨n₁, h7⟩
    have h8 : ∀ m : ℕ, ∃ k : ℕ, m ≤ k ∧ g' k = n₁ := round1_h8 n₀ g' n₁ h7
    let n₁' := n₁.val
    have hn₁'_lt : n₁' < n₀ := n₁.is_lt
    have h9 : ∀ m : ℕ, ∃ k : ℕ, m ≤ k ∧ g k = n₁' := by
      intro m
      rcases h8 m with ⟨k, hk1, hk2⟩
      refine ⟨k, hk1, ?_⟩
      simpa [g'] using congr_arg (fun (x : Fin n₀) => x.val) hk2
    have h10 : ∀ m : ℕ, f n₁' ≥ m + b + 1 := by
      intro m
      have h11 : ∃ k : ℕ, m ≤ k ∧ g k = n₁' := h9 m
      rcases h11 with ⟨k, hk1, hk2⟩
      have h12 : f (g k) ≥ k + b + 1 := (h5 k).2
      rw [hk2] at h12
      linarith
    have h13 := h10 (f n₁')
    linarith
  have h12 : ∀ (n₀ : ℕ), (⨆ (i' : ℕ) (h : i' ≥ n₀), (f i' : ℕ∞)) = ⊤ := by
    intro n₀
    by_contra h12₂
    have h12₃ : ∃ (b : ℕ), (⨆ (i' : ℕ) (h : i' ≥ n₀), (f i' : ℕ∞)) = ((b : ℕ∞)) := by
      exact Option.ne_none_iff_exists'.mp h12₂
    rcases h12₃ with ⟨b, hb⟩
    have h12₄ : ∀ (i' : ℕ), i' ≥ n₀ → (f i' : ℕ∞) ≤ (b : ℕ∞) := by
      intro i' hi'
      have h12₅ : (f i' : ℕ∞) ≤ (⨆ (i' : ℕ) (h : i' ≥ n₀), (f i' : ℕ∞)) := by
        apply le_iSup₂ i' hi'
      rw [hb] at h12₅
      exact h12₅
    have h12₅ : ∀ (i' : ℕ), i' ≥ n₀ → f i' ≤ b := by
      intro i' hi'
      have h12₆ : (f i' : ℕ∞) ≤ (b : ℕ∞) := h12₄ i' hi'
      exact_mod_cast h12₆
    exact h_main n₀ b h12₅
  have h11 : atTop.limsup (fun n => (f n : ℕ∞)) = ⨅ n₀ : ℕ, (⨆ (i' : ℕ) (h : i' ≥ n₀), (f i' : ℕ∞)) := by
    simpa using limsup_eq_iInf_iSup_of_nat (u := fun n => (f n : ℕ∞))
  rw [h11]
  have h13 : ∀ n₀ : ℕ, (⨆ (i' : ℕ) (h : i' ≥ n₀), (f i' : ℕ∞)) = ⊤ := h12
  simp [h13]
end depth_0_lemma_5


theorem erdos_379 : atTop.limsup (fun n => (S n : ℕ∞)) = ⊤ := by
  have h1 := depth_0_lemma_1.dirichlet_type_lemma
  have h2 := depth_0_lemma_2.kummer_application_lemma
  have h3 := depth_0_lemma_3.valuation_2_lemma
  have h4 := depth_0_lemma_4.S_unbounded_from_lemmas h1 h2 h3
  have h5 := depth_0_lemma_5.limsup_from_unbounded_lemma (S) h4
  exact h5
