import ErdosProblems.Erdos248.PrimeSumBounds
import Util.TaoTeravainen.PrimePowerCounting

/-!
# Tao--Teräväinen: elementary prime-power series budgets

The sieve estimates for a prime power carry a geometric density factor.
This file records deliberately coarse finite bounds for the resulting
geometric sums.  Keeping these estimates elementary avoids importing any
analytic-number-theory input into the multiplicity argument.
-/

noncomputable section

open scoped BigOperators

namespace TaoTeravainen

local instance primePowerSeriesDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A coarse elementary exponential domination, convenient after clearing
the denominators in the geometric exponent sums. -/
theorem cube_le_sixteen_mul_two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    n ^ 3 ≤ 16 * 2 ^ (n - 1) := by
  by_cases hn4 : 4 ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn4
    induction m with
    | zero => norm_num
    | succ m ih =>
      let r := 4 + m
      have hr : 4 ≤ r := by dsimp [r]; omega
      have hstep : (r + 1) ^ 3 ≤ 2 * r ^ 3 := by
        have hnonneg : 0 ≤ (r - 4) * (r ^ 2 + r + 1) := by positivity
        nlinarith [hnonneg]
      have hpow : 16 * 2 ^ (r - 1) * 2 = 16 * 2 ^ r := by
        calc
          16 * 2 ^ (r - 1) * 2 = 16 * (2 ^ (r - 1) * 2) := by ring
          _ = 16 * 2 ^ ((r - 1) + 1) := by rw [pow_succ]
          _ = 16 * 2 ^ r := by congr 2 <;> omega
      calc
        (4 + (m + 1)) ^ 3 = (r + 1) ^ 3 := by dsimp [r]; ring
        _ ≤ 2 * r ^ 3 := hstep
        _ ≤ 2 * (16 * 2 ^ (r - 1)) := by
          gcongr
          simpa [r] using ih (by omega) (by omega)
        _ = 16 * 2 ^ r := by rw [mul_comm, hpow]
        _ = 16 * 2 ^ (4 + (m + 1) - 1) := by congr 2 <;> dsimp [r] <;> omega
  · interval_cases n <;> norm_num at hn ⊢

/-- The exponent weight occurring in a same-base prime-power pair is
dominated by a reciprocal square. -/
theorem exponent_div_prime_pow_sub_one_le_sixteen_div_sq
    {p a : ℕ} (hp : 2 ≤ p) (ha : 2 ≤ a) :
    (a : ℝ) / (p : ℝ) ^ (a - 1) ≤ 16 / (a : ℝ) ^ 2 := by
  have hpow : (2 : ℝ) ^ (a - 1) ≤ (p : ℝ) ^ (a - 1) := by
    gcongr
    exact_mod_cast hp
  have hleft : (a : ℝ) / (p : ℝ) ^ (a - 1) ≤
      (a : ℝ) / (2 : ℝ) ^ (a - 1) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  refine hleft.trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hcube : (a : ℝ) ^ 3 ≤ 16 * (2 : ℝ) ^ (a - 1) := by
    exact_mod_cast cube_le_sixteen_mul_two_pow_sub_one ha
  nlinarith [hcube]

/-- The corresponding density with the full prime power in the denominator
is no larger than the preceding coarse budget. -/
theorem exponent_div_prime_pow_le_sixteen_div_sq
    {p a : ℕ} (hp : 2 ≤ p) (ha : 2 ≤ a) :
    (a : ℝ) / (p : ℝ) ^ a ≤ 16 / (a : ℝ) ^ 2 := by
  calc
    (a : ℝ) / (p : ℝ) ^ a ≤ (a : ℝ) / (p : ℝ) ^ (a - 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega))
        (Nat.sub_le a 1)
    _ ≤ 16 / (a : ℝ) ^ 2 :=
      exponent_div_prime_pow_sub_one_le_sixteen_div_sq hp ha

/-- Summing the coarse exponent budget over any initial exponent interval
costs at most thirty two. -/
theorem sum_Icc_exponent_div_prime_pow_sub_one_le_thirtytwo
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ (a - 1)) ≤ 32 := by
  calc
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ (a - 1)) ≤
        ∑ a ∈ Finset.Icc 2 B, 16 / (a : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact exponent_div_prime_pow_sub_one_le_sixteen_div_sq hp
        (Finset.mem_Icc.mp ha).1
    _ = 16 * ∑ a ∈ Finset.Icc 2 B, (1 : ℝ) / (a : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ 16 * ∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr
          ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp ha).1,
            (Finset.mem_Icc.mp ha).2⟩
      · intro a ha hnot
        positivity
    _ ≤ 32 := by
      nlinarith [Erdos248.sum_Icc_one_div_sq_le_two B]

/-- The same thirty-two budget also covers the full prime-power denominator. -/
theorem sum_Icc_exponent_div_prime_pow_le_thirtytwo
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ a) ≤ 32 := by
  calc
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ a) ≤
        ∑ a ∈ Finset.Icc 2 B,
          (a : ℝ) / (p : ℝ) ^ (a - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega))
        (Nat.sub_le a 1)
    _ ≤ 32 := sum_Icc_exponent_div_prime_pow_sub_one_le_thirtytwo B p hp

/-- The unweighted proper-exponent geometric series keeps the base-prime
square visible. -/
theorem sum_Icc_inv_prime_pow_le_two_div_sq
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B, (1 : ℝ) / (p : ℝ) ^ a) ≤
      2 / (p : ℝ) ^ 2 := by
  have hsets : Finset.Icc 2 B = Finset.Ico 2 (B + 1) := by
    ext a
    simp
  calc
    (∑ a ∈ Finset.Icc 2 B, (1 : ℝ) / (p : ℝ) ^ a) =
        (1 : ℝ) / (p : ℝ) ^ 2 *
          ∑ a ∈ Finset.Icc 2 B, (1 : ℝ) / (p : ℝ) ^ (a - 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha2 := (Finset.mem_Icc.mp ha).1
      rw [show a = 2 + (a - 2) by omega, pow_add]
      field_simp
      congr 1
      omega
    _ ≤ (1 : ℝ) / (p : ℝ) ^ 2 *
          ∑ a ∈ Finset.Icc 2 B, (1 / (2 : ℝ)) ^ (a - 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro a ha
        have hpow : (2 : ℝ) ^ (a - 2) ≤ (p : ℝ) ^ (a - 2) := by
          gcongr
          exact_mod_cast hp
        rw [one_div_pow]
        exact div_le_div_of_nonneg_left (by norm_num)
          (pow_pos (by norm_num) _) hpow
      · positivity
    _ = (1 : ℝ) / (p : ℝ) ^ 2 *
          ∑ i ∈ Finset.range (B + 1 - 2), (1 / (2 : ℝ)) ^ i := by
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      apply congrArg (fun z : ℝ => (1 : ℝ) / (p : ℝ) ^ 2 * z)
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    _ ≤ (1 : ℝ) / (p : ℝ) ^ 2 * 2 := by
      apply mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = 2 / (p : ℝ) ^ 2 := by ring

/-- Removing two powers from the denominator costs only one further factor
two in the coarse reciprocal-square majorant. -/
theorem exponent_div_prime_pow_sub_two_le_thirtytwo_div_sq
    {p a : ℕ} (hp : 2 ≤ p) (ha : 2 ≤ a) :
    (a : ℝ) / (p : ℝ) ^ (a - 2) ≤ 32 / (a : ℝ) ^ 2 := by
  have hpow : (2 : ℝ) ^ (a - 2) ≤ (p : ℝ) ^ (a - 2) := by
    gcongr
    exact_mod_cast hp
  have hleft : (a : ℝ) / (p : ℝ) ^ (a - 2) ≤
      (a : ℝ) / (2 : ℝ) ^ (a - 2) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  refine hleft.trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hcube : (a : ℝ) ^ 3 ≤ 16 * (2 : ℝ) ^ (a - 1) := by
    exact_mod_cast cube_le_sixteen_mul_two_pow_sub_one ha
  have htwo : 16 * (2 : ℝ) ^ (a - 1) =
      32 * (2 : ℝ) ^ (a - 2) := by
    rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
    ring
  rw [htwo] at hcube
  nlinarith [hcube]

theorem sum_Icc_exponent_div_prime_pow_sub_two_le_sixtyfour
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ (a - 2)) ≤ 64 := by
  calc
    (∑ a ∈ Finset.Icc 2 B,
        (a : ℝ) / (p : ℝ) ^ (a - 2)) ≤
        ∑ a ∈ Finset.Icc 2 B, 32 / (a : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact exponent_div_prime_pow_sub_two_le_thirtytwo_div_sq hp
        (Finset.mem_Icc.mp ha).1
    _ = 32 * ∑ a ∈ Finset.Icc 2 B, (1 : ℝ) / (a : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ 32 * ∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr
          ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp ha).1,
            (Finset.mem_Icc.mp ha).2⟩
      · intro a ha hnot
        positivity
    _ ≤ 64 := by
      nlinarith [Erdos248.sum_Icc_one_div_sq_le_two B]

/-- Keeping one visible base-prime denominator gives a reciprocal-prime
budget for the active small-power series. -/
theorem sum_Icc_inv_prime_pow_sub_one_le_sixtyfour_div
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (a - 1)) ≤ 64 / (p : ℝ) := by
  calc
    (∑ a ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (a - 1)) =
        (1 : ℝ) / p * ∑ a ∈ Finset.Icc 2 B,
          (1 : ℝ) / (p : ℝ) ^ (a - 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha2 := (Finset.mem_Icc.mp ha).1
      rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
      field_simp
    _ ≤ (1 : ℝ) / p * ∑ a ∈ Finset.Icc 2 B,
          (a : ℝ) / (p : ℝ) ^ (a - 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro a ha
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show 1 ≤ a by
            exact (show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp ha).1)
        · positivity
      · positivity
    _ ≤ (1 : ℝ) / p * 64 := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_exponent_div_prime_pow_sub_two_le_sixtyfour B p hp)
        (by positivity)
    _ = 64 / (p : ℝ) := by ring

/-- Counting an initial interval of exponents below a given exponent costs
at most that exponent times the common nonnegative summand. -/
theorem sum_Icc_if_le_const_le_index_mul
    (B b : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a ∈ Finset.Icc 2 B, if a ≤ b then x else 0) ≤ (b : ℝ) * x := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  have hsub : (Finset.Icc 2 B).filter (fun a => a ≤ b) ⊆
      Finset.Icc 1 b := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_Icc.mpr
      ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp ha'.1).1, ha'.2⟩
  have hcard : ((Finset.Icc 2 B).filter (fun a => a ≤ b)).card ≤ b := by
    calc
      ((Finset.Icc 2 B).filter (fun a => a ≤ b)).card ≤
          (Finset.Icc 1 b).card := Finset.card_le_card hsub
      _ = b := by rw [Nat.card_Icc]; omega
  have hcardR :
      (((Finset.Icc 2 B).filter (fun a => a ≤ b)).card : ℝ) ≤ b := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcardR hx

/-- The strict complementary half of the exponent square has the same
cardinality bound. -/
theorem sum_Icc_if_lt_const_le_index_mul
    (B a : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ b ∈ Finset.Icc 2 B, if b < a then x else 0) ≤ (a : ℝ) * x := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  have hsub : (Finset.Icc 2 B).filter (fun b => b < a) ⊆
      Finset.Icc 1 a := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact Finset.mem_Icc.mpr
      ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp hb'.1).1, hb'.2.le⟩
  have hcard : ((Finset.Icc 2 B).filter (fun b => b < a)).card ≤ a := by
    calc
      ((Finset.Icc 2 B).filter (fun b => b < a)).card ≤
          (Finset.Icc 1 a).card := Finset.card_le_card hsub
      _ = a := by rw [Nat.card_Icc]; omega
  have hcardR :
      (((Finset.Icc 2 B).filter (fun b => b < a)).card : ℝ) ≤ a := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcardR hx

/-- For one base prime, summing all pairs of proper exponents with the
pre-sieved density costs an absolute constant. -/
theorem sum_Icc_pair_inv_pow_max_sub_one_le_sixtyfour
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) ≤ 64 := by
  let E := Finset.Icc 2 B
  have hsplit :
      (∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) =
        (∑ a ∈ E, ∑ b ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ (b - 1) else 0) +
        ∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ (a - 1) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a ≤ b
    · simp [hab, max_eq_right hab]
    · have hba : b < a := by omega
      simp [hab, hba, max_eq_left hba.le]
  rw [hsplit]
  have hfirst :
      (∑ a ∈ E, ∑ b ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ (b - 1) else 0) ≤ 32 := by
    rw [Finset.sum_comm]
    calc
      (∑ b ∈ E, ∑ a ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ (b - 1) else 0) ≤
          ∑ b ∈ E, (b : ℝ) / (p : ℝ) ^ (b - 1) := by
        apply Finset.sum_le_sum
        intro b hb
        simpa [E, div_eq_mul_inv] using
          (sum_Icc_if_le_const_le_index_mul B b
            (x := (1 : ℝ) / (p : ℝ) ^ (b - 1))
            (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg p) _)))
      _ ≤ 32 := sum_Icc_exponent_div_prime_pow_sub_one_le_thirtytwo B p hp
  have hsecond :
      (∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ (a - 1) else 0) ≤ 32 := by
    calc
      (∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ (a - 1) else 0) ≤
          ∑ a ∈ E, (a : ℝ) / (p : ℝ) ^ (a - 1) := by
        apply Finset.sum_le_sum
        intro a ha
        simpa [E, div_eq_mul_inv] using
          (sum_Icc_if_lt_const_le_index_mul B a
            (x := (1 : ℝ) / (p : ℝ) ^ (a - 1))
            (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg p) _)))
      _ ≤ 32 := sum_Icc_exponent_div_prime_pow_sub_one_le_thirtytwo B p hp
  linarith

/-- With the full denominator, the same-base pair budget retains an explicit
reciprocal-square factor in the base prime. -/
theorem sum_Icc_pair_inv_pow_max_le_onehundredtwentyeight_div_sq
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (max a b)) ≤
      128 / (p : ℝ) ^ 2 := by
  let E := Finset.Icc 2 B
  have hsplit :
      (∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b)) =
        (∑ a ∈ E, ∑ b ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ b else 0) +
        ∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a ≤ b
    · simp [hab, max_eq_right hab]
    · have hba : b < a := by omega
      simp [hab, hba, max_eq_left hba.le]
  rw [hsplit]
  have hfirst :
      (∑ a ∈ E, ∑ b ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ b else 0) ≤
        64 / (p : ℝ) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ b ∈ E, ∑ a ∈ E,
          if a ≤ b then (1 : ℝ) / (p : ℝ) ^ b else 0) ≤
          ∑ b ∈ E, (b : ℝ) / (p : ℝ) ^ b := by
        apply Finset.sum_le_sum
        intro b hb
        simpa [E, div_eq_mul_inv] using
          (sum_Icc_if_le_const_le_index_mul B b
            (x := (1 : ℝ) / (p : ℝ) ^ b)
            (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg p) _)))
      _ = (1 : ℝ) / (p : ℝ) ^ 2 *
          ∑ b ∈ E, (b : ℝ) / (p : ℝ) ^ (b - 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        have hb2 := (Finset.mem_Icc.mp hb).1
        rw [show b = 2 + (b - 2) by omega, pow_add]
        field_simp
        congr 1
        omega
      _ ≤ (1 : ℝ) / (p : ℝ) ^ 2 * 64 := by
        apply mul_le_mul_of_nonneg_left
          (sum_Icc_exponent_div_prime_pow_sub_two_le_sixtyfour B p hp)
          (by positivity)
      _ = 64 / (p : ℝ) ^ 2 := by ring
  have hsecond :
      (∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ a else 0) ≤
        64 / (p : ℝ) ^ 2 := by
    calc
      (∑ a ∈ E, ∑ b ∈ E,
          if b < a then (1 : ℝ) / (p : ℝ) ^ a else 0) ≤
          ∑ a ∈ E, (a : ℝ) / (p : ℝ) ^ a := by
        apply Finset.sum_le_sum
        intro a ha
        simpa [E, div_eq_mul_inv] using
          (sum_Icc_if_lt_const_le_index_mul B a
            (x := (1 : ℝ) / (p : ℝ) ^ a)
            (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg p) _)))
      _ = (1 : ℝ) / (p : ℝ) ^ 2 *
          ∑ a ∈ E, (a : ℝ) / (p : ℝ) ^ (a - 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have ha2 := (Finset.mem_Icc.mp ha).1
        rw [show a = 2 + (a - 2) by omega, pow_add]
        field_simp
        congr 1
        omega
      _ ≤ (1 : ℝ) / (p : ℝ) ^ 2 * 64 := by
        apply mul_le_mul_of_nonneg_left
          (sum_Icc_exponent_div_prime_pow_sub_two_le_sixtyfour B p hp)
          (by positivity)
      _ = 64 / (p : ℝ) ^ 2 := by ring
  calc
    (∑ a ∈ E, ∑ b ∈ E,
        if a ≤ b then (1 : ℝ) / (p : ℝ) ^ b else 0) +
      (∑ a ∈ E, ∑ b ∈ E,
        if b < a then (1 : ℝ) / (p : ℝ) ^ a else 0) ≤
        64 / (p : ℝ) ^ 2 + 64 / (p : ℝ) ^ 2 :=
      add_le_add hfirst hsecond
    _ = 128 / (p : ℝ) ^ 2 := by ring

/-- The same-base pre-sieved pair budget keeps one reciprocal base factor. -/
theorem sum_Icc_pair_inv_pow_max_sub_one_le_onehundredtwentyeight_div
    (B p : ℕ) (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) ≤
      128 / (p : ℝ) := by
  have hfull := sum_Icc_pair_inv_pow_max_le_onehundredtwentyeight_div_sq B p hp
  have hident :
      (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
          (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) =
        (p : ℝ) * (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
          (1 : ℝ) / (p : ℝ) ^ (max a b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hmax : 2 ≤ max a b :=
      (Finset.mem_Icc.mp ha).1.trans (le_max_left _ _)
    rw [show max a b = (max a b - 1) + 1 by omega, pow_succ]
    field_simp
    congr 1
  rw [hident]
  calc
    (p : ℝ) * (∑ a ∈ Finset.Icc 2 B, ∑ b ∈ Finset.Icc 2 B,
        (1 : ℝ) / (p : ℝ) ^ (max a b)) ≤
        (p : ℝ) * (128 / (p : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = 128 / (p : ℝ) := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      field_simp

/-- Density used for a proper prime power in the mixed pre-sieved/non-tiny
moment calculation.  A small base contributes only when it divides the
shift, because the pre-sieve otherwise makes the event empty. -/
def primePowerDensity (K k : ℕ) (pa : ℕ × ℕ) : ℝ :=
  if pa.1 ≤ Erdos248.tinyCutoff K then
    if pa.1 ∣ k then (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1) else 0
  else (1 : ℝ) / (pa.1 : ℝ) ^ pa.2

/-- Active small prime-power indices at one shift. -/
def smallActivePrimePowerIndices (B K k : ℕ) : Finset (ℕ × ℕ) :=
  (properPrimePowerIndices B).filter fun pa =>
    pa.1 ≤ Erdos248.tinyCutoff K ∧ pa.1 ∣ k

/-- Indices whose base lies above the pre-sieve cutoff. -/
def nonTinyPrimePowerIndices (B K : ℕ) : Finset (ℕ × ℕ) :=
  (properPrimePowerIndices B).filter fun pa =>
    Erdos248.tinyCutoff K < pa.1

/-- Density for the diagonal `p = q` part of a prime-power pair. -/
def samePrimePowerDensity (K k : ℕ) (pa qb : ℕ × ℕ) : ℝ :=
  if pa.1 = qb.1 then
    if pa.1 ≤ Erdos248.tinyCutoff K then
      if pa.1 ∣ k then
        (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1)
      else 0
    else (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2)
  else 0

/-- Reindex an equality-of-bases double sum by a base and two exponents.
This is the finite combinatorial bridge used for the diagonal pair budget. -/
theorem sum_eq_base_pair_le_triple
    (I : Finset (ℕ × ℕ)) (P E : Finset ℕ)
    (F : ℕ → ℕ → ℕ → ℝ)
    (hI : I ⊆ P.product E)
    (hF : ∀ p ∈ P, ∀ a ∈ E, ∀ b ∈ E, 0 ≤ F p a b) :
    (∑ pa ∈ I, ∑ qb ∈ I,
        if pa.1 = qb.1 then F pa.1 pa.2 qb.2 else 0) ≤
      ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E, F p a b := by
  have hinner : ∀ pa ∈ I,
      (∑ qb ∈ I,
          if pa.1 = qb.1 then F pa.1 pa.2 qb.2 else 0) ≤
        ∑ b ∈ E, F pa.1 pa.2 b := by
    intro pa hpa
    let J := I.filter fun qb => pa.1 = qb.1
    have hJinj : Set.InjOn (fun qb : ℕ × ℕ => qb.2) J := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      cases x with
      | mk px ax =>
        cases y with
        | mk py ay =>
          simp only at hx' hy' hxy ⊢
          subst ay
          simp only [Prod.mk.injEq, and_true]
          omega
    have hJimage : J.image (fun qb : ℕ × ℕ => qb.2) ⊆ E := by
      intro b hb
      obtain ⟨qb, hqb, rfl⟩ := Finset.mem_image.mp hb
      exact (Finset.mem_product.mp (hI ((Finset.mem_filter.mp hqb).1))).2
    calc
      (∑ qb ∈ I,
          if pa.1 = qb.1 then F pa.1 pa.2 qb.2 else 0) =
          ∑ qb ∈ J, F pa.1 pa.2 qb.2 := by
        rw [Finset.sum_filter]
      _ = ∑ b ∈ J.image (fun qb : ℕ × ℕ => qb.2),
          F pa.1 pa.2 b := by
        exact (Finset.sum_image hJinj).symm
      _ ≤ ∑ b ∈ E, F pa.1 pa.2 b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hJimage
        intro b hb hnot
        have hpaPE := Finset.mem_product.mp (hI hpa)
        exact hF pa.1 hpaPE.1 pa.2 hpaPE.2 b hb
  calc
    (∑ pa ∈ I, ∑ qb ∈ I,
        if pa.1 = qb.1 then F pa.1 pa.2 qb.2 else 0) ≤
        ∑ pa ∈ I, ∑ b ∈ E, F pa.1 pa.2 b := by
      apply Finset.sum_le_sum hinner
    _ ≤ ∑ pa ∈ P.product E, ∑ b ∈ E, F pa.1 pa.2 b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hI
      intro pa hpa hnot
      apply Finset.sum_nonneg
      intro b hb
      have hpaPE := Finset.mem_product.mp hpa
      exact hF pa.1 hpaPE.1 pa.2 hpaPE.2 b hb
    _ = ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E, F p a b := by
      exact Finset.sum_product P E
        (fun pa : ℕ × ℕ => ∑ b ∈ E, F pa.1 pa.2 b)

/-- The diagonal pair density from active pre-sieved primes is linear in the
shift. -/
theorem sum_smallActive_samePrimePowerDensity_le
    (B K k : ℕ) (hk : 1 ≤ k) :
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
      ∑ qb ∈ smallActivePrimePowerIndices B K k,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) ≤
      64 * (k : ℝ) := by
  let P := (Finset.Icc 2 B).filter fun p => p ∣ k
  let E := Finset.Icc 2 B
  have hsub : smallActivePrimePowerIndices B K k ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hdata.1, hdata.2.1⟩, hpa'.2.2⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  have hPsub : P ⊆ Finset.Icc 1 k := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr
      ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp hp'.1).1,
        Nat.le_of_dvd (by omega) hp'.2⟩
  have hPcard : P.card ≤ k := by
    calc
      P.card ≤ (Finset.Icc 1 k).card := Finset.card_le_card hPsub
      _ = k := by rw [Nat.card_Icc]; omega
  calc
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
      ∑ qb ∈ smallActivePrimePowerIndices B K k,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) ≤
        ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b - 1) := by
      apply sum_eq_base_pair_le_triple
        (smallActivePrimePowerIndices B K k) P E
        (fun p a b => (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) hsub
      intro p hp a ha b hb
      positivity
    _ ≤ ∑ p ∈ P, (64 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_pair_inv_pow_max_sub_one_le_sixtyfour B p
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = (P.card : ℝ) * 64 := by simp
    _ ≤ 64 * (k : ℝ) := by
      have hcardR : (P.card : ℝ) ≤ k := by exact_mod_cast hPcard
      nlinarith

/-- The diagonal pair density from non-tiny primes is absolute. -/
theorem sum_nonTiny_samePrimePowerDensity_le (B K : ℕ) :
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
      ∑ qb ∈ nonTinyPrimePowerIndices B K,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤ 256 := by
  let P := Finset.Icc 2 B
  let E := Finset.Icc 2 B
  have hsub : nonTinyPrimePowerIndices B K ⊆ P.product E := by
    intro pa hpa
    have hdata := mem_properPrimePowerIndices_iff.mp (Finset.mem_filter.mp hpa).1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdata.1, hdata.2.1⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  calc
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
      ∑ qb ∈ nonTinyPrimePowerIndices B K,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤
        ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b) := by
      apply sum_eq_base_pair_le_triple
        (nonTinyPrimePowerIndices B K) P E
        (fun p a b => (1 : ℝ) / (p : ℝ) ^ (max a b)) hsub
      intro p hp a ha b hb
      positivity
    _ ≤ ∑ p ∈ P, 128 / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_pair_inv_pow_max_le_onehundredtwentyeight_div_sq B p
        (Finset.mem_Icc.mp hp).1
    _ = 128 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ 128 * ∑ p ∈ Finset.Icc 1 B, (1 : ℝ) / (p : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Icc.mpr
          ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp hp).1,
            (Finset.mem_Icc.mp hp).2⟩
      · intro p hp hnot
        positivity
    _ ≤ 256 := by
      nlinarith [Erdos248.sum_Icc_one_div_sq_le_two B]

/-- The sharper diagonal non-tiny budget also retains the cutoff reciprocal. -/
theorem sum_nonTiny_samePrimePowerDensity_le_div_tiny (B K : ℕ) :
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
      ∑ qb ∈ nonTinyPrimePowerIndices B K,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤
      256 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) := by
  let P := Erdos248.primesBetween (Erdos248.tinyCutoff K) B
  let E := Finset.Icc 2 B
  have hsub : nonTinyPrimePowerIndices B K ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Erdos248.mem_primesBetween.mpr
          ⟨hpa'.2, hdata.2.1, hdata.2.2.2.2.1⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  calc
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
      ∑ qb ∈ nonTinyPrimePowerIndices B K,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤
        ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b) := by
      apply sum_eq_base_pair_le_triple
        (nonTinyPrimePowerIndices B K) P E
        (fun p a b => (1 : ℝ) / (p : ℝ) ^ (max a b)) hsub
      intro p hp a ha b hb
      positivity
    _ ≤ ∑ p ∈ P, 128 / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_pair_inv_pow_max_le_onehundredtwentyeight_div_sq B p
        (Erdos248.mem_primesBetween.mp hp).2.2.two_le
    _ = 128 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ 128 * (2 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Erdos248.sum_primesBetween_inv_sq_le _ _) (by norm_num)
    _ = 256 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- Combining the two diagonal ranges gives a linear-in-shift budget. -/
theorem sum_samePrimePowerDensity_le
    (B K k : ℕ) (hk : 1 ≤ k) :
    (∑ pa ∈ properPrimePowerIndices B,
      ∑ qb ∈ properPrimePowerIndices B,
        samePrimePowerDensity K k pa qb) ≤ 64 * (k : ℝ) + 256 := by
  have hsmall := sum_smallActive_samePrimePowerDensity_le B K k hk
  have hlarge := sum_nonTiny_samePrimePowerDensity_le B K
  have hdecomp :
      (∑ pa ∈ properPrimePowerIndices B,
        ∑ qb ∈ properPrimePowerIndices B,
          samePrimePowerDensity K k pa qb) =
        (∑ pa ∈ smallActivePrimePowerIndices B K k,
          ∑ qb ∈ smallActivePrimePowerIndices B K k,
            if pa.1 = qb.1 then
              (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) +
        ∑ pa ∈ nonTinyPrimePowerIndices B K,
          ∑ qb ∈ nonTinyPrimePowerIndices B K,
            if pa.1 = qb.1 then
              (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0 := by
    unfold samePrimePowerDensity smallActivePrimePowerIndices
      nonTinyPrimePowerIndices
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pa hpa
    by_cases hsmall : pa.1 ≤ Erdos248.tinyCutoff K
    · by_cases hdvd : pa.1 ∣ k
      · simp [hsmall, hdvd, not_lt_of_ge hsmall]
        apply Finset.sum_congr rfl
        intro qb hqb
        by_cases heq : pa.1 = qb.1
        · have hqsmall : qb.1 ≤ Erdos248.tinyCutoff K := heq ▸ hsmall
          have hqdvd : qb.1 ∣ k := heq ▸ hdvd
          simp [heq, hqsmall, hqdvd]
        · simp [heq]
      · simp [hsmall, hdvd, not_lt_of_ge hsmall]
    · have hlarge : Erdos248.tinyCutoff K < pa.1 := by omega
      simp [hsmall, hlarge]
      apply Finset.sum_congr rfl
      intro qb hqb
      by_cases heq : pa.1 = qb.1
      · have hqlarge : Erdos248.tinyCutoff K < qb.1 := heq ▸ hlarge
        have hqnotSmall : ¬ qb.1 ≤ Erdos248.tinyCutoff K := by omega
        simp [heq, hsmall, hlarge, hqlarge, hqnotSmall]
      · simp [heq]
  rw [hdecomp]
  exact add_le_add hsmall hlarge

/-- The ordinary reciprocal budget for all proper prime powers is absolute.
We use the already-formalized proper-prime-power reciprocal estimate, after
reindexing by the unique prime/exponent representation. -/
theorem sum_properPrimePowerIndices_inv_pow_le_forty (B : ℕ) :
    (∑ pa ∈ properPrimePowerIndices B,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤ 40 := by
  by_cases hB : 2 ≤ B
  · calc
      (∑ pa ∈ properPrimePowerIndices B,
          (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) =
          ∑ pa ∈ properPrimePowerIndices B,
            ((pa.1 ^ pa.2 : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro pa hpa
        simp [one_div, Nat.cast_pow]
      _ = ∑ q ∈ Erdos297.FactorDensity.properPrimePowersUpTo B,
          (q : ℝ)⁻¹ := by
        rw [← image_properPrimePowerIndices B]
        exact (Finset.sum_image
          (f := fun q : ℕ => (q : ℝ)⁻¹)
          properPrimePowerIndices_power_injective).symm
      _ = Erdos285.PositiveReservoir.properPrimePowerReciprocalInterval 2 B :=
        Erdos297.FactorDensity.properPrimePowersUpTo_reciprocal_sum B
      _ ≤ 40 * (2 : ℝ) ^ (-1 / 4 : ℝ) :=
        Erdos285.PositiveReservoir.properPrimePowerReciprocalInterval_le
          2 B (by norm_num) hB
      _ ≤ 40 := by
        have hpow : (2 : ℝ) ^ (-1 / 4 : ℝ) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos
          · norm_num
          · norm_num
        nlinarith
  · have hempty : properPrimePowerIndices B = ∅ := by
      ext pa
      constructor
      · intro hpa
        have hdata := mem_properPrimePowerIndices_iff.mp hpa
        exact False.elim (hB (hdata.1.trans hdata.2.1))
      · simp
    rw [hempty]
    norm_num

/-- The active small-base density budget is at most linear in the shift.
For each base we spend the absolute geometric exponent budget, and there are
at most `k` positive divisors of `k`. -/
theorem sum_smallActivePrimePowerDensity_le
    (B K k : ℕ) (hk : 1 ≤ k) :
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
        (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1)) ≤ 32 * (k : ℝ) := by
  let P := (Finset.Icc 2 B).filter fun p => p ∣ k
  let E := Finset.Icc 2 B
  have hsub : smallActivePrimePowerIndices B K k ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hdata.1, hdata.2.1⟩, hpa'.2.2⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  have hPsub : P ⊆ Finset.Icc 1 k := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hp2 := (Finset.mem_Icc.mp hp'.1).1
    have hple : p ≤ k := Nat.le_of_dvd (by omega) hp'.2
    exact Finset.mem_Icc.mpr ⟨by omega, hple⟩
  have hPcard : P.card ≤ k := by
    calc
      P.card ≤ (Finset.Icc 1 k).card := Finset.card_le_card hPsub
      _ = k := by rw [Nat.card_Icc]; omega
  calc
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
        (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1)) ≤
        ∑ pa ∈ P.product E,
          (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro pa hpa hnot
      positivity
    _ = ∑ p ∈ P, ∑ a ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (a - 1) := by
      exact Finset.sum_product P E
        (fun pa : ℕ × ℕ => (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1))
    _ ≤ ∑ p ∈ P, (32 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      calc
        (∑ a ∈ E, (1 : ℝ) / (p : ℝ) ^ (a - 1)) ≤
            ∑ a ∈ E, (a : ℝ) / (p : ℝ) ^ (a - 1) := by
          apply Finset.sum_le_sum
          intro a ha
          apply div_le_div_of_nonneg_right
          · exact_mod_cast (show 1 ≤ a by
              exact (show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp ha).1)
          · positivity
        _ ≤ 32 := sum_Icc_exponent_div_prime_pow_sub_one_le_thirtytwo B p hp2
    _ = (P.card : ℝ) * 32 := by simp
    _ ≤ 32 * (k : ℝ) := by
      have hcardR : (P.card : ℝ) ≤ k := by exact_mod_cast hPcard
      nlinarith

/-- Above the pre-sieve cutoff, the full prime-power reciprocal budget is
absolute. -/
theorem sum_nonTinyPrimePowerDensity_le (B K : ℕ) :
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤ 40 := by
  calc
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤
        ∑ pa ∈ properPrimePowerIndices B,
          (1 : ℝ) / (pa.1 : ℝ) ^ pa.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro pa hpa
        exact (Finset.mem_filter.mp hpa).1
      · intro pa hpa hnot
        positivity
    _ ≤ 40 := sum_properPrimePowerIndices_inv_pow_le_forty B

/-- Keeping track of the lower cutoff gives the sharper non-tiny budget
needed to absorb the finite-dimensional comparison factor. -/
theorem sum_nonTinyPrimePowerDensity_le_div_tiny
    (B K : ℕ) :
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤
      4 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) := by
  let P := Erdos248.primesBetween (Erdos248.tinyCutoff K) B
  let E := Finset.Icc 2 B
  have hsub : nonTinyPrimePowerIndices B K ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Erdos248.mem_primesBetween.mpr
          ⟨hpa'.2, hdata.2.1, hdata.2.2.2.2.1⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  calc
    (∑ pa ∈ nonTinyPrimePowerIndices B K,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤
        ∑ pa ∈ P.product E, (1 : ℝ) / (pa.1 : ℝ) ^ pa.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro pa hpa hnot
      positivity
    _ = ∑ p ∈ P, ∑ a ∈ E, (1 : ℝ) / (p : ℝ) ^ a := by
      exact Finset.sum_product P E
        (fun pa : ℕ × ℕ => (1 : ℝ) / (pa.1 : ℝ) ^ pa.2)
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_inv_prime_pow_le_two_div_sq B p
        (Erdos248.mem_primesBetween.mp hp).2.2.two_le
    _ = 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ 2 * (2 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Erdos248.sum_primesBetween_inv_sq_le _ _) (by norm_num)
    _ = 4 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- The total one-prime-power density budget is linear in a positive shift. -/
theorem sum_primePowerDensity_le (B K k : ℕ) (hk : 1 ≤ k) :
    (∑ pa ∈ properPrimePowerIndices B, primePowerDensity K k pa) ≤
      32 * (k : ℝ) + 40 := by
  have hsmall := sum_smallActivePrimePowerDensity_le B K k hk
  have hlarge := sum_nonTinyPrimePowerDensity_le B K
  unfold primePowerDensity
  rw [Finset.sum_ite]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  simpa [smallActivePrimePowerIndices, nonTinyPrimePowerIndices,
    Finset.filter_filter, and_assoc, not_le] using add_le_add hsmall hlarge

end TaoTeravainen
