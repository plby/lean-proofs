/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

namespace Erdos518

/-! ## The square-root decomposition -/

/-- The amount left over after subtracting the square of the integer square root. -/
def sqrtRemainder (n : ℕ) : ℕ := n - (Nat.sqrt n) ^ 2

/-- The square of the integer square root does not exceed the original number. -/
lemma sqrt_sq_le (n : ℕ) : (Nat.sqrt n) ^ 2 ≤ n :=
  Nat.sqrt_le' n

/-- Every natural is the square of its integer square root plus its remainder. -/
lemma sqrt_sq_add_remainder (n : ℕ) :
    (Nat.sqrt n) ^ 2 + sqrtRemainder n = n := by
  exact Nat.add_sub_of_le (sqrt_sq_le n)

/-- The remainder after the largest square below `n` is at most twice its square root. -/
lemma sqrt_remainder_le_two_mul (n : ℕ) :
    sqrtRemainder n ≤ 2 * Nat.sqrt n := by
  have h := Nat.sqrt_le_add n
  have h' : (Nat.sqrt n) ^ 2 + sqrtRemainder n ≤
      (Nat.sqrt n) ^ 2 + 2 * Nat.sqrt n := by
    calc
      (Nat.sqrt n) ^ 2 + sqrtRemainder n = n := sqrt_sq_add_remainder n
      _ ≤ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n := h
      _ = (Nat.sqrt n) ^ 2 + 2 * Nat.sqrt n := by ring
  exact Nat.le_of_add_le_add_left h'

/-- The complete natural-number decomposition used in the minimal-counterexample proof. -/
lemma sqrt_decomposition (n : ℕ) :
    let c := Nat.sqrt n
    let r := n - c ^ 2
    c ^ 2 ≤ n ∧ n = c ^ 2 + r ∧ r ≤ 2 * c := by
  dsimp only
  exact ⟨sqrt_sq_le n, (sqrt_sq_add_remainder n).symm, sqrt_remainder_le_two_mul n⟩

/-- A number at most `c² - 1` has integer square root at most `c - 1`. -/
lemma sqrt_le_sub_one_of_le_sq_sub_one {m c : ℕ} (hc : 0 < c)
    (hm : m ≤ c ^ 2 - 1) : Nat.sqrt m ≤ c - 1 := by
  have hm' : m < c ^ 2 := by
    have hc2 : 0 < c ^ 2 := pow_pos hc _
    omega
  have hs : Nat.sqrt m < c := Nat.sqrt_lt'.2 hm'
  omega

/-- The integer square root immediately below a positive square is exact. -/
lemma sqrt_sq_sub_one (c : ℕ) (hc : 0 < c) :
    Nat.sqrt (c ^ 2 - 1) = c - 1 := by
  apply le_antisymm
  · exact sqrt_le_sub_one_of_le_sq_sub_one hc le_rfl
  · rw [Nat.le_sqrt']
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
    simp only [Nat.succ_sub_one]
    have hsquare : (d + 1) ^ 2 = d ^ 2 + 2 * d + 1 := by ring
    rw [Nat.succ_eq_add_one, hsquare]
    omega

/-- A convenient specialization of the previous bound to `c = Nat.sqrt n`. -/
lemma sqrt_le_sqrt_sub_one_of_le {m n : ℕ} (hn : 0 < n)
    (hm : m ≤ (Nat.sqrt n) ^ 2 - 1) :
    Nat.sqrt m ≤ Nat.sqrt n - 1 := by
  exact sqrt_le_sub_one_of_le_sq_sub_one (Nat.sqrt_pos.2 hn) hm

/-- Comparing an integer to a real square root is the same as comparing it to the
integer square root.  This formulation also handles negative integers. -/
lemma int_le_real_sqrt_iff (k : ℤ) (n : ℕ) :
    (k : ℝ) ≤ Real.sqrt n ↔ k ≤ (Nat.sqrt n : ℤ) := by
  rw [← Int.le_floor]
  simp only [Real.floor_real_sqrt_eq_nat_sqrt]

/-- The natural-cast version of `int_le_real_sqrt_iff`. -/
lemma nat_le_real_sqrt_iff (k n : ℕ) :
    (k : ℝ) ≤ Real.sqrt n ↔ k ≤ Nat.sqrt n := by
  exact_mod_cast int_le_real_sqrt_iff (k : ℤ) n

/-! ## Ceiling halves -/

/-- The natural-number expression for `⌈a / 2⌉`. -/
def ceilHalf (a : ℕ) : ℕ := (a + 1) / 2

/-- `ceilHalf` agrees with Mathlib's ceiling division by two. -/
lemma ceilHalf_eq_ceilDiv (a : ℕ) : ceilHalf a = a ⌈/⌉ 2 := by
  rw [ceilHalf, Nat.ceilDiv_eq_add_pred_div]
  congr 1

/-- The floor and ceiling halves add back to the original number. -/
lemma div_two_add_ceilHalf (a : ℕ) : a / 2 + ceilHalf a = a := by
  rw [ceilHalf]
  omega

lemma ceilHalf_add_div_two (a : ℕ) : ceilHalf a + a / 2 = a := by
  rw [add_comm]
  exact div_two_add_ceilHalf a

/-- Ceiling-half is the complement of floor-half. -/
lemma ceilHalf_eq_sub_div_two (a : ℕ) : ceilHalf a = a - a / 2 := by
  rw [ceilHalf]
  omega

/-- Removing the ceiling half leaves the floor half. -/
lemma sub_ceilHalf_eq_div_two (a : ℕ) : a - ceilHalf a = a / 2 := by
  rw [ceilHalf]
  omega

/-- Doubling the ceiling half rounds `a` upwards by at most one. -/
lemma le_two_mul_ceilHalf (a : ℕ) : a ≤ 2 * ceilHalf a := by
  rw [ceilHalf]
  omega

lemma two_mul_ceilHalf_le_add_one (a : ℕ) : 2 * ceilHalf a ≤ a + 1 := by
  rw [ceilHalf]
  omega

lemma two_mul_ceilHalf_bounds (a : ℕ) :
    a ≤ 2 * ceilHalf a ∧ 2 * ceilHalf a ≤ a + 1 :=
  ⟨le_two_mul_ceilHalf a, two_mul_ceilHalf_le_add_one a⟩

/-- Order characterization of the ceiling half. -/
lemma ceilHalf_le_iff {a b : ℕ} : ceilHalf a ≤ b ↔ a ≤ 2 * b := by
  rw [ceilHalf, Nat.div_le_iff_le_mul (by omega : 0 < 2)]
  omega

lemma ceilHalf_lt_iff {a b : ℕ} : ceilHalf a < b ↔ a + 1 < 2 * b := by
  rw [ceilHalf, Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]
  omega

lemma le_ceilHalf_iff {a b : ℕ} : b ≤ ceilHalf a ↔ 2 * b ≤ a + 1 := by
  rw [ceilHalf, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  omega

/-- For even inputs ceiling-half and floor-half agree. -/
lemma ceilHalf_eq_div_two_of_even {a : ℕ} (ha : Even a) : ceilHalf a = a / 2 := by
  have hmod : a % 2 = 0 := Nat.even_iff.mp ha
  rw [ceilHalf]
  omega

/-- For odd inputs ceiling-half is one more than floor-half. -/
lemma ceilHalf_eq_div_two_add_one_of_odd {a : ℕ} (ha : Odd a) :
    ceilHalf a = a / 2 + 1 := by
  have hmod : a % 2 = 1 := Nat.odd_iff.mp ha
  rw [ceilHalf]
  omega

lemma two_mul_ceilHalf_of_even {a : ℕ} (ha : Even a) :
    2 * ceilHalf a = a := by
  have hmod : a % 2 = 0 := Nat.even_iff.mp ha
  rw [ceilHalf_eq_div_two_of_even ha]
  omega

lemma two_mul_ceilHalf_of_odd {a : ℕ} (ha : Odd a) :
    2 * ceilHalf a = a + 1 := by
  have hmod : a % 2 = 1 := Nat.odd_iff.mp ha
  rw [ceilHalf_eq_div_two_add_one_of_odd ha]
  omega

/-! The following aliases expose the same facts with `(a + 1) / 2` literally in the
statement, which is convenient when translating displayed ceiling calculations. -/

lemma div_two_add_add_one_div_two (a : ℕ) :
    a / 2 + (a + 1) / 2 = a := by
  simpa [ceilHalf] using div_two_add_ceilHalf a

lemma add_one_div_two_add_div_two (a : ℕ) :
    (a + 1) / 2 + a / 2 = a := by
  simpa [ceilHalf] using ceilHalf_add_div_two a

lemma le_two_mul_add_one_div_two (a : ℕ) :
    a ≤ 2 * ((a + 1) / 2) := by
  simpa [ceilHalf] using le_two_mul_ceilHalf a

lemma two_mul_add_one_div_two_le (a : ℕ) :
    2 * ((a + 1) / 2) ≤ a + 1 := by
  simpa [ceilHalf] using two_mul_ceilHalf_le_add_one a

lemma add_one_div_two_eq_div_two_of_even {a : ℕ} (ha : Even a) :
    (a + 1) / 2 = a / 2 := by
  simpa [ceilHalf] using ceilHalf_eq_div_two_of_even ha

lemma add_one_div_two_eq_div_two_add_one_of_odd {a : ℕ} (ha : Odd a) :
    (a + 1) / 2 = a / 2 + 1 := by
  simpa [ceilHalf] using ceilHalf_eq_div_two_add_one_of_odd ha

end Erdos518
