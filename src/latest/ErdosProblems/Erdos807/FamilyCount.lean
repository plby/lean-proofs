/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos807.Parameters

/-!
# Counting the canonical bit matrices for Erdős Problem 807

The ABH construction has `r` labelled ten-vertex blocks and `90 * r`
labelled vertices on the other shore.  Once these roles are fixed, its free
data is exactly an `r × (90r)` Boolean matrix.  This file records that exact
count and a division-free sufficient condition ensuring that the corresponding
first-moment quantity is at least `2^(100r)`.
-/

open scoped BigOperators

namespace Erdos807
namespace FamilyCount

/-- The Boolean incidence matrix of the canonical ABH presentation. -/
abbrev BitMatrix (r : ℕ) := Fin r → Fin (90 * r) → Bool

/-- The number of free bits in a canonical presentation. -/
def bitCount (r : ℕ) : ℕ := 90 * r * r

/-- The order of the induced structured graph associated to `r` blocks. -/
def structuredOrder (r : ℕ) : ℕ := 100 * r

/-- Exact number of canonical Boolean presentations. -/
@[simp] theorem card_bitMatrix (r : ℕ) :
  Fintype.card (BitMatrix r) = 2 ^ bitCount r := by
  simp [BitMatrix, bitCount, pow_mul]

/-- The first-moment expression before any second-moment argument: choose the
`100r` vertices, choose their canonical matrix, and divide by the number of
possible graphs on those vertices. -/
noncomputable def firstMoment (n r : ℕ) : ℝ :=
  (n.choose (structuredOrder r) : ℝ) *
      (2 : ℝ) ^ bitCount r /
    (2 : ℝ) ^ (structuredOrder r).choose 2

/-- First moment for the stable slot model used by the second-moment proof.
There are `structuredOrder r` labelled slots and `n / structuredOrder r`
choices in each slot. -/
noncomputable def slotFirstMoment (n r : ℕ) : ℝ :=
  (((n / structuredOrder r : ℕ) : ℝ) ^ structuredOrder r) *
      (2 : ℝ) ^ bitCount r /
    (2 : ℝ) ^ (structuredOrder r).choose 2

/-- Closed form for the power of two which the binomial coefficient must
contribute in order that `firstMoment n r ≥ 2^(100r)`. -/
def requiredChooseExponent (r : ℕ) : ℕ := 4910 * r * r + 100 * r

/-- A convenient integral ceiling for
`requiredChooseExponent r / structuredOrder r`. -/
def chooseExponentPerVertex (r : ℕ) : ℕ :=
  49 * r + (r + 9) / 10 + 1

lemma choose_two_structuredOrder_le (r : ℕ) :
    (structuredOrder r).choose 2 ≤ 5000 * r * r := by
  rw [Nat.choose_two_right]
  calc
    structuredOrder r * (structuredOrder r - 1) / 2 ≤
        structuredOrder r * structuredOrder r / 2 := by
      gcongr
      exact Nat.sub_le _ _
    _ = 5000 * r * r := by
      simp only [structuredOrder]
      rw [show 100 * r * (100 * r) = 2 * (5000 * r * r) by ring]
      simp

lemma requiredChooseExponent_inequality (r : ℕ) :
    structuredOrder r + (structuredOrder r).choose 2 ≤
      bitCount r + requiredChooseExponent r := by
  have h := choose_two_structuredOrder_le r
  calc
    structuredOrder r + (structuredOrder r).choose 2 ≤
        structuredOrder r + 5000 * r * r := Nat.add_le_add_left h _
    _ = bitCount r + requiredChooseExponent r := by
      simp only [structuredOrder, bitCount, requiredChooseExponent]
      ring

lemma requiredChooseExponent_le_mul (r : ℕ) :
    requiredChooseExponent r ≤
      structuredOrder r * chooseExponentPerVertex r := by
  simp only [requiredChooseExponent, structuredOrder, chooseExponentPerVertex]
  have hceil : r ≤ 10 * ((r + 9) / 10) := by omega
  nlinarith

lemma ten_mul_chooseExponentPerVertex_le (r : ℕ) :
    10 * chooseExponentPerVertex r ≤ 491 * r + 19 := by
  simp only [chooseExponentPerVertex]
  have hdiv := Nat.div_mul_le_self (r + 9) 10
  omega

@[simp] lemma structuredOrder_blockCount (n : ℕ) :
    structuredOrder (blockCount n) = structuredSize n := by
  rw [structuredOrder, structuredSize_eq_mul_blockCount]

/-- A deliberately elementary polynomial-versus-exponential estimate used to
absorb the factor `structuredOrder r` in the first-moment threshold. -/
lemma linear_le_two_pow {x : ℕ} (hx : 20 ≤ x) :
    2400 * (x + 1) ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
      rw [pow_succ]
      have hstep : 2400 ≤ 2400 * (x + 1) := by omega
      omega

/-- At the repository's coefficient `k = 2.03 floor(log₂ n)`, the dyadic
exponent gap absorbs the polynomial factor in the sufficient first-moment
condition.  The numerical threshold is intentionally coarse. -/
lemma room_of_logParameter_ge {n : ℕ} (hn : 8000 ≤ logParameter n) :
    2 ^ chooseExponentPerVertex (blockCount n) *
        structuredOrder (blockCount n) ≤
      n + 1 - structuredOrder (blockCount n) := by
  let m := logParameter n
  let r := blockCount n
  let x := m / 400
  let k := structuredOrder r
  have hm : 8000 ≤ m := hn
  have hrbound : 10000 * r ≤ 203 * m := by
    calc
      10000 * r = structuredSize n * 100 := by
        rw [structuredSize_eq_mul_blockCount]
        simp only [r]
        ring
      _ ≤ 203 * m := structuredSize_mul_100_le n
  have hqbound : 10 * chooseExponentPerVertex r ≤ 491 * r + 19 :=
    ten_mul_chooseExponentPerVertex_le r
  have hxmul : 400 * x ≤ m := by
    simpa only [x, Nat.mul_comm] using Nat.div_mul_le_self m 400
  have hgap : chooseExponentPerVertex r + x ≤ m := by
    omega
  have hx : 20 ≤ x := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 400)).2
    omega
  have hklog : k ≤ 3 * m := by
    simpa [k, r, m, structuredOrder_blockCount] using
      structuredSize_le_three_mul_logParameter n
  have hm_lt : m < 400 * (x + 1) := by
    have h := Nat.lt_div_mul_add (a := m) (b := 400) (by norm_num)
    simpa only [x] using (show m < 400 * (m / 400 + 1) by omega)
  have hpoly : 2 * k ≤ 2 ^ x := by
    calc
      2 * k ≤ 6 * m := by omega
      _ ≤ 2400 * (x + 1) := by omega
      _ ≤ 2 ^ x := linear_le_two_pow hx
  have hpowgap : 2 ^ chooseExponentPerVertex r * (2 * k) ≤ 2 ^ m := by
    calc
      2 ^ chooseExponentPerVertex r * (2 * k) ≤
          2 ^ chooseExponentPerVertex r * 2 ^ x :=
        Nat.mul_le_mul_left _ hpoly
      _ = 2 ^ (chooseExponentPerVertex r + x) := (pow_add _ _ _).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hgap
  have hnpos : 0 < n := by
    by_contra hzero
    have : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [m, logParameter] at hm
  have hsum :
      2 ^ chooseExponentPerVertex r * k + k ≤ n := by
    calc
      2 ^ chooseExponentPerVertex r * k + k ≤
          2 ^ chooseExponentPerVertex r * k +
            2 ^ chooseExponentPerVertex r * k := by
        gcongr
        exact Nat.le_mul_of_pos_left k (by positivity)
      _ = 2 ^ chooseExponentPerVertex r * (2 * k) := by ring
      _ ≤ 2 ^ m := hpowgap
      _ ≤ n := pow_logParameter_le hnpos
  have hsum' :
      2 ^ chooseExponentPerVertex (blockCount n) *
          structuredOrder (blockCount n) + structuredOrder (blockCount n) ≤ n := by
    simpa only [r, k] using hsum
  omega

/-- A real-valued lower bound for a binomial coefficient, in a form that is
well suited to exponent comparisons. -/
lemma choose_lower_bound {n k : ℕ} :
    ((n + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k ≤ (n.choose k : ℝ) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  calc
    ((n + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k ≤
        ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := by
      gcongr
      exact_mod_cast k.factorial_le_pow
    _ ≤ (n.choose k : ℝ) := Nat.pow_le_choose k n

/-- If the available vertex count dominates the per-vertex exponential cost,
then the binomial coefficient supplies every power of two required by the
first moment. -/
lemma pow_requiredChooseExponent_le_choose
    {n r : ℕ} (hr : 0 < r)
    (hroom : 2 ^ chooseExponentPerVertex r * structuredOrder r ≤
      n + 1 - structuredOrder r) :
    (2 : ℝ) ^ requiredChooseExponent r ≤
      (n.choose (structuredOrder r) : ℝ) := by
  let k := structuredOrder r
  let q := chooseExponentPerVertex r
  have hk : 0 < k := by simp [k, structuredOrder, hr]
  have hroomR : (2 : ℝ) ^ q * k ≤ (n + 1 - k : ℕ) := by
    exact_mod_cast hroom
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : (2 : ℝ) ^ q ≤ ((n + 1 - k : ℕ) : ℝ) / k := by
    rw [le_div_iff₀ hkR]
    simpa [mul_comm] using hroomR
  have hpow : (2 : ℝ) ^ (k * q) ≤
      (((n + 1 - k : ℕ) : ℝ) / k) ^ k := by
    rw [mul_comm k q, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hexp : requiredChooseExponent r ≤ k * q := by
    simpa [k, q] using requiredChooseExponent_le_mul r
  calc
    (2 : ℝ) ^ requiredChooseExponent r ≤ (2 : ℝ) ^ (k * q) := by
      exact pow_le_pow_right₀ (by norm_num) hexp
    _ ≤ (((n + 1 - k : ℕ) : ℝ) / k) ^ k := hpow
    _ = ((n + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k := by
      rw [div_pow]
    _ ≤ (n.choose k : ℝ) := choose_lower_bound

/-- The explicit lower-threshold lemma used for `h(n,100r)`: under the
displayed integer inequality, the expected number of canonical structured
induced subgraphs is at least `2^(100r)`. -/
theorem firstMoment_ge_two_pow
    {n r : ℕ} (hr : 0 < r)
    (hroom : 2 ^ chooseExponentPerVertex r * structuredOrder r ≤
      n + 1 - structuredOrder r) :
    (2 : ℝ) ^ structuredOrder r ≤ firstMoment n r := by
  have hchoose := pow_requiredChooseExponent_le_choose hr hroom
  have hden : (0 : ℝ) < (2 : ℝ) ^ (structuredOrder r).choose 2 := by positivity
  rw [firstMoment, le_div_iff₀ hden]
  rw [← pow_add]
  calc
    (2 : ℝ) ^ (structuredOrder r + (structuredOrder r).choose 2) ≤
        (2 : ℝ) ^ (bitCount r + requiredChooseExponent r) := by
      exact pow_le_pow_right₀ (by norm_num) (requiredChooseExponent_inequality r)
    _ = (2 : ℝ) ^ requiredChooseExponent r * (2 : ℝ) ^ bitCount r := by
      rw [pow_add]
      ring
    _ ≤ (n.choose (structuredOrder r) : ℝ) * (2 : ℝ) ^ bitCount r :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)

/-- Slot-model counterpart of `firstMoment_ge_two_pow`.  Its hypothesis is
division-free and says exactly that the quotient `n / structuredOrder r`
dominates the required power of two per chosen vertex. -/
theorem slotFirstMoment_ge_two_pow
    {n r : ℕ} (hr : 0 < r)
    (hroom : 2 ^ chooseExponentPerVertex r * structuredOrder r ≤ n) :
    (2 : ℝ) ^ structuredOrder r ≤ slotFirstMoment n r := by
  let k := structuredOrder r
  let q := chooseExponentPerVertex r
  have hk : 0 < k := by simp [k, structuredOrder, hr]
  have hbase : 2 ^ q ≤ n / k := by
    apply (Nat.le_div_iff_mul_le hk).2
    simpa [mul_comm] using hroom
  have hrequiredNat :
      2 ^ requiredChooseExponent r ≤ (n / k) ^ k := by
    calc
      2 ^ requiredChooseExponent r ≤ 2 ^ (k * q) :=
        Nat.pow_le_pow_right (by norm_num) (by
          simpa [k, q] using requiredChooseExponent_le_mul r)
      _ = (2 ^ q) ^ k := by rw [mul_comm k q, pow_mul]
      _ ≤ (n / k) ^ k := Nat.pow_le_pow_left hbase k
  have hrequired :
      (2 : ℝ) ^ requiredChooseExponent r ≤
        (((n / k : ℕ) : ℝ) ^ k) := by
    exact_mod_cast hrequiredNat
  have hden : (0 : ℝ) < (2 : ℝ) ^ (structuredOrder r).choose 2 := by positivity
  rw [slotFirstMoment, le_div_iff₀ hden]
  rw [← pow_add]
  calc
    (2 : ℝ) ^ (structuredOrder r + (structuredOrder r).choose 2) ≤
        (2 : ℝ) ^ (bitCount r + requiredChooseExponent r) := by
      exact pow_le_pow_right₀ (by norm_num) (requiredChooseExponent_inequality r)
    _ = (2 : ℝ) ^ requiredChooseExponent r * (2 : ℝ) ^ bitCount r := by
      rw [pow_add]
      ring
    _ ≤ (((n / structuredOrder r : ℕ) : ℝ) ^ structuredOrder r) *
        (2 : ℝ) ^ bitCount r := by
      simpa only [k] using mul_le_mul_of_nonneg_right hrequired (by positivity)

/-- End-to-end first-moment lower bound for the rounded parameters used in
the main proof. -/
theorem eventually_firstMoment_ge_two_pow :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ structuredSize n ≤ firstMoment n (blockCount n) := by
  filter_upwards
      [tendsto_logParameter_atTop.eventually_ge_atTop 8000,
        eventually_one_le_blockCount] with n hn hr
  rw [← structuredOrder_blockCount]
  exact firstMoment_ge_two_pow (n := n) (r := blockCount n) hr
    (room_of_logParameter_ge hn)

/-- The room estimate in the exact form required by stable slots. -/
lemma slot_room_of_logParameter_ge {n : ℕ} (hn : 8000 ≤ logParameter n) :
    2 ^ chooseExponentPerVertex (blockCount n) *
        structuredOrder (blockCount n) ≤ n := by
  have h := room_of_logParameter_ge hn
  have hr : 0 < structuredOrder (blockCount n) := by
    have : 0 < blockCount n := by
      rw [blockCount_eq]
      apply Nat.div_pos
      · calc
          10000 ≤ 203 * 8000 := by norm_num
          _ ≤ 203 * logParameter n := Nat.mul_le_mul_left 203 hn
      · norm_num
    exact Nat.mul_pos (by norm_num) this
  omega

/-- End-to-end lower bound for the stable-slot first moment. -/
theorem eventually_slotFirstMoment_ge_two_pow :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ structuredSize n ≤ slotFirstMoment n (blockCount n) := by
  filter_upwards
      [tendsto_logParameter_atTop.eventually_ge_atTop 8000,
        eventually_one_le_blockCount] with n hn hr
  rw [← structuredOrder_blockCount]
  exact slotFirstMoment_ge_two_pow (n := n) (r := blockCount n) hr
    (slot_room_of_logParameter_ge hn)

end FamilyCount
end Erdos807
