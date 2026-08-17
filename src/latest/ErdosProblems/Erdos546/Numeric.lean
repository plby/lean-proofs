import Mathlib

/-!
# Numeric estimates for Erdős Problem 546

This file contains the rounding-safe natural-number estimates used by the
dyadic Sudakov iteration.  In particular, all divisions which represent a
cardinality threshold are ceiling divisions.
-/

namespace Erdos546

/-- Natural-number ceiling division, given a local name for the Ramsey argument. -/
def ceilDiv (a b : ℕ) : ℕ := a ⌈/⌉ b

@[simp]
lemma ceilDiv_eq (a b : ℕ) : ceilDiv a b = (a + b - 1) / b := rfl

lemma ceilDiv_le_iff {a b c : ℕ} (hb : 0 < b) : ceilDiv a b ≤ c ↔ a ≤ b * c := by
  exact ceilDiv_le_iff_le_mul hb

lemma le_mul_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  exact (ceilDiv_le_iff hb).1 le_rfl

lemma mul_ceilDiv_le_add (a b : ℕ) : b * ceilDiv a b ≤ a + b := by
  rw [ceilDiv_eq]
  exact (Nat.mul_div_le (a + b - 1) b).trans (Nat.sub_le _ _)

lemma ceilDiv_mono_left {a₁ a₂ b : ℕ} (h : a₁ ≤ a₂) :
    ceilDiv a₁ b ≤ ceilDiv a₂ b := by
  by_cases hb : b = 0
  · simp [ceilDiv, hb]
  · exact (gc_mul_ceilDiv (Nat.pos_of_ne_zero hb)).monotone_l h

/-- Cancelling a common positive factor can only decrease the ceiling quotient. -/
lemma ceilDiv_mul_le (a b k : ℕ) (hk : 0 < k) (hb : 0 < b) :
    ceilDiv (k * a) (k * b) ≤ ceilDiv a b := by
  apply (ceilDiv_le_iff (Nat.mul_pos hk hb)).2
  calc
    k * a ≤ k * (b * ceilDiv a b) :=
      Nat.mul_le_mul_left k (le_mul_ceilDiv a hb)
    _ = (k * b) * ceilDiv a b := by ring

/-- Ceiling division by `2q` is controlled by first dividing by `q`, then by two. -/
lemma ceilDiv_two_mul_le (s q : ℕ) (hq : 0 < q) :
    ceilDiv s (2 * q) ≤ ceilDiv (ceilDiv s q) 2 := by
  apply (ceilDiv_le_iff (by positivity : 0 < 2 * q)).2
  calc
    s ≤ q * ceilDiv s q := le_mul_ceilDiv s hq
    _ ≤ q * (2 * ceilDiv (ceilDiv s q) 2) :=
      Nat.mul_le_mul_left q (le_mul_ceilDiv (ceilDiv s q) (by norm_num))
    _ = (2 * q) * ceilDiv (ceilDiv s q) 2 := by ring

lemma ceilDiv_two (a : ℕ) : ceilDiv a 2 = (a + 1) / 2 := by
  simp [ceilDiv, Nat.ceilDiv_eq_add_pred_div]

/-- The integral square-root scale. -/
def sqrtScale (m : ℕ) : ℕ := Nat.sqrt m + 1

lemma lt_sqrtScale_sq (m : ℕ) : m < sqrtScale m ^ 2 := by
  simpa [sqrtScale, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' m

lemma le_sqrtScale_sq (m : ℕ) : m ≤ sqrtScale m ^ 2 :=
  (lt_sqrtScale_sq m).le

lemma natSqrt_cast_le_realSqrt (m : ℕ) :
    (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast Nat.sqrt_le' m

/-- For positive `m`, replacing `sqrt m` by `Nat.sqrt m + 1` costs at most a factor two. -/
lemma sqrtScale_cast_le_two_sqrt {m : ℕ} (hm : 0 < m) :
    (sqrtScale m : ℝ) ≤ 2 * Real.sqrt m := by
  have hroot : (1 : ℝ) ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hm
  rw [sqrtScale, Nat.cast_add, Nat.cast_one]
  linarith [natSqrt_cast_le_realSqrt m]

lemma three_mul_ge_fifteen {q : ℕ} (hq : 5 ≤ q) : 15 ≤ 3 * q := by omega

lemma two_mul_le_two_pow_of_five_le : ∀ {q : ℕ}, 5 ≤ q → 2 * q ≤ 2 ^ q := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases h : 5 ≤ q
      · calc
          2 * (q + 1) ≤ 2 * (2 * q) := by omega
          _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 (ih h)
          _ = 2 ^ (q + 1) := by rw [pow_succ]; ring
      · have hq4 : q = 4 := by omega
        subst q
        norm_num

/-- A cubic scale is absorbed by the next dyadic first-set size. -/
lemma two_mul_cube_le_two_pow {q : ℕ} (hq : 5 ≤ q) :
    (2 * q) ^ 3 ≤ 2 ^ (2 * q + 1) := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases h : 5 ≤ q
      · calc
          (2 * (q + 1)) ^ 3 ≤ (3 * q) ^ 3 :=
            Nat.pow_le_pow_left (by omega) 3
          _ ≤ 4 * (2 * q) ^ 3 := by
            ring_nf
            omega
          _ ≤ 4 * 2 ^ (2 * q + 1) := Nat.mul_le_mul_left 4 (ih h)
          _ = 2 ^ (2 * (q + 1) + 1) := by
            rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega, pow_add]
            norm_num
            ring
      · have hq4 : q = 4 := by omega
        subst q
        norm_num

/-- The numerical inequality which turns the sparse-pair loss into `300 s / q`. -/
lemma quadratic_le_two_pow {q : ℕ} (hq : 5 ≤ q) :
    288 * q ^ 2 ≤ 300 * 2 ^ q := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases h : 5 ≤ q
      · calc
          288 * (q + 1) ^ 2 ≤ 2 * (288 * q ^ 2) := by nlinarith
          _ ≤ 2 * (300 * 2 ^ q) := Nat.mul_le_mul_left 2 (ih h)
          _ = 300 * 2 ^ (q + 1) := by rw [pow_succ]; ring
      · have hq4 : q = 4 := by omega
        subst q
        norm_num

/-- The dyadic size requested from the sparse-colour lemma at scale `q`. -/
def pairTarget (q s : ℕ) : ℕ := 2 ^ (2 * q + 1) * s

/-- The exponent lost in the exact sparse-colour lemma. -/
def sparsePairLoss (q s : ℕ) : ℕ :=
  32 * (3 * q) * ceilDiv (pairTarget q s) (2 ^ (3 * q))

/-- The exponent lost in the exact dyadic sparsification lemma. -/
def sparsificationLoss (D q : ℕ) : ℕ := 8 * D * (3 * q) ^ 2

lemma ceilDiv_pairTarget_le (q s : ℕ) :
    ceilDiv (pairTarget q s) (2 ^ (3 * q)) ≤ ceilDiv (2 * s) (2 ^ q) := by
  let k := 2 ^ (2 * q)
  have hk : 0 < k := by positivity
  have hqpow : 0 < 2 ^ q := by positivity
  have hnum : pairTarget q s = k * (2 * s) := by
    simp [pairTarget, k, pow_succ]
    ring
  have hden : 2 ^ (3 * q) = k * 2 ^ q := by
    rw [show 3 * q = 2 * q + q by omega, pow_add]
  rw [hnum, hden]
  exact ceilDiv_mul_le (2 * s) (2 ^ q) k hk hqpow

lemma two_le_ceilDiv_of_two_mul_le {s q : ℕ} (hq : 0 < q) (h : 2 * q ≤ s) :
    2 ≤ ceilDiv s q := by
  by_contra hn
  have hc : ceilDiv s q ≤ 1 := by omega
  have hs : s ≤ q * ceilDiv s q := le_mul_ceilDiv s hq
  have hmul : q * ceilDiv s q ≤ q * 1 := Nat.mul_le_mul_left q hc
  omega

/-- The exact ceiling-halving estimate used to preserve the reservoir invariant. -/
lemma reservoir_ceiling_halving {s q : ℕ} (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s) :
    2048 * ceilDiv s (2 * q) ≤ 1536 * ceilDiv s q := by
  have hqpos : 0 < q := by omega
  have htwoq : 2 * q ≤ s :=
    (two_mul_le_two_pow_of_five_le hq).trans hlegal
  let c := ceilDiv s q
  have hc : 2 ≤ c := two_le_ceilDiv_of_two_mul_le hqpos htwoq
  have hhalve : ceilDiv s (2 * q) ≤ (c + 1) / 2 := by
    simpa [c, ceilDiv_two] using ceilDiv_two_mul_le s q hqpos
  have hdiv : (c + 1) / 2 * 2 ≤ c + 1 := Nat.div_mul_le_self (c + 1) 2
  calc
    2048 * ceilDiv s (2 * q) ≤ 2048 * ((c + 1) / 2) :=
      Nat.mul_le_mul_left 2048 hhalve
    _ ≤ 1536 * c := by omega

lemma sparsificationLoss_le {D q s : ℕ} (hq : 0 < q)
    (hdegree : D * q ^ 3 ≤ 2 * s) :
    sparsificationLoss D q ≤ 144 * ceilDiv s q := by
  have hs : s ≤ q * ceilDiv s q := le_mul_ceilDiv s hq
  apply Nat.le_of_mul_le_mul_left (c := q) (hc := hq)
  calc
    q * sparsificationLoss D q = 72 * (D * q ^ 3) := by
      simp [sparsificationLoss]
      ring
    _ ≤ 72 * (2 * s) := Nat.mul_le_mul_left 72 hdegree
    _ = 144 * s := by ring
    _ ≤ 144 * (q * ceilDiv s q) := Nat.mul_le_mul_left 144 hs
    _ = q * (144 * ceilDiv s q) := by ring

/-- At a legal scale, the exact sparse-pair loss is at most
`300 * ceil(s/q)`. -/
lemma sparsePairLoss_le {q s : ℕ} (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s) :
    sparsePairLoss q s ≤ 300 * ceilDiv s q := by
  let z := ceilDiv (pairTarget q s) (2 ^ (3 * q))
  let z' := ceilDiv (2 * s) (2 ^ q)
  have hzz : z ≤ z' := by
    exact ceilDiv_pairTarget_le q s
  have hz' : z' * 2 ^ q ≤ 3 * s := by
    have hupper : 2 ^ q * z' ≤ 2 * s + 2 ^ q :=
      mul_ceilDiv_le_add (2 * s) (2 ^ q)
    rw [mul_comm] at hupper
    omega
  have hz : z * 2 ^ q ≤ 3 * s :=
    (Nat.mul_le_mul_right (2 ^ q) hzz).trans hz'
  have hcoreMul : (96 * q ^ 2 * z) * 2 ^ q ≤ (300 * s) * 2 ^ q := by
    calc
      (96 * q ^ 2 * z) * 2 ^ q = (96 * q ^ 2) * (z * 2 ^ q) := by ring
      _ ≤ (96 * q ^ 2) * (3 * s) := Nat.mul_le_mul_left (96 * q ^ 2) hz
      _ = (288 * q ^ 2) * s := by ring
      _ ≤ (300 * 2 ^ q) * s := Nat.mul_le_mul_right s (quadratic_le_two_pow hq)
      _ = (300 * s) * 2 ^ q := by ring
  have hcore : 96 * q ^ 2 * z ≤ 300 * s :=
    Nat.le_of_mul_le_mul_right hcoreMul (by positivity)
  have hqpos : 0 < q := by omega
  have hs : s ≤ q * ceilDiv s q := le_mul_ceilDiv s hqpos
  apply Nat.le_of_mul_le_mul_left (c := q) (hc := hqpos)
  calc
    q * sparsePairLoss q s = 96 * q ^ 2 * z := by
      simp [sparsePairLoss, z]
      ring
    _ ≤ 300 * s := hcore
    _ ≤ 300 * (q * ceilDiv s q) := Nat.mul_le_mul_left 300 hs
    _ = q * (300 * ceilDiv s q) := by ring

lemma total_loss_le {D q s : ℕ} (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s)
    (hdegree : D * q ^ 3 ≤ 2 * s) :
    sparsificationLoss D q + sparsePairLoss q s ≤ 512 * ceilDiv s q := by
  have hE := sparsificationLoss_le (D := D) (q := q) (s := s) (by omega) hdegree
  have hF := sparsePairLoss_le (q := q) (s := s) hq hlegal
  omega

/-- After paying both losses, the exponent left at scale `q` pays the full
reservoir invariant at scale `2q`. -/
lemma loss_budget_for_next_scale {D q s : ℕ} (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s)
    (hdegree : D * q ^ 3 ≤ 2 * s) :
    2048 * ceilDiv s (2 * q) +
        (sparsificationLoss D q + sparsePairLoss q s) ≤
      2048 * ceilDiv s q := by
  have hhalf := reservoir_ceiling_halving (s := s) (q := q) hq hlegal
  have hloss := total_loss_le (D := D) (q := q) (s := s) hq hlegal hdegree
  omega

lemma pairTarget_ge_density_denominator {q s : ℕ} (hlegal : 2 ^ q ≤ s) :
    2 ^ (3 * q) ≤ pairTarget q s := by
  calc
    2 ^ (3 * q) = 2 ^ (2 * q) * 2 ^ q := by
      rw [show 3 * q = 2 * q + q by omega, pow_add]
    _ ≤ 2 ^ (2 * q) * s := Nat.mul_le_mul_left (2 ^ (2 * q)) hlegal
    _ ≤ 2 * (2 ^ (2 * q) * s) := by omega
    _ = pairTarget q s := by
      simp [pairTarget, pow_succ]
      ring

lemma pairTarget_le_buffer {q s : ℕ} (hlegal : 2 ^ q ≤ s) :
    pairTarget q s ≤ 2 * s ^ 3 := by
  have hsq : (2 ^ q) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hlegal 2
  calc
    pairTarget q s = 2 * (2 ^ q) ^ 2 * s := by
      rw [pairTarget, show 2 * q + 1 = (q + q) + 1 by omega, pow_succ, pow_add]
      ring
    _ ≤ 2 * s ^ 2 * s := Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 hsq)
    _ = 2 * s ^ 3 := by ring

lemma next_cube_le_pairTarget {q s : ℕ} (hq : 5 ≤ q) :
    (2 * q) ^ 3 * s ≤ pairTarget q s := by
  have h := Nat.mul_le_mul_right s (two_mul_cube_le_two_pow hq)
  simpa [pairTarget] using h

lemma crossing_pairTarget_gt {q s : ℕ} (hs : 0 < s) (hcross : s < 2 ^ (2 * q)) :
    2 * s ^ 2 < pairTarget q s := by
  have hmul : s * s < 2 ^ (2 * q) * s := (Nat.mul_lt_mul_right hs).2 hcross
  calc
    2 * s ^ 2 = 2 * (s * s) := by ring
    _ < 2 * (2 ^ (2 * q) * s) := (Nat.mul_lt_mul_left (by norm_num)).2 hmul
    _ = pairTarget q s := by
      simp [pairTarget, pow_succ]
      ring

/-- The polynomial exponent needed for the bounded small-scale branch. -/
lemma small_scale_exponent_bound {s n : ℕ} (hs : s < 32) (hn : n ≤ 2 * s ^ 2) :
    2 * n ≤ 124 * s := by
  have hs31 : s ≤ 31 := by omega
  calc
    2 * n ≤ 2 * (2 * s ^ 2) := Nat.mul_le_mul_left 2 hn
    _ = (4 * s) * s := by ring
    _ ≤ (4 * s) * 31 := Nat.mul_le_mul_left (4 * s) hs31
    _ = 124 * s := by ring

/-- The fixed multiplicative buffer retained in every reservoir. -/
def reservoirBuffer (s : ℕ) : ℕ := 2 * s ^ 3

/-- The exponent in the scale-`q` reservoir invariant. -/
def reservoirExponent (q s : ℕ) : ℕ := 2048 * ceilDiv s q

lemma ceilDiv_le_self (s : ℕ) {q : ℕ} (hq : 0 < q) : ceilDiv s q ≤ s := by
  apply (ceilDiv_le_iff hq).2
  nlinarith

lemma reservoirBuffer_le_two_pow {s : ℕ} (hs : 0 < s) :
    reservoirBuffer s ≤ 2 ^ (4 * s) := by
  have hsPow : s ≤ 2 ^ s := (Nat.lt_two_pow_self).le
  have hcube : s ^ 3 ≤ (2 ^ s) ^ 3 := Nat.pow_le_pow_left hsPow 3
  calc
    reservoirBuffer s = 2 * s ^ 3 := rfl
    _ ≤ 2 * (2 ^ s) ^ 3 := Nat.mul_le_mul_left 2 hcube
    _ = 2 ^ (s * 3 + 1) := by
      rw [← pow_mul, pow_succ]
      ring
    _ ≤ 2 ^ (4 * s) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Coarse domination of the initial reservoir target. -/
lemma starting_target_le_coarse {s : ℕ} (hs : 0 < s) :
    reservoirBuffer s * 2 ^ reservoirExponent 5 s ≤ 2 ^ (2052 * s) := by
  have hceil : ceilDiv s 5 ≤ s := ceilDiv_le_self s (by norm_num)
  have hexp : reservoirExponent 5 s ≤ 2048 * s :=
    Nat.mul_le_mul_left 2048 hceil
  calc
    reservoirBuffer s * 2 ^ reservoirExponent 5 s ≤
        2 ^ (4 * s) * 2 ^ (2048 * s) :=
      Nat.mul_le_mul (reservoirBuffer_le_two_pow hs)
        (Nat.pow_le_pow_right (by norm_num) hexp)
    _ = 2 ^ (2052 * s) := by
      rw [← pow_add]
      congr 1
      omega

/-- With `C₀ = 32768`, the initial Erdős--Szekeres subtraction is harmless. -/
lemma starting_reservoir_add_le {s : ℕ} (hs : 32 ≤ s) :
    reservoirBuffer s * 2 ^ reservoirExponent 5 s + 250 * s ≤
      2 ^ ((32768 - 250) * s) := by
  have hspos : 0 < s := by omega
  have htarget := starting_target_le_coarse hspos
  have hlinear : 250 * s ≤ 2 ^ (2052 * s) := by
    have hsPow : s ≤ 2 ^ s := (Nat.lt_two_pow_self).le
    calc
      250 * s ≤ 2 ^ 8 * 2 ^ s := Nat.mul_le_mul (by norm_num) hsPow
      _ = 2 ^ (8 + s) := by rw [pow_add]
      _ ≤ 2 ^ (2052 * s) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    reservoirBuffer s * 2 ^ reservoirExponent 5 s + 250 * s ≤
        2 ^ (2052 * s) + 2 ^ (2052 * s) := Nat.add_le_add htarget hlinear
    _ = 2 ^ (2052 * s + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ((32768 - 250) * s) :=
      Nat.pow_le_pow_right (by norm_num) (by norm_num; omega)

lemma starting_reservoir_le_sub {s : ℕ} (hs : 32 ≤ s) :
    reservoirBuffer s * 2 ^ reservoirExponent 5 s ≤
      2 ^ ((32768 - 250) * s) - 250 * s :=
  Nat.le_sub_of_add_le (starting_reservoir_add_le hs)

end Erdos546
