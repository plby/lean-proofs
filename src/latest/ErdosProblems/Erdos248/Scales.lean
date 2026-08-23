import ErdosProblems.Erdos248.Arithmetic
import BoundedGaps.Maynard.ImprovedGPY.PairSum

/-!
# Erdős Problem 248: an explicit Tao--Teräväinen scale hierarchy

For the integer parameter `K > 0` put

* `M = 100^(100 K)` and `x = 2^M`;
* `w = 2^(100 K)` and `W = primorial w`;
* `R_k = 2^(100^(100 K-k))` for `1 ≤ k ≤ K`.

Thus `R_k = x^(1/100^k)` at the level of binary exponents.  The essential
feature is the convergent geometric budget
`sum_{k≥1} 2 / 100^k < 1/40`: after the Selberg square is expanded, every
CRT modulus is still a small fixed power of `x`.  Meanwhile the smallest
near radius has logarithm `100^(99 K)`, overwhelmingly larger than the
dimension and the pre-sieve cutoff.
-/

open scoped BigOperators

namespace Erdos248

/-- Binary exponent of the dyadic interval endpoint. -/
def intervalExponent (K : ℕ) : ℕ :=
  100 ^ (100 * K)

/-- Left endpoint of the dyadic interval carrying the sieve measure. -/
def intervalStart (K : ℕ) : ℕ :=
  2 ^ intervalExponent K

/-- Cutoff of the primorial pre-sieve. -/
def tinyCutoff (K : ℕ) : ℕ :=
  2 ^ (100 * K)

/-- Radius assigned to the near shift `k`.  Only its values for
`1 ≤ k ≤ K` are used. -/
def shiftRadius (K k : ℕ) : ℕ :=
  2 ^ (100 ^ (100 * K - k))

/-- A half-logarithmic coordinate radius.  On every near coordinate its
square is exactly `shiftRadius K k`.  It is used to obtain a fixed positive
lower bound for the quadratic cutoff in the Y-diagonal. -/
def innerShiftRadius (K k : ℕ) : ℕ :=
  2 ^ (50 * 100 ^ (100 * K - k - 1))

/-- Common normalization radius for the generic finite Y-transform.  The
actual support is the much smaller coordinate box `r k < R_k`; the geometric
sum of its logarithmic side lengths is less than `log(globalRadius)`. -/
def globalRadius (K : ℕ) : ℕ :=
  intervalStart K

/-- The shifts handled directly by the multidimensional Selberg weight. -/
def nearShifts (K : ℕ) : Finset ℕ :=
  Finset.Icc 1 K

@[simp] theorem mem_nearShifts {K k : ℕ} :
    k ∈ nearShifts K ↔ 1 ≤ k ∧ k ≤ K := by
  simp [nearShifts]

theorem nearShifts_nonempty {K : ℕ} (hK : 0 < K) :
    (nearShifts K).Nonempty := by
  exact ⟨1, mem_nearShifts.mpr ⟨by omega, hK⟩⟩

@[simp] theorem nearShifts_card (K : ℕ) : (nearShifts K).card = K := by
  simp [nearShifts]

theorem intervalExponent_pos (K : ℕ) : 0 < intervalExponent K := by
  unfold intervalExponent
  exact pow_pos (by norm_num) _

theorem intervalStart_pos (K : ℕ) : 0 < intervalStart K := by
  unfold intervalStart
  exact pow_pos (by norm_num) _

theorem tinyCutoff_pos (K : ℕ) : 0 < tinyCutoff K := by
  unfold tinyCutoff
  exact pow_pos (by norm_num) _

theorem shiftRadius_pos (K k : ℕ) : 0 < shiftRadius K k := by
  unfold shiftRadius
  exact pow_pos (by norm_num) _

theorem innerShiftRadius_pos (K k : ℕ) : 0 < innerShiftRadius K k := by
  unfold innerShiftRadius
  exact pow_pos (by norm_num) _

theorem one_lt_shiftRadius (K k : ℕ) : 1 < shiftRadius K k := by
  unfold shiftRadius
  exact one_lt_pow₀ (by norm_num) (pow_pos (by norm_num) _).ne'

theorem one_lt_innerShiftRadius (K k : ℕ) : 1 < innerShiftRadius K k := by
  unfold innerShiftRadius
  exact one_lt_pow₀ (by norm_num) (by positivity)

theorem globalRadius_pos (K : ℕ) : 0 < globalRadius K := by
  unfold globalRadius
  exact pow_pos (by norm_num) _

theorem one_lt_globalRadius (K : ℕ) : 1 < globalRadius K := by
  unfold globalRadius intervalStart
  exact one_lt_pow₀ (by norm_num) (intervalExponent_pos K).ne'

theorem K_le_tinyCutoff (K : ℕ) : K ≤ tinyCutoff K := by
  calc
    K ≤ 2 ^ K := K.lt_two_pow_self.le
    _ ≤ 2 ^ (100 * K) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

theorem nearShifts_diameter (K : ℕ) :
    BoundedGaps.Maynard.ShiftDiameterBound (nearShifts K) K := by
  intro a b hab
  have ha := (mem_nearShifts.mp a.property).2
  have hb := (mem_nearShifts.mp b.property).2
  unfold Nat.dist
  omega

/-- Every prime that could cause two different near coordinates to collide
is absorbed into the primorial pre-sieve. -/
theorem nearShifts_cover (K : ℕ) :
    BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (nearShifts K) (primorial (tinyCutoff K)) := by
  apply BoundedGaps.Maynard.coversShiftDifferencePrimes_of_diameter
    (D₀ := tinyCutoff K)
  intro a b hab
  exact (nearShifts_diameter K hab).trans (K_le_tinyCutoff K)

theorem shiftRadius_eq_pow (K k : ℕ) :
    shiftRadius K k = 2 ^ (100 ^ (100 * K - k)) := rfl

/-- The exponent in a near coordinate is twice the exponent defining the
inner radius. -/
theorem shiftExponent_eq_two_mul_innerExponent {K k : ℕ}
    (hK : 0 < K) (hk : k ≤ K) :
    100 ^ (100 * K - k) =
      2 * (50 * 100 ^ (100 * K - k - 1)) := by
  have hpos : 0 < 100 * K - k := by omega
  calc
    100 ^ (100 * K - k) =
        100 ^ ((100 * K - k - 1) + 1) := by congr 1 <;> omega
    _ = 100 ^ (100 * K - k - 1) * 100 := by
      simp [pow_succ', Nat.mul_comm]
    _ = 2 * (50 * 100 ^ (100 * K - k - 1)) := by ring

theorem innerShiftRadius_sq {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    innerShiftRadius K k ^ 2 = shiftRadius K k := by
  rw [innerShiftRadius, shiftRadius, ← pow_mul]
  congr 1
  simpa [mul_comm] using (shiftExponent_eq_two_mul_innerExponent hK hk).symm

theorem innerShiftRadius_le_shiftRadius {K k : ℕ}
    (hK : 0 < K) (hk : k ≤ K) :
    innerShiftRadius K k ≤ shiftRadius K k := by
  rw [← innerShiftRadius_sq hK hk]
  exact Nat.le_pow (by norm_num)

theorem innerShiftRadius_mono_near {K h : ℕ} (hK : 0 < K)
    (hh : h ≤ K) :
    innerShiftRadius K K ≤ innerShiftRadius K h := by
  unfold innerShiftRadius
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem log_shiftRadius_eq_two_mul_log_inner {K k : ℕ}
    (hK : 0 < K) (hk : k ≤ K) :
    Real.log (shiftRadius K k) =
      2 * Real.log (innerShiftRadius K k) := by
  have hsquare :
      ((innerShiftRadius K k : ℕ) : ℝ) ^ 2 = shiftRadius K k := by
    exact_mod_cast innerShiftRadius_sq hK hk
  rw [← hsquare, Real.log_pow]
  norm_num

theorem log_tinyCutoff (K : ℕ) :
    Real.log (tinyCutoff K) =
      ((100 * K : ℕ) : ℝ) * Real.log 2 := by
  rw [tinyCutoff]
  push_cast
  rw [Real.log_pow]
  norm_num

/-- On a near coordinate, subtraction in the exponent is exact. -/
theorem intervalExponent_eq_pow_mul_shiftExponent {K k : ℕ}
    (hk : k ≤ K) :
    intervalExponent K = 100 ^ k * 100 ^ (100 * K - k) := by
  unfold intervalExponent
  rw [← pow_add]
  congr 1
  omega

/-- Exact logarithmic relation between a coordinate radius and the common
normalization radius. -/
theorem log_shiftRadius_div_log_globalRadius {K k : ℕ}
    (hk : k ≤ K) :
    Real.log (shiftRadius K k) / Real.log (globalRadius K) =
      1 / ((100 ^ k : ℕ) : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [shiftRadius, globalRadius, intervalStart]
  push_cast
  rw [Real.log_pow, Real.log_pow, intervalExponent_eq_pow_mul_shiftExponent hk]
  push_cast
  field_simp

/-- The inner radius has normalized logarithm `1 / (2 * 100^k)`. -/
theorem log_innerShiftRadius_div_log_globalRadius {K k : ℕ}
    (hK : 0 < K) (hk : k ≤ K) :
    Real.log (innerShiftRadius K k) / Real.log (globalRadius K) =
      1 / (2 * ((100 ^ k : ℕ) : ℝ)) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [innerShiftRadius, globalRadius, intervalStart]
  push_cast
  rw [Real.log_pow, Real.log_pow, intervalExponent_eq_pow_mul_shiftExponent hk,
    shiftExponent_eq_two_mul_innerExponent hK hk]
  push_cast
  field_simp

/-- Finite geometric-series identity in the subtraction-oriented form used by
the varying radii. -/
theorem geometric_reverse_sum_mul (A K : ℕ) (hK : K ≤ A) :
    99 * ∑ k ∈ Finset.Icc 1 K, 100 ^ (A - k) =
      100 ^ A - 100 ^ (A - K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [mul_add, ih (by omega)]
      have hp : 100 ^ (A - K) = 100 * 100 ^ (A - (K + 1)) := by
        rw [show A - K = (A - (K + 1)) + 1 by omega, pow_succ']
      have hpowle : 100 ^ (A - K) ≤ 100 ^ A :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hp]
      omega

/-- Sum of the binary exponents of all coordinate radii. -/
def radiusExponentBudget (K : ℕ) : ℕ :=
  ∑ k ∈ nearShifts K, 100 ^ (100 * K - k)

/-- Product of all coordinate radii. -/
def radiusProduct (K : ℕ) : ℕ :=
  ∏ k ∈ nearShifts K, shiftRadius K k

theorem radiusExponentBudget_mul (K : ℕ) :
    99 * radiusExponentBudget K =
      intervalExponent K - 100 ^ (99 * K) := by
  simpa [radiusExponentBudget, nearShifts, intervalExponent,
    show 100 * K - K = 99 * K by omega] using
      geometric_reverse_sum_mul (100 * K) K (by omega)

theorem radiusExponentBudget_mul_lt {K : ℕ} (hK : 0 < K) :
    99 * radiusExponentBudget K < intervalExponent K := by
  rw [radiusExponentBudget_mul]
  have hsmall : 0 < 100 ^ (99 * K) := pow_pos (by norm_num) _
  have hle : 100 ^ (99 * K) ≤ intervalExponent K := by
    unfold intervalExponent
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem radiusProduct_eq_pow (K : ℕ) :
    radiusProduct K = 2 ^ radiusExponentBudget K := by
  unfold radiusProduct shiftRadius radiusExponentBudget
  exact Finset.prod_pow_eq_pow_sum (nearShifts K)
    (fun k => 100 ^ (100 * K - k)) 2

/-- Even the 99th power of the full coordinate-radius product fits inside
the dyadic interval.  In particular all divisor-pair CRT moduli have a large
power saving. -/
theorem radiusProduct_pow_lt_intervalStart {K : ℕ} (hK : 0 < K) :
    radiusProduct K ^ 99 < intervalStart K := by
  rw [radiusProduct_eq_pow, ← pow_mul, intervalStart]
  apply Nat.pow_lt_pow_right (by norm_num)
  simpa [mul_comm] using radiusExponentBudget_mul_lt hK

theorem radiusProduct_lt_intervalStart {K : ℕ} (hK : 0 < K) :
    radiusProduct K < intervalStart K := by
  exact lt_of_le_of_lt
    (Nat.le_pow (by norm_num))
    (radiusProduct_pow_lt_intervalStart hK)

/-- The scale sequence is cofinal, in a form convenient for producing a
witness above an arbitrary bound. -/
theorem exists_intervalStart_gt (B : ℕ) :
    ∃ K : ℕ, 0 < K ∧ B < intervalStart K := by
  refine ⟨B + 1, by omega, ?_⟩
  unfold intervalStart intervalExponent
  calc
    B < 2 ^ B := B.lt_two_pow_self
    _ ≤ 2 ^ (B + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    _ ≤ 2 ^ (100 ^ (100 * (B + 1))) := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      calc
        B + 1 ≤ 2 ^ (B + 1) := (B + 1).lt_two_pow_self.le
        _ ≤ 100 ^ (B + 1) := Nat.pow_le_pow_left (by norm_num) _
        _ ≤ 100 ^ (100 * (B + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)

end Erdos248
