import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Arithmetic identities for Erdős 633

These are unconditional algebraic lemmas used in the count calculations.
They do not assert the geometric classification or rational-point exhaustion.
-/

namespace Erdos633b

theorem isSquare_mul_sq_iff (u q : ℚ) (hq : q ≠ 0) :
    IsSquare (u * q ^ 2) ↔ IsSquare u := by
  constructor
  · intro h
    simpa [pow_ne_zero 2 hq] using h.div (IsSquare.sq q)
  · intro h
    exact h.mul (IsSquare.sq q)

theorem isSquare_sq_mul_iff (q u : ℚ) (hq : q ≠ 0) :
    IsSquare (q ^ 2 * u) ↔ IsSquare u := by
  rw [mul_comm, isSquare_mul_sq_iff u q hq]

theorem isSquare_div_sq_iff (u q : ℚ) (hq : q ≠ 0) :
    IsSquare (u / q ^ 2) ↔ IsSquare u := by
  rw [div_eq_mul_inv, ← inv_pow, isSquare_mul_sq_iff u q⁻¹ (inv_ne_zero hq)]

/-- The case-(7) count is independent of the choice of rational representation. -/
theorem triquadratic_representation_identity (m k M K : ℚ)
    (hk : k ≠ 0) (hK : K ≠ 0) (h : m / k = M / K) :
    2 * k ^ 2 - m ^ 2 = (k / K) ^ 2 * (2 * K ^ 2 - M ^ 2) := by
  have hcross : m * K = M * k := (div_eq_div_iff hk hK).mp h
  field_simp
  nlinarith [sq_nonneg (m * K - M * k), congrArg (fun z : ℚ => z ^ 2) hcross]

theorem triquadratic_representation_isSquare (m k M K : ℚ)
    (hk : k ≠ 0) (hK : K ≠ 0) (h : m / k = M / K) :
    IsSquare (2 * k ^ 2 - m ^ 2) ↔ IsSquare (2 * K ^ 2 - M ^ 2) := by
  rw [triquadratic_representation_identity m k M K hk hK h,
    isSquare_sq_mul_iff (k / K) _ (div_ne_zero hk hK)]

theorem triquadratic_integer_representation_isSquare (m k M K : ℤ)
    (hk : k ≠ 0) (hK : K ≠ 0)
    (h : (m : ℚ) / k = (M : ℚ) / K) :
    IsSquare (2 * k ^ 2 - m ^ 2) ↔ IsSquare (2 * K ^ 2 - M ^ 2) := by
  rw [← Rat.isSquare_intCast_iff, ← Rat.isSquare_intCast_iff]
  push_cast
  exact triquadratic_representation_isSquare m k M K
    (by exact_mod_cast hk) (by exact_mod_cast hK) h

/-- Algebraic count of the triquadratic construction; geometry is a separate obligation. -/
theorem triquadratic_block_count (a b c J : ℚ)
    (hb : b = c - J) (hJ : J * c = a ^ 2) :
    2 * b ^ 2 + a ^ 2 + 2 * b * J = 2 * c ^ 2 - a ^ 2 := by
  rw [hb]
  linear_combination -2 * hJ

theorem groupOne_block_count (s l : ℚ) (hs : s ≠ 0) :
    3 * l ^ 2 + (l * (1 - s ^ 2)) ^ 2 + (l * s) ^ 2 +
        2 * (l * (1 - s ^ 2) / s - l * s) * (l * s) =
      l ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) := by
  field_simp
  ring

def quarticX (t s a : ℚ) : ℚ := 2 * t ^ 2 - 2 * s + a

def quarticY (t s a : ℚ) : ℚ := 2 * t * quarticX t s a

/-- The quartic-to-cubic map is a polynomial identity, with no rank assumption. -/
theorem quartic_to_cubic (t s a b : ℚ) (h : s ^ 2 = t ^ 4 + a * t ^ 2 + b) :
    (quarticY t s a) ^ 2 = (quarticX t s a) ^ 3 -
      2 * a * (quarticX t s a) ^ 2 + (a ^ 2 - 4 * b) * quarticX t s a := by
  dsimp [quarticX, quarticY]
  linear_combination -4 * (2 * t ^ 2 - 2 * s + a) * h

theorem quarticX_ne_zero (t s a b : ℚ)
    (h : s ^ 2 = t ^ 4 + a * t ^ 2 + b) (hab : a ^ 2 ≠ 4 * b) :
    quarticX t s a ≠ 0 := by
  intro hx
  apply hab
  dsimp [quarticX] at hx
  linear_combination 4 * h + (2 * s + 2 * t ^ 2 + a) * hx

theorem quartic_inverse_t (t s a : ℚ) (hx : quarticX t s a ≠ 0) :
    quarticY t s a / (2 * quarticX t s a) = t := by
  dsimp only [quarticY]
  field_simp

theorem quartic_inverse_s (t s a : ℚ) (hx : quarticX t s a ≠ 0) :
    (quarticY t s a / (2 * quarticX t s a)) ^ 2 -
      (quarticX t s a - a) / 2 = s := by
  rw [quartic_inverse_t t s a hx]
  dsimp [quarticX]
  ring

theorem caseSix_to_cubic (t s : ℚ) (h : s ^ 2 = (t ^ 2 - 2) * (t ^ 2 - 3)) :
    (quarticY t s (-5)) ^ 2 = (quarticX t s (-5)) ^ 3 +
      10 * (quarticX t s (-5)) ^ 2 + quarticX t s (-5) := by
  have hq : s ^ 2 = t ^ 4 + (-5) * t ^ 2 + 6 := by nlinarith [h]
  convert quartic_to_cubic t s (-5) 6 hq using 1
  ring

theorem caseSix_cubic_x_ne_zero (t s : ℚ)
    (h : s ^ 2 = (t ^ 2 - 2) * (t ^ 2 - 3)) : quarticX t s (-5) ≠ 0 := by
  exact quarticX_ne_zero t s (-5) 6 (by nlinarith [h]) (by norm_num)

def caseFiveFactor (t : ℚ) : ℚ :=
  (2 / 3) * (3 * t ^ 2 - 1) / ((3 * t + 1) * (t - 1))

def caseFiveX (t : ℚ) : ℚ := (9 * t + 3) / (t - 1)

def caseEightFactor (t : ℚ) : ℚ :=
  (3 * t ^ 2 - 6 * t - 1) / ((t - 1) * (3 * t + 1))

def caseEightX (t : ℚ) : ℚ := (1 + 3 * t) / (1 - t)

theorem caseFive_factor_identity (t : ℚ) (h1 : t ≠ 1) (h3 : 3 * t + 1 ≠ 0) :
    caseFiveFactor t = ((caseFiveX t) ^ 2 + 18 * caseFiveX t - 27) /
      (36 * caseFiveX t) := by
  have hd : 9 * t + 3 ≠ 0 := by intro h; apply h3; linarith
  have hx : caseFiveX t ≠ 0 := div_ne_zero hd (sub_ne_zero.mpr h1)
  apply (eq_div_iff (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) hx)).mpr
  dsimp [caseFiveFactor, caseFiveX]
  field_simp [sub_ne_zero.mpr h1, h3]
  ring

theorem caseFive_x_lt (t : ℚ) (ht : 0 < t) (ht1 : t < 1) :
    caseFiveX t < -3 := by
  dsimp [caseFiveX]
  apply (div_lt_iff_of_neg (by linarith : t - 1 < 0)).mpr
  linarith

theorem caseEight_factor_identity (t : ℚ) (h1 : t ≠ 1) (h3 : 3 * t + 1 ≠ 0) :
    caseEightFactor t = ((caseEightX t) ^ 2 + 6 * caseEightX t - 3) /
      (4 * caseEightX t) := by
  have hd : 1 + 3 * t ≠ 0 := by simpa [add_comm] using h3
  dsimp [caseEightFactor, caseEightX]
  field_simp [sub_ne_zero.mpr h1, sub_ne_zero.mpr h1.symm, h3, hd]
  ring

theorem caseEight_x_bounds (t : ℚ) (ht : 0 < t) (ht3 : t < 1 / 3) :
    1 < caseEightX t ∧ caseEightX t < 3 := by
  have hd : 0 < 1 - t := by linarith
  constructor
  · exact (lt_div_iff₀ hd).mpr (by linarith)
  · exact (div_lt_iff₀ hd).mpr (by linarith)

theorem caseFive_square_gives_cubic (t z : ℚ) (ht : 0 < t) (ht3 : t < 1 / 3)
    (hz : caseFiveFactor t = z ^ 2) :
    ∃ x y : ℚ, x < -3 ∧ y ^ 2 = x ^ 3 + 18 * x ^ 2 - 27 * x := by
  have hxlt := caseFive_x_lt t ht (by linarith)
  have hx : caseFiveX t ≠ 0 := by linarith
  have he := caseFive_factor_identity t (by linarith) (by linarith)
  rw [hz] at he
  have he' := (eq_div_iff (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) hx)).mp he
  refine ⟨caseFiveX t, 6 * caseFiveX t * z, hxlt, ?_⟩
  linear_combination caseFiveX t * he'

theorem caseEight_square_gives_cubic (t z : ℚ) (ht : 0 < t) (ht3 : t < 1 / 3)
    (hz : caseEightFactor t = z ^ 2) :
    ∃ x y : ℚ, 1 < x ∧ x < 3 ∧ y ^ 2 = x ^ 3 + 6 * x ^ 2 - 3 * x := by
  have hxb := caseEight_x_bounds t ht ht3
  have hx : caseEightX t ≠ 0 := by linarith [hxb.1]
  have he := caseEight_factor_identity t (by linarith) (by linarith)
  rw [hz] at he
  have he' := (eq_div_iff (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hx)).mp he
  refine ⟨caseEightX t, 2 * caseEightX t * z, hxb.1, hxb.2, ?_⟩
  linear_combination caseEightX t * he'

/-- Exact counterexample to the unrestricted version of the source's case-(8) lemma. -/
theorem caseEight_factor_zero : caseEightFactor 0 = 1 := by
  norm_num [caseEightFactor]

/-- A valid group-1 parameter where the published row count needs a different construction. -/
theorem groupOne_negative_rows :
    (7 : ℚ) = 16 - 12 ^ 2 / 16 ∧
      (48 * 7 / 12 - 48 * 12 / 16 : ℚ) = -8 := by
  norm_num

end Erdos633b
