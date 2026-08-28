import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cross-ratios of three points on the unit circle

The cross-ratio sending `a`, `b`, and `c` to `0`, `1`, and infinity has a
constant nonzero sign on the unit disc.  This file proves the exact
imaginary-part identity, independently of the construction of the associated
automorphism of the Riemann sphere.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannSphere.MobiusCircle

/-- The affine formula for the cross-ratio normalized at `a`, `b`, and `c`.
At its pole it has the field's totalized value; the sphere construction
handles the pole separately. -/
def crossRatio (a b c z : ℂ) : ℂ :=
  ((z - a) * (b - c)) / ((z - c) * (b - a))

/-- The constant coefficient of the normalized cross-ratio. -/
def coefficient (a b c : ℂ) : ℂ := (b - c) / (b - a)

/-- The sign of this nonzero real constant selects the image half-plane. -/
def orientation (a b c : ℂ) : ℝ := -(coefficient a b c).im

theorem crossRatio_eq_coefficient (a b c z : ℂ) :
    crossRatio a b c z = coefficient a b c * ((z - a) / (z - c)) := by
  simp only [crossRatio, coefficient, div_eq_mul_inv, mul_inv_rev]
  ring

theorem coefficient_ne_zero {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    coefficient a b c ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hba)

theorem unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

/-- Conjugating the coefficient interchanges the two factors corresponding
to the zero and the pole. -/
theorem coefficient_mul_eq_conj_mul {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) :
    coefficient a b c * a = conj (coefficient a b c) * c := by
  have ha0 := unit_ne_zero ha
  have hb0 := unit_ne_zero hb
  have hc0 := unit_ne_zero hc
  have hba0 := sub_ne_zero.mpr hba
  simp only [coefficient, map_div₀, map_sub, ← inv_eq_conj ha,
    ← inv_eq_conj hb, ← inv_eq_conj hc]
  field_simp
  ring

/-- The constant selecting a half-plane is nonzero for a genuine triple. -/
theorem orientation_ne_zero {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    orientation a b c ≠ 0 := by
  intro h
  have him : (coefficient a b c).im = 0 := neg_eq_zero.mp h
  have hd := coefficient_mul_eq_conj_mul ha hb hc hba
  rw [conj_eq_iff_im.mpr him] at hd
  exact hac (mul_left_cancel₀ (coefficient_ne_zero hba hbc) hd)

/-- The mixed terms in the imaginary part cancel because they are conjugates. -/
theorem numerator_im {a c d : ℂ} (hc : ‖c‖ = 1)
    (hd : d * a = conj d * c) (z : ℂ) :
    (d * (z - a) * conj (z - c)).im = d.im * (normSq z - 1) := by
  have hcross : conj (d * z * conj c) = conj d * c * conj z := by
    simp only [map_mul, starRingEnd_self_apply]
    ring
  have hconst : conj d * c * conj c = conj d := by
    rw [mul_assoc, mul_conj, normSq_eq_norm_sq, hc]
    simp
  have heq : d * (z - a) * conj (z - c) =
      d * (normSq z : ℂ) - (d * z * conj c + conj (d * z * conj c)) + conj d := by
    calc
      d * (z - a) * conj (z - c) =
          d * (z * conj z) - (d * z * conj c + d * a * conj z) + d * a * conj c := by
        rw [map_sub]
        ring
      _ = _ := by rw [mul_conj, hd, hconst, hcross]
  rw [heq]
  simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, conj_im]
  ring

/-- The exact imaginary-part formula. It even includes the totalized value
at the pole, where both sides are zero. -/
theorem crossRatio_im {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    (crossRatio a b c z).im =
      orientation a b c * (1 - ‖z‖ ^ 2) / normSq (z - c) := by
  have heq : crossRatio a b c z =
      (coefficient a b c * (z - a) * conj (z - c)) / (normSq (z - c) : ℂ) := by
    rw [crossRatio_eq_coefficient, div_eq_mul_inv, inv_def]
    simp only [div_eq_mul_inv, ofReal_inv]
    ring
  rw [heq, div_ofReal_im,
    numerator_im hc (coefficient_mul_eq_conj_mul ha hb hc hba), normSq_eq_norm_sq]
  unfold orientation
  ring

/-- The unit circle is mapped to the real axis away from the pole.
The affine formula is real at its totalized pole as well. -/
theorem crossRatio_im_eq_zero_of_norm_eq_one {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a)
    (hz : ‖z‖ = 1) : (crossRatio a b c z).im = 0 := by
  rw [crossRatio_im ha hb hc hba, hz]
  simp

/-- Away from the pole, the real-axis preimage is precisely the unit circle. -/
theorem crossRatio_im_eq_zero_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    (crossRatio a b c z).im = 0 ↔ ‖z‖ = 1 := by
  have hK := orientation_ne_zero ha hb hc hba hbc hac
  have hd : normSq (z - c) ≠ 0 :=
    ne_of_gt (normSq_pos.mpr (sub_ne_zero.mpr hzc))
  rw [crossRatio_im ha hb hc hba]
  simp only [div_eq_zero_iff, mul_eq_zero, hK, hd, or_false, false_or, sub_eq_zero]
  constructor
  · intro hz
    nlinarith [norm_nonneg z]
  · intro hz
    rw [hz, one_pow]

theorem orientation_mul_crossRatio_im {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hba : b ≠ a) (z : ℂ) :
    orientation a b c * (crossRatio a b c z).im =
      orientation a b c ^ 2 * (1 - ‖z‖ ^ 2) / normSq (z - c) := by
  rw [crossRatio_im ha hb hc hba]
  ring

/-- Exact membership in the oriented image half-plane characterizes the
unit disc; the excluded pole is one of the prescribed boundary points. -/
theorem orientation_mul_crossRatio_im_pos_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    0 < orientation a b c * (crossRatio a b c z).im ↔ ‖z‖ < 1 := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < normSq (z - c) := normSq_pos.mpr (sub_ne_zero.mpr hzc)
  rw [orientation_mul_crossRatio_im ha hb hc hba,
    div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_left hK, sub_pos,
    sq_lt_one_iff₀ (norm_nonneg z)]

/-- The exterior is mapped into the opposite open half-plane. -/
theorem orientation_mul_crossRatio_im_neg_iff {a b c z : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    orientation a b c * (crossRatio a b c z).im < 0 ↔ 1 < ‖z‖ := by
  have hK := sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac)
  have hd : 0 < normSq (z - c) := normSq_pos.mpr (sub_ne_zero.mpr hzc)
  have heq : -(orientation a b c * (crossRatio a b c z).im) =
      orientation a b c ^ 2 * (‖z‖ ^ 2 - 1) / normSq (z - c) := by
    rw [orientation_mul_crossRatio_im ha hb hc hba]
    ring
  rw [← neg_pos, heq, div_pos_iff_of_pos_right hd,
    mul_pos_iff_of_pos_left hK, sub_pos, one_lt_sq_iff₀ (norm_nonneg z)]

/-- The value of the sphere cross-ratio at infinity is the coefficient;
it lies strictly in the exterior half-plane. -/
theorem orientation_mul_coefficient_im (a b c : ℂ) :
    orientation a b c * (coefficient a b c).im = -(orientation a b c ^ 2) := by
  unfold orientation
  ring

theorem orientation_mul_coefficient_im_neg {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    orientation a b c * (coefficient a b c).im < 0 := by
  rw [orientation_mul_coefficient_im]
  exact neg_neg_of_pos (sq_pos_of_ne_zero (orientation_ne_zero ha hb hc hba hbc hac))

theorem crossRatio_at_zero (a b c : ℂ) : crossRatio a b c a = 0 := by
  simp [crossRatio]

theorem crossRatio_at_one {a b c : ℂ} (hba : b ≠ a) (hbc : b ≠ c) :
    crossRatio a b c b = 1 := by
  unfold crossRatio
  rw [mul_comm (b - c) (b - a)]
  exact div_self (mul_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hbc))

end Wikipedia.HopfProblem.RiemannSphere.MobiusCircle
