import Wikipedia.NoExoticSixSphere.SkewWedge
import Wikipedia.NoExoticSixSphere.SkewRotationComplement

/-!
# Mixing two invariant rotation planes

Two actual skew wedge combinations form a commutator rotation plane whose
speed is the sum of the two original speeds. Their Hilbert--Schmidt pairings
are computed on the actual codimension-two complement.
-/

namespace NoExoticSixSphere.SkewPlaneMixing

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator
  SkewWedge SkewRotationComplement

variable {n : ℕ}

noncomputable def mixing (x y v w : Vector n) : SkewOperators n := skew x v - skew y w

noncomputable def companion (x y v w : Vector n) : SkewOperators n := skew x w + skew y v

theorem commutator_mixing (K : SkewOperators n) {α β : ℝ} {x y v w : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
    (hv : (K : Vector n →L[ℝ] Vector n) v = β • w)
    (hw : (K : Vector n →L[ℝ] Vector n) w = (-β) • v) :
    commutator (K : Vector n →L[ℝ] Vector n) (mixing x y v w : Vector n →L[ℝ] Vector n) =
      (α + β) • (companion x y v w : Vector n →L[ℝ] Vector n) := by
  change commutator (K : Vector n →L[ℝ] Vector n) (operator x v - operator y w) =
    (α + β) • (operator x w + operator y v)
  rw [commutator_sub_right, commutator_operator, commutator_operator, hx, hy, hv, hw,
    operator_smul_left, operator_smul_left, operator_smul_right, operator_smul_right]
  module

theorem commutator_companion (K : SkewOperators n) {α β : ℝ} {x y v w : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
    (hv : (K : Vector n →L[ℝ] Vector n) v = β • w)
    (hw : (K : Vector n →L[ℝ] Vector n) w = (-β) • v) :
    commutator (K : Vector n →L[ℝ] Vector n) (companion x y v w : Vector n →L[ℝ] Vector n) =
      (-(α + β)) • (mixing x y v w : Vector n →L[ℝ] Vector n) := by
  change commutator (K : Vector n →L[ℝ] Vector n) (operator x w + operator y v) =
    (-(α + β)) • (operator x v - operator y w)
  rw [commutator_add_right, commutator_operator, commutator_operator, hx, hy, hv, hw,
    operator_smul_left, operator_smul_left, operator_smul_right, operator_smul_right]
  module

theorem innerForm_mixing {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (v w v' w' : complement x y) :
    innerForm (mixing x y v w : Vector n →L[ℝ] Vector n)
      (mixing x y v' w' : Vector n →L[ℝ] Vector n) =
        2 * (inner ℝ (v : Vector n) v' + inner ℝ (w : Vector n) w') := by
  obtain ⟨hxv, hyv⟩ := (mem_complement x y v').mp v'.2
  obtain ⟨hxw, hyw⟩ := (mem_complement x y w').mp w'.2
  have hyx : inner ℝ y x = 0 := by rw [real_inner_comm x y]; exact hxy
  change innerForm (operator x v - operator y w) (operator x v' - operator y w') = _
  simp only [innerForm_sub_left, innerForm_sub_right, innerForm_operator,
    real_inner_self_eq_norm_sq, hx, hy, one_pow, hxy, hyx, hxv, hyv, hxw, hyw,
    zero_mul, one_mul, sub_zero]
  ring

theorem innerForm_companion {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (v w v' w' : complement x y) :
    innerForm (companion x y v w : Vector n →L[ℝ] Vector n)
      (companion x y v' w' : Vector n →L[ℝ] Vector n) =
        2 * (inner ℝ (v : Vector n) v' + inner ℝ (w : Vector n) w') := by
  obtain ⟨hxv, hyv⟩ := (mem_complement x y v').mp v'.2
  obtain ⟨hxw, hyw⟩ := (mem_complement x y w').mp w'.2
  have hyx : inner ℝ y x = 0 := by rw [real_inner_comm x y]; exact hxy
  change innerForm (operator x w + operator y v) (operator x w' + operator y v') = _
  simp only [innerForm_add_left, innerForm_add_right, innerForm_operator,
    real_inner_self_eq_norm_sq, hx, hy, one_pow, hxy, hyx, hxv, hyv, hxw, hyw,
    zero_mul, one_mul, sub_zero]
  ring

end NoExoticSixSphere.SkewPlaneMixing
