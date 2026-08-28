import Wikipedia.NoExoticSixSphere.OrthogonalIndexTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A fixed-endpoint test field for the orthogonal index form

Multiplying the rotating field by `sin(π t)` gives a smooth skew-adjoint field
vanishing at zero and one. Its derivative cancels the commutator term in the
completed square, leaving an explicit scalar trigonometric expression.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalIndexTestField

open GLOrthonormalization CayleyTransform OrthogonalIndexTransport
  OrthogonalIndexForm OrthogonalCommutator HilbertSchmidt

variable {n : ℕ}

noncomputable def field (K A : SkewOperators n) (t : ℝ) : SkewOperators n :=
  Real.sin (Real.pi * t) • transport K A t

theorem field_zero (K A : SkewOperators n) : field K A 0 = 0 := by
  simp only [field, mul_zero, Real.sin_zero, zero_smul]

theorem field_one (K A : SkewOperators n) : field K A 1 = 0 := by
  simp only [field, mul_one, Real.sin_pi, zero_smul]

theorem contDiff_field (K A : SkewOperators n) : ContDiff ℝ ∞ (field K A) :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).smul (contDiff_transport K A)

noncomputable def fieldDerivative (K A : SkewOperators n) (t : ℝ) :
    Vector n →L[ℝ] Vector n :=
  (Real.cos (Real.pi * t) * Real.pi) • (transport K A t : Vector n →L[ℝ] Vector n) +
    Real.sin (Real.pi * t) • ((-1 / 2 : ℝ) •
      commutator (K : Vector n →L[ℝ] Vector n) (transport K A t : Vector n →L[ℝ] Vector n))

theorem hasDerivAt_field (K A : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun r ↦ (field K A r : Vector n →L[ℝ] Vector n)) (fieldDerivative K A t) t := by
  have hl : HasDerivAt (fun r : ℝ ↦ Real.pi * r) Real.pi t := by
    simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul Real.pi
  have hs : HasDerivAt (fun r : ℝ ↦ Real.sin (Real.pi * r))
      (Real.cos (Real.pi * t) * Real.pi) t :=
    (Real.hasDerivAt_sin (Real.pi * t)).comp t hl
  have hc := hasDerivAt_transport (n := n) K A t
  convert! hs.fun_smul hc using 1
  exact add_comm _ _

theorem deriv_field_coe (K A : SkewOperators n) (t : ℝ) :
    ((deriv (field K A) t : SkewOperators n) : Vector n →L[ℝ] Vector n) =
      fieldDerivative K A t := by
  let L : SkewOperators n →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL
  have hd := L.hasFDerivAt.comp_hasDerivAt t
    ((((contDiff_field K A).differentiable (by simp)) t).hasDerivAt)
  exact hd.unique (hasDerivAt_field K A t)

theorem commutator_field (K A : SkewOperators n) (t : ℝ) :
    commutator (K : Vector n →L[ℝ] Vector n) (field K A t : Vector n →L[ℝ] Vector n) =
      Real.sin (Real.pi * t) • commutator (K : Vector n →L[ℝ] Vector n)
        (transport K A t : Vector n →L[ℝ] Vector n) := commutator_smul_right _ _ _

theorem derivative_add_half_commutator (K A : SkewOperators n) (t : ℝ) :
    fieldDerivative K A t + (1 / 2 : ℝ) •
      commutator (K : Vector n →L[ℝ] Vector n) (field K A t : Vector n →L[ℝ] Vector n) =
        (Real.cos (Real.pi * t) * Real.pi) •
          (transport K A t : Vector n →L[ℝ] Vector n) := by
  rw [commutator_field]
  unfold fieldDerivative
  simp only [smul_smul]
  rw [add_assoc, ← add_smul]
  have hc : Real.sin (Real.pi * t) * (-1 / 2) + (1 / 2) * Real.sin (Real.pi * t) = 0 := by ring
  rw [hc, zero_smul, add_zero]

theorem density_field (K A : SkewOperators n) (t : ℝ) :
    density K (field K A t : Vector n →L[ℝ] Vector n)
      ((deriv (field K A) t : SkewOperators n) : Vector n →L[ℝ] Vector n) =
        Real.pi ^ 2 * Real.cos (Real.pi * t) ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n) -
          (1 / 4 : ℝ) * Real.sin (Real.pi * t) ^ 2 *
            squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
              (A : Vector n →L[ℝ] Vector n)) := by
  rw [deriv_field_coe, density_completedSquare, derivative_add_half_commutator,
    squareNorm_smul, squareNorm_transport, commutator_field, squareNorm_smul,
    squareNorm_commutator_transport]
  ring

end NoExoticSixSphere.OrthogonalIndexTestField
