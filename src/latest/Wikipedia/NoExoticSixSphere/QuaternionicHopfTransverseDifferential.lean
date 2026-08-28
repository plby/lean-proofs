import Wikipedia.NoExoticSixSphere.QuaternionicHopfNorthFiber
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The exact transverse differential of the quaternionic Hopf polynomial

Along its north fiber, variation in the second quaternion coordinate
has zero first output coordinate and quaternion output 2 a conjugate(w).
This is the differential of the actual polynomial, not an assigned
normal-framing or degree formula.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def secondAxis : ℍ →L[ℝ] V 8 :=
  planeCoordinates.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ ℍ ℍ))

theorem first_secondAxis (w : ℍ) : first (secondAxis w) = 0 := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2 ((0 : ℍ), w)))).fst = 0
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_secondAxis (w : ℍ) : second (secondAxis w) = w := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2 ((0 : ℍ), w)))).snd = w
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem polynomial_fderiv_second (x : V 8) (hx : second x = 0) (w : ℍ) :
    fderiv ℝ polynomial x (secondAxis w) =
      SphereCylinder.join 3 (0,
        Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (first x * star w))) := by
  have h₁ := (hasStrictFDerivAt_norm_sq (first x)).hasFDerivAt.comp x first.hasFDerivAt
  have h₂ := (hasStrictFDerivAt_norm_sq (second x)).hasFDerivAt.comp x second.hasFDerivAt
  have hmul := first.hasFDerivAt.mul' (conjugation.hasFDerivAt.comp x second.hasFDerivAt)
  have htail := Quaternion.linearIsometryEquivTuple.hasFDerivAt.comp x
    ((hasFDerivAt_const (2 : ℝ) x).smul hmul)
  have h := (SphereCylinder.join 3).hasFDerivAt.comp x ((h₁.sub h₂).prodMk htail)
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply,
    norm_sq_eq_normSq] at h
  change HasFDerivAt (𝕜 := ℝ) polynomial _ x at h
  rw [h.fderiv]
  simp [first_secondAxis, second_secondAxis, hx, conjugation]

theorem inner_secondAxis (x : V 8) (hx : second x = 0) (w : ℍ) :
    inner ℝ x (secondAxis w) = 0 := by
  have he : x = planeCoordinates (WithLp.toLp 2 (first x, (0 : ℍ))) := by
    rw [← hx]
    exact (planeCoordinates.apply_symm_apply x).symm
  rw [he]
  change inner ℝ (planeCoordinates (WithLp.toLp 2 (first x, (0 : ℍ))))
    (planeCoordinates (WithLp.toLp 2 ((0 : ℍ), w))) = 0
  rw [planeCoordinates.inner_map_map]
  simp

end NoExoticSixSphere.QuaternionicHopf
