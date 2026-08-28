import Wikipedia.HopfProblem.ConifoldPolarNativeFramingRotation
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingScale

/-!
# The corrected standard-complement coordinates

The fixed orthogonal correction changes the Hermitian coordinates to the
original real-sphere frame.  The separately proved positive scale sends
polar radius `3/4` to the complement radius `sqrt 3` of the chosen half-radius
standard tube.  Both corrections extend to the whole Euclidean three-space.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

/-- The explicit orthogonal change followed by the required positive radial scale. -/
def correctedBaseEquiv : Base ≃L[ℝ] Base :=
  orthogonalEquiv.toContinuousLinearEquiv.trans rescaleEquiv

@[simp] theorem correctedBaseEquiv_apply (b : Base) :
    correctedBaseEquiv b = rescalingFactor • orthogonalMap b := rfl

@[simp] theorem correctedBaseEquiv_symm_apply (b : Base) :
    correctedBaseEquiv.symm b = orthogonalEquiv.symm (rescalingFactor⁻¹ • b) := rfl

theorem correctedBaseEquiv_norm (b : Base) :
    ‖correctedBaseEquiv b‖ = rescalingFactor * ‖b‖ := by
  change ‖rescaleEquiv (orthogonalEquiv b)‖ = _
  rw [rescaleEquiv_norm, orthogonalEquiv.norm_map]

def correctedProductHomeomorph : (Base × NormalSphere) ≃ₜ (Base × NormalSphere) :=
  correctedBaseEquiv.toHomeomorph.prodCongr (Homeomorph.refl NormalSphere)

@[simp] theorem correctedProductHomeomorph_apply (q : Base × NormalSphere) :
    correctedProductHomeomorph q = (correctedBaseEquiv q.1, q.2) := rfl

@[simp] theorem correctedProductHomeomorph_symm_apply (q : Base × NormalSphere) :
    correctedProductHomeomorph.symm q = (correctedBaseEquiv.symm q.1, q.2) := rfl

/-- Both corrections are smooth in the unchanged Euclidean atlas. -/
def correctedBaseDiffeomorph : Base ≃ₘ⟮𝓘(ℝ, Base), 𝓘(ℝ, Base)⟯ Base where
  toEquiv := correctedBaseEquiv.toEquiv
  contMDiff_toFun := correctedBaseEquiv.contDiff.contMDiff
  contMDiff_invFun := correctedBaseEquiv.symm.contDiff.contMDiff

/-- The normal sphere keeps its original stereographic atlas and is not changed. -/
def correctedProductDiffeomorph :
    (Base × NormalSphere) ≃ₘ⟮ProductModel, ProductModel⟯ (Base × NormalSphere) :=
  correctedBaseDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 3) NormalSphere ∞)

@[simp] theorem correctedProductDiffeomorph_apply (q : Base × NormalSphere) :
    correctedProductDiffeomorph q = (correctedBaseEquiv q.1, q.2) := rfl

/-- This is a new, explicitly corrected map; the original unscaled polar map is unchanged. -/
def correctedComplementHomeomorph : SpecialLinear ≃ₜ StandardSixSphereCircleModel.Complement :=
  (ConifoldPolar.homeomorph.trans correctedProductHomeomorph).trans
    StandardSixSphereCircleModel.homeomorph.symm

@[simp] theorem correctedComplementHomeomorph_apply (M : SpecialLinear) :
    correctedComplementHomeomorph M = StandardSixSphereCircleModel.inverse
      (correctedBaseEquiv (ConifoldPolar.forward M).1, (ConifoldPolar.forward M).2) := rfl

@[simp] theorem correctedComplementHomeomorph_symm_apply
    (p : StandardSixSphereCircleModel.Complement) :
    correctedComplementHomeomorph.symm p = ConifoldPolar.inverse
      (correctedBaseEquiv.symm (StandardSixSphereCircleModel.forward p).1,
        (StandardSixSphereCircleModel.forward p).2) := rfl

theorem forward_correctedComplementHomeomorph (M : SpecialLinear) :
    StandardSixSphereCircleModel.forward (correctedComplementHomeomorph M) =
      (correctedBaseEquiv (ConifoldPolar.forward M).1, (ConifoldPolar.forward M).2) :=
  StandardSixSphereCircleModel.forward_inverse _

/-- Correcting only the fixed base coordinate preserves the literal native circle action. -/
theorem correctedComplementHomeomorph_circleAction (u : ℂˣ)
    (hu : ‖(u : ℂ)‖ = 1) (M : SpecialLinear) :
    correctedComplementHomeomorph (circleAction (u : ℂ) hu M) =
      StandardSixSphereCircleModel.Isometries.complementMap (RealFour.rotation u hu)
        (correctedComplementHomeomorph M) := by
  rw [correctedComplementHomeomorph_apply, forward_circleAction]
  exact (StandardSixSphereCircleModel.Isometries.inverse_equivariant
    (RealFour.rotation u hu)
    (correctedBaseEquiv (ConifoldPolar.forward M).1, (ConifoldPolar.forward M).2)).symm

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
