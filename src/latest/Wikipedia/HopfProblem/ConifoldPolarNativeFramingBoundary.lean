import Wikipedia.HopfProblem.ConifoldPolarNativeFramingComplement
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingMatrix

/-!
# Exact agreement with the chosen native half-radius boundary

The original normalized frontier map retains its original sphere frame and
normal unit vector.  The explicit orthogonal change and positive radial
scale turn its polar coordinates into the literal boundary coordinates of
the chosen normal-radius-one-half standard sphere neighborhood.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

theorem standard_unit_normal_radius (p : StandardBoundary) :
    radiusSq (RealFour.coordinateEquiv.symm (p.2 : RealFour.Space)) = 1 := by
  rw [RealFour.coordinateEquiv_symm_radiusSq,
    StandardSixSphereCircleModel.normalSphere_norm, one_pow]

/-- The three polar coordinates retain the original base with its precise coordinate convention. -/
theorem forward_smoothingPoint_fst (p : StandardBoundary) :
    (ConifoldPolar.forward (smoothingPoint p)).1 = (3 / 4 : ℝ) •
      lineDirection (RealSphere.sphereDiffeomorph.symm p.1) := by
  rw [ConifoldPolar.forward_fst, smoothingPoint_val]
  exact baseCoordinates_positivePart_normalizedMatrix _ (standard_unit_normal_radius p)

/-- The normal three-sphere coordinate is exactly unchanged, not merely isometric to it. -/
theorem forward_smoothingPoint_snd (p : StandardBoundary) :
    (ConifoldPolar.forward (smoothingPoint p)).2 = p.2 := by
  apply Subtype.ext
  rw [ConifoldPolar.forward_snd_val, smoothingPoint_val,
    normalCoordinates_unitaryPart_normalizedMatrix _ (standard_unit_normal_radius p)]
  exact RealFour.coordinateEquiv.apply_symm_apply _

theorem correctedBaseEquiv_forward_smoothingPoint (p : StandardBoundary) :
    correctedBaseEquiv (ConifoldPolar.forward (smoothingPoint p)).1 =
      Real.sqrt 3 • p.1.val := by
  change rescalingFactor • orthogonalEquiv (ConifoldPolar.forward (smoothingPoint p)).1 = _
  rw [forward_smoothingPoint_fst, orthogonalEquiv.map_smul,
    orthogonalEquiv_lineDirection, RealSphere.sphereDiffeomorph.apply_symm_apply,
    smul_smul, rescalingFactor_mul_three_quarters]

/-- The literal product marking required by the original standard half-radius boundary. -/
theorem correctedProduct_smoothingPoint (p : StandardBoundary) :
    correctedProductHomeomorph (ConifoldPolar.forward (smoothingPoint p)) =
      (Real.sqrt 3 • p.1.val, p.2) := by
  apply Prod.ext
  · exact correctedBaseEquiv_forward_smoothingPoint p
  · exact forward_smoothingPoint_snd p

/-- The canonical smoothing boundary agrees pointwise with the chosen
original standard boundary map. -/
theorem correctedComplement_smoothingPoint (p : StandardBoundary) :
    correctedComplementHomeomorph (smoothingPoint p) =
      StandardSixSphereCircleModel.boundaryPoint (1 / 2) (by norm_num) (by norm_num) p := by
  apply StandardSixSphereCircleModel.homeomorph.injective
  change StandardSixSphereCircleModel.forward (correctedComplementHomeomorph (smoothingPoint p)) =
    StandardSixSphereCircleModel.forward
      (StandardSixSphereCircleModel.boundaryPoint (1 / 2) _ _ p)
  rw [forward_correctedComplementHomeomorph, half_forward_boundaryPoint]
  exact correctedProduct_smoothingPoint p

/-- The same equality in the literal ambient Euclidean seven-space. -/
theorem correctedComplement_smoothingPoint_ambient (p : StandardBoundary) :
    (correctedComplementHomeomorph (smoothingPoint p)).val.val =
      StandardSixSphereCircleModel.boundaryAmbient (1 / 2) p :=
  congrArg (fun q : StandardSixSphereCircleModel.Complement => q.val.val)
    (correctedComplement_smoothingPoint p)

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
