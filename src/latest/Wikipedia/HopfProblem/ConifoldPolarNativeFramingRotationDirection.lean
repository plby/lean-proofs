import Wikipedia.HopfProblem.ConifoldPolarNativeFramingDefs

/-!
# The fixed rotation of the original image-line direction

The line direction in the ordered Hermitian coordinates is carried to the
already chosen native real-sphere parametrization.  The finite-chart proof
uses the real linearity of the actual equatorial isometry, without choosing
new axes in its orthogonal hyperplane.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

@[simp] theorem lineDirection_coe (a : ℂ) :
    lineDirection (a : RiemannSphere) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![(1 - Complex.normSq a) / (Complex.normSq a + 1),
          2 * a.re / (Complex.normSq a + 1),
          -(2 * a.im) / (Complex.normSq a + 1)] := rfl

@[simp] theorem lineDirection_infinity :
    lineDirection (OnePoint.infty : RiemannSphere) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-1, 0, 0] := rfl

/-- The explicit coordinate correction sends every original line direction to its native point. -/
theorem orthogonalMap_lineDirection (p : RiemannSphere) :
    orthogonalMap (lineDirection p) = (RealSphere.sphereDiffeomorph p : Base) := by
  induction p using OnePoint.rec with
  | infty =>
      simp [orthogonalMap, lineDirection, RealSphere.north, Complex.ext_iff]
  | coe a =>
      rw [RealSphere.sphereDiffeomorph_coe, RealSphere.left_coe]
      change -((1 - Complex.normSq a) / (Complex.normSq a + 1)) •
          RealSphere.northVector +
        (RealSphere.equatorEquiv
          (⟨2 * a.re / (Complex.normSq a + 1),
            -(-(2 * a.im) / (Complex.normSq a + 1))⟩ : ℂ) : Base) = _
      have he :
          (⟨2 * a.re / (Complex.normSq a + 1),
            -(-(2 * a.im) / (Complex.normSq a + 1))⟩ : ℂ) =
            (2 / (Complex.normSq a + 1) : ℝ) • a := by
        apply Complex.ext <;>
          simp only [Complex.smul_re, Complex.smul_im] <;> ring
      have hn : -((1 - Complex.normSq a) / (Complex.normSq a + 1)) =
          (Complex.normSq a - 1) / (Complex.normSq a + 1) := by ring
      rw [he, RealSphere.equatorEquiv.map_smul, Submodule.coe_smul, hn]
      exact add_comm _ _

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
