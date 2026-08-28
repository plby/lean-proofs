import Wikipedia.HopfProblem.ConifoldPolar
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundary

/-!
# Fixed coordinates for the native boundary-framing comparison

These definitions retain the original normal boundary, original conifold
matrix map, and original real-sphere stereographic parametrization.  The
coordinate correction is an explicit linear map, not an identification of
two sphere parametrizations by their names or dimensions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary CuspCircleNormalTrivialization

abbrev StandardBoundary := StandardNormalBoundary

/-- The original image-line direction in the ordered three Hermitian coordinates. -/
def lineDirection (p : RiemannSphere) : Base :=
  p.elim ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![-1, 0, 0])
    (fun a => (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![(1 - Complex.normSq a) / (Complex.normSq a + 1),
        2 * a.re / (Complex.normSq a + 1),
        -(2 * a.im) / (Complex.normSq a + 1)])

/-- The literal coordinate correction to the already chosen native real-sphere frame. -/
def orthogonalMap (x : Base) : Base :=
  -(x 0) • RealSphere.northVector +
    (RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base)

/-- The actual normalized smoothing matrix in the unchanged product normal coordinates. -/
def normalizedMatrix (p : RiemannSphere × Fibre) : MatrixSpace :=
  ConifoldStandardBoundary.forward 2 ((2 : ℂ) • Conifold.productMap p)

/-- The existing native frontier comparison, regarded as an element of the original matrix group. -/
def smoothingPoint (p : StandardBoundary) : SpecialLinear :=
  ⟨(standardBoundaryNormalizedHomeomorph p).val,
    (standardBoundaryNormalizedHomeomorph p).property.1⟩

@[simp] theorem smoothingPoint_val (p : StandardBoundary) :
    (smoothingPoint p).val = normalizedMatrix
      (RealSphere.sphereDiffeomorph.symm p.1,
        RealFour.coordinateEquiv.symm (p.2 : RealFour.Space)) :=
  standardBoundaryNormalizedHomeomorph_apply_val p

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
