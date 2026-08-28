import Wikipedia.HopfProblem.ConifoldStandardBoundaryFrame
import Wikipedia.HopfProblem.StandardSixSphereCircleModelCoordinates
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Explicit coordinates for the standard two-by-two polar decomposition

The source is the existing determinant-one matrix group with its original
subspace topology.  The target coordinates are the existing Euclidean spaces
used for the standard six-sphere model.  No polar decomposition or manifold
recognition theorem is assumed in these definitions.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

abbrev SpecialLinear := Matrix.SpecialLinearGroup (Fin 2) ℂ
abbrev Base := StandardSixSphereCircleModel.Base
abbrev Normal := StandardSixSphereCircleModel.Normal
abbrev NormalSphere := StandardSixSphereCircleModel.NormalSphere

/-- Positive scalar part of the Hermitian determinant-one factor. -/
def hyperbolicScale (b : Base) : ℝ := Real.sqrt (1 + ‖b‖ ^ 2)

/-- Literal traceless Hermitian matrix for the chosen three real coordinates. -/
def tracelessMatrix (b : Base) : MatrixSpace :=
  !![(b 0 : ℂ), (b 1 : ℂ) + (b 2 : ℂ) * Complex.I;
    (b 1 : ℂ) - (b 2 : ℂ) * Complex.I, -(b 0 : ℂ)]

/-- The explicit Hermitian positive factor associated to a Euclidean point. -/
def positiveMatrix (b : Base) : MatrixSpace :=
  (hyperbolicScale b : ℂ) • (1 : MatrixSpace) + tracelessMatrix b

/-- Complete the original unit normal vector to an `SU(2)` matrix using its second column. -/
def unitaryMatrix (z : Normal) : MatrixSpace :=
  !![(z 2 : ℂ) - (z 3 : ℂ) * Complex.I,
      (z 0 : ℂ) + (z 1 : ℂ) * Complex.I;
    -(z 0 : ℂ) + (z 1 : ℂ) * Complex.I,
      (z 2 : ℂ) + (z 3 : ℂ) * Complex.I]

/-- The real and imaginary coordinates of the matrix's original second column. -/
def normalCoordinates (M : MatrixSpace) : Normal :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    ![(M 0 1).re, (M 0 1).im, (M 1 1).re, (M 1 1).im]

/-- The three real coordinates of the traceless part of a Hermitian matrix. -/
def baseCoordinates (M : MatrixSpace) : Base :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![((M 0 0).re - (M 1 1).re) / 2, (M 0 1).re, (M 0 1).im]

/-- The positive denominator used by the explicit polar formula. -/
def denominator (M : MatrixSpace) : ℝ := Real.sqrt (frobeniusSq M + 2)

/-- The explicit normalized quaternionic part of a determinant-one matrix. -/
def unitaryPart (M : MatrixSpace) : MatrixSpace :=
  ((denominator M)⁻¹ : ℂ) • deform 1 M

/-- The corresponding left Hermitian factor, defined by the original matrix product. -/
def positivePart (M : MatrixSpace) : MatrixSpace :=
  M * (unitaryPart M).conjTranspose

/-- The original ambient matrix formula in the reverse direction. -/
def inverseMatrix (b : Base) (z : Normal) : MatrixSpace :=
  positiveMatrix b * unitaryMatrix z

end Wikipedia.HopfProblem.ConifoldPolar
