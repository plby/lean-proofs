import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanNormalFrame
import Wikipedia.NoExoticSixSphere.OrthogonalRightInverseSourceIsometry

/-!
# The full circle-double frame retains its original ambient equation coordinates

The fixed Euclidean block isometry and the ordered normal-coordinate
equivalence transport the entire actual normal operator. The framed
collared state's frame is therefore tied to the original Hilbert-product
equations, not merely to an isomorphic normal bundle.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem euclideanNormalFrame_from_ambient (a : Sphere 1 × Sphere m)
    (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFrame d a k hd).ambient p =
      ((ambientCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ambientNormalFrame d a k hd).ambient p)).comp
          (normalCoordinates k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  rw [euclideanNormalFrame_ambient, fderiv_euclideanEquations,
    orthogonalRightInverse_source_isometry _ (surjective_fderiv_ambientEquations d a p),
    ambientNormalFrame_ambient]
  rfl

end NoExoticSixSphere.CircleCylinder
