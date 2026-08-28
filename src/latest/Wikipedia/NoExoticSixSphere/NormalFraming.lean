import Wikipedia.NoExoticSixSphere.RankSixVanishing
import Wikipedia.NoExoticSixSphere.FramingFromComplexStructures

/-!
# Unconditional smooth normal framing of smooth topological six-spheres

The checked rank-six nullhomotopy discharges the input of the orthogonal
deformation, stable-rank, and clutching construction. This gives an actual
smoothly framed Euclidean embedding, not the final diffeomorphism classification.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

theorem fiveSphereOrthogonalSixteenVanishing
    (f : C(Sphere 5, OrthogonalOperators 16)) :
    ∃ a, f.Homotopic (ContinuousMap.const _ a) :=
  fiveSphereOrthogonalSixteenVanishing_of_complexStructureSix
    OrthogonalComplexStructures.fourthSphere_nullhomotopic f

theorem fiveSphereOrthogonalSevenVanishing
    (f : C(Sphere 5, OrthogonalOperators 7)) :
    ∃ a, f.Homotopic (ContinuousMap.const _ a) :=
  fiveSphereOrthogonalSevenVanishing_of_complexStructureSix
    OrthogonalComplexStructures.fourthSphere_nullhomotopic f

theorem exists_framedEmbedding {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) :=
  exists_framedEmbedding_of_complexStructureSixVanishing
    OrthogonalComplexStructures.fourthSphere_nullhomotopic h

end NoExoticSixSphere
