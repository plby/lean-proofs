import Wikipedia.NoExoticSixSphere.ReflectedFillingFrame
import Wikipedia.HopfProblem.DegreeCollapseOriginalAtlasCylinder
import Wikipedia.HopfProblem.DegreeCollapseReflectedLowCollaredState

/-!
# A finite collapse nullhomotopy supplies an actual two-connected framed filling

The original smooth six-manifold is only required to be simply connected
with zero second integral homology. Its third homology need not vanish.
The actual nullhomotopy constructs the initial cylinder; reflection and
native low surgeries construct a two-connected compact normally framed
filling whose whole boundary is diffeomorphic to the original atlas.

No initial filling or connectivity surgery sequence is assumed. The
construction now retains the exact induced original endpoint-fiber frame
through reflection and every connectivity step. The finite nullhomotopy
remains an input; comparing the endpoint frame with the prescribed
Euclidean collapse frame remains a separate obligation.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open SphereMapSuspension Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}

theorem exists_twoConnected_filling_of_finite_null
    (d : e.FramedCollapseData a) (m : M) (r : ℕ)
    (hnull : (iterate d.sphereMap r).Nullhomotopic) :
    ∃ F : FramedSevenFilling.{0, 0, 0, 0} (𝓡 6) M,
      letI := F.topology;
      SimplyConnectedSpace F.W ∧ ∀ w : F.W, Subsingleton (π_ 2 F.W w) := by
  have hdim : e.ambientDimension + (r + 1) =
      ((e.ambientDimension - 6) + (r + 1)) + 6 := by
    have hn := e.dimension_le_ambient m
    omega
  obtain ⟨C, _, hmiss, D, _⟩ :=
    exists_original_atlas_cylinder_of_iterate_nullhomotopic d m r hnull
  let := regularFiberAtlas C.leftMap C.smooth_left
    (equators (e.ambientDimension - 6) (r + 1) (sphereZero (e.ambientDimension - 6)))
    C.regular_left 6 (by simpa using hdim)
  let : SimplyConnectedSpace (ReflectedCylinder.EndpointFiber C) :=
    D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology (ReflectedCylinder.EndpointFiber C) 2) :=
    (homotopyEquivHomologyEquiv D.symm.toHomeomorph.toHomotopyEquiv 2).injective.subsingleton
  let p := sphereZero (e.ambientDimension + (r + 1))
  obtain ⟨U, F, hF, hpi⟩ := ReflectedSeam.exists_twoConnected_endpoint_filling
    C hmiss hdim p (D m)
  let W := ReflectedSeam.endpointFilling C hmiss hdim p (D m) F
  exact ⟨W.reparametrizeBoundary D, hF, hpi⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
