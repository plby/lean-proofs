import Wikipedia.HopfProblem.DegreeCollapseOriginalAtlasCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativeFramedFillingRecognition

/-!
# Recognition of the original smooth six-sphere from a finite collapse nullhomotopy

The actual framed collapse of a candidate six-sphere supplies a regular
collared cylinder after a finite nullhomotopy and one further suspension.
The native filling recognition constructs the connectivity and homology
reductions and the smooth sphere identification. Composing with the proved
original-atlas endpoint diffeomorphism retains the candidate's given atlas.

The finite collapse nullhomotopy remains a hypothesis. In particular, this
result does not prove that every candidate has such a nullhomotopy, and it
does not assert the unconditional proposition `SixSphereRigidity`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open SphereMapSuspension Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}

theorem nonempty_sphere_diffeomorph_of_iterate_nullhomotopic
    (d : e.FramedCollapseData a) (h : M ≃ₜ Sphere 6) (r : ℕ)
    (hnull : (iterate d.sphereMap r).Nullhomotopic) :
    Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let m : M := h.symm (sphereZero 6)
  have hdim : e.ambientDimension + (r + 1) =
      ((e.ambientDimension - 6) + (r + 1)) + 6 := by
    have hn := e.dimension_le_ambient m
    omega
  obtain ⟨C, _, hmiss, D, _⟩ :=
    exists_original_atlas_cylinder_of_iterate_nullhomotopic d m r hnull
  let := regularFiberAtlas C.leftMap C.smooth_left
    (equators (e.ambientDimension - 6) (r + 1) (sphereZero (e.ambientDimension - 6)))
    C.regular_left 6 (by simpa using hdim)
  obtain ⟨F⟩ := ReflectedCylinder.nonempty_endpoint_sphere_diffeomorph_of_framed_filling
    C hmiss hdim (sphereZero (e.ambientDimension + (r + 1)))
    (D.toHomeomorph.symm.trans h)
  exact ⟨D.trans F⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
