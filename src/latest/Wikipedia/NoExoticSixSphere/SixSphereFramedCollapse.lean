import Wikipedia.NoExoticSixSphere.NormalFraming
import Wikipedia.NoExoticSixSphere.CollapseRegularFiber

/-!
# Unconditional framed collapse data for a candidate six-sphere

The homeomorphism hypothesis supplies compactness and nonemptiness. The
proved normal-framing theorem then supplies the frame; the geometric collapse
has smooth finite coordinates and the specified normal differential.
This does not assert a nullbordism or a diffeomorphism classification.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem exists_sixSphereFramedCollapseData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      ∃ a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel,
        Nonempty (e.FramedCollapseData a) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : Nonempty (Sphere 6) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty M := h.toEquiv.nonempty
  obtain ⟨e, ⟨a⟩⟩ := exists_framedEmbedding h
  exact ⟨e, a, e.nonempty_framedCollapseData a⟩

end NoExoticSixSphere
