import Wikipedia.NoExoticSixSphere.NormalClutching
import Wikipedia.NoExoticSixSphere.HemisphereExtension

/-!
# From an actual normal clutching nullhomotopy to a smooth normal frame

This connects the continuous homotopy problem on the standard five-sphere to
the independently given smooth atlas of a candidate six-sphere. The nullhomotopy
is an explicit premise, not an asserted vanishing homotopy group.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M) (h : M ≃ₜ Sphere 6) (v : Sphere 6)

/-- Nullhomotopy of the concrete five-sphere clutching map yields a smooth normal frame. -/
theorem nonempty_smoothNormalFrame_of_clutchingNullhomotopy
    (c : InvertibleOperators e.NormalModel)
    (H : (e.normalSixClutchingMap h v).Homotopy (ContinuousMap.const _ c)) :
    Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  let u := equatorSixHomeomorph v
  let : Nonempty (Equator v) := nonempty_equatorSix v
  let H' : (e.normalClutchingMap h v).Homotopy (ContinuousMap.const _ c) := {
    toFun := fun p ↦ H (p.1, u p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (u.continuous.comp continuous_snd))
    map_zero_left := fun x ↦ by
      rw [H.apply_zero]
      change e.normalClutchingMap h v (u.symm (u x)) = e.normalClutchingMap h v x
      rw [u.symm_apply_apply]
    map_one_left := fun x ↦ H.apply_one (u x) }
  obtain ⟨g, hg⟩ := exists_southernExtension_of_nullhomotopy v (e.normalClutchingMap h v) c H'
  exact e.nonempty_smoothNormalFrame_of_extension h v g hg

end NoExoticSixSphere.EuclideanEmbedding
