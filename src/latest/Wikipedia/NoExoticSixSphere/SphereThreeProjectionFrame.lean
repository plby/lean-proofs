import Wikipedia.NoExoticSixSphere.OrthogonalSecondHomotopy
import Wikipedia.NoExoticSixSphere.ClutchingExtension
import Wikipedia.NoExoticSixSphere.HemisphereExtension
import Wikipedia.NoExoticSixSphere.FrameSmoothing

/-!
# Actual rank-three projection frames on the three-sphere

The hemisphere clutching map has values in the genuine rank-three general
linear space. Its proved two-sphere nullhomotopy extends over the southern
hemisphere and glues the two transported frames. Smooth projections then
have smooth global frames by the existing approximation theorem.
No trivialization, stable framing, or vanishing disk parity is an input.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeProjection

open GLOrthonormalization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem nonempty_continuousFrame (P : Sphere 3 → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (hc : Continuous P)
    (hr : ∀ x, Module.finrank ℝ (P x).range = 3) :
    Nonempty (ContinuousRangeFrame P (Vector 3)) := by
  let v := spherePole 3
  obtain ⟨qN⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector 3) = Module.finrank ℝ (P v).range by
      rw [finrank_euclideanSpace_fin, hr v])
  obtain ⟨qS⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector 3) = Module.finrank ℝ (P (antipode v)).range by
      rw [finrank_euclideanSpace_fin, hr (antipode v)])
  let c := sphereClutchingMap P hP hc v qN qS
  let e : Equator v ≃ₜ Sphere 2 :=
    equatorEuclideanHomeomorph v (n := 3) finrank_euclideanSpace_fin
  let : Nonempty (Equator v) := e.toEquiv.nonempty
  obtain ⟨d, ⟨H⟩⟩ := OrthogonalSecondHomotopy.generalLinear_rankThree_nullhomotopic
    (c.comp (e.symm : C(_, _)))
  let H' : c.Homotopy (ContinuousMap.const _ d) := {
    toFun := fun p ↦ H (p.1, e p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := fun x ↦ by
      rw [H.apply_zero]
      change c (e.symm (e x)) = c x
      rw [e.symm_apply_apply]
    map_one_left := fun x ↦ H.apply_one (e x) }
  obtain ⟨g, hg⟩ := exists_southernExtension_of_nullhomotopy v c d H'
  exact ⟨sphereFrameOfClutchingExtension P hP hc v qN qS g hg⟩

theorem nonempty_smoothFrame (P : Sphere 3 → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (hs : ContMDiff (𝓡 3) 𝓘(ℝ, F →L[ℝ] F) ∞ P)
    (hr : ∀ x, Module.finrank ℝ (P x).range = 3) :
    Nonempty (SmoothRangeFrame (𝓡 3) P (Vector 3)) := by
  obtain ⟨a⟩ := nonempty_continuousFrame P hP hs.continuous hr
  exact nonempty_smoothRangeFrame_of_continuous P hP hs a

end NoExoticSixSphere.SphereThreeProjection
