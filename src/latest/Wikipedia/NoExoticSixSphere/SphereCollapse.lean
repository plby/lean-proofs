import Wikipedia.NoExoticSixSphere.FramedPontryaginThom
import Wikipedia.NoExoticSixSphere.SixSphereFramedCollapse
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# The framed collapse as a map between actual spheres

The one-point compactifications are identified with standard Euclidean
spheres. The map preserves the specified points at infinity, and its fiber
over the specified finite zero is exactly the compactified embedded manifold.
No bordism or homotopy-class classification is asserted here.
-/

open scoped Manifold ContDiff
open Topology

namespace NoExoticSixSphere

noncomputable def sphereInfinity (n : ℕ) : Sphere n :=
  euclideanOnePointSphere n OnePoint.infty

noncomputable def sphereZero (n : ℕ) : Sphere n :=
  euclideanOnePointSphere n ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _)

theorem sphereZero_ne_infinity (n : ℕ) : sphereZero n ≠ sphereInfinity n := by
  intro h
  exact OnePoint.coe_ne_infty (0 : EuclideanSpace ℝ (Fin n))
    ((euclideanOnePointSphere n).injective h)

namespace EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : EuclideanEmbedding n M)

noncomputable def compactifiedEmbedding : M → Sphere e.ambientDimension :=
  fun x ↦ euclideanOnePointSphere e.ambientDimension (e.toFun x)

theorem compactifiedEmbedding_isEmbedding : IsEmbedding e.compactifiedEmbedding :=
  (euclideanOnePointSphere e.ambientDimension).isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp e.closedEmbedding.isEmbedding)

theorem contMDiff_compactifiedEmbedding :
    ContMDiff (𝓡 n) (𝓡 e.ambientDimension) ∞ e.compactifiedEmbedding :=
  (contMDiff_euclideanOnePointSphere_coe e.ambientDimension).comp e.smooth

variable [IsManifold (𝓡 n) ∞ M] [Nonempty M] [CompactSpace M]
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

include a in
theorem exists_sphereCollapse :
    ∃ F : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)),
      F (sphereInfinity e.ambientDimension) = sphereInfinity (e.ambientDimension - n) ∧
      ∀ y, F y = sphereZero (e.ambientDimension - n) ↔
        ∃ x, e.compactifiedEmbedding x = y := by
  obtain ⟨F, hinfty, hfiber⟩ := e.exists_framedCollapse a
  let s := euclideanOnePointSphere e.ambientDimension
  let t := euclideanOnePointSphere (e.ambientDimension - n)
  let G : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)) :=
    ⟨fun y ↦ t (F (s.symm y)), t.continuous.comp (F.continuous.comp s.symm.continuous)⟩
  refine ⟨G, ?_, fun y ↦ ?_⟩
  · change t (F (s.symm (s OnePoint.infty))) = t OnePoint.infty
    rw [s.symm_apply_apply, hinfty]
  · change t (F (s.symm y)) = t (↑(0 : e.NormalModel)) ↔ _
    rw [t.injective.eq_iff, hfiber]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change s (↑(e.toFun x)) = y
      rw [hx, s.apply_symm_apply]
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have h := congrArg s.symm hx
      change s.symm (s (↑(e.toFun x))) = s.symm y at h
      simpa only [s.symm_apply_apply] using h

end EuclideanEmbedding

theorem exists_sixSphereCollapse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      ∃ F : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)),
        F (sphereInfinity e.ambientDimension) = sphereInfinity (e.ambientDimension - 6) ∧
        ∀ y, F y = sphereZero (e.ambientDimension - 6) ↔
          ∃ x, e.compactifiedEmbedding x = y := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : Nonempty (Sphere 6) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty M := h.toEquiv.nonempty
  obtain ⟨e, ⟨a⟩⟩ := exists_framedEmbedding h
  exact ⟨e, e.exists_sphereCollapse a⟩

end NoExoticSixSphere
