import Wikipedia.NoExoticSixSphere.InternalSphereTube
import Wikipedia.NoExoticSixSphere.CompactLocalDiffeomorph
import Wikipedia.NoExoticSixSphere.LocalInjectiveProductRelation

/-!
# Uniform internal tubes for immersed spheres, with diagonal separation

The internal tube of an immersion is a local diffeomorphism near its zero
section even when the sphere has double points. Compactness gives one small
radius valid at every point. A separate uniform local-injectivity argument
excludes intersections of a nonzero push-off with the original sheet near
the source diagonal; distant sheets are not asserted to be disjoint.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension) (r : TubularRetraction e)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include hf hC hd hiC hCr in
theorem exists_immersed_internalSphereTube_radius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s v, ‖v‖ ≤ ε →
      (s, v) ∈ e.sphereTubeDomain f C r ∧
        IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
          (e.internalSphereTube f C r) (s, v) := by
  let U := e.sphereTubeDomain f C r ∩
    {p | IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞ (e.internalSphereTube f C r) p}
  have hU : IsOpen U := (e.isOpen_sphereTubeDomain f C r hf hC).inter
    (isOpen_localDiffeomorphLocus (e.internalSphereTube f C r))
  exact exists_uniform_closedProductTube hU fun s ↦
    ⟨e.core_mem_sphereTubeDomain f C r s,
      e.isLocalDiffeomorphAt_internalSphereTube_core f C r hf hC hd hiC hCr s⟩

include hf hC hd hiC hCr in
theorem exists_internalSphereTube_diagonal_separation :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set (Sphere 3 × Sphere 3), IsOpen V ∧
      (∀ s, (s, s) ∈ V) ∧
      (∀ s t, (s, t) ∈ V → f s = f t → s = t) ∧
      ∀ s t, (s, t) ∈ V → ∀ v : Vector 3,
        ‖v‖ ≤ ε → v ≠ 0 → f s ≠ e.internalSphereTube f C r (t, v) := by
  have hlocal : ∀ s, ∃ U : Set (Sphere 3 × Vector 3),
      IsOpen U ∧ (s, 0) ∈ U ∧ InjOn (e.internalSphereTube f C r) U := by
    intro s
    obtain ⟨Φ, hs, heq⟩ :=
      e.isLocalDiffeomorphAt_internalSphereTube_core f C r hf hC hd hiC hCr s
    refine ⟨Φ.source, Φ.open_source, hs, ?_⟩
    intro p hp q hq he
    apply Φ.injOn hp hq
    rw [← heq hp, ← heq hq]
    exact he
  obtain ⟨ε, hε, V, hV, hdiag, hinj⟩ :=
    exists_uniform_localInjective_product_relation (e.internalSphereTube f C r) hlocal
  have hz : ‖(0 : Vector 3)‖ ≤ ε := by simpa only [norm_zero] using hε.le
  refine ⟨ε, hε, V, hV, hdiag, ?_, ?_⟩
  · intro s t hst he
    exact (hinj s t hst 0 0 hz hz
      ((e.internalSphereTube_core f C r s).trans
        (he.trans (e.internalSphereTube_core f C r t).symm))).1
  · intro s t hst v hv hvne he
    have hpair := hinj s t hst 0 v hz hv ((e.internalSphereTube_core f C r s).trans he)
    exact hvne hpair.2.symm

end NoExoticSixSphere.EuclideanEmbedding
