import Wikipedia.NoExoticSixSphere.TransverseSphereChartDifference

/-!
# Spatial coordinate regularity implies native transversality

The exact chart-derivative factorization is reflected through the injective
target-chart derivative. Thus the regularity supplied by parametric Sard
is transversality of the original manifold tangent maps, not merely a
coordinate-level condition.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization

theorem surjective_coprod_of_signed_chart
    (A B : Vector 3 →L[ℝ] Vector 6) (C : Vector 6 →L[ℝ] Vector 6)
    (S T : Vector 3 →L[ℝ] Vector 3) (hC : Injective C)
    (h : Surjective ((C.comp (A.comp S)).coprod (-(C.comp (B.comp T))))) :
    Surjective (A.coprod B) := by
  intro v
  obtain ⟨q, hq⟩ := h (C v)
  refine ⟨(S q.1, -(T q.2)), hC ?_⟩
  change C (A (S q.1) + B (-(T q.2))) = C v
  rw [map_add, map_neg, map_neg]
  exact hq

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf hg in
theorem native_transverse_of_spatial_regular (t : ℝ) (x y : Sphere 3)
    (s z : SphereChart) (c : ManifoldChart M) (hx : x ∈ s.source) (hy : y ∈ z.source)
    (hc : f t x ∈ c.source) (hxy : f t x = g t y)
    (ht : Surjective (fderiv ℝ (fun q : Vector 3 × Vector 3 ↦
      coordinateDifference f g s z c (t, q)) (s x, z y))) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g t) y)) := by
  rw [fderiv_spatial_difference_formula f g hf hg t x y s z c hx hy hc hxy] at ht
  have hC : IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ c (f t x) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  exact surjective_coprod_of_signed_chart _ _ _ _ _
    (hC.mfderivToContinuousLinearEquiv (by simp)).injective ht

end NoExoticSixSphere.IntersectionTrace
