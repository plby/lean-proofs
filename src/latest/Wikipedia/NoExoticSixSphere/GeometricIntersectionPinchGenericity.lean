import Wikipedia.NoExoticSixSphere.GeometricIntersectionPinchFlattening
import Wikipedia.NoExoticSixSphere.CommonTransverseRepresentative

/-!
# Pinch additivity with a constructed common generic comparison map

Smooth the comparison map, move it off the common base value by the proved
low-dimensional avoidance theorem, and choose one small parameter transverse
to both inputs while retaining avoidance. Geometric homotopy invariance then
removes all transversality and avoidance hypotheses from pinch additivity
for smooth inputs and an arbitrary continuous comparison map.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.MapIntersections

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem transverse_swap (f g : C(Sphere 3, M))
    (ht : ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) :
    ∀ x y, g x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)) := by
  intro x y hxy
  let A : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) f y
  let B : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) g x
  have h : Surjective (A.coprod B) := ht y x hxy.symm
  intro w
  obtain ⟨z, hz⟩ := h w
  refine ⟨(z.2, z.1), ?_⟩
  change B z.2 + A z.1 = w
  rw [add_comm]
  exact hz

end NoExoticSixSphere.MapIntersections

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections SphereFold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_smooth_common_transverse_avoiding (k f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (m : M) :
    ∃ K : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧ k.Homotopic K ∧
      m ∉ range K ∧
      (∀ x y, K x = f y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) K x).coprod (mfderiv (𝓡 3) (𝓡 6) f y))) ∧
      (∀ x y, K x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) K x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  obtain ⟨k₀, hk₀, Hk₀⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) k
  let p : C(Vector 0, M) := ContinuousMap.const _ m
  obtain ⟨k₁, hk₁, Hk₁, hdis⟩ :=
    Wikipedia.SmoothSixDPoincare.GeneralPosition.exists_disjoint_smooth_map_homotopicRel
      (I := 𝓡 3) (I' := 𝓡 0) (J := 𝓡 6) k₀ p hk₀ contMDiff_const
      (by simp [GLOrthonormalization.Vector]) isClosed_empty
      (fun _ h ↦ (notMem_empty _ h).elim)
  have havoid (x : Sphere 3) : k₁ x ∈ ({m} : Set M)ᶜ := by
    intro h
    have he : k₁ x = m := mem_singleton_iff.mp h
    exact disjoint_left.mp hdis (mem_range_self x) ⟨0, he.symm⟩
  obtain ⟨K, hK, HK, hKV, hKf, hKg⟩ :=
    e.exists_smooth_common_transverse_homotopic r k₁ f g hk₁ hf hg
      isClosed_singleton.isOpen_compl havoid
  refine ⟨K, hK, Hk₀.trans (Hk₁.homotopic.trans HK), ?_, hKf, hKg⟩
  rintro ⟨x, hx⟩
  exact hKV x (mem_singleton_iff.mpr hx)

theorem sphereIntersectionNumber_pinch_of_smooth (v : Sphere 3)
    (f g k : C(Sphere 3, M)) (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) :
    sphereIntersectionNumber e r (pinch v f g hbase) k =
      sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k := by
  obtain ⟨K, hK, HK, hm, hKf, hKg⟩ :=
    e.exists_smooth_common_transverse_avoiding r k f g hf hg (f (antipode v))
  calc
    sphereIntersectionNumber e r (pinch v f g hbase) k =
        sphereIntersectionNumber e r (pinch v f g hbase) K :=
      sphereIntersectionNumber_homotopic e r _ _ k K (.refl _) HK
    _ = sphereIntersectionNumber e r f K + sphereIntersectionNumber e r g K :=
      sphereIntersectionNumber_pinch_of_transverse e r v f g K hbase hf hg hK hm
        (transverse_swap K f hKf) (transverse_swap K g hKg)
    _ = sphereIntersectionNumber e r f k + sphereIntersectionNumber e r g k :=
      congrArg₂ (· + ·)
        (sphereIntersectionNumber_homotopic e r f f k K (.refl _) HK).symm
        (sphereIntersectionNumber_homotopic e r g g k K (.refl _) HK).symm

end NoExoticSixSphere.EuclideanEmbedding
