import Wikipedia.NoExoticSixSphere.ImmersedSpherePushOffCount
import Wikipedia.NoExoticSixSphere.SelfTransverseSphereRepresentative
import Wikipedia.NoExoticSixSphere.GeometricIntersectionFundamentalClass
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Alternation of the actual geometric middle-dimensional pairing

Every continuous three-sphere map has a genuine self-transverse immersed
representative. Its constructed normal push-off is homotopic to it and
has a finite, transverse, even-count coincidence set. Homotopy invariance
therefore proves zero self-intersection for every original sphere map.
Actual sphere-class surjectivity gives alternation on native middle homology.

An actual full normal frame of the six-manifold is a hypothesis. This is
not a nondegeneracy, quadratic-refinement, bordism-detection, or smooth
classification theorem.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

section General

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

include a in
theorem sphereIntersectionNumber_self_of_selfTransverse (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ s t, s ≠ t → f s = f t → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f s).coprod (mfderiv (𝓡 3) (𝓡 6) f t))) :
    sphereIntersectionNumber e r f f = 0 := by
  obtain ⟨G, hG, hG₀, hnear⟩ := e.exists_even_transverse_pushOff_intersections a r f hf hd ht
  have hnear' := hnear.filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  obtain ⟨t, htnear, htn⟩ := (hnear'.and self_mem_nhdsWithin).exists
  have htn' : t ≠ 0 := htn
  obtain ⟨_, hpar, htrans⟩ := htnear htn'
  have hg : ContMDiff (𝓡 3) (𝓡 6) ∞ (G t) :=
    hG.comp (contMDiff_const.prodMk contMDiff_id)
  let g : C(Sphere 3, M) := ⟨G t, hg.continuous⟩
  have H : f.Homotopic g := by
    refine ⟨{
      toFun := fun q ↦ G ((q.1 : ℝ) * t) q.2
      continuous_toFun := hG.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_
    }⟩
    · intro s
      change G ((0 : ℝ) * t) s = f s
      rw [zero_mul]
      exact hG₀ s
    · intro s
      change G ((1 : ℝ) * t) s = G t s
      rw [one_mul]
  exact (sphereIntersectionNumber_homotopic e r f f f g (ContinuousMap.Homotopic.refl f) H).trans
    ((sphereIntersectionNumber_eq_parity e r f g hf hg htrans).trans hpar)

include a in
theorem sphereIntersectionNumber_self (f : C(Sphere 3, M)) :
    sphereIntersectionNumber e r f f = 0 := by
  obtain ⟨g, hg, H, hd, ht⟩ := e.exists_selfTransverse_immersed_homotopic r f
  exact (sphereIntersectionNumber_homotopic e r f g f g H H).trans
    (sphereIntersectionNumber_self_of_selfTransverse e a r g hg hd ht)

include a in
theorem homotopyIntersection_self {m : M} (c : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r c c = 0 :=
  sphereIntersectionNumber_self e a r (SmoothCube.classRepresentative c).val

end General

section Homology

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (m : M) [Subsingleton (π_ 2 M m)]

include a in
theorem integralHomologyIntersection_self (c : SingularHomology M 3) :
    integralHomologyIntersection e r m c c = 0 := by
  obtain ⟨f, rfl⟩ := SmoothCube.hurewiczSphereClass_surjective m c
  rw [integralHomologyIntersection_sphereClass]
  exact sphereIntersectionNumber_self e a r f.val

include a in
theorem modTwoHomologyIntersection_self (c : ModHomology 2 M 3) :
    modTwoHomologyIntersection e r m c c = 0 := by
  obtain ⟨f, rfl⟩ := SmoothCube.modTwoSphereClass_surjective m c
  rw [modTwoHomologyIntersection_sphereClass]
  exact sphereIntersectionNumber_self e a r f.val

include a in
theorem modTwoHomologyIntersection_isAlt : (modTwoHomologyIntersection e r m).IsAlt :=
  modTwoHomologyIntersection_self e a r m

end Homology

end NoExoticSixSphere.EuclideanEmbedding
