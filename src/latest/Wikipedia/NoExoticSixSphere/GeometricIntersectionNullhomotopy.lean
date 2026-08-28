import Wikipedia.NoExoticSixSphere.GeometricSphereIntersection
import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance

/-!
# Nullhomotopic sphere maps have zero geometric intersection number

The actual low-dimensional avoidance theorem moves a point off a smooth
three-sphere image through a genuine homotopy. Thus a constant sphere map
has a disjoint smooth representative. Smoothing the second map and using
the checked homotopy invariance gives the zero law for arbitrary continuous
maps, without a path-connectivity or a preassigned disjoint-point hypothesis.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e in
theorem exists_constant_homotopic_avoiding (m : M) (g : C(Sphere 3, M))
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) :
    ∃ y : M, y ∉ range g ∧
      (ContinuousMap.const (Sphere 3) m).Homotopic (ContinuousMap.const (Sphere 3) y) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  let f : C(Vector 0, M) := ContinuousMap.const _ m
  obtain ⟨F, _, ⟨H⟩, hdis⟩ :=
    Wikipedia.SmoothSixDPoincare.GeneralPosition.exists_disjoint_smooth_map_homotopicRel
      (I := 𝓡 0) (I' := 𝓡 3) (J := 𝓡 6) f g contMDiff_const hg
      (by simp [GLOrthonormalization.Vector]) isClosed_empty
      (fun _ h ↦ (notMem_empty _ h).elim)
  refine ⟨F 0, ?_, ⟨{
    toFun q := H (q.1, 0)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk continuous_const)
    map_zero_left := fun _ ↦ H.apply_zero 0
    map_one_left := fun _ ↦ H.apply_one 0 }⟩⟩
  exact fun hy ↦ disjoint_left.mp hdis (mem_range_self 0) hy

theorem sphereIntersectionNumber_const_left (m : M) (g : C(Sphere 3, M)) :
    sphereIntersectionNumber e r (ContinuousMap.const _ m) g = 0 := by
  obtain ⟨g', hg', Hg⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) g
  obtain ⟨y, hy, Hm⟩ := e.exists_constant_homotopic_avoiding m g' hg'
  have hdis : Disjoint (range (ContinuousMap.const (Sphere 3) y)) (range g') := by
    rw [disjoint_left]
    rintro z ⟨x, rfl⟩ hz
    exact hy hz
  rw [sphereIntersectionNumber_homotopic e r (ContinuousMap.const _ m)
    (ContinuousMap.const _ y) g g' Hm Hg]
  exact sphereIntersectionNumber_zero_of_disjoint e r (ContinuousMap.const _ y) g'
    contMDiff_const hg' hdis

theorem sphereIntersectionNumber_const_right (f : C(Sphere 3, M)) (m : M) :
    sphereIntersectionNumber e r f (ContinuousMap.const _ m) = 0 := by
  rw [sphereIntersectionNumber_comm, sphereIntersectionNumber_const_left]

theorem sphereIntersectionNumber_zero_of_nullhomotopic_left
    (f g : C(Sphere 3, M)) (m : M) (H : f.Homotopic (ContinuousMap.const _ m)) :
    sphereIntersectionNumber e r f g = 0 := by
  rw [sphereIntersectionNumber_homotopic e r f (ContinuousMap.const _ m) g g H
    (ContinuousMap.Homotopic.refl g), sphereIntersectionNumber_const_left]

theorem sphereIntersectionNumber_zero_of_nullhomotopic_right
    (f g : C(Sphere 3, M)) (m : M) (H : g.Homotopic (ContinuousMap.const _ m)) :
    sphereIntersectionNumber e r f g = 0 := by
  rw [sphereIntersectionNumber_comm]
  exact sphereIntersectionNumber_zero_of_nullhomotopic_left e r g f m H

end NoExoticSixSphere.EuclideanEmbedding
