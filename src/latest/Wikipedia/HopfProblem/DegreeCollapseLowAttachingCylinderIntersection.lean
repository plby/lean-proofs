import Wikipedia.HopfProblem.DegreeCollapseLowFramedAttachingProduct
import Wikipedia.HopfProblem.DegreeCollapseLowHeightCylinder
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!

# An actual short height cylinder meets the low-surgery handle only on its face

The compact inner handle misses the height-zero cylinder. A uniform height
bound keeps it disjoint from the actual short cylinder. On the outer collar,
the exact signed height identifies every intersection. Avoidance of the old
ambient plane alone is never taken to imply cylinder avoidance.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem exists_heightCylinder_avoids_inner [CompactSpace M] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closedBall (0 : Vector (d + 1)) A.innerRadius,
      ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius, ∀ m : M, ∀ t : ℝ,
        ‖t‖ ≤ ε → A.map (x, v) ≠ (LowHeightCylinder.heightCylinder d e) (m, t) := by
  let K := closedBall (0 : Vector (d + 1)) A.innerRadius ×ˢ
    closedBall (0 : Vector (7 - d)) A.radius
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hH : ContinuousOn A.map K := by
    intro p hp
    exact (A.smooth p.1 ((closedBall_subset_closedBall A.innerRadius_lt_one.le) hp.1)
      p.2 hp.2).continuousAt.continuousWithinAt
  let L := A.map '' K
  have hL : IsClosed L := (hK.image_of_continuousOn hH).isClosed
  let U := (LowHeightCylinder.heightCylinder d e) ⁻¹' Lᶜ
  have hU : IsOpen U := hL.isOpen_compl.preimage (LowHeightCylinder.continuous_heightCylinder d e)
  have hzero (m : M) : (m, (0 : ℝ)) ∈ U := by
    rintro ⟨⟨x, v⟩, hp, he⟩
    apply A.interior_avoids x ((closedBall_subset_ball A.innerRadius_lt_one) hp.1) v hp.2
    refine ⟨e.toFun m, ?_⟩
    exact ((LowHeightCylinder.heightCylinder_zero d e) m).symm.trans he.symm
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hzero
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv m t ht he
  exact hεU m t ht ⟨(x, v), ⟨hx, hv⟩, he⟩

theorem collar_eq_heightCylinder_iff {x : Vector (d + 1)}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector (7 - d)} (hv : v ∈ closedBall 0 A.radius) (m : M) {t : ℝ} (ht : 0 ≤ t) :
    A.map (x, v) = (LowHeightCylinder.heightCylinder d e) (m, t) ↔
      ∃ s : NoExoticSixSphere.Sphere d, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 := by
  constructor
  · intro he
    rw [A.collar_map x hx hxr v hv] at he
    have hp := (coordinates e.ambientDimension (d + 1)).injective he
    have hρ : definingFunction x = t := congrArg (fun z ↦ z.1.2) hp
    have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hρ0 : definingFunction x ≤ 0 := by
      dsimp only [definingFunction]
      nlinarith [norm_nonneg x]
    have ht0 : t = 0 := le_antisymm (hρ ▸ hρ0) ht
    have hs : x ∈ sphere (0 : Vector (d + 1)) 1 :=
      (definingFunction_eq_zero_iff x).mp (hρ.trans ht0)
    let s : NoExoticSixSphere.Sphere d := ⟨x, hs⟩
    have hm : e.toFun (A.tube (SphereRadialRetraction.retract (spherePole d) x, v)) =
        e.toFun m := congrArg (fun z ↦ z.1.1) hp
    have hr : SphereRadialRetraction.retract (spherePole d) x = s :=
      SphereRadialRetraction.retract_coe (spherePole d) s
    rw [hr] at hm
    exact ⟨s, rfl, e.closedEmbedding.injective hm, ht0⟩
  · rintro ⟨s, rfl, rfl, rfl⟩
    exact (A.map_boundary s v hv).trans
      ((LowHeightCylinder.heightCylinder_zero d e) (A.tube (s, v))).symm

theorem exists_heightCylinder_intersection [CompactSpace M] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
      ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius, ∀ m : M, ∀ t ∈ Icc (0 : ℝ) ε,
        A.map (x, v) = (LowHeightCylinder.heightCylinder d e) (m, t) ↔
          ∃ s : NoExoticSixSphere.Sphere d, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 := by
  obtain ⟨ε, hε, havoid⟩ := A.exists_heightCylinder_avoids_inner
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv m t ht
  by_cases hxr : A.innerRadius ≤ ‖x‖
  · exact A.collar_eq_heightCylinder_iff hx hxr hv m ht.1
  · have hxinner : x ∈ closedBall (0 : Vector (d + 1)) A.innerRadius := by
      simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hxr).le
    constructor
    · intro he
      have htnorm : ‖t‖ ≤ ε := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
      exact (havoid x hxinner v hv m t htnorm he).elim
    · rintro ⟨s, rfl, rfl, rfl⟩
      exact (A.map_boundary s v hv).trans
        ((LowHeightCylinder.heightCylinder_zero d e) (A.tube (s, v))).symm

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
