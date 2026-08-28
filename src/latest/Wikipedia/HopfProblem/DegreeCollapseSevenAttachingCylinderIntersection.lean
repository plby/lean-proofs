import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingLocalization
import Wikipedia.HopfProblem.DegreeCollapseGeneralHeightCylinder
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# A short original-manifold cylinder meets the handle exactly at its attaching face

The inner handle image is compact and misses the height-zero cylinder. The
tube lemma gives a uniform height bound keeping these sets disjoint. On the
outer collar the exact signed-height formula identifies every intersection.
No assertion that old-ambient avoidance implies cylinder avoidance is used.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem exists_heightCylinder_avoids_inner [CompactSpace M] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closedBall (0 : Vector 4) A.innerRadius,
      ∀ v ∈ closedBall (0 : Vector 4) A.radius, ∀ m : M, ∀ t : ℝ,
        ‖t‖ ≤ ε → A.map (x, v) ≠ (HeightCylinder.heightCylinder e) (m, t) := by
  let K := closedBall (0 : Vector 4) A.innerRadius ×ˢ
    closedBall (0 : Vector 4) A.radius
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hH : ContinuousOn A.map K := by
    intro p hp
    exact (A.smooth p.1 ((closedBall_subset_closedBall A.innerRadius_lt_one.le) hp.1)
      p.2 hp.2).continuousAt.continuousWithinAt
  let L := A.map '' K
  have hL : IsClosed L := (hK.image_of_continuousOn hH).isClosed
  let U := (HeightCylinder.heightCylinder e) ⁻¹' Lᶜ
  have hU : IsOpen U := hL.isOpen_compl.preimage (HeightCylinder.continuous_heightCylinder e)
  have hzero (m : M) : (m, (0 : ℝ)) ∈ U := by
    rintro ⟨⟨x, v⟩, hp, he⟩
    apply A.interior_avoids x ((closedBall_subset_ball A.innerRadius_lt_one) hp.1) v hp.2
    refine ⟨e.toFun m, ?_⟩
    exact ((HeightCylinder.heightCylinder_zero e) m).symm.trans he.symm
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hzero
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv m t ht he
  exact hεU m t ht ⟨(x, v), ⟨hx, hv⟩, he⟩

theorem collar_eq_heightCylinder_iff {x : Vector 4}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector 4} (hv : v ∈ closedBall 0 A.radius) (m : M) {t : ℝ} (ht : 0 ≤ t) :
    A.map (x, v) = (HeightCylinder.heightCylinder e) (m, t) ↔
      ∃ s : Sphere 3, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 := by
  constructor
  · intro he
    rw [A.collar_map x hx hxr v hv] at he
    have hp := (coordinates e.ambientDimension 4).injective he
    have hρ : definingFunction x = t := congrArg (fun z ↦ z.1.2) hp
    have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hρ0 : definingFunction x ≤ 0 := by
      dsimp only [definingFunction]
      nlinarith [norm_nonneg x]
    have ht0 : t = 0 := le_antisymm (hρ ▸ hρ0) ht
    have hs : x ∈ sphere (0 : Vector 4) 1 :=
      (definingFunction_eq_zero_iff x).mp (hρ.trans ht0)
    let s : Sphere 3 := ⟨x, hs⟩
    have hm : e.toFun (A.tube (SphereRadialRetraction.retract (pole 3) x, v)) =
        e.toFun m := congrArg (fun z ↦ z.1.1) hp
    have hr : SphereRadialRetraction.retract (pole 3) x = s :=
      SphereRadialRetraction.retract_coe (pole 3) s
    rw [hr] at hm
    exact ⟨s, rfl, e.closedEmbedding.injective hm, ht0⟩
  · rintro ⟨s, rfl, rfl, rfl⟩
    exact (A.map_boundary s v hv).trans ((HeightCylinder.heightCylinder_zero e) (A.tube (s, v))).symm

theorem exists_heightCylinder_intersection [CompactSpace M] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closedBall (0 : Vector 4) 1,
      ∀ v ∈ closedBall (0 : Vector 4) A.radius, ∀ m : M, ∀ t ∈ Icc (0 : ℝ) ε,
        A.map (x, v) = (HeightCylinder.heightCylinder e) (m, t) ↔
          ∃ s : Sphere 3, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 := by
  obtain ⟨ε, hε, havoid⟩ := A.exists_heightCylinder_avoids_inner
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv m t ht
  by_cases hxr : A.innerRadius ≤ ‖x‖
  · exact A.collar_eq_heightCylinder_iff hx hxr hv m ht.1
  · have hxinner : x ∈ closedBall (0 : Vector 4) A.innerRadius := by
      simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hxr).le
    constructor
    · intro he
      have htnorm : ‖t‖ ≤ ε := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
      exact (havoid x hxinner v hv m t htnorm he).elim
    · rintro ⟨s, rfl, rfl, rfl⟩
      exact (A.map_boundary s v hv).trans ((HeightCylinder.heightCylinder_zero e) (A.tube (s, v))).symm

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
