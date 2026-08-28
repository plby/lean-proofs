import Wikipedia.NoExoticSixSphere.SphereSumGluing

/-! # Exact open cap germs and the actual southern cap inverse -/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem southCap_head {x : Sphere 3} (hx : x ∈ southRegion) :
    0 < (reflectHead x).val 0 := by
  rw [reflectHead_head]
  exact neg_pos.mpr (southRegion_head_neg hx)

theorem isLocalDiffeomorphAt_southCap {ε : ℝ} (hε : ε ≠ 0) {x : Sphere 3}
    (hx : x ∈ southRegion) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (sphereCap ε ∘ reflectHead) x := by
  have hr : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ reflectHead x :=
    ⟨reflectHeadDiffeomorph.toPartialDiffeomorph, mem_univ _, fun _ _ ↦ rfl⟩
  exact hr.comp (𝓡 3) (Sphere 3) (isLocalDiffeomorphAt_sphereCap hε (southCap_head hx))

theorem northCap_injOn {ε : ℝ} (hε : ε ≠ 0) : InjOn (sphereCap ε) northRegion :=
  fun _ hx _ hy he ↦ sphereCap_injOn hε (northRegion_head_pos hx) (northRegion_head_pos hy) he

theorem southCap_injOn {ε : ℝ} (hε : ε ≠ 0) :
    InjOn (sphereCap ε ∘ reflectHead) southRegion := by
  intro x hx y hy he
  exact reflectHead_involutive.injective
    (sphereCap_injOn hε (southCap_head hx) (southCap_head hy) he)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε ha hprod

theorem gluedSphere_eventuallyEq_north
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
    {x : Sphere 3} (hx : x ∈ northRegion) :
    gluedSphere Φ ε a F G =ᶠ[𝓝 x] F ∘ sphereCap ε := by
  filter_upwards [isOpen_northRegion.mem_nhds hx] with y hy
  exact gluedSphere_north Φ F G hε ha hprod hleft hy

theorem gluedSphere_eventuallyEq_south
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
    {x : Sphere 3} (hx : x ∈ southRegion) :
    gluedSphere Φ ε a F G =ᶠ[𝓝 x] G ∘ (sphereCap ε ∘ reflectHead) := by
  filter_upwards [isOpen_southRegion.mem_nhds hx] with y hy
  exact gluedSphere_south Φ F G hε ha hprod hright hy

end NoExoticSixSphere.SphereSumNeck
