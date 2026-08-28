import Wikipedia.NoExoticSixSphere.SphereRemainderChartFormula

/-!
# Actual product-chart sheet germs on the removed source disks

Membership in a removed disk supplies the original inverse source chart and
its domain. The sheet identities therefore give equality on a neighborhood,
not just equality at the point. These germs can be differentiated in the
original sphere atlas.
-/

noncomputable section

open Set Function Metric Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def leftSourceCoordinate (x : Sphere 3) : Vector 3 × Vector 3 := (sourceChart.symm x, 0)

def rightSourceCoordinate (x : Sphere 3) : Vector 3 × Vector 3 := (0, sourceChart.symm x)

theorem removedSourceDisk_subset_chartTarget (ε : ℝ) :
    removedSourceDisk ε ⊆ sourceChart.target := by
  rintro x ⟨v, _, rfl⟩
  apply sourceChart.map_source
  rw [sourceChart_source]
  trivial

theorem contMDiffAt_leftSourceCoordinate {ε : ℝ} {x : Sphere 3}
    (hx : x ∈ removedSourceDisk ε) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ leftSourceCoordinate x :=
  (sourceChart.symm.contMDiffOn_toFun.contMDiffAt
    (sourceChart.open_target.mem_nhds
      (removedSourceDisk_subset_chartTarget ε hx))).prodMk_space contMDiffAt_const

theorem contMDiffAt_rightSourceCoordinate {ε : ℝ} {x : Sphere 3}
    (hx : x ∈ removedSourceDisk ε) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ rightSourceCoordinate x :=
  contMDiffAt_const.prodMk_space (sourceChart.symm.contMDiffOn_toFun.contMDiffAt
    (sourceChart.open_target.mem_nhds (removedSourceDisk_subset_chartTarget ε hx)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  {ε : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε hprod in
theorem leftSourceCoordinate_mem_source {x : Sphere 3} (hx : x ∈ removedSourceDisk ε) :
    leftSourceCoordinate x ∈ Φ.source :=
  hprod ⟨ball_subset_closedBall (sourceCoordinate_of_removed hx).2,
    mem_closedBall_self (by positivity)⟩

include hε hprod in
theorem rightSourceCoordinate_mem_source {x : Sphere 3} (hx : x ∈ removedSourceDisk ε) :
    rightSourceCoordinate x ∈ Φ.source :=
  hprod ⟨mem_closedBall_self (by positivity),
    ball_subset_closedBall (sourceCoordinate_of_removed hx).2⟩

include hε hprod in
theorem leftSheet_eventuallyEq (F : Sphere 3 → M)
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
    {x : Sphere 3} (hx : x ∈ removedSourceDisk ε) :
    F =ᶠ[𝓝 x] Φ ∘ leftSourceCoordinate := by
  have hs := leftSourceCoordinate_mem_source Φ hε hprod hx
  have hb : ∀ᶠ y in 𝓝 x, leftSourceCoordinate y ∈ Φ.source :=
    (contMDiffAt_leftSourceCoordinate hx).continuousAt.eventually (Φ.open_source.mem_nhds hs)
  filter_upwards [hb,
    sourceChart.open_target.mem_nhds (removedSourceDisk_subset_chartTarget ε hx)] with y hy hyt
  exact (congrArg F (sourceChart.right_inv hyt)).symm.trans
    (hleft (sourceChart.symm y) hy).symm

include hε hprod in
theorem rightSheet_eventuallyEq (G : Sphere 3 → M)
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
    {x : Sphere 3} (hx : x ∈ removedSourceDisk ε) :
    G =ᶠ[𝓝 x] Φ ∘ rightSourceCoordinate := by
  have hs := rightSourceCoordinate_mem_source Φ hε hprod hx
  have hb : ∀ᶠ y in 𝓝 x, rightSourceCoordinate y ∈ Φ.source :=
    (contMDiffAt_rightSourceCoordinate hx).continuousAt.eventually (Φ.open_source.mem_nhds hs)
  filter_upwards [hb,
    sourceChart.open_target.mem_nhds (removedSourceDisk_subset_chartTarget ε hx)] with y hy hyt
  exact (congrArg G (sourceChart.right_inv hyt)).symm.trans
    (hright (sourceChart.symm y) hy).symm

end NoExoticSixSphere.SphereSumNeck
