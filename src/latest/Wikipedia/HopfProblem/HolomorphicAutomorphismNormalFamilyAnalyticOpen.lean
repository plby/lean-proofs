import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticBasic

/-!
# Holomorphic functions on open subsets of three complex variables

Every point admits an actual closed polydisc contained in the open set.
The triple Cauchy formula on that polydisc gives analyticity near the
point and therefore on the entire open set.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

/-- Complex differentiability on an open subset of three product
coordinates implies genuine joint analyticity. -/
theorem analyticOnNhd_product_of_differentiableOn {f : ProductModel → ℂ}
    {s : Set ProductModel} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  let g : ProductModel → ℂ := fun w => f (z + w)
  have hmem (w : ProductModel) (hw : w ∈ closedCube r) : z + w ∈ s := by
    apply hball
    have hw' : w ∈ closedBall (0 : ProductModel) r := by
      simpa only [closedCube, Prod.zero_eq_mk, closedBall_prod_same] using hw
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw'
  have hg : DifferentiableOn ℂ g (closedCube r) :=
    hf.comp ((differentiable_const z).add differentiable_id).differentiableOn hmem
  have hga₀ : AnalyticAt ℂ g (0 : ProductModel) :=
    analyticOnNhd_cube_of_differentiableOn hr hg 0
      ⟨mem_ball_self hr, mem_ball_self hr, mem_ball_self hr⟩
  have hga : AnalyticAt ℂ g (z - z) := by simpa only [sub_self] using hga₀
  have hshift : AnalyticAt ℂ (fun w : ProductModel => w - z) z :=
    analyticAt_id.sub analyticAt_const
  have hres : AnalyticAt ℂ (fun w => g (w - z)) z :=
    AnalyticAt.comp (f := fun w : ProductModel => w - z) hga hshift
  have heq : (fun w => g (w - z)) = f := by
    funext w
    dsimp only [g]
    congr 1
    abel
  rwa [heq] at hres

theorem analyticOnNhd_product_iff_differentiableOn {f : ProductModel → ℂ}
    {s : Set ProductModel} (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_product_of_differentiableOn hs⟩

theorem contDiffOn_product_of_differentiableOn {f : ProductModel → ℂ}
    {s : Set ProductModel} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℂ ω f s :=
  (analyticOnNhd_product_of_differentiableOn hs hf).contDiffOn_of_completeSpace

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
