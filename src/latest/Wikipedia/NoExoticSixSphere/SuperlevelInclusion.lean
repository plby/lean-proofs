import Wikipedia.NoExoticSixSphere.SuperlevelAtlas

/-!
# Smooth maps into the constructed superlevel manifold

The actual subtype inclusion is smooth. A map into the superlevel manifold
is smooth precisely when its ambient-valued map is smooth. All chart
identifications are restricted to their proved open sources.
-/

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SuperlevelAtlas

variable {B H M K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)

theorem contMDiffOn_chartInverse_val (x : {x : M // 0 ≤ f x}) :
    ContMDiffOn (ProductHalfSpace.model K) I ∞
      (fun z ↦ ((A.chart x).symm z).val) (A.chart x).target := by
  have h := (A.normalForm x).contMDiffOn_invFun.comp
    (ProductHalfSpace.model K).contMDiff.contMDiffOn (fun _ hz ↦ hz)
  exact h.congr (fun _ hz ↦ A.chart_symm_val x hz)

theorem contMDiff_subtype_val : letI := A.chartedSpace;
    ContMDiff (ProductHalfSpace.model K) I ∞ ((↑) : {x : M // 0 ≤ f x} → M) := by
  let := A.chartedSpace
  let := A.isManifold
  intro x
  have hc : ContMDiffAt (ProductHalfSpace.model K) (ProductHalfSpace.model K) ∞
      (A.chart x) x :=
    (contMDiffOn_chart (I := ProductHalfSpace.model K) (n := ∞) (x := x)).contMDiffAt
      ((A.chart x).open_source.mem_nhds (A.mem_chart_source x))
  have hi := (A.contMDiffOn_chartInverse_val x).contMDiffAt
    ((A.chart x).open_target.mem_nhds ((A.chart x).map_source (A.mem_chart_source x)))
  apply (hi.comp x hc).congr_of_eventuallyEq
  filter_upwards [(A.chart x).open_source.mem_nhds (A.mem_chart_source x)] with y hy
  exact (congrArg Subtype.val ((A.chart x).left_inv hy)).symm

variable {B' H' N : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ B' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

theorem contMDiffAt_iff_ambient (g : N → {x : M // 0 ≤ f x}) (x : N) :
    letI := A.chartedSpace;
    ContMDiffAt J (ProductHalfSpace.model K) ∞ g x ↔
      ContMDiffAt J I ∞ (fun z ↦ (g z).val) x := by
  let := A.chartedSpace
  let := A.isManifold
  constructor
  · intro hg
    exact A.contMDiff_subtype_val.contMDiffAt.comp x hg
  · intro hg
    rw [contMDiffAt_iff_target]
    refine ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
    have hn := (A.normalForm (g x)).contMDiffOn_toFun.contMDiffAt
      ((A.normalForm (g x)).open_source.mem_nhds (A.mem_source (g x)))
    apply (hn.comp x hg).congr_of_eventuallyEq
    filter_upwards [hg.continuousAt
      ((A.normalForm (g x)).open_source.mem_nhds (A.mem_source (g x)))] with z hz
    change (A.chart (g x) (g z)).val = A.normalForm (g x) (g z).val
    exact A.chart_apply_val (g x) (g z) hz

theorem contMDiff_iff_ambient (g : N → {x : M // 0 ≤ f x}) :
    letI := A.chartedSpace;
    ContMDiff J (ProductHalfSpace.model K) ∞ g ↔
      ContMDiff J I ∞ (fun z ↦ (g z).val) := by
  let := A.chartedSpace
  exact forall_congr' (fun x ↦ A.contMDiffAt_iff_ambient g x)

end NoExoticSixSphere.SuperlevelAtlas
