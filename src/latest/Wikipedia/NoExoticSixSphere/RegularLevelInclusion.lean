import Wikipedia.NoExoticSixSphere.RegularLevelAtlas

/-!
# Smooth inclusion and the smooth-map criterion for regular level sets

The constructed level atlas makes the actual subtype inclusion smooth.
A map into the level set is smooth exactly when its ambient-valued map is
smooth; this identifies the atlas with the intended embedded smooth structure.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.RegularLevelAtlas

variable {B H M F K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → F} (A : RegularLevelAtlas (K := K) I f)

theorem contMDiffOn_chartInverse_val (x : {x : M // f x = 0}) :
    ContMDiffOn 𝓘(ℝ, K) I ∞ (fun z ↦ ((A.chart x).symm z).val) (A.chart x).target := by
  have hj : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, F × K) ∞ (fun z : K ↦ ((0 : F), z)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  have h := (A.normalForm x).contMDiffOn_invFun.comp
    hj.contMDiffOn (fun _ hz ↦ hz)
  exact h.congr (fun z hz ↦ A.chart_symm_val x hz)

theorem contMDiff_subtype_val : letI := A.chartedSpace;
    ContMDiff 𝓘(ℝ, K) I ∞ ((↑) : {x : M // f x = 0} → M) := by
  let := A.chartedSpace
  let := A.isManifold
  intro x
  rw [contMDiffAt_iff_source]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, range_id,
    contMDiffWithinAt_univ]
  change ContMDiffAt 𝓘(ℝ, K) I ∞ (fun z ↦ ((A.chart x).symm z).val) (A.chart x x)
  exact (A.contMDiffOn_chartInverse_val x).contMDiffAt
    ((A.chart x).open_target.mem_nhds ((A.chart x).map_source (A.mem_chart_source x)))

variable {B' H' N : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ B' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

theorem contMDiffAt_iff_ambient (g : N → {x : M // f x = 0}) (x : N) :
    letI := A.chartedSpace;
    ContMDiffAt J 𝓘(ℝ, K) ∞ g x ↔ ContMDiffAt J I ∞ (fun z ↦ (g z).val) x := by
  let := A.chartedSpace
  let := A.isManifold
  constructor
  · intro hg
    exact A.contMDiff_subtype_val.contMDiffAt.comp x hg
  · intro hg
    rw [contMDiffAt_iff_target]
    refine ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    change ContMDiffAt J 𝓘(ℝ, K) ∞ (fun z ↦ (A.normalForm (g x) (g z).val).2) x
    have hnormal := (A.normalForm (g x)).contMDiffOn_toFun.contMDiffAt
      ((A.normalForm (g x)).open_source.mem_nhds (A.mem_source (g x)))
    exact contDiff_snd.contMDiff.contMDiffAt.comp x (hnormal.comp x hg)

theorem contMDiff_iff_ambient (g : N → {x : M // f x = 0}) :
    letI := A.chartedSpace;
    ContMDiff J 𝓘(ℝ, K) ∞ g ↔ ContMDiff J I ∞ (fun z ↦ (g z).val) := by
  let := A.chartedSpace
  exact forall_congr' (fun x ↦ A.contMDiffAt_iff_ambient g x)

end NoExoticSixSphere.RegularLevelAtlas
