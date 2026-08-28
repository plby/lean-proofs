import Wikipedia.NoExoticSixSphere.RegularLevelChart
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth atlas of an actual regular level set

Local smooth normal forms restrict to charts of the zero fiber with its
subspace topology. Their transitions are restrictions of the ambient smooth
partial diffeomorphisms, composed with the zero-slice inclusion and projection.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere

variable {B H M F K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] (I : ModelWithCorners ℝ B H)
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
  (f : M → F)

structure RegularLevelAtlas where
  normalForm : ∀ _ : {x : M // f x = 0}, PartialDiffeomorph I 𝓘(ℝ, F × K) M (F × K) ∞
  mem_source : ∀ x, (x : M) ∈ (normalForm x).source
  first_eq : ∀ x y, y ∈ (normalForm x).source → (normalForm x y).1 = f y

namespace RegularLevelAtlas

variable {I f} (A : RegularLevelAtlas (K := K) I f)

noncomputable def chart (x : {x : M // f x = 0}) : OpenPartialHomeomorph {x : M // f x = 0} K :=
  RegularLevelChart.chart (A.normalForm x).toOpenPartialHomeomorph (A.first_eq x) x

theorem chart_source (x : {x : M // f x = 0}) : (A.chart x).source =
    ((↑) : {x : M // f x = 0} → M) ⁻¹' (A.normalForm x).source := rfl

theorem chart_target (x : {x : M // f x = 0}) : (A.chart x).target =
    (fun z : K ↦ (0, z)) ⁻¹' (A.normalForm x).target := rfl

theorem chart_apply (x y : {x : M // f x = 0}) : A.chart x y = (A.normalForm x y).2 := rfl

theorem chart_symm_val (x : {x : M // f x = 0}) {z : K} (hz : z ∈ (A.chart x).target) :
    ((A.chart x).symm z).val = (A.normalForm x).symm (0, z) :=
  RegularLevelChart.chart_symm_val (A.normalForm x).toOpenPartialHomeomorph (A.first_eq x) x hz

theorem mem_chart_source (x : {x : M // f x = 0}) : x ∈ (A.chart x).source := A.mem_source x

@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace K {x : M // f x = 0} where
  atlas := range A.chart
  chartAt := A.chart
  mem_chart_source := A.mem_chart_source
  chart_mem_atlas x := ⟨x, rfl⟩

theorem transition_mapsTo (x y : {x : M // f x = 0}) :
    MapsTo (fun z : K ↦ (0, z)) ((A.chart x).symm.trans (A.chart y)).source
      (((A.normalForm x).symm).trans (A.normalForm y)).source := by
  intro z hz
  change z ∈ (A.chart x).target ∧ (A.chart x).symm z ∈ (A.chart y).source at hz
  change (0, z) ∈ (A.normalForm x).target ∧
    (A.normalForm x).symm (0, z) ∈ (A.normalForm y).source
  refine ⟨hz.1, ?_⟩
  have h := hz.2
  change ((A.chart x).symm z).val ∈ (A.normalForm y).source at h
  rwa [A.chart_symm_val x hz.1] at h

theorem transition_eq (x y : {x : M // f x = 0}) {z : K}
    (hz : z ∈ ((A.chart x).symm.trans (A.chart y)).source) :
    ((A.chart x).symm.trans (A.chart y)) z =
      ((((A.normalForm x).symm).trans (A.normalForm y)) (0, z)).2 := by
  change (A.normalForm y ((A.chart x).symm z).val).2 =
    (A.normalForm y ((A.normalForm x).symm (0, z))).2
  rw [A.chart_symm_val x hz.1]

theorem contDiffOn_transition (x y : {x : M // f x = 0}) :
    ContDiffOn ℝ ∞ ((A.chart x).symm.trans (A.chart y))
      ((A.chart x).symm.trans (A.chart y)).source := by
  let Φ := ((A.normalForm x).symm).trans (A.normalForm y)
  have h := Φ.contMDiffOn_toFun.contDiffOn.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (A.transition_mapsTo x y)
  exact (contDiff_snd.comp_contDiffOn h).congr (fun z hz ↦ A.transition_eq x y hz)

theorem isManifold : letI := A.chartedSpace; IsManifold 𝓘(ℝ, K) ∞ {x : M // f x = 0} := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn 𝓘(ℝ, K) ∞ {x : M // f x = 0}
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using
    A.contDiffOn_transition x y

end RegularLevelAtlas
end NoExoticSixSphere
