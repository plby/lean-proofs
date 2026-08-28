import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Native tangent coordinates on the Riemann sphere

The two affine coordinates below are the coordinates of the actual tangent
bundle trivializations of the standard analytic sphere.
-/

open Set Topology TopologicalSpace Bundle OnePoint
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields

def chartCenter (b : Bool) : RiemannSphere := if b then ∞ else (0 : ℂ)

theorem preferredChart_chartCenter (b : Bool) :
    standardCharts.preferredChart (chartCenter b) = b := by
  classical
  cases b <;> simp [chartCenter, TwoAffineCharts.preferredChart, standardCharts]

theorem chartAt_chartCenter (b : Bool) :
    chartAt ℂ (chartCenter b) = (standardCharts.parametrization b).symm := by
  change (standardCharts.parametrization
    (standardCharts.preferredChart (chartCenter b))).symm = _
  rw [preferredChart_chartCenter]

noncomputable def chartOpen (b : Bool) : Opens RiemannSphere :=
  ⟨(chartAt ℂ (chartCenter b)).source, (chartAt ℂ (chartCenter b)).open_source⟩

theorem chartOpen_eq_range (b : Bool) :
    (chartOpen b : Set RiemannSphere) = range (standardCharts.affineMap b) := by
  change (chartAt ℂ (chartCenter b)).source = _
  rw [chartAt_chartCenter]
  exact standardCharts.parametrization_target b

theorem mem_chartOpen_cover (y : RiemannSphere) :
    y ∈ chartOpen false ∨ y ∈ chartOpen true := by
  change y ∈ (chartOpen false : Set _) ∨ y ∈ (chartOpen true : Set _)
  rw [chartOpen_eq_range, chartOpen_eq_range]
  exact standardCharts.covered y

noncomputable def parametrization (b : Bool) (z : ℂ) : chartOpen b :=
  ⟨standardCharts.affineMap b z, by
    change standardCharts.affineMap b z ∈ (chartOpen b : Set _)
    rw [chartOpen_eq_range]
    exact mem_range_self z⟩

theorem parametrization_coe (b : Bool) (z : ℂ) :
    (parametrization b z : RiemannSphere) = standardCharts.affineMap b z := rfl

theorem parametrization_surjective (b : Bool) : Function.Surjective (parametrization b) := by
  intro y
  have hy := y.property
  change (y : RiemannSphere) ∈ (chartOpen b : Set _) at hy
  rw [chartOpen_eq_range] at hy
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, Subtype.ext hz⟩

theorem parametrization_holomorphic (b : Bool) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (parametrization b) := by
  intro z
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ parametrization b) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (parametrization b) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (standardCharts.affineMap_holomorphic b z)

noncomputable def coordinate (b : Bool) (y : RiemannSphere)
    (v : TangentSpace 𝓘(ℂ) y) : ℂ :=
  (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b) ⟨y, v⟩).2

theorem coordinate_eq_continuousLinearMapAt (b : Bool) {y : RiemannSphere}
    (hy : y ∈ chartOpen b) (v : TangentSpace 𝓘(ℂ) y) :
    coordinate b y v =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).continuousLinearMapAt ℂ y v := by
  exact ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).continuousLinearMapAt_apply_of_mem
    ℂ hy v).symm

theorem coordinate_injective (b : Bool) {y : RiemannSphere} (hy : y ∈ chartOpen b) :
    Function.Injective (coordinate b y) := by
  exact ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).linearEquivAt
    ℂ y hy).injective

theorem coordinate_add (b : Bool) {y : RiemannSphere} (hy : y ∈ chartOpen b)
    (v w : TangentSpace 𝓘(ℂ) y) :
    coordinate b y (v + w) = coordinate b y v + coordinate b y w := by
  simp only [coordinate_eq_continuousLinearMapAt b hy, map_add]

theorem coordinate_smul (b : Bool) {y : RiemannSphere} (hy : y ∈ chartOpen b)
    (c : ℂ) (v : TangentSpace 𝓘(ℂ) y) :
    coordinate b y (c • v) = c * coordinate b y v := by
  simp only [coordinate_eq_continuousLinearMapAt b hy, map_smul, smul_eq_mul]

theorem coordinate_eq_mfderiv (b : Bool) {y : RiemannSphere}
    (hy : y ∈ chartOpen b) (v : TangentSpace 𝓘(ℂ) y) :
    coordinate b y v = mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) y v := by
  rw [coordinate_eq_continuousLinearMapAt b hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hy]
  rfl

theorem coordinate_eq_tangentCoordChange (b : Bool) (y : RiemannSphere)
    (v : TangentSpace 𝓘(ℂ) y) :
    coordinate b y v = tangentCoordChange 𝓘(ℂ) y (chartCenter b) y v := rfl

theorem extChartAt_chartCenter_apply (b : Bool) (y : RiemannSphere) :
    extChartAt 𝓘(ℂ) (chartCenter b) y = (standardCharts.parametrization b).symm y := by
  change chartAt ℂ (chartCenter b) y = _
  rw [chartAt_chartCenter]

theorem extChartAt_chartCenter_symm_apply (b : Bool) (z : ℂ) :
    (extChartAt 𝓘(ℂ) (chartCenter b)).symm z = standardCharts.affineMap b z := by
  change (chartAt ℂ (chartCenter b)).symm z = _
  rw [chartAt_chartCenter]
  rfl

theorem extChartAt_chartCenter_affineMap (b : Bool) (z : ℂ) :
    extChartAt 𝓘(ℂ) (chartCenter b) (standardCharts.affineMap b z) = z := by
  rw [extChartAt_chartCenter_apply, TwoAffineCharts.parametrization_symm_apply]

theorem coe_mem_chartOpen_false (z : ℂ) : (z : RiemannSphere) ∈ chartOpen false := by
  change (z : RiemannSphere) ∈ (chartOpen false : Set _)
  rw [chartOpen_eq_range]
  exact ⟨z, rfl⟩

theorem coe_mem_chartOpen_true {z : ℂ} (hz : z ≠ 0) :
    (z : RiemannSphere) ∈ chartOpen true := by
  change (z : RiemannSphere) ∈ (chartOpen true : Set _)
  rw [chartOpen_eq_range]
  exact ⟨z⁻¹, (standardCharts.affineMap_inversion false z hz).symm⟩

theorem extChartAt_chartCenter_transition {z : ℂ} (hz : z ≠ 0) :
    (extChartAt 𝓘(ℂ) (chartCenter true) ∘
      (extChartAt 𝓘(ℂ) (chartCenter false)).symm) z = z⁻¹ := by
  rw [Function.comp_apply, extChartAt_chartCenter_symm_apply,
    standardCharts.affineMap_inversion false z hz]
  exact extChartAt_chartCenter_affineMap true z⁻¹

theorem tangentCoordChange_false_true {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    tangentCoordChange 𝓘(ℂ) (chartCenter false) (chartCenter true) (z : RiemannSphere) v =
      -(z ^ 2)⁻¹ * v := by
  have heq : (extChartAt 𝓘(ℂ) (chartCenter true) ∘
      (extChartAt 𝓘(ℂ) (chartCenter false)).symm) =ᶠ[𝓝 z] (fun t : ℂ => t⁻¹) := by
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with t ht
    exact extChartAt_chartCenter_transition ht
  rw [tangentCoordChange_def]
  simp only [modelWithCornersSelf_coe, range_id]
  change fderivWithin ℂ (extChartAt 𝓘(ℂ) (chartCenter true) ∘
      (extChartAt 𝓘(ℂ) (chartCenter false)).symm) Set.univ
    (extChartAt 𝓘(ℂ) (chartCenter false) (standardCharts.affineMap false z)) v = _
  rw [extChartAt_chartCenter_affineMap, fderivWithin_univ, heq.fderiv_eq,
    fderiv_eq_deriv_mul, deriv_inv]

theorem coordinate_transition {w : ℂ} (hw : w ≠ 0)
    (v : TangentSpace 𝓘(ℂ) ((w⁻¹ : ℂ) : RiemannSphere)) :
    coordinate true ((w⁻¹ : ℂ) : RiemannSphere) v =
      -(w ^ 2) * coordinate false ((w⁻¹ : ℂ) : RiemannSphere) v := by
  have hfalse := coe_mem_chartOpen_false w⁻¹
  have htrue := coe_mem_chartOpen_true (inv_ne_zero hw)
  have hcomp := tangentCoordChange_comp (I := 𝓘(ℂ))
    (w := ((w⁻¹ : ℂ) : RiemannSphere)) (x := chartCenter false)
    (y := chartCenter true) (z := ((w⁻¹ : ℂ) : RiemannSphere)) (v := v)
    ⟨⟨mem_extChartAt_source _, by rw [extChartAt_source]; exact hfalse⟩,
      by rw [extChartAt_source]; exact htrue⟩
  rw [coordinate_eq_tangentCoordChange, coordinate_eq_tangentCoordChange, ← hcomp,
    tangentCoordChange_false_true (inv_ne_zero hw)]
  simp only [inv_pow, inv_inv]

end Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields
