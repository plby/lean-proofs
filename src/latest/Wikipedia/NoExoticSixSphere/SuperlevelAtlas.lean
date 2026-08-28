import Wikipedia.NoExoticSixSphere.SuperlevelChart
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A smooth half-space atlas from actual sign-preserving normal forms

The superlevel keeps its existing subtype topology. Chart transitions agree
on the half-space model range with the actual ambient smooth transitions.
The data are later constructed from regularity, rather than assumed for the
rounded collar.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] (I : ModelWithCorners ℝ B H)
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K] (f : M → ℝ)

structure SuperlevelAtlas where
  normalForm : ∀ _ : {x : M // 0 ≤ f x}, PartialDiffeomorph I 𝓘(ℝ, ℝ × K) M (ℝ × K) ∞
  mem_source : ∀ x, x.val ∈ (normalForm x).source
  sign_iff : ∀ x y, y ∈ (normalForm x).source → (0 ≤ (normalForm x y).1 ↔ 0 ≤ f y)
  zero_iff : ∀ x y, y ∈ (normalForm x).source → ((normalForm x y).1 = 0 ↔ f y = 0)

namespace SuperlevelAtlas

variable {I f} (A : SuperlevelAtlas (K := K) I f)

def chart (x : {x : M // 0 ≤ f x}) :
    OpenPartialHomeomorph {x : M // 0 ≤ f x} (ProductHalfSpace.Space K) :=
  SuperlevelChart.chart (A.normalForm x).toOpenPartialHomeomorph (A.sign_iff x) x

theorem chart_source (x : {x : M // 0 ≤ f x}) :
    (A.chart x).source = Subtype.val ⁻¹' (A.normalForm x).source := rfl

theorem chart_target (x : {x : M // 0 ≤ f x}) :
    (A.chart x).target = Subtype.val ⁻¹' (A.normalForm x).target := rfl

theorem chart_apply_val (x y : {x : M // 0 ≤ f x}) (hy : y.val ∈ (A.normalForm x).source) :
    (A.chart x y).val = A.normalForm x y.val :=
  SuperlevelChart.chart_apply_val (A.normalForm x).toOpenPartialHomeomorph (A.sign_iff x) x y hy

theorem chart_symm_val (x : {x : M // 0 ≤ f x}) {z : ProductHalfSpace.Space K}
    (hz : z ∈ (A.chart x).target) :
    ((A.chart x).symm z).val = (A.normalForm x).symm z.val :=
  SuperlevelChart.chart_symm_val (A.normalForm x).toOpenPartialHomeomorph (A.sign_iff x) x hz

theorem mem_chart_source (x : {x : M // 0 ≤ f x}) : x ∈ (A.chart x).source := A.mem_source x

@[instance_reducible]
def chartedSpace : ChartedSpace (ProductHalfSpace.Space K) {x : M // 0 ≤ f x} where
  atlas := range A.chart
  chartAt := A.chart
  mem_chart_source := A.mem_chart_source
  chart_mem_atlas x := ⟨x, rfl⟩

def transitionDomain (x y : {x : M // 0 ≤ f x}) : Set (ℝ × K) :=
  (ProductHalfSpace.model K).symm ⁻¹' ((A.chart x).symm.trans (A.chart y)).source ∩
    range (ProductHalfSpace.model K)

theorem transition_mapsTo (x y : {x : M // 0 ≤ f x}) :
    A.transitionDomain x y ⊆ ((A.normalForm x).symm.trans (A.normalForm y)).source := by
  intro z hz
  have hnonneg : 0 ≤ z.1 := by
    have h := hz.2
    rw [ProductHalfSpace.model_range] at h
    exact h
  have hval := ProductHalfSpace.model_symm_val K hnonneg
  have hz₁ : (ProductHalfSpace.model K).symm z ∈ (A.chart x).target := hz.1.1
  have hz₂ : ((A.chart x).symm ((ProductHalfSpace.model K).symm z)).val ∈
      (A.normalForm y).source := hz.1.2
  have hz₁' : ((ProductHalfSpace.model K).symm z).val ∈ (A.normalForm x).target := hz₁
  rw [A.chart_symm_val x hz₁, hval] at hz₂
  rw [hval] at hz₁'
  exact ⟨hz₁', hz₂⟩

theorem transition_eq (x y : {x : M // 0 ≤ f x}) {z : ℝ × K}
    (hz : z ∈ A.transitionDomain x y) :
    ProductHalfSpace.model K (((A.chart x).symm.trans (A.chart y))
      ((ProductHalfSpace.model K).symm z)) =
        ((A.normalForm x).symm.trans (A.normalForm y)) z := by
  have hnonneg : 0 ≤ z.1 := by
    have h := hz.2
    rw [ProductHalfSpace.model_range] at h
    exact h
  have hval := ProductHalfSpace.model_symm_val K hnonneg
  change (A.chart y ((A.chart x).symm ((ProductHalfSpace.model K).symm z))).val =
    A.normalForm y ((A.normalForm x).symm z)
  have hz₁ : (ProductHalfSpace.model K).symm z ∈ (A.chart x).target := hz.1.1
  have hz₂ : ((A.chart x).symm ((ProductHalfSpace.model K).symm z)).val ∈
      (A.normalForm y).source := hz.1.2
  rw [A.chart_apply_val y _ hz₂, A.chart_symm_val x hz₁, hval]

theorem contDiffOn_transition (x y : {x : M // 0 ≤ f x}) :
    ContDiffOn ℝ ∞ (ProductHalfSpace.model K ∘ ((A.chart x).symm.trans (A.chart y)) ∘
      (ProductHalfSpace.model K).symm) (A.transitionDomain x y) :=
  (((A.normalForm x).symm.trans (A.normalForm y)).contMDiffOn_toFun.contDiffOn.mono
    (A.transition_mapsTo x y)).congr (fun _ hz ↦ A.transition_eq x y hz)

theorem isManifold : letI := A.chartedSpace;
    IsManifold (ProductHalfSpace.model K) ∞ {x : M // 0 ≤ f x} := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn (ProductHalfSpace.model K) ∞ {x : M // 0 ≤ f x}
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  exact A.contDiffOn_transition x y

end SuperlevelAtlas

end NoExoticSixSphere
