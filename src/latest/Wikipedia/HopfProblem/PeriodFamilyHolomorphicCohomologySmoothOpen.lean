import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothBase

/-!
# Real calculus in the unchanged open-base product charts

A real-smooth ambient function on the full first-coordinate preimage of an
open complex base defines a real-smooth map on that base times its original
normed fibre. This uses only the inherited open chart and the usual product
chart; no period-dependent atlas is introduced.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

/-- The literal full preimage of the original open base in a product chart. -/
def baseProductDomain (U : Opens ℂ) (F : Type*) : Set (ℂ × F) :=
  Prod.fst ⁻¹' (U : Set ℂ)

@[simp] theorem mem_baseProductDomain (U : Opens ℂ) (F : Type*) (x : ℂ × F) :
    x ∈ baseProductDomain U F ↔ x.1 ∈ U := Iff.rfl

theorem baseProductDomain_isOpen (U : Opens ℂ) (F : Type*) [TopologicalSpace F] :
    IsOpen (baseProductDomain U F) := U.isOpen.preimage continuous_fst

variable {U : Opens ℂ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance smoothOpenProductChartedSpace : ChartedSpace (ℂ × F) (U × F) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ F) (U × F))

/-- The literal open-base inclusion is real smooth in the original product chart. -/
theorem productOpenInclusion_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × F)) (modelWithCornersSelf ℝ (ℂ × F)) ∞
      (fun x : U × F => ((x.1 : ℂ), x.2)) := by
  have hval : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (Subtype.val : U → ℂ) := contMDiff_subtype_val
  have hfst : ContMDiff (modelWithCornersSelf ℝ (ℂ × F))
      (modelWithCornersSelf ℝ ℂ) ∞ (Prod.fst : U × F → U) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hsnd : ContMDiff (modelWithCornersSelf ℝ (ℂ × F))
      (modelWithCornersSelf ℝ F) ∞ (Prod.snd : U × F → F) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  exact (hval.comp hfst).prodMk_space hsnd

/-- Ambient real smoothness on the actual open domain gives real smoothness
on the unchanged native open-base product. -/
theorem contMDiff_productOpen_of_contDiffOn {f : ℂ × F → G}
    (hf : ContDiffOn ℝ ∞ f (baseProductDomain U F)) :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × F)) (modelWithCornersSelf ℝ G) ∞
      (fun x : U × F => f ((x.1 : ℂ), x.2)) := by
  rw [← contMDiffOn_univ]
  exact hf.contMDiffOn.comp (productOpenInclusion_contMDiff (U := U) (F := F)).contMDiffOn
    (fun x _ => x.1.property)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
