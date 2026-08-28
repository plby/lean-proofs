import Wikipedia.NoExoticSixSphere.OpenFiberCollapse

/-! # Exact equivariance of tube collapse under an ambient coordinate change -/

open Function Set

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M K Y Z : Type*} (τ : M × K → Y)

theorem collapse_ambientEquiv (e : Y ≃ Z) (hi : Injective τ) (y : Y) :
    collapse (e ∘ τ) (e y) = collapse τ y := by
  by_cases hy : y ∈ range τ
  · obtain ⟨p, rfl⟩ := hy
    change collapse (e ∘ τ) ((e ∘ τ) p) = collapse τ (τ p)
    rw [collapse_apply _ (e.injective.comp hi), collapse_apply τ hi]
  · have hn : e y ∉ range (e ∘ τ) := by
      rintro ⟨p, hp⟩
      exact hy ⟨p, e.injective hp⟩
    rw [collapse_of_not_mem _ hn, collapse_of_not_mem _ hy]

variable [TopologicalSpace Y] [TopologicalSpace Z]

theorem collapseOnePoint_ambientEquiv (e : Y ≃ₜ Z) (hi : Injective τ) (y : OnePoint Y) :
    collapseOnePoint (e ∘ τ) (e.onePointCongr y) = collapseOnePoint τ y := by
  change collapse (e.onePointCongr ∘ (fun p : M × K ↦ (τ p : OnePoint Y)))
    (e.onePointCongr y) = collapse (fun p : M × K ↦ (τ p : OnePoint Y)) y
  exact collapse_ambientEquiv _ e.onePointCongr.toEquiv (OnePoint.coe_injective.comp hi) y

end NoExoticSixSphere.OpenFiberCollapse
