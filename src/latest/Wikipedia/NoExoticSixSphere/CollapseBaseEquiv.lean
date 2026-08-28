import Wikipedia.NoExoticSixSphere.OpenFiberCollapse

/-! # Changing only the base parametrization leaves the collapse map unchanged -/

open Set Function

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M N K Y : Type*} (τ : M × K → Y) (e : N ≃ M)

theorem collapse_baseEquiv (hi : Injective τ) (y : Y) :
    collapse (fun p : N × K ↦ τ (e p.1, p.2)) y = collapse τ y := by
  have hi' : Injective (fun p : N × K ↦ τ (e p.1, p.2)) := by
    intro p q h
    have he := hi h
    exact Prod.ext (e.injective (congrArg (fun z : M × K ↦ z.1) he))
      (congrArg (fun z : M × K ↦ z.2) he)
  by_cases hy : y ∈ range τ
  · obtain ⟨⟨m, k⟩, rfl⟩ := hy
    have he : τ (m, k) = (fun p : N × K ↦ τ (e p.1, p.2)) (e.symm m, k) := by
      change τ (m, k) = τ (e (e.symm m), k)
      rw [e.apply_symm_apply]
    rw [he, collapse_apply _ hi']
    rw [← he, collapse_apply τ hi]
  · have hy' : y ∉ range (fun p : N × K ↦ τ (e p.1, p.2)) := by
      rintro ⟨p, hp⟩
      exact hy ⟨(e p.1, p.2), hp⟩
    rw [collapse_of_not_mem _ hy', collapse_of_not_mem _ hy]

theorem collapseOnePoint_baseEquiv (hi : Injective τ) (y : OnePoint Y) :
    collapseOnePoint (fun p : N × K ↦ τ (e p.1, p.2)) y = collapseOnePoint τ y :=
  collapse_baseEquiv (fun p ↦ (τ p : OnePoint Y)) e (OnePoint.coe_injective.comp hi) y

end NoExoticSixSphere.OpenFiberCollapse
