import Wikipedia.NoExoticSixSphere.OpenFiberCollapse

/-! # Exact equivariance of collapse under a change of fiber coordinates -/

open Function Set

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M J K Y : Type*} (τ : M × K → Y) (e : J ≃ K)

theorem injective_fiberEquiv (hi : Injective τ) :
    Injective (fun p : M × J ↦ τ (p.1, e p.2)) := by
  intro p q h
  have he := hi h
  have hm := congrArg (fun z : M × K ↦ z.1) he
  have hk := congrArg (fun z : M × K ↦ z.2) he
  exact Prod.ext hm (e.injective hk)

theorem collapse_fiberEquiv (hi : Injective τ) (y : Y) :
    collapse (fun p : M × J ↦ τ (p.1, e p.2)) y = OnePoint.map e.symm (collapse τ y) := by
  have hi' := injective_fiberEquiv τ e hi
  by_cases hy : y ∈ range τ
  · obtain ⟨⟨m, k⟩, rfl⟩ := hy
    have he : τ (m, k) = (fun p : M × J ↦ τ (p.1, e p.2)) (m, e.symm k) := by
      change τ (m, k) = τ (m, e (e.symm k))
      rw [e.apply_symm_apply]
    rw [he, collapse_apply _ hi']
    rw [← he, collapse_apply τ hi, OnePoint.map_some]
  · have hy' : y ∉ range (fun p : M × J ↦ τ (p.1, e p.2)) := by
      rintro ⟨p, hp⟩
      exact hy ⟨(p.1, e p.2), hp⟩
    rw [collapse_of_not_mem _ hy', collapse_of_not_mem _ hy, OnePoint.map_infty]

theorem collapseOnePoint_fiberEquiv (hi : Injective τ) (y : OnePoint Y) :
    collapseOnePoint (fun p : M × J ↦ τ (p.1, e p.2)) y =
      OnePoint.map e.symm (collapseOnePoint τ y) :=
  collapse_fiberEquiv (fun p ↦ (τ p : OnePoint Y)) e (OnePoint.coe_injective.comp hi) y

end NoExoticSixSphere.OpenFiberCollapse
