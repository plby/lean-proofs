import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra
import Mathlib.Tactic.Abel

/-!
# Integral normalization of a three-overlap Mayer--Vietoris map

The map `(a,b,c) ↦ (a+b+c, -(a+P b+Q c))` is reduced by explicit
invertible integral changes of coordinates to the identity together with
`(b,c) ↦ (P-id)b+(Q-id)c`. No freeness or finite generation is needed.
-/

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

open PeriodTorusHigherHomology

variable (H : Type*) [AddCommGroup H]

/-- The source coordinate change records the sum on the first component. -/
def columnEquiv : (H × (H × H)) ≃ₗ[ℤ] (H × (H × H)) :=
  ({ toFun := fun x => (x.1 + x.2.1 + x.2.2, x.2)
     invFun := fun x => (x.1 - x.2.1 - x.2.2, x.2)
     left_inv := by
       rintro ⟨a, b, c⟩
       apply Prod.ext
       · dsimp; abel
       · rfl
     right_inv := by
       rintro ⟨a, b, c⟩
       apply Prod.ext
       · dsimp; abel
       · rfl
     map_add' := by
       rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
       apply Prod.ext
       · dsimp; abel
       · rfl
   } : (H × (H × H)) ≃+ (H × (H × H))).toIntLinearEquiv

@[simp] theorem columnEquiv_apply (x : H × (H × H)) :
    columnEquiv H x = (x.1 + x.2.1 + x.2.2, x.2) := rfl

@[simp] theorem columnEquiv_symm_apply (x : H × (H × H)) :
    (columnEquiv H).symm x = (x.1 - x.2.1 - x.2.2, x.2) := rfl

/-- The target coordinate change is an integral involution. -/
def rowEquiv : (H × H) ≃ₗ[ℤ] (H × H) :=
  ({ toFun := fun x => (x.1, -x.1 - x.2)
     invFun := fun x => (x.1, -x.1 - x.2)
     left_inv := by
       rintro ⟨a, b⟩
       apply Prod.ext
       · rfl
       · dsimp; abel
     right_inv := by
       rintro ⟨a, b⟩
       apply Prod.ext
       · rfl
       · dsimp; abel
     map_add' := by
       rintro ⟨a, b⟩ ⟨a', b'⟩
       apply Prod.ext
       · rfl
       · dsimp; abel
   } : (H × H) ≃+ (H × H)).toIntLinearEquiv

@[simp] theorem rowEquiv_apply (x : H × H) :
    rowEquiv H x = (x.1, -x.1 - x.2) := rfl

@[simp] theorem rowEquiv_symm_apply (x : H × H) :
    (rowEquiv H).symm x = (x.1, -x.1 - x.2) := rfl

variable {H} [Module ℤ H] (P Q : H →ₗ[ℤ] H)

/-- The two monodromy differences combined into one actual linear map. -/
def delta : (H × H) →ₗ[ℤ] H :=
  intLinearMapOfAddHom
    { toFun x := (P x.1 - x.1) + (Q x.2 - x.2)
      map_zero' := by simp
      map_add' x y := by
        dsimp
        rw [map_add, map_add]
        abel }

@[simp] theorem delta_apply (x : H × H) :
    delta P Q x = (P x.1 - x.1) + (Q x.2 - x.2) := rfl

/-- The actual integral map associated with three normalized overlap components. -/
def overlapMap : (H × (H × H)) →ₗ[ℤ] (H × H) :=
  intLinearMapOfAddHom
    { toFun x := (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2))
      map_zero' := by simp
      map_add' x y := by
        apply Prod.ext
        · dsimp; abel
        · dsimp
          rw [map_add, map_add]
          abel }

@[simp] theorem overlapMap_apply (x : H × (H × H)) :
    overlapMap P Q x =
      (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2)) := rfl

/-- The row change separates the sum coordinate from the monodromy differences. -/
theorem row_overlapMap (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q x) = (x.1 + x.2.1 + x.2.2, delta P Q x.2) := by
  apply Prod.ext
  · rfl
  · change -(x.1 + x.2.1 + x.2.2) - -(x.1 + P x.2.1 + Q x.2.2) =
      (P x.2.1 - x.2.1) + (Q x.2.2 - x.2.2)
    abel

/-- Explicit integral row and column reduction to the identity plus the difference map. -/
theorem row_overlapMap_column_symm (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q ((columnEquiv H).symm x)) =
      (x.1, delta P Q x.2) := by
  rw [row_overlapMap, columnEquiv_symm_apply]
  apply Prod.ext
  · dsimp; abel
  · rfl

/-- The kernel is specified by the sum equation and the genuine monodromy difference equation. -/
theorem overlapMap_eq_zero_iff (x : H × (H × H)) :
    overlapMap P Q x = 0 ↔ x.1 + x.2.1 + x.2.2 = 0 ∧ delta P Q x.2 = 0 := by
  constructor
  · intro h
    have hr := congrArg (rowEquiv H) h
    rw [row_overlapMap, map_zero] at hr
    exact ⟨congrArg Prod.fst hr, congrArg Prod.snd hr⟩
  · rintro ⟨hs, hd⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap, map_zero]
    exact Prod.ext hs hd

/-- Membership in the overlap image is exactly membership of the reduced second coordinate
in the range of the monodromy difference map. -/
theorem overlapMap_mem_range_iff (y : H × H) :
    y ∈ LinearMap.range (overlapMap P Q) ↔ -y.1 - y.2 ∈ LinearMap.range (delta P Q) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.2, ?_⟩
    exact (congrArg Prod.snd (row_overlapMap P Q x)).symm
  · rintro ⟨bc, hbc⟩
    refine ⟨(columnEquiv H).symm (y.1, bc), ?_⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap_column_symm, rowEquiv_apply, hbc]

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
