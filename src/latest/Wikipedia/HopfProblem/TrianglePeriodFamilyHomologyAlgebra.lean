import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraReduction
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraDiagonal
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraExact

/-!
# Kernels and cokernels of the three-overlap integral map

The explicit row and column changes reduce the overlap map to an identity
block and the monodromy-difference map. Its actual kernel and quotient
cokernel are therefore identified with those of the difference map, with
formulas on the underlying elements and quotient representatives.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

open PeriodTorusHigherHomology

variable {H : Type*} [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H)

/-- The actual row and column changes reduce the map to the literal diagonal block. -/
theorem overlapMap_normalized_apply (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q ((columnEquiv H).symm x)) = diagonalMap (delta P Q) x :=
  row_overlapMap_column_symm P Q x

/-- The normalization as an equality of integral linear maps.
The additive composition is converted back to a linear map with the
ambient integer-module structures on the source and target. -/
theorem overlapMap_normalized :
    intLinearMapOfAddHom ((rowEquiv H).toAddEquiv.toAddMonoidHom.comp
      ((overlapMap P Q).toAddMonoidHom.comp
        (columnEquiv H).symm.toAddEquiv.toAddMonoidHom)) = diagonalMap (delta P Q) := by
  apply LinearMap.ext
  exact overlapMap_normalized_apply P Q

/-- Projection to the two non-common overlap coordinates is an actual kernel equivalence. -/
def overlapKerEquiv : LinearMap.ker (overlapMap P Q) ≃ₗ[ℤ] LinearMap.ker (delta P Q) :=
  ({ toFun x := ⟨x.val.2, ((overlapMap_eq_zero_iff P Q x.val).mp x.property).2⟩
     invFun y := ⟨(-y.val.1 - y.val.2, y.val),
       (overlapMap_eq_zero_iff P Q _).mpr ⟨by dsimp; abel, y.property⟩⟩
     left_inv x := by
       apply Subtype.ext
       apply Prod.ext
       · have h := ((overlapMap_eq_zero_iff P Q x.val).mp x.property).1
         change -x.val.2.1 - x.val.2.2 = x.val.1
         calc
           -x.val.2.1 - x.val.2.2 =
               x.val.1 - (x.val.1 + x.val.2.1 + x.val.2.2) := by abel
           _ = x.val.1 := by rw [h, sub_zero]
       · rfl
     right_inv _ := rfl
     map_add' _ _ := rfl
   } : LinearMap.ker (overlapMap P Q) ≃+ LinearMap.ker (delta P Q)).toIntLinearEquiv

@[simp] theorem overlapKerEquiv_apply_val (x : LinearMap.ker (overlapMap P Q)) :
    (overlapKerEquiv P Q x : H × H) = x.val.2 := rfl

@[simp] theorem overlapKerEquiv_symm_apply_val (y : LinearMap.ker (delta P Q)) :
    ((overlapKerEquiv P Q).symm y : H × (H × H)) =
      (-y.val.1 - y.val.2, y.val) := rfl

/-- The quotient projection after the explicit target row change. -/
def overlapCokernelProjection : (H × H) →ₗ[ℤ] H ⧸ LinearMap.range (delta P Q) :=
  intLinearMapOfAddHom ((diagonalCokernelProjection (delta P Q)).toAddMonoidHom.comp
    (rowEquiv H).toAddEquiv.toAddMonoidHom)

@[simp] theorem overlapCokernelProjection_apply (y : H × H) :
    overlapCokernelProjection P Q y = Submodule.Quotient.mk (-y.1 - y.2) := rfl

/-- The reduced quotient map is surjective, with representatives `(0,-y)`. -/
theorem overlapCokernelProjection_surjective :
    Function.Surjective (overlapCokernelProjection P Q) := by
  intro q
  obtain ⟨y, rfl⟩ := (LinearMap.range (delta P Q)).mkQ_surjective q
  refine ⟨(0, -y), ?_⟩
  simp only [overlapCokernelProjection_apply, neg_zero, zero_sub, neg_neg]
  rfl

/-- The reduced quotient projection kills exactly the original overlap image. -/
theorem overlapMap_range_eq_ker_projection :
    LinearMap.range (overlapMap P Q) = LinearMap.ker (overlapCokernelProjection P Q) := by
  ext y
  rw [overlapMap_mem_range_iff]
  change -y.1 - y.2 ∈ LinearMap.range (delta P Q) ↔
    (Submodule.Quotient.mk (-y.1 - y.2) : H ⧸ LinearMap.range (delta P Q)) = 0
  exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (delta P Q))
    (x := -y.1 - y.2)).symm

/-- The actual quotient cokernel of the overlap map is the actual quotient
cokernel of the monodromy-difference map. -/
def overlapCokernelEquiv :
    ((H × H) ⧸ LinearMap.range (overlapMap P Q)) ≃ₗ[ℤ]
      H ⧸ LinearMap.range (delta P Q) :=
  ((Submodule.quotEquivOfEq _ _ (overlapMap_range_eq_ker_projection P Q)).toAddEquiv.trans
    ((overlapCokernelProjection P Q).quotKerEquivOfSurjective
      (overlapCokernelProjection_surjective P Q)).toAddEquiv).toIntLinearEquiv

/-- On quotient classes the cokernel equivalence is the negative coordinate sum. -/
@[simp] theorem overlapCokernelEquiv_mk (y : H × H) :
    overlapCokernelEquiv P Q (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (-y.1 - y.2) := by
  change (overlapCokernelProjection P Q).quotKerEquivOfSurjective
      (overlapCokernelProjection_surjective P Q)
      (Submodule.quotEquivOfEq _ _ (overlapMap_range_eq_ker_projection P Q)
        (Submodule.Quotient.mk y)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    overlapCokernelProjection_apply]

/-- The inverse cokernel equivalence has the explicit representative `(0,-y)`. -/
@[simp] theorem overlapCokernelEquiv_symm_mk (y : H) :
    (overlapCokernelEquiv P Q).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (0, -y) := by
  apply (overlapCokernelEquiv P Q).injective
  rw [LinearEquiv.apply_symm_apply, overlapCokernelEquiv_mk]
  simp only [neg_zero, zero_sub, neg_neg]

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
