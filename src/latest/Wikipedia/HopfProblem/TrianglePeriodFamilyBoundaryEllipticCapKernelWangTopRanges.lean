import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopColumns
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopIndex

/-!
# Exact images of the actual degree-four elliptic cap-kernel Wang map

The original surface third homology, the literal cap kernel, and the
original flat-torus third homology are used throughout.  The image is
identified integrally inside the full monodromy-invariant lattice.  Its
cyclic quotient has order three or four; the actual order-four surface
shear is retained in the quotient's residue formula.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling PeriodTorusHigherHomologyExterior
open ThreefoldOverlapMappingTorus MappingTorusHomology EllipticCapProduct

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The actual image equals the explicit integral two-column image. -/
theorem h3Coordinates_range_matrix (j : Kind) :
    LinearMap.range (h3Coordinates j) =
      LinearMap.range (topWangMatrix j (sourceShearThree j)).mulVecLin := by
  rw [← h3Coordinates_conjugate,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- Exact membership in the actual order-three cap-kernel Wang image. -/
theorem h3Coordinates_mem_range_three (v : Lattice) :
    v ∈ LinearMap.range (h3Coordinates .three) ↔
      cubeA₁ *ᵥ v = v ∧ (3 : ℤ) ∣ v 3 := by
  rw [h3Coordinates_range_matrix, topWangMatrix_mem_range_three_iff_fixed]

/-- Exact membership in the actual order-four image, with the genuine retained shear. -/
theorem h3Coordinates_mem_range_four (v : Lattice) :
    v ∈ LinearMap.range (h3Coordinates .four) ↔
      cubeA₂ *ᵥ v = v ∧ (4 : ℤ) ∣ v 3 + 2 * sourceShearThree .four * v 1 := by
  rw [h3Coordinates_range_matrix, topWangMatrix_mem_range_four_iff_fixed]

/-- The genuine positive-circle cross map followed by Wang is injective in this degree. -/
theorem h3Coordinates_injective (j : Kind) : Function.Injective (h3Coordinates j) := by
  intro a b hab
  apply (surfaceH3Equiv j (specialLocalData j).centralPeriod).injective
  apply topWangMatrix_injective j (sourceShearThree j)
  simpa only [Matrix.mulVecLin_apply, h3Coordinates_formula] using hab

/-- The actual Wang image is contained in the full original integral invariant lattice. -/
theorem h3Coordinates_mem_invariants (j : Kind) (a : SingularHomology (S j) 3) :
    h3Coordinates j a ∈ topInvariantLattice j := by
  rw [h3Coordinates_formula]
  exact topWangMatrix_mem_invariants j (sourceShearThree j) _

/-- The genuine map with codomain restricted to its original monodromy invariants. -/
def h3InvariantCoordinates (j : Kind) :
    SingularHomology (S j) 3 →ₗ[ℤ] topInvariantLattice j :=
  (h3Coordinates j).codRestrict _ (h3Coordinates_mem_invariants j)

@[simp] theorem h3InvariantCoordinates_val (j : Kind) (a : SingularHomology (S j) 3) :
    (h3InvariantCoordinates j a).val = h3Coordinates j a := rfl

/-- Its equality with the computed matrix keeps the original surface marking. -/
theorem h3InvariantCoordinates_eq (j : Kind) :
    h3InvariantCoordinates j = (topWangInvariantMap j (sourceShearThree j)).comp
      (surfaceH3Equiv j (specialLocalData j).centralPeriod).toLinearMap := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simpa only [h3InvariantCoordinates_val, LinearMap.comp_apply, LinearEquiv.coe_coe,
    topWangInvariantMap_val] using h3Coordinates_formula j a

/-- The exact image inside the full invariant lattice, not merely its rational span. -/
theorem h3InvariantCoordinates_range (j : Kind) :
    LinearMap.range (h3InvariantCoordinates j) =
      LinearMap.range (topWangInvariantMap j (sourceShearThree j)) := by
  rw [h3InvariantCoordinates_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The actual invariant-lattice image is the kernel of its explicit integral residue. -/
theorem h3InvariantCoordinates_range_eq_ker (j : Kind) :
    LinearMap.range (h3InvariantCoordinates j) =
      LinearMap.ker (topInvariantResidue j (sourceShearThree j)) := by
  rw [h3InvariantCoordinates_range, topWangInvariantMap_range_eq_ker]

/-- The actual cap-kernel Wang image has the stated cyclic cokernel in the full invariants. -/
def h3InvariantCokernelEquiv (j : Kind) :
    (topInvariantLattice j ⧸ LinearMap.range (h3InvariantCoordinates j)) ≃ₗ[ℤ] ZMod j.order :=
  (Submodule.quotEquivOfEq _ _ (h3InvariantCoordinates_range j)).trans
    (topWangInvariantCokernelEquiv j (sourceShearThree j))

@[simp] theorem h3InvariantCokernelEquiv_mk (j : Kind) (v : topInvariantLattice j) :
    h3InvariantCokernelEquiv j (Submodule.Quotient.mk v) =
      ((v.val 3 + topResidueCoefficient j (sourceShearThree j) * v.val 1 : ℤ) :
        ZMod j.order) := by
  change topWangInvariantCokernelEquiv j (sourceShearThree j) (Submodule.Quotient.mk v) = _
  exact topWangInvariantCokernelEquiv_mk j (sourceShearThree j) v

/-- The genuine image has index exactly three or four inside the full invariant lattice. -/
theorem h3InvariantCoordinates_index (j : Kind) :
    (LinearMap.range (h3InvariantCoordinates j)).toAddSubgroup.index = j.order := by
  rw [h3InvariantCoordinates_range, topWangInvariantMap_index]

/-- The literal fourth-degree cap kernel followed by the actual Wang map and flat marking. -/
def capKernelWangH4Coordinates (j : Kind) :
    LinearMap.ker (boundaryFillingHomologyMap (some j) 4) →ₗ[ℤ] Lattice :=
  AddMonoidHom.toIntLinearMap
    (FlatTorus.singularH3Coordinates.toAddEquiv.toAddMonoidHom.comp
      ((wangBoundary (flatTorusAffine j j.twist) 3).toAddMonoidHom.comp
        (LinearMap.ker (boundaryFillingHomologyMap (some j) 4)).subtype.toAddMonoidHom))

@[simp] theorem capKernelWangH4Coordinates_apply (j : Kind)
    (a : LinearMap.ker (boundaryFillingHomologyMap (some j) 4)) :
    capKernelWangH4Coordinates j a =
      FlatTorus.singularH3Coordinates (wangBoundary (flatTorusAffine j j.twist) 3 a.val) := rfl

/-- The existing cap-kernel coordinate equivalence gives the proved matrix, without
replacing that equivalence or its surface basis. -/
theorem capKernelWangH4Coordinates_symm (j : Kind) (a : Fin 2 → ℤ) :
    capKernelWangH4Coordinates j ((boundaryCapH4KernelEquiv j).symm a) =
      topWangMatrix j (sourceShearThree j) *ᵥ a := by
  rw [capKernelWangH4Coordinates_apply, boundaryCapH4KernelEquiv_symm_val]
  simpa only [h3Coordinates_apply, crossWang_apply, LinearEquiv.apply_symm_apply] using
    h3Coordinates_formula j ((surfaceH3Equiv j (specialLocalData j).centralPeriod).symm a)

/-- The entire literal cap-kernel map is computed in the existing kernel marking. -/
theorem capKernelWangH4Coordinates_formula (j : Kind)
    (a : LinearMap.ker (boundaryFillingHomologyMap (some j) 4)) :
    capKernelWangH4Coordinates j a =
      topWangMatrix j (sourceShearThree j) *ᵥ boundaryCapH4KernelEquiv j a := by
  simpa only [LinearEquiv.symm_apply_apply] using
    capKernelWangH4Coordinates_symm j (boundaryCapH4KernelEquiv j a)

/-- The positive first cap-kernel axis has the actual order times the positive `uwδ` coordinate. -/
theorem capKernelWangH4Coordinates_first_axis (j : Kind) :
    capKernelWangH4Coordinates j ((boundaryCapH4KernelEquiv j).symm ![1, 0]) =
      (j.order : ℤ) • ![0, 0, 0, 1] := by
  rw [capKernelWangH4Coordinates_symm]
  cases j
  · rw [topWangMatrix_mulVec_three]
    simp [Kind.order]
  · rw [topWangMatrix_mulVec_four]
    simp [Kind.order]

/-- The literal fourth-degree cap-kernel Wang map is injective. -/
theorem capKernelWangH4Coordinates_injective (j : Kind) :
    Function.Injective (capKernelWangH4Coordinates j) := by
  intro a b hab
  apply (boundaryCapH4KernelEquiv j).injective
  apply topWangMatrix_injective j (sourceShearThree j)
  simpa only [Matrix.mulVecLin_apply, capKernelWangH4Coordinates_formula] using hab

/-- Its image is precisely the actual positive-circle Wang image described above. -/
theorem capKernelWangH4Coordinates_range (j : Kind) :
    LinearMap.range (capKernelWangH4Coordinates j) = LinearMap.range (h3Coordinates j) := by
  rw [h3Coordinates_range_matrix]
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨boundaryCapH4KernelEquiv j a, ?_⟩
    simpa only [Matrix.mulVecLin_apply] using (capKernelWangH4Coordinates_formula j a).symm
  · rintro ⟨a, rfl⟩
    refine ⟨(boundaryCapH4KernelEquiv j).symm a, ?_⟩
    simpa only [Matrix.mulVecLin_apply] using capKernelWangH4Coordinates_symm j a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
