import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordRowHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordCrossProduct
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCornerReal

/-! # The based symmetric Clifford-to-reduced homotopy with actual block coordinates -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

local notation "BlockIndex" => Fin 3 ⊕ Fin 1

def blockUnitaryReindex :
    C(unitary (Matrix (Fin 4) (Fin 4) ℂ), unitary (Matrix BlockIndex BlockIndex ℂ)) where
  toFun U := ⟨Matrix.reindex blockIndex.symm blockIndex.symm U.val,
    reindex_unitary blockIndex.symm U⟩
  continuous_toFun := (continuous_subtype_val.matrix_reindex _ _).subtype_mk _

def blockCliffordMap : C(UnitSphere, unitary (Matrix BlockIndex BlockIndex ℂ)) :=
  blockUnitaryReindex.comp unitaryMap

def blockRowHomotopy : blockCliffordMap.Homotopy swappedMap :=
  (ContinuousMap.Homotopy.refl blockUnitaryReindex).comp rowHomotopy

theorem blockRowHomotopy_axis_real (t : I) (i j : BlockIndex) :
    star ((blockRowHomotopy (t, axis)).val i j) = (blockRowHomotopy (t, axis)).val i j :=
  rowHomotopy_axis_real t (blockIndex i) (blockIndex j)

theorem swappedMap_axis_real (i j : BlockIndex) :
    star ((swappedMap axis).val i j) = (swappedMap axis).val i j := by
  have h := blockRowHomotopy_axis_real 1 i j
  rw [blockRowHomotopy.apply_one] at h
  exact h

theorem rankReductionHomotopy_axis_real (t : I) (i j : BlockIndex) :
    star ((rankReductionHomotopy (t, axis)).val i j) =
      (rankReductionHomotopy (t, axis)).val i j :=
  UnitaryZeroCorner.atAngle_real ((t : ℝ) * (Real.pi / 2)) (cornerMap axis)
    swappedMap_axis_real i j

def blockSymmetricClifford : C(UnitSphere, Space BlockIndex) :=
  unitaryProjection.comp blockCliffordMap

def blockSymmetricReduced : C(UnitSphere, Space BlockIndex) :=
  unitaryProjection.comp (UnitaryZeroCorner.reducedInclusion.comp cornerMap)

def symmetricReductionHomotopy :
    blockSymmetricClifford.HomotopyRel blockSymmetricReduced {axis} :=
  (unitaryProjectionHomotopyRel blockRowHomotopy axis blockRowHomotopy_axis_real).trans
    (unitaryProjectionHomotopyRel rankReductionHomotopy axis rankReductionHomotopy_axis_real)

theorem blockSymmetricReduced_val (z : UnitSphere) :
    (blockSymmetricReduced z).val.val =
      Matrix.fromBlocks ((reduced z).val * (reduced z).val.transpose) 0 0 1 := by
  change (unitaryProjection (UnitaryZeroCorner.reducedInclusion (cornerMap z))).val.val = _
  rw [unitaryProjection_val, UnitaryZeroCorner.reducedInclusion_val,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.one_mul]
  rfl

theorem blockSymmetricClifford_axis : blockSymmetricClifford axis = identity := by
  have hb : blockCliffordMap axis = 1 := by
    change blockUnitaryReindex (unitaryMap axis) = 1
    rw [unitaryMap_axis]
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv ℂ blockIndex.symm).map_one
  change unitaryProjection (blockCliffordMap axis) = identity
  rw [hb, unitaryProjection_one]

theorem blockSymmetricReduced_axis : blockSymmetricReduced axis = identity := by
  have h := symmetricReductionHomotopy.eq_fst 1 (Set.mem_singleton axis)
  rw [symmetricReductionHomotopy.apply_one] at h
  exact h.trans blockSymmetricClifford_axis

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
