import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupFreeCover
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCovering

/-!
# Free-word monodromy of the actual positive meridians

The free-group covering gives an opposite-valued fundamental-group
homomorphism.  Inversion identifies the opposite group with the free
group itself.  The explicit transition values then send the actual
positive meridians to the two specified free generators.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] discreteFreeGroup

/-- Read actual covering monodromy as a word in the two positive meridians. -/
def meridianFreeWordHom :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint →* FreeGroup Bool :=
  (MulEquiv.inv' (FreeGroup Bool)).symm.toMonoidHom.comp
    (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
      freeGroupCover_basepoint_mem.1)

/-- The actual positively oriented zero meridian reads as the first free generator. -/
@[simp] theorem meridianFreeWordHom_positiveMeridianZero :
    meridianFreeWordHom (.mk positiveMeridianZero) = FreeGroup.of false := by
  have hzero := freeGroupCover.fundamentalGroupToMulOpposite_trans_U_V
    freeGroupCover_basepoint_mem freeGroupCover_leftPoint_mem
    upperZeroPath lowerZeroPath.symm
    (fun s => upperZeroPath_mem_upperSlitPlane s)
    (fun s => lowerZeroPath_mem_lowerSlitPlane (unitInterval.symm s))
  change (MulEquiv.inv' (FreeGroup Bool)).symm
    (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
      freeGroupCover_basepoint_mem.1 (.mk (upperZeroPath.trans lowerZeroPath.symm))) = _
  rw [hzero]
  change (freeGroupTransition meridianLeftPoint *
    (freeGroupTransition meridianBasepoint)⁻¹)⁻¹ = _
  simp

/-- The actual positively oriented one meridian reads as the second free generator. -/
@[simp] theorem meridianFreeWordHom_positiveMeridianOne :
    meridianFreeWordHom (.mk positiveMeridianOne) = FreeGroup.of true := by
  have hone := freeGroupCover.fundamentalGroupToMulOpposite_trans_U_V
    freeGroupCover_basepoint_mem freeGroupCover_rightPoint_mem
    upperOnePath lowerOnePath.symm
    (fun s => upperOnePath_mem_upperSlitPlane s)
    (fun s => lowerOnePath_mem_lowerSlitPlane (unitInterval.symm s))
  have hword : meridianFreeWordHom (.mk (upperOnePath.trans lowerOnePath.symm)) =
      (FreeGroup.of true)⁻¹ := by
    change (MulEquiv.inv' (FreeGroup Bool)).symm
      (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
        freeGroupCover_basepoint_mem.1 (.mk (upperOnePath.trans lowerOnePath.symm))) = _
    rw [hone]
    change (freeGroupTransition meridianRightPoint *
      (freeGroupTransition meridianBasepoint)⁻¹)⁻¹ = _
    simp
  let q : FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
    .mk (upperOnePath.trans lowerOnePath.symm)
  have hpath : (.mk positiveMeridianOne :
      FundamentalGroup TwicePuncturedPlane meridianBasepoint) = q⁻¹ := by
    rw [FundamentalGroup.inv_def]
    change .mk positiveMeridianOne =
      (Path.Homotopic.Quotient.mk (upperOnePath.trans lowerOnePath.symm)).symm
    rw [← Path.Homotopic.Quotient.mk_symm,
      Path.trans_symm, Path.symm_symm]
    rfl
  rw [hpath, map_inv]
  change (meridianFreeWordHom (.mk (upperOnePath.trans lowerOnePath.symm)))⁻¹ = _
  rw [hword, inv_inv]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
