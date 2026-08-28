import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Restrict an actual diffeomorphism to an open target and its preimage -/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M C K N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace K]
  {J : ModelWithCorners ℝ C K} [TopologicalSpace N] [ChartedSpace K N]
  (d : M ≃ₘ⟮I, J⟯ N) (U : Opens N)

def openDiffeomorphPreimage : Opens M :=
  ⟨d ⁻¹' U, U.isOpen.preimage d.continuous⟩

def openPreimageDiffeomorph : openDiffeomorphPreimage d U ≃ₘ⟮I, J⟯ U := by
  let forward : openDiffeomorphPreimage d U → U := fun p ↦ ⟨d p.val, p.property⟩
  let backward : U → openDiffeomorphPreimage d U := fun p ↦
    ⟨d.symm p.val, by change d (d.symm p.val) ∈ U; rw [d.apply_symm_apply]; exact p.property⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := fun p ↦ Subtype.ext (d.symm_apply_apply p.val)
      right_inv := fun p ↦ Subtype.ext (d.apply_symm_apply p.val)
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff U forward).mp
      (d.contMDiff_toFun.comp contMDiff_subtype_val)
  · exact (ContMDiff.subtypeVal_comp_iff (openDiffeomorphPreimage d U) backward).mp
      (d.symm.contMDiff_toFun.comp contMDiff_subtype_val)

theorem openPreimageDiffeomorph_val (p : openDiffeomorphPreimage d U) :
    (openPreimageDiffeomorph d U p).val = d p.val := rfl

theorem openPreimageDiffeomorph_symm_val (p : U) :
    ((openPreimageDiffeomorph d U).symm p).val = d.symm p.val := rfl

end NoExoticSixSphere
