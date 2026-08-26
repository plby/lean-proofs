import ErdosProblems.Erdos1148.PacketCuspHeight
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.NumberTheory.Modular

/-! # Compact sets covering the complement of the cusp -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma modularVectorLengthSq_one_zero (g : SL(2, ℝ)) :
    modularVectorLengthSq g 1 0 = g 1 0 ^ 2 + g 1 1 ^ 2 := by
  simp [modularVectorLengthSq, modularVector, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, add_comm]

lemma im_smul_I_eq_inv_modularVectorLengthSq (g : SL(2, ℝ)) :
    (g • UpperHalfPlane.I).im = (modularVectorLengthSq g 1 0)⁻¹ := by
  rw [modularVectorLengthSq_one_zero]
  simp only [MulAction.compHom_smul_def, UpperHalfPlane.im_smul_eq_div_normSq,
    Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, abs_one, UpperHalfPlane.I_im, mul_one]
  congr 1
  simp [Complex.normSq, UpperHalfPlane.denom, pow_two, add_comm]

def modularCompactCore (H : ℝ) : Set ModularOrbitSpace :=
  modularMk '' (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹'
    ModularGroup.truncatedFundamentalDomain (H ^ 2)

theorem isCompact_modularCompactCore (H : ℝ) : IsCompact (modularCompactCore H) :=
  (UpperHalfPlane.isProperMap_smul_I.isCompact_preimage
    (ModularGroup.isCompact_truncatedFundamentalDomain (H ^ 2))).image continuous_modularMk

theorem modularCusp_compl_subset_compactCore {H : ℝ} (hH : 0 < H) :
    (modularCusp H)ᶜ ⊆ modularCompactCore H := by
  intro x hx
  let g : SL(2, ℝ) := x.out
  have hgx : modularMk g = x := Quotient.out_eq x
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd (g • UpperHalfPlane.I)
  let g' : SL(2, ℝ) := (γ : SL(2, ℝ)) * g
  have hg'x : modularMk g' = x := (modularMk_integral_mul γ g).trans hgx
  have hfd : g' • UpperHalfPlane.I ∈ ModularGroup.fd := by
    change ((γ : SL(2, ℝ)) * g) • UpperHalfPlane.I ∈ _
    rw [mul_smul]
    convert hγ using 1
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    congr 1
  have hvec : (H ^ 2)⁻¹ ≤ modularVectorLengthSq g' 1 0 := by
    by_contra h
    apply hx
    simp only [modularCusp, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨1, 0, Or.inl (by norm_num), g', lt_of_not_ge h, hg'x⟩
  have him : (g' • UpperHalfPlane.I).im ≤ H ^ 2 := by
    rw [im_smul_I_eq_inv_modularVectorLengthSq]
    have hsq : 0 < H ^ 2 := sq_pos_of_pos hH
    have hv : 0 < modularVectorLengthSq g' 1 0 := (inv_pos.mpr hsq).trans_le hvec
    exact (inv_le_comm₀ hv hsq).mpr hvec
  exact ⟨g', ⟨hfd, him⟩, hg'x⟩

end Erdos1148.DukeArithmetic
