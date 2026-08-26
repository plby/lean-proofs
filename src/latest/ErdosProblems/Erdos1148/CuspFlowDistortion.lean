import ErdosProblems.Erdos1148.FlowVectorLengths

/-! # A cusp height can change by at most exp(|t|/2) under flow -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem modularRightTranslate_mem_cusp_of_scale {H M t : ℝ}
    (hscale : Real.exp |t| * (H ^ 2)⁻¹ ≤ (M ^ 2)⁻¹) {x : ModularOrbitSpace}
    (hx : x ∈ modularCusp H) :
    modularRightTranslate (diagonalFlow t) x ∈ modularCusp M := by
  induction x using Quotient.inductionOn' with | h g =>
    obtain ⟨u, v, huv, hshort⟩ := (mem_modularCusp_iff_representative g H).mp hx
    apply (mem_modularCusp_iff_representative (g * diagonalFlow t) M).mpr
    refine ⟨u, v, huv, ?_⟩
    exact (modularVectorLengthSq_flow_le g t u v).trans_lt
      ((mul_lt_mul_of_pos_left hshort (Real.exp_pos _)).trans_le hscale)

theorem modularRightTranslate_mem_cusp_distortion {H : ℝ} (hH : 0 < H) (t : ℝ)
    {x : ModularOrbitSpace} (hx : x ∈ modularCusp H) :
    modularRightTranslate (diagonalFlow t) x ∈ modularCusp (H * Real.exp (-(|t| / 2))) := by
  apply modularRightTranslate_mem_cusp_of_scale (H := H) (t := t) (hx := hx)
  have hexp : Real.exp (-(|t| / 2)) ^ 2 = Real.exp (-|t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hexp, Real.exp_neg, mul_inv_rev, inv_inv]

end Erdos1148.DukeArithmetic
