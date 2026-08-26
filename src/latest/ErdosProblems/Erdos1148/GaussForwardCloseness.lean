import ErdosProblems.Erdos1148.GaussRelativeBounds
import ErdosProblems.Erdos1148.ForwardBowenTube

/-! # Anisotropic Gauss coordinate boxes are forward Bowen boxes -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem gaussFrame_forward_tube (g : SL(2, ℝ)) {r s x y h k δ S : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hh : 1 / 2 ≤ h) (hk : 1 / 2 ≤ k)
    (hh2 : h ≤ 2) (hk2 : k ≤ 2) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hheight : |k - h| ≤ δ) (hstable : |y - x| ≤ δ)
    (hunstable : |s - r| ≤ δ * Real.exp (-S)) :
    EntryForwardBowenTube (8 * δ) ((8 * δ) * Real.exp (-S))
      ((g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0))⁻¹ *
        (g * unstableHorocycle s * upperTriangularFrame y k (by linarith : k ≠ 0))) := by
  have hε : 0 ≤ δ * Real.exp (-S) := mul_nonneg hδ (Real.exp_pos _).le
  have hεδ : δ * Real.exp (-S) ≤ δ := by
    exact mul_le_of_le_one_right hδ (Real.exp_le_one_iff.mpr (by linarith))
  obtain ⟨hclose, hlow⟩ := upperHorocycleUpper_entry_bounds hx hy hh hk hh2 hk2 hδ hε hεδ
    hheight hstable hunstable
  rw [gaussFrame_relative]
  refine ⟨hclose, hlow.trans ?_⟩
  nlinarith

theorem gaussFrame_forward_close (g : SL(2, ℝ)) {r s x y h k δ S : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hh : 1 / 2 ≤ h) (hk : 1 / 2 ≤ k)
    (hh2 : h ≤ 2) (hk2 : k ≤ 2) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hheight : |k - h| ≤ δ) (hstable : |y - x| ≤ δ)
    (hunstable : |s - r| ≤ δ * Real.exp (-S)) :
    ∀ t ∈ Set.Icc 0 S, EntryCloseOne (8 * δ)
      (((g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) * diagonalFlow t)⁻¹ *
        ((g * unstableHorocycle s * upperTriangularFrame y k (by linarith : k ≠ 0)) * diagonalFlow t)) := by
  have htube := gaussFrame_forward_tube g hx hy hh hk hh2 hk2 hδ hS hheight hstable hunstable
  have hclose := (entryForwardBowenTube_iff_flow_closeness hS _).mp htube
  intro t ht
  have heq (G H : SL(2, ℝ)) :
      (G * diagonalFlow t)⁻¹ * (H * diagonalFlow t) =
        diagonalFlow (-t) * (G⁻¹ * H) * diagonalFlow t := by
    rw [diagonalFlow_neg]
    group
  rw [heq]
  exact hclose t ht

end Erdos1148.DukeArithmetic
