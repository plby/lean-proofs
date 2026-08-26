import ErdosProblems.Erdos1148.UpperTriangularFrames
import ErdosProblems.Erdos1148.RotationEntryBounds
import ErdosProblems.Erdos1148.RealIntervalGrid

/-! # Points in one scaled frame box are close in the modular quotient -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def cuspFrame (x h θ : ℝ) (hh : h ≠ 0) : SL(2, ℝ) :=
  upperTriangularFrame x h hh * rotationFrame θ

lemma entryCloseOne_mono {η δ : ℝ} {g : SL(2, ℝ)} (h : EntryCloseOne η g) (hle : η ≤ δ) :
    EntryCloseOne δ g :=
  ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.1.trans hle, h.2.2.2.trans hle⟩

theorem cuspFrame_relative_close {x y h k θ φ H δ : ℝ}
    (hH : 0 < H) (hh : H ≤ h) (hk : H ≤ k) (hδ : 0 ≤ δ)
    (hheight : |k - h| ≤ δ * H) (hhor : |y - x| ≤ δ * H ^ 2) (hangle : |φ - θ| ≤ δ) :
    EntryCloseOne (5 * δ) ((cuspFrame x h θ (hH.trans_le hh).ne')⁻¹ *
      cuspFrame y k φ (hH.trans_le hk).ne') := by
  have hu := upperTriangularFrame_relative_close hH hh hk hδ hheight hhor
  have hrot := entryCloseOne_rotation_change hδ hu θ φ
  have hclose := entryCloseOne_mono hrot (by linarith : 4 * δ + |φ - θ| ≤ 5 * δ)
  simpa only [cuspFrame, mul_inv_rev, mul_assoc] using hclose

end Erdos1148.DukeArithmetic
