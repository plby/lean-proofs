import StackExchange.Puzzling139335.Definitions
import Mathlib.Tactic.Linarith

/-!
# Equal vertical offsets from top contacts

Two maps with the same linear height coordinate and the same source set
have equal vertical offsets if both images fit in the square and meet its
top side.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

theorem vertical_offset_eq_of_top_contacts {P : Set Plane} (R D : Plane → Plane)
    {c s v w : ℝ}
    (hR : ∀ p, (R p) 1 = v + c * p 0 + s * p 1)
    (hD : ∀ p, (D p) 1 = w + c * p 0 + s * p 1)
    (hRfit : R '' P ⊆ unitSquare) (hDfit : D '' P ⊆ unitSquare)
    (hRtop : ∃ p ∈ P, (R p) 1 = 1) (hDtop : ∃ p ∈ P, (D p) 1 = 1) :
    w = v := by
  obtain ⟨p, hp, hptop⟩ := hRtop
  obtain ⟨q, hq, hqtop⟩ := hDtop
  have hDp : (D p) 1 ≤ 1 := (hDfit ⟨p, hp, rfl⟩).2.2
  have hRq : (R q) 1 ≤ 1 := (hRfit ⟨q, hq, rfl⟩).2.2
  rw [hR p] at hptop
  rw [hD q] at hqtop
  rw [hD p] at hDp
  rw [hR q] at hRq
  linarith only [hptop, hqtop, hDp, hRq]

end Puzzling139335.N5.AlignedFace
