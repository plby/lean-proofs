import StackExchange.Puzzling139335.N4OuterPair.HorizontalBase
import StackExchange.Puzzling139335.N4OuterPair.VerticalBase

/-! # Both components of a middle base and its normal are nonzero -/

open Set Puzzling139335.PlaneIsometries

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

theorem middle_base_nonaxis (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i) :
    linearMatrix e 0 0 ≠ 0 ∧ linearMatrix e 1 0 ≠ 0 :=
  ⟨h.middle_base_not_vertical hc hi e he, h.middle_base_not_horizontal hc hi e he⟩

theorem middle_normal_nonaxis (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i) :
    linearMatrix e 0 0 ≠ 0 ∧ linearMatrix e 0 1 ≠ 0 := by
  have hn := h.middle_base_nonaxis hc hi e he
  refine ⟨hn.1, ?_⟩
  intro hzero
  rcases (RectangularHull.matrix_row_axis_iff_column_axis e).mp (Or.inr hzero) with h₀ | h₁
  · exact hn.1 h₀
  · exact hn.2 h₁

end Puzzling139335.N4OuterPair.Configuration
