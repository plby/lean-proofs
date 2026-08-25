import StackExchange.Puzzling139335.N4Diagonal.SideBounds

/-!
# The side-coverage contradiction for the second corner assignment

Actual coverage supplies two source endpoints. If the first angle vanishes,
the left-side endpoint replaces the top-side one. Both cases contradict
the supporting-line bounds whenever the last angle is strictly interior.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

theorem assignment_two_beta_not_interior_of_side_data (m : Model)
    (he : ∀ x, m.e x = firstPlus 3 m.p m.θ x)
    (hf : (∀ x, m.f x = lastPlus 1 m.q m.β x) ∨
      (∀ x, m.f x = lastMinus 1 m.q m.β x))
    (hfTop : (m.f '' m.P ∩ {x : Plane | x 1 = 1}).Finite)
    (hfLeft : (m.f '' m.P ∩ {x : Plane | x 0 = 0}).Finite)
    (heRight : (m.e '' m.P ∩ {x : Plane | x 0 = 1}).Finite)
    (heBottom : (m.e '' m.P ∩ {x : Plane | x 1 = 0}).Finite)
    {x₀ y₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1) (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P)
    (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hmaxBottom : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀)
    (hmaxLeft : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    m.β ∉ Ioo (0 : ℝ) (Real.pi / 2) := by
  intro hβ
  have hqEnd : m.q - (1 - x₀) • ThreeCorners.ray m.β ∈ m.P := by
    rcases hf with hf | hf
    · exact m.last_incoming_mem_of_right_finite hf heRight hx₀ hmaxBottom
    · exact m.last_incoming_mem_of_bottom_finite hf heBottom hx₀ hmaxBottom
  rcases eq_or_lt_of_le m.theta_bounds.1 with hθzero | hθpos
  · have hpEnd := m.first_outgoing_mem_of_left_finite he hfLeft hy₀ hmaxLeft
    exact m.no_zero_first_angle_of_endpoints hθzero.symm hβ hx₀.2
      hbottom hleft hpEnd hqEnd
  · have hpEnd := m.first_incoming_mem_of_top_finite he hfTop hy₀ hmaxLeft
    exact m.no_interior_angles_of_cross_endpoints hθpos hβ.2 hx₀.2 hy₀.2
      hbottom hleft hpEnd hqEnd

end Puzzling139335.N4Diagonal.Model
