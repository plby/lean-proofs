import StackExchange.Puzzling139335.N4Diagonal.AssignmentOne
import StackExchange.Puzzling139335.N4Diagonal.AssignmentTwo

/-!
# Exhaustion of both corner assignments and both placement parities

The actual reflection operation changes a reversing first placement into
a preserving one. The two assignment theorems then leave only the three
ordered endpoint-angle pairs.
-/

namespace Puzzling139335.N4Diagonal.Model

theorem angles_are_endpoints (m : Model) :
    (m.θ = 0 ∧ m.β = 0) ∨
      (m.θ = 0 ∧ m.β = Real.pi / 2) ∨
      (m.θ = Real.pi / 2 ∧ m.β = Real.pi / 2) := by
  rcases m.corner_order with ⟨hfirst, hlast⟩ | ⟨hfirst, hlast⟩
  · rcases m.first_form with he | he
    · have he' : ∀ x, m.e x = firstPlus 1 m.p m.θ x := by
        simpa only [hfirst] using he
      have hf := m.last_form
      rw [hlast] at hf
      exact m.assignment_one_angles he' hf
    · have he' := m.reflect_first_form he
      change ∀ x, m.reflect.e x = firstPlus m.firstCorner m.p m.θ x at he'
      rw [hfirst] at he'
      have hf := m.reflect.last_form
      change (∀ x, m.reflect.f x = lastPlus m.lastCorner m.q m.β x) ∨
        (∀ x, m.reflect.f x = lastMinus m.lastCorner m.q m.β x) at hf
      rw [hlast] at hf
      exact m.reflect.assignment_one_angles he' hf
  · exact m.assignment_two_angles hfirst hlast

end Puzzling139335.N4Diagonal.Model
