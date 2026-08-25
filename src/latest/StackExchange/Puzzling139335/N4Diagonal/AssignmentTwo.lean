import StackExchange.Puzzling139335.N4Diagonal.AssignmentTwo.Bounds
import StackExchange.Puzzling139335.N4Diagonal.Contacts
import StackExchange.Puzzling139335.N4Diagonal.SideBounds.Maxima
import StackExchange.Puzzling139335.N4Diagonal.Reflection
import StackExchange.Puzzling139335.N4Diagonal.Transpose

/-!
# Both placement parities in the second corner assignment

Finite side contacts and actual coverage exclude an interior last angle.
Reflection handles either first-placement parity. Coordinate transposition
then excludes an interior first angle when the last angle is an endpoint.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

theorem assignment_two_beta_not_interior_of_forms (m : Model)
    (he : ∀ x, m.e x = firstPlus 3 m.p m.θ x)
    (hf : (∀ x, m.f x = lastPlus 1 m.q m.β x) ∨
      (∀ x, m.f x = lastMinus 1 m.q m.β x)) :
    m.β ∉ Ioo (0 : ℝ) (Real.pi / 2) := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hbottom, hleft, hmaxBottom, hmaxLeft⟩ :=
    m.exists_axis_maxima
  have heq : (m.e : Plane → Plane) = firstPlus 3 m.p m.θ := funext he
  have heRight : (m.e '' m.P ∩ {x : Plane | x 0 = 1}).Finite := by
    rw [heq, m.firstPlus_three_right_empty]
    exact finite_empty
  have heBottom : (m.e '' m.P ∩ {x : Plane | x 1 = 0}).Finite := by
    rw [heq]
    exact m.firstPlus_three_bottom_finite
  have hfSides : (m.f '' m.P ∩ {x : Plane | x 1 = 1}).Finite ∧
      (m.f '' m.P ∩ {x : Plane | x 0 = 0}).Finite := by
    rcases hf with hf | hf
    · have hfq : (m.f : Plane → Plane) = lastPlus 1 m.q m.β := funext hf
      rw [hfq]
      constructor
      · rw [m.lastPlus_one_top_empty]
        exact finite_empty
      · exact m.lastPlus_one_left_finite
    · have hfq : (m.f : Plane → Plane) = lastMinus 1 m.q m.β := funext hf
      rw [hfq]
      constructor
      · exact m.lastMinus_one_top_finite
      · rw [m.lastMinus_one_left_empty]
        exact finite_empty
  exact m.assignment_two_beta_not_interior_of_side_data he hf hfSides.1 hfSides.2
    heRight heBottom hx₀ hy₀ hbottom hleft hmaxBottom hmaxLeft

/-- Both actual first-placement parities exclude an interior last angle. -/
theorem assignment_two_beta_not_interior (m : Model)
    (hfirst : m.firstCorner = 3) (hlast : m.lastCorner = 1) :
    m.β ∉ Ioo (0 : ℝ) (Real.pi / 2) := by
  rcases m.first_form with he | he
  · have he' : ∀ x, m.e x = firstPlus 3 m.p m.θ x := by
      simpa only [hfirst] using he
    have hf := m.last_form
    rw [hlast] at hf
    exact m.assignment_two_beta_not_interior_of_forms he' hf
  · have he' := m.reflect_first_form he
    change ∀ x, m.reflect.e x = firstPlus m.firstCorner m.p m.θ x at he'
    rw [hfirst] at he'
    have hf := m.reflect.last_form
    change (∀ x, m.reflect.f x = lastPlus m.lastCorner m.q m.β x) ∨
      (∀ x, m.reflect.f x = lastMinus m.lastCorner m.q m.β x) at hf
    rw [hlast] at hf
    exact m.reflect.assignment_two_beta_not_interior_of_forms he' hf

/-- Assignment II leaves only the three endpoint-angle pairs. This result
uses actual coverage and actual placement maps and has no center premise. -/
theorem assignment_two_angles (m : Model)
    (hfirst : m.firstCorner = 3) (hlast : m.lastCorner = 1) :
    (m.θ = 0 ∧ m.β = 0) ∨
      (m.θ = 0 ∧ m.β = Real.pi / 2) ∨
      (m.θ = Real.pi / 2 ∧ m.β = Real.pi / 2) := by
  have hβnot := m.assignment_two_beta_not_interior hfirst hlast
  have hβend : m.β = 0 ∨ m.β = Real.pi / 2 := by
    rcases eq_or_lt_of_le m.beta_nonneg with hzero | hpos
    · exact Or.inl hzero.symm
    · right
      apply le_antisymm m.beta_bounds.2
      exact le_of_not_gt (fun hlt => hβnot ⟨hpos, hlt⟩)
  rcases hβend with hβzero | hβhalf
  · left
    exact ⟨by linarith [m.theta_bounds.1, m.beta_bounds.1], hβzero⟩
  · by_cases hθzero : m.θ = 0
    · exact Or.inr (Or.inl ⟨hθzero, hβhalf⟩)
    by_cases hθhalf : m.θ = Real.pi / 2
    · exact Or.inr (Or.inr ⟨hθhalf, hβhalf⟩)
    have hθpos : 0 < m.θ := by
      by_contra h
      exact hθzero (le_antisymm (le_of_not_gt h) m.theta_bounds.1)
    have hθlt : m.θ < Real.pi / 2 := by
      by_contra h
      exact hθhalf (le_antisymm m.theta_bounds.2 (le_of_not_gt h))
    have hn := m.transpose.assignment_two_beta_not_interior
      (by simpa only [transpose_firstCorner] using hfirst)
      (by simpa only [transpose_lastCorner] using hlast)
    apply False.elim
    apply hn
    change 0 < Real.pi / 2 - m.θ ∧ Real.pi / 2 - m.θ < Real.pi / 2
    constructor <;> linarith

end Puzzling139335.N4Diagonal.Model
