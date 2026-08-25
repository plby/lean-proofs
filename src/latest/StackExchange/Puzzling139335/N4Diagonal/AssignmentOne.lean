import StackExchange.Puzzling139335.N4Diagonal.Contacts
import StackExchange.Puzzling139335.N4Diagonal.SideBounds
import StackExchange.Puzzling139335.N4Diagonal.SideBounds.Maxima

/-!
# Endpoint angles in the first diagonal-corner assignment

The first singleton uses the lower-right square corner and the last
singleton uses the upper-left corner.  Actual side coverage supplies the
two incoming source endpoints.  Their supporting-line bounds exclude
every angle strictly between zero and a quarter-turn.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

namespace Model

private theorem endpoint_pairs_of_not_interior (m : Model)
    (hθ : m.θ ∉ Ioo (0 : ℝ) (Real.pi / 2))
    (hβ : m.β ∉ Ioo (0 : ℝ) (Real.pi / 2)) :
    (m.θ = 0 ∧ m.β = 0) ∨
      (m.θ = 0 ∧ m.β = Real.pi / 2) ∨
      (m.θ = Real.pi / 2 ∧ m.β = Real.pi / 2) := by
  have hθend : m.θ = 0 ∨ m.θ = Real.pi / 2 := by
    by_cases hzero : m.θ = 0
    · exact Or.inl hzero
    · right
      by_contra hhalf
      apply hθ
      exact ⟨lt_of_le_of_ne m.theta_bounds.1 (Ne.symm hzero),
        lt_of_le_of_ne m.theta_bounds.2 hhalf⟩
  have hβend : m.β = 0 ∨ m.β = Real.pi / 2 := by
    by_cases hzero : m.β = 0
    · exact Or.inl hzero
    · right
      by_contra hhalf
      apply hβ
      exact ⟨lt_of_le_of_ne m.beta_nonneg (Ne.symm hzero),
        lt_of_le_of_ne m.beta_bounds.2 hhalf⟩
  rcases hθend with hθzero | hθhalf
  · rcases hβend with hβzero | hβhalf
    · exact Or.inl ⟨hθzero, hβzero⟩
    · exact Or.inr (Or.inl ⟨hθzero, hβhalf⟩)
  · have hβhalf : m.β = Real.pi / 2 :=
      le_antisymm m.beta_bounds.2 (hθhalf ▸ m.beta_bounds.1)
    exact Or.inr (Or.inr ⟨hθhalf, hβhalf⟩)

/-- The two source endpoints forced by Assignment I side coverage leave
exactly the three ordered endpoint-angle pairs. -/
theorem assignmentI_angles_of_source_endpoints (m : Model) {x₀ y₀ : ℝ}
    (hx₀ : x₀ < 1) (hy₀ : y₀ < 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P)
    (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hpEnd : m.p - (1 - x₀) • ray m.θ ∈ m.P)
    (hqEnd : m.q - (1 - y₀) • ray m.β ∈ m.P) :
    (m.θ = 0 ∧ m.β = 0) ∨
      (m.θ = 0 ∧ m.β = Real.pi / 2) ∨
      (m.θ = Real.pi / 2 ∧ m.β = Real.pi / 2) :=
  m.endpoint_pairs_of_not_interior
    (m.first_incoming_not_interior_angle hx₀ hbottom hpEnd)
    (m.last_incoming_not_interior_angle hy₀ hleft hqEnd)

/-- In Assignment I, either parity of the last placement forces both
angles to be endpoints.  All finite contacts and source endpoints are
derived from the actual model and its placement maps. -/
theorem assignment_one_angles (m : Model)
    (he : ∀ x, m.e x = firstPlus 1 m.p m.θ x)
    (hf : (∀ x, m.f x = lastPlus 3 m.q m.β x) ∨
      (∀ x, m.f x = lastMinus 3 m.q m.β x)) :
    (m.θ = 0 ∧ m.β = 0) ∨
      (m.θ = 0 ∧ m.β = Real.pi / 2) ∨
      (m.θ = Real.pi / 2 ∧ m.β = Real.pi / 2) := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hbottom, hleft, hmaxBottom, hmaxLeft⟩ :=
    m.exists_axis_maxima
  have heImage : m.e '' m.P = firstPlus 1 m.p m.θ '' m.P :=
    congrArg (fun g : Plane → Plane => g '' m.P) (funext he)
  have heLeft : (m.e '' m.P ∩ {x : Plane | x 0 = 0}).Finite := by
    rw [heImage, m.firstPlus_one_left_empty]
    exact finite_empty
  have heTop : (m.e '' m.P ∩ {x : Plane | x 1 = 1}).Finite := by
    rw [heImage]
    exact m.firstPlus_one_top_finite
  have hfBottom : (m.f '' m.P ∩ {x : Plane | x 1 = 0}).Finite := by
    rcases hf with hf | hf
    · rw [congrArg (fun g : Plane → Plane => g '' m.P) (funext hf),
        m.lastPlus_three_bottom_empty]
      exact finite_empty
    · rw [congrArg (fun g : Plane → Plane => g '' m.P) (funext hf)]
      exact m.lastMinus_three_bottom_finite
  have hpEnd := m.first_incoming_mem_of_bottom_finite he hfBottom hx₀ hmaxBottom
  have hqEnd : m.q - (1 - y₀) • ray m.β ∈ m.P := by
    rcases hf with hf | hf
    · exact m.last_incoming_mem_of_left_finite hf heLeft hy₀ hmaxLeft
    · exact m.last_incoming_mem_of_top_finite hf heTop hy₀ hmaxLeft
  exact m.assignmentI_angles_of_source_endpoints hx₀.2 hy₀.2 hbottom hleft hpEnd hqEnd

end Model

end Puzzling139335.N4Diagonal
