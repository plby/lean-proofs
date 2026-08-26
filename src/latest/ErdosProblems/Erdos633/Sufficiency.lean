import ErdosProblems.Erdos633.OneTwentyAngleCriteria
import ErdosProblems.Erdos633.GroupOneCriteria
import ErdosProblems.Erdos633.RightCriteria

/-!
# The complete sufficient direction of the eight-family classification

`ListedNonsquareAngles` records the eight conditions for one labelling of
the actual Euclidean triangle. `HasListedNonsquareShape` permits any
presentation of the same closed triangle. This module supplies sufficiency;
the unrestricted converse is proved in the subsequent `Classification` module.
-/

namespace Erdos633

def ListedNonsquareAngles (P : Triangle) : Prop :=
  P.angleA = P.angleB ∨
  (P.angleC = Real.pi / 2 ∧ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
    dist P.b P.c / dist P.a P.c = (m : ℝ) / n ∧ ¬ IsSquare (m ^ 2 + n ^ 2)) ∨
  (P.angleA = Real.pi / 6 ∧ P.angleB = Real.pi / 2 ∧ P.angleC = Real.pi / 3) ∨
  (P.angleC = Real.pi / 3 ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) ∨
  (P.angleB = 2 * P.angleA ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) ∨
  (P.angleB = 2 * P.angleA ∧
    ∃ q : ℚ, (q : ℝ) = Real.sin (P.angleA / 2)) ∨
  (P.angleC = P.angleA / 2 + P.angleB ∧ ∃ m n : ℕ, 0 < n ∧
    2 * Real.sin (P.angleA / 4) = (m : ℝ) / n ∧ ¬ IsSquare (2 * n ^ 2 - m ^ 2)) ∨
  (P.angleC = 2 * P.angleA + P.angleB / 2 ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2))

def HasListedNonsquareShape (P : Triangle) : Prop :=
  ∃ Q : Triangle, Q.carrier = P.carrier ∧ ListedNonsquareAngles Q

theorem Triangle.admitsNonsquareTiling_of_listed_angles (P : Triangle)
    (h : ListedNonsquareAngles P) : AdmitsNonsquareTiling P := by
  rcases h with h | h | h | h | h | h | h | h
  · exact P.admitsNonsquareTiling_of_equal_angleA_angleB h
  · obtain ⟨hC, m, n, hm, hn, hratio, hns⟩ := h
    have hright : P.rotate.angleB = Real.pi / 2 := by simpa using hC
    have hT := P.rotate.admitsNonsquareTiling_of_right_ratio hright m n hm hn
      (by simpa only [Triangle.rotate, dist_comm] using hratio) hns
    exact admitsNonsquareTiling_of_carrier_eq hT P.rotate_carrier
  · obtain ⟨_, hB, hC⟩ := h
    have hright : P.rotate.angleA = Real.pi / 2 := by simpa using hB
    have hsixty : P.rotate.angleB = Real.pi / 3 := by simpa using hC
    have hT := P.rotate.admitsNonsquareTiling_of_right_sixty hright hsixty
    exact admitsNonsquareTiling_of_carrier_eq hT P.rotate_carrier
  · exact P.admitsNonsquareTiling_of_sixty_rational_half_tangent h.1 h.2
  · exact P.admitsNonsquareTiling_of_double_angle_half_tangent h.1 h.2
  · exact P.admitsNonsquareTiling_of_double_angle_half_sine h.1 h.2
  · obtain ⟨hC, m, n, hn, hs, hns⟩ := h
    exact P.admitsNonsquareTiling_of_V_integer_parameter hC m n hn hs hns
  · exact P.admitsNonsquareTiling_of_Y_angle_relation h.1 h.2

theorem Triangle.admitsNonsquareTiling_of_listed_shape (P : Triangle)
    (h : HasListedNonsquareShape P) : AdmitsNonsquareTiling P := by
  obtain ⟨Q, hcarrier, hQ⟩ := h
  exact admitsNonsquareTiling_of_carrier_eq (Q.admitsNonsquareTiling_of_listed_angles hQ) hcarrier

end Erdos633
