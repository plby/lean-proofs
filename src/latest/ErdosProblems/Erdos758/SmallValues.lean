import ErdosProblems.Erdos758.SmallUpper
import ErdosProblems.Erdos758.SmallLower

namespace Erdos758

/-- The exact values of the maximum cochromatic number on `n` vertices for
every `1 ≤ n ≤ 19`. -/
theorem small_values_exact :
    z 1 = 1 ∧ z 2 = 1 ∧ z 3 = 2 ∧ z 4 = 2 ∧
    z 5 = 3 ∧ z 6 = 3 ∧ z 7 = 3 ∧ z 8 = 3 ∧
    z 9 = 4 ∧ z 10 = 4 ∧ z 11 = 4 ∧ z 12 = 4 ∧
    z 13 = 5 ∧ z 14 = 5 ∧ z 15 = 5 ∧
    z 16 = 6 ∧ z 17 = 6 ∧ z 18 = 6 ∧ z 19 = 6 := by
  rcases small_values_upper_bounds with
    ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12,
      u13, u14, u15, u16, u17, u18, u19⟩
  rcases small_values_lower_bounds with
    ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12,
      l13, l14, l15, l16, l17, l18, l19⟩
  exact ⟨Nat.le_antisymm u1 l1, Nat.le_antisymm u2 l2,
    Nat.le_antisymm u3 l3, Nat.le_antisymm u4 l4,
    Nat.le_antisymm u5 l5, Nat.le_antisymm u6 l6,
    Nat.le_antisymm u7 l7, Nat.le_antisymm u8 l8,
    Nat.le_antisymm u9 l9, Nat.le_antisymm u10 l10,
    Nat.le_antisymm u11 l11, Nat.le_antisymm u12 l12,
    Nat.le_antisymm u13 l13, Nat.le_antisymm u14 l14,
    Nat.le_antisymm u15 l15, Nat.le_antisymm u16 l16,
    Nat.le_antisymm u17 l17, Nat.le_antisymm u18 l18,
    Nat.le_antisymm u19 l19⟩

/-- The same result in the sequence notation used in the statement of
Erdős Problem 758. -/
theorem small_values_sequence :
    [z 1, z 2, z 3, z 4, z 5, z 6, z 7, z 8, z 9, z 10,
      z 11, z 12, z 13, z 14, z 15, z 16, z 17, z 18, z 19] =
    [1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6] := by
  rcases small_values_exact with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19⟩
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms small_values_exact
#print axioms small_values_sequence

end Erdos758
