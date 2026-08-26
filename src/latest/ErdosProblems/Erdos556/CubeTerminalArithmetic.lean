import ErdosProblems.Erdos556.CubeWeights

/-!
# The two terminal quadratic inequalities

After compression, the higher-dimensional support consists either of
the whole cube, or of two opposite faces. These are the corresponding
real algebraic inequalities and their necessary equality conditions.
-/

namespace Erdos556

theorem cube_terminal_bound (z E S : ℝ) (hz : 0 ≤ z) (hE : 0 ≤ E)
    (htotal : E + z = 4) (hS : E ^ 2 ≤ 4 * S) :
    z ≤ z ^ 2 + 2 * z * E + S - E - 3 * z := by
  have hzE : 0 ≤ z * E := mul_nonneg hz hE
  nlinarith

theorem opposite_faces_terminal_bound (y₀ y₁ E₀ E₁ S₀ S₁ : ℝ)
    (hE₀ : 0 ≤ E₀) (hE₀' : E₀ ≤ 2) (hE₁ : 0 ≤ E₁) (hE₁' : E₁ ≤ 2)
    (hS₀ : E₀ ^ 2 ≤ 2 * S₀) (hS₁ : E₁ ^ 2 ≤ 2 * S₁)
    (htotal : y₀ + E₀ + y₁ + E₁ = 4) :
    0 ≤ y₀ ^ 2 + 2 * y₀ * E₀ + S₀ - 2 * y₀ - E₀ +
      (y₁ ^ 2 + 2 * y₁ * E₁ + S₁ - 2 * y₁ - E₁) := by
  have hprod₀ := mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁ := mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀ := sq_nonneg (y₀ + E₀ - 2)
  have hs₁ := sq_nonneg (y₁ + E₁ - 2)
  nlinarith

theorem opposite_faces_terminal_eq (y₀ y₁ E₀ E₁ S₀ S₁ : ℝ)
    (hE₀ : 0 ≤ E₀) (hE₀' : E₀ ≤ 2) (hE₁ : 0 ≤ E₁) (hE₁' : E₁ ≤ 2)
    (hS₀ : E₀ ^ 2 ≤ 2 * S₀) (hS₁ : E₁ ^ 2 ≤ 2 * S₁)
    (htotal : y₀ + E₀ + y₁ + E₁ = 4)
    (hzero : y₀ ^ 2 + 2 * y₀ * E₀ + S₀ - 2 * y₀ - E₀ +
      (y₁ ^ 2 + 2 * y₁ * E₁ + S₁ - 2 * y₁ - E₁) = 0) :
    y₀ + E₀ = 2 ∧ y₁ + E₁ = 2 ∧ (E₀ = 0 ∨ E₀ = 2) ∧ (E₁ = 0 ∨ E₁ = 2) := by
  have hprod₀ := mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁ := mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀ := sq_nonneg (y₀ + E₀ - 2)
  have hs₁ := sq_nonneg (y₁ + E₁ - 2)
  have hL₀ : y₀ + E₀ = 2 := by nlinarith
  have hL₁ : y₁ + E₁ = 2 := by nlinarith
  have hE₀zero : E₀ * (2 - E₀) = 0 := by nlinarith
  have hE₁zero : E₁ * (2 - E₁) = 0 := by nlinarith
  refine ⟨hL₀, hL₁, ?_, ?_⟩
  · rcases mul_eq_zero.mp hE₀zero with h | h
    · exact Or.inl h
    · right; linarith
  · rcases mul_eq_zero.mp hE₁zero with h | h
    · exact Or.inl h
    · right; linarith

#print axioms cube_terminal_bound
#print axioms opposite_faces_terminal_eq

end Erdos556
