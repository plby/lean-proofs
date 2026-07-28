import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace MO508681

noncomputable def r : ℝ := Real.sqrt 2 - 1

noncomputable def c : ℝ := 2 * r - 1

noncomputable def w (x : ℝ) : ℝ :=
  if x < r then c else 2 * x - 1

noncomputable def D (k : ℕ) (x : ℝ) : ℝ :=
  if x < r then 2 * (x ^ (k + 1) / r ^ k) - 1 else 2 * x - 1

noncomputable def g (x : ℝ) : ℝ :=
  if x < r then -1 else (2 * x - 1 - r) / (1 - r)

noncomputable def C_r (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * ((1 - r) * g x + r * f x) + ∫ u in x..1, ((1 - r) * g u + r * f u)

noncomputable def game_value : ℝ :=
  ∫ x in 0..1, w x

def is_solution (W : ℕ → ℝ → ℝ) : Prop :=
  ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = max (D k x) (C_r (W (k + 1)) x)

def is_uniformly_bounded (W : ℕ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ k x, 0 ≤ x ∧ x ≤ 1 → |W k x| ≤ M

noncomputable def W_star (_ : ℕ) (x : ℝ) : ℝ := w x

theorem game_value_eq : game_value = 3 - 2 * Real.sqrt 2 := by
  sorry

theorem unique_solution :
    is_solution W_star ∧ is_uniformly_bounded W_star ∧
    ∀ W, is_solution W → is_uniformly_bounded W →
    (∀ k, IntervalIntegrable (W k) MeasureTheory.volume 0 1) →
    ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = W_star k x := by
  sorry

end MO508681
