import ErdosProblems.Erdos796.MainReduction
import ErdosProblems.Erdos796.Extremal
import ErdosProblems.Erdos796.Lift

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Converting a uniform finite upper bound into structural reduction

Once every admissible set is bounded by `G(n)` plus a uniform error whose
ratio to `n/log n` tends to zero, the structural reduction follows by a
direct squeeze argument.  This module isolates that final analytic wrapper
from the combinatorial pruning proof.
-/

namespace Erdos796

open Filter Topology

/-- A natural-valued error is negligible on the second-order scale. -/
def NegligibleNatError (E : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (E n : ℝ) / secondOrderScale n)
    atTop (𝓝 0)

/-- A uniform eventual finite upper bound for every admissible set. -/
def UniformStructuralUpperBound (E : ℕ → ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, Admissible n A → A.card ≤ G n + E n

theorem g3_le_G_add_of_uniform_bound {E : ℕ → ℕ}
    (hUpper : UniformStructuralUpperBound E) :
    ∀ᶠ n : ℕ in atTop, g3 n ≤ G n + E n := by
  filter_upwards [hUpper] with n hn
  obtain ⟨A, hA, hcard⟩ := g3_attained n
  rw [← hcard]
  exact hn A hA

/-- The generic wrapper proving the manuscript's structural reduction. -/
theorem structuralReduction_of_uniform_upper_bound
    {E : ℕ → ℕ}
    (hUpper : UniformStructuralUpperBound E)
    (hNegligible : NegligibleNatError E) :
    StructuralReduction := by
  have hg3upper := g3_le_G_add_of_uniform_bound hUpper
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      rw [secondOrderScale]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hgap : (G n : ℝ) ≤ (g3 n : ℝ) := by
      exact_mod_cast model_lower n
    exact div_nonneg (sub_nonneg.mpr hgap) hscale.le
  · filter_upwards [Filter.eventually_ge_atTop 2, hg3upper] with n hn hupper
    have hscale : 0 < secondOrderScale n := by
      rw [secondOrderScale]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hupperReal : (g3 n : ℝ) ≤ (G n : ℝ) + (E n : ℝ) := by
      exact_mod_cast hupper
    have hgap : (g3 n : ℝ) - (G n : ℝ) ≤ (E n : ℝ) := by
      linarith
    exact (div_le_div_iff_of_pos_right hscale).mpr hgap
  · exact hNegligible

end Erdos796
