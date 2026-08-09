import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1048

noncomputable def branch (n : ℕ) (k : ℕ) (w : ℂ) : ℂ :=
  (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) *
    Complex.exp
      (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ))
open Polynomial

def erdos_1048 : Prop :=
  ∀ f : ℂ[X],
    f.Monic →
    degree f ≥ 1 →
  ∀ r : ℝ,
    r < 2 →
    (∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ r) →
      let U : Set ℂ := { z : ℂ | ‖f.eval z‖ < 1 }
      ∃ x : ↥U,
        (2 - r) ≤
          Metric.diam (Subtype.val '' (connectedComponent x : Set (↥U)))
end Erdos1048

attribute [local instance] Classical.propDecidable

theorem Erdos1048.not_erdos_1048 :
    Not Erdos1048.erdos_1048
  := by
  sorry
