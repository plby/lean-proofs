/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open BigOperators Polynomial

namespace Erdos990

def IsArgument (z : ℂ) (θ : ℝ) : Prop :=
  z = (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

noncomputable def argumentRepresentative (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

noncomputable def coeffSupportCardUpTo (f : Polynomial ℂ) (d : ℕ) : ℕ :=
  ((Finset.range (d + 1)).filter fun k => f.coeff k ≠ 0).card

noncomputable def coefficientRatio (f : Polynomial ℂ) (d : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (d + 1), ‖f.coeff k‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.coeff d‖)

noncomputable def argumentCount {d : ℕ} (θ : Fin d → ℝ) (α β : ℝ) : ℕ :=
  (Finset.univ.filter fun i => α ≤ θ i ∧ θ i ≤ β).card

def HasRootsWithArguments (f : Polynomial ℂ) (d : ℕ) (z : Fin d → ℂ)
    (θ : Fin d → ℝ) : Prop :=
  f.natDegree = d ∧
    f.coeff d ≠ 0 ∧
    f.coeff 0 ≠ 0 ∧
    f = Polynomial.C (f.coeff d) * ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i)) ∧
    ∀ i : Fin d, IsArgument (z i) (θ i) ∧ θ i ∈ Set.Ico (0 : ℝ) (2 * Real.pi)

def SparseErdosTuranEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ) (θ : Fin d → ℝ),
      HasRootsWithArguments f d z θ →
        ∀ α β : ℝ,
          0 ≤ α → α ≤ β → β ≤ 2 * Real.pi →
            |(argumentCount θ α β : ℝ) - ((β - α) / (2 * Real.pi)) * d| ≤
              C * Real.sqrt
                ((coeffSupportCardUpTo f d : ℝ) * Real.log (coefficientRatio f d))
end Erdos990


open scoped Classical in
theorem Erdos990.erdos990 :
    Not Erdos990.SparseErdosTuranEstimate
  := by
  sorry
