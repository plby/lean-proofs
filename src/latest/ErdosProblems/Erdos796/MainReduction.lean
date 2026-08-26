import ErdosProblems.Erdos796.Statement
import ErdosProblems.Erdos796.Model
import ErdosProblems.Erdos796.BaselineIdentity
import ErdosProblems.Erdos796.GammaBasic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of the three asymptotic components

The manuscript's final asymptotic follows formally from structural reduction,
the cofactor-model limit, and the baseline asymptotic.  This file proves that
assembly without assuming or declaring any of those components as axioms.
-/

namespace Erdos796

open Filter Topology

/-- The normalized structural error between the extremal problem and the
finite cofactor model. -/
def StructuralReduction : Prop :=
  Tendsto
    (fun n : ℕ => ((g3 n : ℝ) - (G n : ℝ)) / secondOrderScale n)
    atTop (𝓝 0)

/-- The normalized limit of the finite cofactor model around its baseline. -/
def CofactorModelLimit : Prop :=
  Tendsto
    (fun n : ℕ => ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n)
    atTop (𝓝 Gamma)

/-- The second-order baseline asymptotic with constant `1 + M`. -/
def BaselineAsymptotic (M : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      ((baseline n : ℝ) - leadingTerm n) / secondOrderScale n)
    atTop (𝓝 (1 + M))

/-- Exact algebraic decomposition of the normalized error. -/
theorem normalized_error_decomposition (n : ℕ) :
    ((g3 n : ℝ) - leadingTerm n) / secondOrderScale n =
      ((g3 n : ℝ) - (G n : ℝ)) / secondOrderScale n +
      ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n +
      ((baseline n : ℝ) - leadingTerm n) / secondOrderScale n := by
  ring

/-- Formal final assembly: the three named limits imply the corrected Erdős
796 conclusion, with constant `1 + M + Gamma`. -/
theorem hasSecondOrderConstant_of_components (M : ℝ)
    (hStructural : StructuralReduction)
    (hModel : CofactorModelLimit)
    (hBaseline : BaselineAsymptotic M) :
    HasSecondOrderConstant (1 + M + Gamma) := by
  have hsum := (hStructural.add hModel).add hBaseline
  have hsum' : Tendsto
      (fun n : ℕ =>
        ((g3 n : ℝ) - (G n : ℝ)) / secondOrderScale n +
      ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n +
      ((baseline n : ℝ) - leadingTerm n) / secondOrderScale n)
      atTop (𝓝 (1 + M + Gamma)) := by
    simpa [add_assoc, add_left_comm, add_comm] using! hsum
  exact hsum'.congr' <| Eventually.of_forall fun n =>
    (normalized_error_decomposition n).symm

/-- Consequently the three components imply the existential problem
statement itself. -/
theorem erdosProblem796_of_components (M : ℝ)
    (hStructural : StructuralReduction)
    (hModel : CofactorModelLimit)
    (hBaseline : BaselineAsymptotic M) :
    ErdosProblem796 :=
  ⟨1 + M + Gamma,
    hasSecondOrderConstant_of_components M hStructural hModel hBaseline⟩

end Erdos796
