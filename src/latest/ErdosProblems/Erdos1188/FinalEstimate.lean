import ErdosProblems.Erdos1188.AllCutoffLower
import ErdosProblems.Erdos1188.UpperBound

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Two-sided estimate for Erdős Problem 1188
-/

namespace Erdos1188

/-- A single exact theorem collecting the explicit lower and upper estimates.
The lower index is asymptotic to `log x / log log x`. -/
theorem erdos1188_two_sided_estimate (x : ℕ) (hx : x ≠ 0)
    (hlarge : 6 ≤ lowerFrameIndex x) :
    2 ^ ((lowerFrameIndex x - 1) * 2 ^ (lowerFrameIndex x - 2)) ≤
      coveringCount x ∧ coveringCount x ≤ (x + 2) ^ (x + 1) := by
  exact ⟨explicit_all_cutoffs_lower_strong x hx hlarge,
    coveringCount_le_elementary x⟩

end Erdos1188
