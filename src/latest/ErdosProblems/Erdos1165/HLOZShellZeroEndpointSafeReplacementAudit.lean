/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroReplacementRankObstruction
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows

/-!
# Endpoint-safe shell replacement audit

Requiring the partner endpoint to remain below level `m` would restore the
statement that an `I₁ → I₀` move creates exactly one new threshold site.
On a fixed external word this is a coordinatewise restriction, so it can be
inserted into a conditional product denominator syntactically.

It does *not*, however, preserve the literal source-to-replacement window
comparison.  Already on the one-coordinate obstruction fibre, the whole
`I₀` comparison window violates partner safety, while the `I₁` source window
has positive negative-binomial mass.  Thus no finite multiplicative ratio
can compare the old source window to the endpoint-safe replacement window.
The shell replacement must retain the actual endpoint-count increment (and
hence use a finite increment/rank union), unless an additional probabilistic
payment for the discarded comparison vectors is supplied.
-/

open scoped BigOperators

namespace Erdos1165.HLOZShellZeroEndpointSafeReplacementAudit

open HLOZShellZeroReplacementWindows SmallWindow

noncomputable section

/-- The artificial `I₀` lazy-count window restricted to assignments whose
partner endpoint remains strictly below level `m`.  `baseExternal` and
`partnerExternal` are the two fixed boundary local times on the external
word; the same inserted domino total `v` is added to both endpoints. -/
def endpointSafeReplacementFailureWindow
    (m w baseExternal partnerExternal : ℕ) : Finset ℕ :=
  (shellZeroReplacementFailureWindow m w baseExternal).filter
    (fun v ↦ partnerExternal + v < m)

/-- On the explicit one-coordinate obstruction carrier, the base boundary
contributes one visit and the partner boundary contributes zero.  Every
literal `I₀` value then raises the partner to at least `m`, so the safe
replacement window is empty. -/
theorem endpointSafeReplacementFailureWindow_one_zero_eq_empty
    (m w : ℕ) :
    endpointSafeReplacementFailureWindow m w 1 0 = ∅ := by
  ext v
  simp [endpointSafeReplacementFailureWindow,
    mem_shellZeroReplacementFailureWindow]
  omega

/-- The corresponding source `I₁` window still has positive mass.  Hence
adding partner safety destroys every finite source-to-replacement ratio on
this fibre; it cannot be absorbed for free into the fixed-central product
comparison. -/
theorem no_finite_window_ratio_after_endpointSafe_restriction
    {m w : ℕ} (hw : 2 ≤ w) (hwm : w ≤ m) (C : ℝ) :
    ¬ windowMass 1 (shellZeroSourceFailureWindow m w 1) ≤
      C * windowMass 1
        (endpointSafeReplacementFailureWindow m w 1 0) := by
  have hi : 1 ≤ m - w + 1 := by omega
  have hsource :
      (shellZeroSourceFailureWindow m w 1).Nonempty :=
    shellZeroSourceFailureWindow_nonempty hi hw hwm
  have hpos : 0 < windowMass 1
      (shellZeroSourceFailureWindow m w 1) :=
    windowMass_pos (by omega) hsource
  rw [endpointSafeReplacementFailureWindow_one_zero_eq_empty]
  simp only [windowMass, Finset.sum_empty, mul_zero]
  exact not_le_of_gt hpos

end

end Erdos1165.HLOZShellZeroEndpointSafeReplacementAudit
