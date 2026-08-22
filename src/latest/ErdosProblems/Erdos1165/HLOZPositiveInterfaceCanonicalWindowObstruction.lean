/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure

/-!
# The canonical active windows do not classify deficit shells

The positive-interface screen currently uses failure-count windows beginning
at the negative-binomial mean `i / 15`.  A physical first deficit shell lies
on the other side of that mean.  The elementary family below makes the
mismatch explicit: it is in shell zero, has deviation exactly `-1`, but is in
neither active window.  Thus the missing physical-to-screen bridge cannot be
repaired by paying a moderate-deviation complement around the current
windows; the windows themselves must be translated by the physical deficit
shell.
-/

namespace Erdos1165.HLOZPositiveInterfaceCanonicalWindowObstruction

open HLOZSharpWindowProductClosure NegativeBinomialLocalCLT
open ScreeningInstantiation

/-- At level `m = 16q`, retained count `i = 15q`, and failure count
`v = q - 1`, the physical total is `m - 1`, hence belongs to deficit shell
zero for every width at least two.  Nevertheless `v` is below both canonical
active windows, even though its deviation from the mean is exactly `-1`. -/
theorem first_deficit_shell_missed_by_canonical_active_windows
    {q width : ℕ} (hq : 0 < q) (hwidth : 2 ≤ width) :
    let m := 16 * q
    let i := 15 * q
    let v := q - 1
    (m - (i + v)) / width = 0 ∧
      v ∉ activeLowerFailureWindow m i ∧
      v ∉ activeUpperFailureWindow m i ∧
      deviation i v = -1 := by
  dsimp only
  have hactive : (16 * q) / 2 ≤ 15 * q := by omega
  rw [activeLowerFailureWindow_eq_of_active hactive,
    activeUpperFailureWindow_eq_of_active hactive]
  simp only [lowerFailureWindow, upperFailureWindow, Finset.mem_Ico, not_and_or]
  have hiDiv : (15 * q) / 15 = q := by omega
  rw [hiDiv]
  constructor
  · have hnum : 16 * q - (15 * q + (q - 1)) = 1 := by omega
    rw [hnum]
    exact Nat.div_eq_of_lt hwidth
  constructor
  · omega
  constructor
  · omega
  · unfold deviation
    push_cast
    have hqCast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hqCast]
    ring

end Erdos1165.HLOZPositiveInterfaceCanonicalWindowObstruction
