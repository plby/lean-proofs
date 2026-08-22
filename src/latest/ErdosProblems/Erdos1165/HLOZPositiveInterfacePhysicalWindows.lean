/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceCanonicalWindowObstruction

/-!
# Physical coordinate windows for a deficit-shell interface

For retained endpoint count `i` and inserted domino total `v`, the physical
endpoint local time is `i + v`.  The coordinate window associated with shell
`j` must therefore be defined by the actual deficit label of `i + v`.
This differs from the mean-centred windows currently used by the preliminary
positive-interface screen.

The finite range `0, ..., m` is harmless only after intersecting with the
same-rank accepted base window.  In particular Nat-subtraction saturation
makes bare shell zero contain values with `i + v ≥ m`; no cardinal or local
ratio claim is made for the bare window below.
-/

namespace Erdos1165.HLOZPositiveInterfacePhysicalWindows

open ScreeningInstantiation

/-- Failure-count values with physical deficit label `j`.  Analytic consumers
must intersect this with their same-rank accepted base window. -/
def physicalDeficitFailureWindow
    (m width i shell : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter fun v ↦
    (m - (i + v)) / width = shell

@[simp] theorem mem_physicalDeficitFailureWindow
    {m width i shell v : ℕ} :
    v ∈ physicalDeficitFailureWindow m width i shell ↔
      v < m + 1 ∧ (m - (i + v)) / width = shell := by
  simp [physicalDeficitFailureWindow]

/-- The physical windows for distinct deficit shells are disjoint. -/
theorem disjoint_physicalDeficitFailureWindow
    {m width i shell shell' : ℕ} (hne : shell ≠ shell') :
    Disjoint (physicalDeficitFailureWindow m width i shell)
      (physicalDeficitFailureWindow m width i shell') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_physicalDeficitFailureWindow] at hv hv'
  exact hne (hv.2.symm.trans hv'.2)

/-- Consecutive physical windows are the exact predicates needed by an
adjacent-shell upper-tail screen.  The numerator is shell `j+1`; it is not
the mean-centred interval above shell `j`. -/
def physicalAdjacentFailureWindows
    (m width i shell : ℕ) : Finset ℕ × Finset ℕ :=
  (physicalDeficitFailureWindow m width i (shell + 1),
    physicalDeficitFailureWindow m width i shell)

theorem physicalAdjacentFailureWindows_disjoint
    {m width i shell : ℕ} :
    Disjoint (physicalAdjacentFailureWindows m width i shell).1
      (physicalAdjacentFailureWindows m width i shell).2 := by
  exact disjoint_physicalDeficitFailureWindow (by omega)

/-- The obstruction family really lies in the corrected physical shell-zero
window. -/
theorem obstruction_mem_physical_shell_zero
    {q width : ℕ} (hq : 0 < q) (hwidth : 2 ≤ width) :
    q - 1 ∈ physicalDeficitFailureWindow
      (16 * q) width (15 * q) 0 := by
  rw [mem_physicalDeficitFailureWindow]
  constructor
  · omega
  · have hnum : 16 * q - (15 * q + (q - 1)) = 1 := by omega
    rw [hnum]
    exact Nat.div_eq_of_lt hwidth

end Erdos1165.HLOZPositiveInterfacePhysicalWindows
