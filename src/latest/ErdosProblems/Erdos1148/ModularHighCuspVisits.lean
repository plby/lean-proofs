import ErdosProblems.Erdos1148.InitialCuspReturn
import ErdosProblems.Erdos1148.CuspRunGeometry

/-! # Global cusp-visit events and their buffered initial coordinates -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def modularHighCuspVisits (H Y : ℝ) (n : ℕ) (A : ℝ) : Set ModularOrbitSpace :=
  {x | x ∉ modularCusp Y ∧ A ≤ ((modularCuspVisitTimes H n x).card : ℝ)}

def modularBufferedHighCuspVisits (H Y : ℝ) (n : ℕ) (A : ℝ) : Set ModularOrbitSpace :=
  (modularRightTranslate (diagonalFlow (2 * Real.log H))) ⁻¹' modularHighCuspVisits H Y n A

theorem not_mem_cusp_before_log_buffer {H Y : ℝ} (hH : 1 ≤ H) (x : ModularOrbitSpace)
    (hx : modularRightTranslate (diagonalFlow (2 * Real.log H)) x ∉ modularCusp Y) :
    x ∉ modularCusp (Y * H) := by
  induction x using Quotient.inductionOn' with | h g =>
    exact not_cusp_before_log_buffer g hH hx

end Erdos1148.DukeArithmetic
