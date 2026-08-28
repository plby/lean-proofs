import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottOriginalMap
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableRange
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

/-!
# The first Bott reduction for the two quaternionic unitary groups still needed

Actual stable inclusions and the proved minimum-path comparison identify
`π₆(Sp(2))` with `π₅` of a quaternionic complex-structure space, and
`π₇(Sp(2))` with its `π₆`. These are reductions, not vanishing or cyclicity
assertions. No numerical homotopy input is assumed.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-- Iterate the actual stable matrix inclusions. -/
def stabilizationInRangeIterate (n k : ℕ) [NeZero k] (hk : k ≤ 4 * n + 1) (r : ℕ) :
    π_ k (SpGroup (Fin n)) 1 ≃* π_ k (SpGroup (Fin (n + r))) 1 := by
  induction r with
  | zero => exact MulEquiv.refl _
  | succ r ih => exact ih.trans (stabilizationInRange (n + r) k (by omega))

theorem stabilizationInRangeIterate_succ (n k : ℕ) [NeZero k]
    (hk : k ≤ 4 * n + 1) (r : ℕ) (x : π_ k (SpGroup (Fin n)) 1) :
    stabilizationInRangeIterate n k hk (r + 1) x =
      stabilizationMap (n + r) k (stabilizationInRangeIterate n k hk r x) := by
  change stabilizationInRange (n + r) k (by omega)
    (stabilizationInRangeIterate n k hk r x) = _
  exact stabilizationInRange_apply (n + r) k (by omega) _

def piSixSpTwoEquivFifthComplexStructures (n : ℕ) (hn : 6 < n) :
    π_ 6 QuaternionicFibration.SpTwo 1 ≃*
      π_ 5 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 6 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 5
    (ComplexStructures.standard n) hn).symm

def piSevenSpTwoEquivSixthComplexStructures (n : ℕ) (hn : 7 < n) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃*
      π_ 6 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 7 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 6
    (ComplexStructures.standard n) hn).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
