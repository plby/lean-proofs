import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairHomology
import Mathlib.GroupTheory.Index

/-!
# Finite homology through the actual surgery body

Finite old homology and a zero attaching-sphere group make the common
body's homology finite. If the actual new belt image is finite as well,
exactness makes the new endpoint homology finite. The proof uses the
original endpoint maps, their actual kernel, and the finite range.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle
open SingularMayerVietoris

variable {E F R X Y : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] (d : SurgeryBoundaryPair E F R X Y)

theorem new_homology_finite (k : ℕ)
    [Finite (SingularHomology X (k + 1))]
    [Subsingleton (SingularHomology (UnitSphere E) k)]
    [Finite (LinearMap.range (singularHomologyMap d.beltSphere (k + 1)))] :
    Finite (SingularHomology Y (k + 1)) := by
  let : Finite (SingularHomology (Space d) (k + 1)) :=
    Finite.of_surjective (singularHomologyMap (oldMap d) (k + 1))
      ((oldHandleData d).old_surjective k)
  let : Finite (singularHomologyMap (newMap d) (k + 1)).toAddMonoidHom.ker := by
    change Finite (LinearMap.ker (singularHomologyMap (newMap d) (k + 1)))
    rw [← exact_at_new d (k + 1) (Nat.succ_ne_zero k)]
    infer_instance
  exact (AddMonoidHom.finite_iff_finite_ker_range
    (singularHomologyMap (newMap d) (k + 1)).toAddMonoidHom).2 ⟨inferInstance, inferInstance⟩

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
