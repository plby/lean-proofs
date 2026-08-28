import Wikipedia.HopfProblem.HigherHurewiczNormalizedCycleAssignmentBasic
import Wikipedia.HopfProblem.HigherHurewiczHomologyDescentAugmentation
import Wikipedia.HopfProblem.HigherHurewiczPrismCycles

/-!
# Corrected normalization preserves actual homology in every positive degree

An actual based endpoint family which agrees with coherent simplex
homotopies gives the original homology class on every genuine cycle.
In positive even degree the constant corrections cancel exactly by the
proved augmentation identity. In odd degree the remaining constant cycle
is the boundary of the next constant simplex. The actual prism then
identifies the terminal class with the original one.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (n : ℕ) (x : X)
  (f : SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)

/-- On arbitrary chains the correction is exactly the coefficient sum times
the actual constant simplex. -/
theorem normalizedCycleAssignment_val_endpoint
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (hf : ∀ smp, (f smp).val = timeSlice (H' smp) 1) (c : Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      simplexEndpointOperator (n + 1) H' 1 c -
        chainAugmentation X (n + 1) c • constantSimplexChain (n + 1) x := by
  rw [normalizedCycleAssignment_val, chainLift_sub_constant]
  have hmap : chainLift X (n + 1) (fun smp => simplexChain X (n + 1) (f smp).val) =
      simplexEndpointOperator (n + 1) H' 1 := by
    apply chainMap_ext X (n + 1)
    intro smp
    rw [chainLift_simplex, simplexEndpointOperator_simplex, hf]
  rw [hmap]

/-- In positive even degree the corrected assignment is literally the terminal cycle. -/
theorem normalizedCycleAssignment_evenCycle
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (hface : FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = timeSlice (H' smp) 1)
    (heven : Even (n + 1)) (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c := by
  apply Subtype.ext
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    chainAugmentation_evenCycle X (n + 1) heven (Nat.zero_lt_succ n),
    zero_smul, sub_zero, straightenedCycle_val]

/-- In odd degree the correction is an explicit multiple of the genuine constant cycle. -/
theorem normalizedCycleAssignment_oddCycle
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (hface : FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = timeSlice (H' smp) 1)
    (hodd : Odd (n + 1)) (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c -
      chainAugmentation X (n + 1) c.val • constantSimplexCycle (n + 1) x hodd := by
  apply Subtype.ext
  change (normalizedCycleAssignment n x f c.val).val =
    (straightenedCycle n H H' hface c).val -
      chainAugmentation X (n + 1) c.val • (constantSimplexCycle (n + 1) x hodd).val
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    straightenedCycle_val, constantSimplexCycle_val]

/-- Actual coherent normalization, with its actual based endpoints, preserves
the original integral singular homology class in every positive degree. -/
theorem normalizedCycleAssignment_class
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (hface : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, timeSlice (H' smp) 0 = smp)
    (hf : ∀ smp, (f smp).val = timeSlice (H' smp) 1)
    (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    ModuleHomology.cycleClass (singularComplex X) (n + 1)
        (normalizedCycleAssignment n x f c.val) =
      ModuleHomology.cycleClass (singularComplex X) (n + 1) c := by
  by_cases heven : Even (n + 1)
  · rw [normalizedCycleAssignment_evenCycle n x f H H' hface hf heven]
    exact straightenedCycle_class n H H' hface h₀ c
  · have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp heven
    rw [normalizedCycleAssignment_oddCycle n x f H H' hface hf hodd,
      map_sub, map_zsmul, constantSimplexCycle_class, zsmul_zero, sub_zero]
    exact straightenedCycle_class n H H' hface h₀ c

end Wikipedia.HopfProblem.HigherHurewicz
