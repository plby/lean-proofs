import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Actual simplex-prism straightening in every positive degree

The parameter `n` denotes the lower of two adjacent simplex dimensions.
Compatible homotopies in dimensions `n` and `n + 1` act on the actual
singular cycles in degree `n + 1`. The genuine prism in degree `n + 2`
is a boundary witness for preservation of their original homology class.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]

variable (n : ℕ)
  (H : SingularSimplex X n → C(I × Simplex n, X))
  (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
  (h : FaceCompatibleHomotopies n H H')

/-- The genuine terminal cycle in positive degree `n + 1`. -/
def straightenedCycle (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    ModuleHomology.Cycle (singularComplex X) (n + 1) :=
  ModuleHomology.mkCycle (singularComplex X) (n + 1)
    (simplexEndpointOperator (n + 1) H' 1 c.1) (by
      have hc : ((singularComplex X).d (n + 1) n).hom c.1 = 0 := by
        exact ModuleHomology.cycle_condition (singularComplex X) (n + 1) c
      rw [Nat.add_sub_cancel, simplexEndpointOperator_boundary n H H' h, hc, map_zero])

@[simp] theorem straightenedCycle_val
    (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    (straightenedCycle n H H' h c).1 = simplexEndpointOperator (n + 1) H' 1 c.1 := rfl

variable (h₀ : ∀ smp, timeSlice (H' smp) 0 = smp)

include h₀

/-- The actual singular prism bounds the terminal cycle minus the original one. -/
theorem straightenedCycle_boundary
    (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    ((singularComplex X).d (n + 2) (n + 1)).hom (simplexPrismOperator (n + 1) H' c.1) =
      (straightenedCycle n H H' h c).1 - c.1 := by
  have hc : ((singularComplex X).d (n + 1) n).hom c.1 = 0 := by
    exact ModuleHomology.cycle_condition (singularComplex X) (n + 1) c
  rw [simplexPrismOperator_boundary n H H' h,
    simplexEndpointOperator_zero (n + 1) H' h₀, hc, map_zero, sub_zero]
  rfl

/-- Coherent geometric straightening preserves actual positive-degree homology. -/
theorem straightenedCycle_class
    (c : ModuleHomology.Cycle (singularComplex X) (n + 1)) :
    ModuleHomology.cycleClass (singularComplex X) (n + 1) (straightenedCycle n H H' h c) =
      ModuleHomology.cycleClass (singularComplex X) (n + 1) c := by
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) (n + 1) _ _).mpr
  exact ⟨simplexPrismOperator (n + 1) H' c.1, straightenedCycle_boundary n H H' h h₀ c⟩

end Wikipedia.HopfProblem.HigherHurewicz
