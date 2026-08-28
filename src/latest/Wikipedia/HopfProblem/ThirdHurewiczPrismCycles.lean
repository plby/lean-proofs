import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Straightening actual singular three-cycles by simplex homotopies

Face-compatible continuous homotopies on singular two- and three-simplices
give a terminal operator on actual three-cycles. The established genuine
simplex-prism formula supplies an explicit four-chain witnessing that
this operator preserves the original singular third homology class.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]

variable (H₂ : SingularSimplex X 2 → C(I × Simplex 2, X))
  (H₃ : SingularSimplex X 3 → C(I × Simplex 3, X))
  (h : FaceCompatibleHomotopies 2 H₂ H₃)

/-- The terminal operator on a genuine singular three-cycle, with its cycle
condition deduced from compatibility on the actual face inclusions. -/
def straightenedThreeCycle (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  ModuleHomology.mkCycle (singularComplex X) 3 (simplexEndpointOperator 3 H₃ 1 c.1) (by
    rw [simplexEndpointOperator_boundary 2 H₂ H₃ h,
      ModuleHomology.cycle_condition (singularComplex X) 3 c, map_zero])

@[simp] theorem straightenedThreeCycle_val
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    (straightenedThreeCycle H₂ H₃ h c).1 = simplexEndpointOperator 3 H₃ 1 c.1 := rfl

variable (h₀ : ∀ smp, timeSlice (H₃ smp) 0 = smp)

include h₀

/-- The actual singular prism is a boundary witness between the terminal
cycle and the original cycle. -/
theorem straightenedThreeCycle_boundary
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ((singularComplex X).d 4 3).hom (simplexPrismOperator 3 H₃ c.1) =
      (straightenedThreeCycle H₂ H₃ h c).1 - c.1 := by
  rw [simplexPrismOperator_boundary 2 H₂ H₃ h,
    simplexEndpointOperator_zero 3 H₃ h₀,
    ModuleHomology.cycle_condition (singularComplex X) 3 c, map_zero, sub_zero]
  rfl

/-- Straightening by these continuous homotopies preserves the actual
integral singular third homology class. -/
theorem straightenedThreeCycle_class
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.cycleClass (singularComplex X) 3 (straightenedThreeCycle H₂ H₃ h c) =
      ModuleHomology.cycleClass (singularComplex X) 3 c := by
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 3 _ _).mpr
  exact ⟨simplexPrismOperator 3 H₃ c.1, straightenedThreeCycle_boundary H₂ H₃ h h₀ c⟩

end Wikipedia.HopfProblem.ThirdHurewicz
