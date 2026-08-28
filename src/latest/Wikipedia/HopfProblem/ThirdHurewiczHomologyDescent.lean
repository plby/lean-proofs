import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Wikipedia.HopfProblem.SingularMayerVietorisSequence

/-!
# Linear descent from actual singular three-chains

The arbitrary-degree module-homology descent restricts a linear assignment
on singular three-chains to actual cycles and then descends to Mathlib's
integral singular third homology. The only condition on the assignment is
that it annihilates the actual differential from degree four.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

variable (F : Chains X 3 →ₗ[ℤ] M)
  (hF : ∀ b : Chains X 4, F (((singularComplex X).d 4 3).hom b) = 0)

/-- Descent of a chain-linear assignment to actual integral singular third homology. -/
def thirdHomologyDesc : SingularHomology X 3 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (singularComplex X) 3
    (F.comp (ModuleHomology.Cycle (singularComplex X) 3).subtype) (fun b => hF b)

@[simp] theorem thirdHomologyDesc_cycleClass
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    thirdHomologyDesc F hF (ModuleHomology.cycleClass (singularComplex X) 3 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (singularComplex X) 3 _ _ c

/-- The cycle-evaluation identity as an equality of linear maps. -/
theorem thirdHomologyDesc_comp_cycleClass :
    (thirdHomologyDesc F hF).comp (ModuleHomology.cycleClass (singularComplex X) 3) =
      F.comp (ModuleHomology.Cycle (singularComplex X) 3).subtype :=
  PeriodTorusHigherHomology.homologyDesc_comp_cycleClass (singularComplex X) 3 _ _

/-- Actual cycle representatives uniquely determine the descended linear map. -/
theorem thirdHomologyDesc_unique (g : SingularHomology X 3 →ₗ[ℤ] M)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) 3,
      g (ModuleHomology.cycleClass (singularComplex X) 3 c) = F c.1) :
    g = thirdHomologyDesc F hF :=
  PeriodTorusHigherHomology.homologyDesc_unique (singularComplex X) 3 _ _ g hg

/-- A left-inverse identity can be checked on actual cycle representatives. -/
theorem comp_thirdHomologyDesc_eq_id (g : M →ₗ[ℤ] SingularHomology X 3)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) 3,
      g (F c.1) = ModuleHomology.cycleClass (singularComplex X) 3 c) :
    g.comp (thirdHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (singularComplex X) 3
  intro c
  simpa only [LinearMap.comp_apply, thirdHomologyDesc_cycleClass,
    LinearMap.id_apply] using hg c

end Wikipedia.HopfProblem.ThirdHurewicz
