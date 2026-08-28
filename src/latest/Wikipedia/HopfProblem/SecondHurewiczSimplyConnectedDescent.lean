import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Wikipedia.HopfProblem.SingularMayerVietorisSequence

/-!
# Linear descent from actual singular two-chains

A linear map on integral singular two-chains which vanishes on all actual
three-boundaries restricts to cycles and descends through the canonical
module-homology quotient. Its domain is Mathlib's actual singular homology,
not a replacement quotient. The existing arbitrary-degree descent theorem
provides the construction and its universal property.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

variable (F : Chains X 2 →ₗ[ℤ] M)
  (hF : ∀ b : Chains X 3, F (((singularComplex X).d 3 2).hom b) = 0)

/-- A chain-linear map annihilating genuine boundaries descends to the actual
integral singular second homology group. -/
def secondHomologyDesc : SingularHomology X 2 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (singularComplex X) 2
    (F.comp (ModuleHomology.Cycle (singularComplex X) 2).subtype) (fun b => hF b)

@[simp] theorem secondHomologyDesc_cycleClass
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    secondHomologyDesc F hF (ModuleHomology.cycleClass (singularComplex X) 2 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (singularComplex X) 2 _ _ c

/-- The defining cycle-evaluation formula as an equality of linear maps. -/
theorem secondHomologyDesc_comp_cycleClass :
    (secondHomologyDesc F hF).comp (ModuleHomology.cycleClass (singularComplex X) 2) =
      F.comp (ModuleHomology.Cycle (singularComplex X) 2).subtype :=
  PeriodTorusHigherHomology.homologyDesc_comp_cycleClass (singularComplex X) 2 _ _

/-- Evaluation on actual cycle representatives uniquely determines the descent. -/
theorem secondHomologyDesc_unique (g : SingularHomology X 2 →ₗ[ℤ] M)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) 2,
      g (ModuleHomology.cycleClass (singularComplex X) 2 c) = F c.1) :
    g = secondHomologyDesc F hF :=
  PeriodTorusHigherHomology.homologyDesc_unique (singularComplex X) 2 _ _ g hg

/-- A representative-level identity suffices to prove that a linear map
back to second homology is a left inverse of the descent. -/
theorem comp_secondHomologyDesc_eq_id (g : M →ₗ[ℤ] SingularHomology X 2)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) 2,
      g (F c.1) = ModuleHomology.cycleClass (singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass,
    LinearMap.id_apply] using hg c

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
