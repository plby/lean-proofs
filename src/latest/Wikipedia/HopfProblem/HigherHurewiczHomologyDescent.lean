import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Wikipedia.HopfProblem.SingularMayerVietorisSequence

/-!
# Linear descent from actual singular chains in every degree

A linear assignment on the original integral singular chains descends to
Mathlib's actual homology whenever it annihilates the actual incoming
boundaries. This is the chain-level form of the existing arbitrary-degree
module-homology universal property.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

variable (n : ℕ) (F : Chains X n →ₗ[ℤ] M)
  (hF : ∀ b : Chains X (n + 1), F (((singularComplex X).d (n + 1) n).hom b) = 0)

/-- Descent of a chain-linear assignment to the original integral singular homology. -/
def singularHomologyDesc : SingularHomology X n →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (singularComplex X) n
    (F.comp (ModuleHomology.Cycle (singularComplex X) n).subtype) (fun b => hF b)

@[simp] theorem singularHomologyDesc_cycleClass
    (c : ModuleHomology.Cycle (singularComplex X) n) :
    singularHomologyDesc n F hF (ModuleHomology.cycleClass (singularComplex X) n c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (singularComplex X) n _ _ c

theorem singularHomologyDesc_comp_cycleClass :
    (singularHomologyDesc n F hF).comp (ModuleHomology.cycleClass (singularComplex X) n) =
      F.comp (ModuleHomology.Cycle (singularComplex X) n).subtype :=
  PeriodTorusHigherHomology.homologyDesc_comp_cycleClass (singularComplex X) n _ _

/-- Evaluation on actual cycle classes uniquely determines the descended map. -/
theorem singularHomologyDesc_unique (g : SingularHomology X n →ₗ[ℤ] M)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) n,
      g (ModuleHomology.cycleClass (singularComplex X) n c) = F c.1) :
    g = singularHomologyDesc n F hF :=
  PeriodTorusHigherHomology.homologyDesc_unique (singularComplex X) n _ _ g hg

/-- A left-inverse identity can be checked on the original cycle representatives. -/
theorem comp_singularHomologyDesc_eq_id (g : M →ₗ[ℤ] SingularHomology X n)
    (hg : ∀ c : ModuleHomology.Cycle (singularComplex X) n,
      g (F c.1) = ModuleHomology.cycleClass (singularComplex X) n c) :
    g.comp (singularHomologyDesc n F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (singularComplex X) n
  intro c
  simpa only [LinearMap.comp_apply, singularHomologyDesc_cycleClass,
    LinearMap.id_apply] using hg c

end Wikipedia.HopfProblem.HigherHurewicz
