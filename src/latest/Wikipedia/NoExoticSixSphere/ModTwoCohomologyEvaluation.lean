import Wikipedia.NoExoticSixSphere.ModTwoDualFunctor
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Wikipedia.HopfProblem.SingularCohomologyCupDescent

/-!
# Actual mod-two cohomology evaluated on integral homology

Closed cochains annihilate the original boundaries, so their values
descend through the original homology quotient. Incoming coboundaries
vanish on cycles, giving a canonical evaluation on genuine cohomology.
No freeness or universal-coefficient hypothesis is needed to define it.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCohomologyEvaluation

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

abbrev Cohomology := (ModTwoDualComplex.complex K).homology n

abbrev Cocycle := SingularCohomologyFree.Cocycle (ModTwoDualComplex.complex K) n

/-- The literal additive cochain underlying the original cocycle. -/
def cochainValue (α : Cocycle K n) : K.X n →+ ZMod 2 := α.val

theorem cochainValue_boundary (α : Cocycle K n) (b : K.X (n + 1)) :
    cochainValue K n α ((K.d (n + 1) n).hom b) = 0 :=
  congrArg (fun φ : K.X (n + 1) →+ ZMod 2 => φ b)
    (SingularCohomologyFree.cocycle_condition (ModTwoDualComplex.complex K) n α)

/-- Literal evaluation on the original cycle kernel. -/
def cycleValue (α : Cocycle K n) : ModuleHomology.Cycle K n →ₗ[ℤ] ZMod 2 :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((cochainValue K n α).comp (ModuleHomology.Cycle K n).subtype.toAddMonoidHom)

theorem cycleValue_boundary (α : Cocycle K n) (b : K.X (n + 1)) :
    cycleValue K n α (ModuleHomology.boundaryCycle K n b) = 0 :=
  cochainValue_boundary K n α b

/-- Evaluation of an original cocycle on the actual integral homology quotient. -/
def homologyValue (α : Cocycle K n) : K.homology n →ₗ[ℤ] ZMod 2 :=
  PeriodTorusHigherHomology.homologyDesc K n (cycleValue K n α) (cycleValue_boundary K n α)

theorem homologyValue_cycleClass (α : Cocycle K n) (z : ModuleHomology.Cycle K n) :
    homologyValue K n α (ModuleHomology.cycleClass K n z) = cochainValue K n α z.val :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass K n
    (cycleValue K n α) (cycleValue_boundary K n α) z

/-- The actual evaluation varies linearly in the original cocycle. -/
def cocycleEvaluation : Cocycle K n →ₗ[ℤ] (K.homology n →ₗ[ℤ] ZMod 2) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := homologyValue K n
      map_zero' := by
        apply PeriodTorusHigherHomology.homologyLinearMap_ext K n
        intro z
        rw [homologyValue_cycleClass, LinearMap.zero_apply]
        rfl
      map_add' α β := by
        apply PeriodTorusHigherHomology.homologyLinearMap_ext K n
        intro z
        rw [LinearMap.add_apply, homologyValue_cycleClass,
          homologyValue_cycleClass, homologyValue_cycleClass]
        rfl }

theorem cocycleEvaluation_cycleClass (α : Cocycle K n) (z : ModuleHomology.Cycle K n) :
    cocycleEvaluation K n α (ModuleHomology.cycleClass K n z) = cochainValue K n α z.val :=
  homologyValue_cycleClass K n α z

/-- Actual incoming cochain boundaries evaluate to zero on actual homology classes. -/
theorem cocycleEvaluation_coboundary (β : (ModTwoDualComplex.complex K).X (n - 1)) :
    cocycleEvaluation K n
      (SingularCohomologyFree.coboundaryCocycle (ModTwoDualComplex.complex K) n β) = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext K n
  intro z
  rw [cocycleEvaluation_cycleClass, LinearMap.zero_apply]
  let β' : K.X (n - 1) →+ ZMod 2 := β
  change β' ((K.d n (n - 1)).hom z.val) = 0
  exact (congrArg β' (ModuleHomology.cycle_condition K n z)).trans β'.map_zero

/-- Canonical evaluation of actual mod-two cohomology on actual integral homology. -/
def evaluation : Cohomology K n →ₗ[ℤ] (K.homology n →ₗ[ℤ] ZMod 2) :=
  SingularCohomologyCup.cohomologyDesc (ModTwoDualComplex.complex K) n
    (cocycleEvaluation K n) (cocycleEvaluation_coboundary K n)

theorem evaluation_cocycleClass (α : Cocycle K n) :
    evaluation K n
        (SingularCohomologyFree.cocycleClass (ModTwoDualComplex.complex K) n α) =
      cocycleEvaluation K n α :=
  SingularCohomologyCup.cohomologyDesc_cocycleClass (ModTwoDualComplex.complex K) n
    (cocycleEvaluation K n) (cocycleEvaluation_coboundary K n) α

/-- Both genuine representatives retain the original cochain evaluation. -/
theorem evaluation_cocycle_cycle (α : Cocycle K n) (z : ModuleHomology.Cycle K n) :
    evaluation K n (SingularCohomologyFree.cocycleClass (ModTwoDualComplex.complex K) n α)
        (ModuleHomology.cycleClass K n z) = cochainValue K n α z.val := by
  exact (congrArg (fun f => f (ModuleHomology.cycleClass K n z))
    (evaluation_cocycleClass K n α)).trans (cocycleEvaluation_cycleClass K n α z)

variable {K} {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Original cochain pullback and chain pushforward preserve the actual evaluation pairing. -/
theorem evaluation_naturality (f : K ⟶ L) (a : Cohomology L n) (b : K.homology n) :
    evaluation K n ((HomologicalComplex.homologyMap (ModTwoDualComplex.map f) n).hom a) b =
      evaluation L n a ((HomologicalComplex.homologyMap f n).hom b) := by
  obtain ⟨α, rfl⟩ :=
    SingularCohomologyFree.cocycleClass_surjective (ModTwoDualComplex.complex L) n a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective K n b
  rw [SingularCohomologyFree.homologyMap_cocycleClass, evaluation_cocycle_cycle,
    ModuleHomology.homologyMap_cycleClass, evaluation_cocycle_cycle]
  have hα := SingularCohomologyFree.mapCocycles_val (ModTwoDualComplex.map f) n α
  have hz := ModuleHomology.mapCycles_val f n z
  exact (congrArg (fun ψ : K.X n →+ ZMod 2 => ψ z.val) hα).trans
    (congrArg (cochainValue L n α) hz).symm

end NoExoticSixSphere.ModTwoCohomologyEvaluation
