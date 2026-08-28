import Wikipedia.HopfProblem.SingularCohomologyFreeComplex
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationClosed

/-!
# Natural evaluation of actual integral cohomology

Actual cohomology is the categorical homology of the literal integral
cochain complex `Hom(Cₙ, ℤ)`.  Cocycles evaluate on actual homology, and
coboundaries evaluate to zero.  This constructs the canonical evaluation
map without any freeness, projectivity, or universal-coefficient assumption.
Its cycle formula proves naturality for actual chain maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- Actual integral cohomology, computed by the literal cochain dual. -/
abbrev Cohomology := (dualComplex K).homology n

/-- A cocycle in the actual dual complex annihilates the actual chain boundaries. -/
theorem cocycle_isClosedFunctional (c : Cocycle (dualComplex K) n) :
    IsClosedFunctional K n c.val := by
  intro b
  exact congrArg (fun φ : K.X (n + 1) →ₗ[ℤ] ℤ => φ b)
    (cocycle_condition (dualComplex K) n c)

/-- Evaluation of actual cocycles on actual homology classes. -/
def cocycleEvaluation : Cocycle (dualComplex K) n →ₗ[ℤ] (K.homology n →ₗ[ℤ] ℤ) where
  toFun c := evaluationOfClosed K n c.val (cocycle_isClosedFunctional K n c)
  map_add' c d := by
    ext a
    obtain ⟨z, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
    simp only [LinearMap.add_apply, evaluationOfClosed_cycleClass]
    rfl
  map_smul' r c := by
    ext a
    obtain ⟨z, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
    simp only [RingHom.id_apply, LinearMap.smul_apply, evaluationOfClosed_cycleClass]
    rfl

@[simp] theorem cocycleEvaluation_cycleClass (c : Cocycle (dualComplex K) n)
    (z : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cocycleEvaluation K n c
      (SingularMayerVietoris.ModuleHomology.cycleClass K n z) = c.val z.val :=
  evaluationOfClosed_cycleClass K n c.val (cocycle_isClosedFunctional K n c) z

/-- The actual incoming coboundaries lie in the kernel of evaluation. -/
theorem cocycleEvaluation_coboundaries :
    FirstHurewicz.ChainHomology.ShortBoundaries ((dualComplex K).sc n) ≤
      LinearMap.ker (cocycleEvaluation K n) := by
  rintro c ⟨b, rfl⟩
  change cocycleEvaluation K n (((dualComplex K).sc n).moduleCatToCycles b) = 0
  ext a
  obtain ⟨z, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
  apply (cocycleEvaluation_cycleClass K n
    (((dualComplex K).sc n).moduleCatToCycles b) z).trans
  have hz : (K.d n ((ComplexShape.up ℕ).prev n)).hom z.val = 0 := by
    rw [prev_nat]
    exact SingularMayerVietoris.ModuleHomology.cycle_condition K n z
  let b' : K.X ((ComplexShape.up ℕ).prev n) →ₗ[ℤ] ℤ := b
  change b' ((K.d n ((ComplexShape.up ℕ).prev n)).hom z.val) = 0
  rw [hz, map_zero]

/-- The canonical evaluation map from actual cohomology to the integral dual of actual homology. -/
def cohomologyEvaluation : Cohomology K n →ₗ[ℤ] (K.homology n →ₗ[ℤ] ℤ) :=
  ((FirstHurewicz.ChainHomology.ShortBoundaries ((dualComplex K).sc n)).liftQ
    (cocycleEvaluation K n) (cocycleEvaluation_coboundaries K n)).comp
      ((dualComplex K).sc n).moduleCatHomologyIso.hom.hom

/-- The actual cohomology-class map preserves the literal cocycle evaluation. -/
@[simp] theorem cohomologyEvaluation_cocycleClass (c : Cocycle (dualComplex K) n) :
    cohomologyEvaluation K n (cocycleClass (dualComplex K) n c) =
      cocycleEvaluation K n c := by
  change (FirstHurewicz.ChainHomology.ShortBoundaries ((dualComplex K).sc n)).liftQ
    (cocycleEvaluation K n) (cocycleEvaluation_coboundaries K n)
      (((dualComplex K).sc n).moduleCatHomologyIso.hom.hom
        (((dualComplex K).sc n).moduleCatHomologyIso.inv.hom
          (Submodule.Quotient.mk c))) = _
  have h := congrArg (fun f => f.hom (Submodule.Quotient.mk c))
    ((dualComplex K).sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg
    ((FirstHurewicz.ChainHomology.ShortBoundaries ((dualComplex K).sc n)).liftQ
      (cocycleEvaluation K n) (cocycleEvaluation_coboundaries K n)) h

/-- Evaluation of an actual cohomology class on an actual cycle is the original cochain value. -/
theorem cohomologyEvaluation_cocycle_cycle (c : Cocycle (dualComplex K) n)
    (z : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cohomologyEvaluation K n (cocycleClass (dualComplex K) n c)
      (SingularMayerVietoris.ModuleHomology.cycleClass K n z) = c.val z.val := by
  rw [cohomologyEvaluation_cocycleClass, cocycleEvaluation_cycleClass]

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Canonical cohomology evaluation is contravariantly natural for every actual chain map. -/
theorem cohomologyEvaluation_naturality (f : K ⟶ L) (n : ℕ)
    (a : Cohomology L n) (b : K.homology n) :
    cohomologyEvaluation K n ((HomologicalComplex.homologyMap (dualMap f) n).hom a) b =
      cohomologyEvaluation L n a ((HomologicalComplex.homologyMap f n).hom b) := by
  obtain ⟨c, rfl⟩ := cocycleClass_surjective (dualComplex L) n a
  obtain ⟨z, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n b
  rw [homologyMap_cocycleClass, cohomologyEvaluation_cocycle_cycle,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    cohomologyEvaluation_cocycle_cycle, mapCocycles_val,
    SingularMayerVietoris.ModuleHomology.mapCycles_val, dualMap_f_apply]
  rfl

end Wikipedia.HopfProblem.SingularCohomologyFree
