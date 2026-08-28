import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainIntegralCohomology
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalQuasiIsoCriteria
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingBasic

/-!
# Injective coefficient changes in actual second torus cohomology

The coefficient map is literal postcomposition on the original singular
cochains.  If an integral cocycle becomes a coboundary after an injective
coefficient change, it vanishes on every original integral cycle.  The
proved native evaluation equivalence of the original period torus then
makes it an actual integral coboundary.  The source and target cohomology
objects are not replaced by coordinate or rank models.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern.Coefficients

open FirstHurewicz SingularMayerVietoris
open ConstantSheafSingularComparison

/-- Injective coefficient changes detect genuine integral coboundaries in
degree two on the original period torus. -/
theorem coefficientMap_h2_injective (p : PeriodDomain) {A : AddCommGrpCat.{0}}
    (α : AddCommGrpCat.of ℤ ⟶ A) (hα : Function.Injective α) :
    Function.Injective (HomologicalComplex.homologyMap (coefficientMap p.Torus α) 2) := by
  apply GlobalQuasiIsoCriteria.homologyMap_succ_injective_of_boundary_detection
    (coefficientMap p.Torus α) 1
  intro x hx hb
  obtain ⟨b, hb⟩ := hb
  let f : Chains p.Torus 2 →ₗ[ℤ] ℤ := addHomToIntLinearMap x
  have hf : ((SingularCohomologyFree.singularCochainComplex p.Torus).d 2 3).hom f = 0 := by
    ext z
    exact DFunLike.congr_fun hx z
  let c := SingularCohomologyFree.mkCocycle
    (SingularCohomologyFree.singularCochainComplex p.Torus) 2 f hf
  have heval : SingularCohomologyFree.singularEvaluation p.Torus 2
      (SingularCohomologyFree.cocycleClass
        (SingularCohomologyFree.singularCochainComplex p.Torus) 2 c) = 0 := by
    ext z
    obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex p.Torus) 2 z
    rw [SingularCohomologyFree.singularEvaluation_cocycle_cycle]
    change x z.val = 0
    apply hα
    have hz := ModuleHomology.cycle_condition (singularComplex p.Torus) 2 z
    have h := DFunLike.congr_fun hb z.val
    change b (((singularComplex p.Torus).d 2 1).hom z.val) = α (x z.val) at h
    rw [← h, hz, map_zero, map_zero]
  have hclass : SingularCohomologyFree.cocycleClass
      (SingularCohomologyFree.singularCochainComplex p.Torus) 2 c = 0 := by
    apply (PeriodTorusCohomology.evaluationEquiv p 2).injective
    change SingularCohomologyFree.singularEvaluation p.Torus 2 _ =
      SingularCohomologyFree.singularEvaluation p.Torus 2 0
    rw [heval, map_zero]
  obtain ⟨a, ha⟩ := (SingularCohomologyFree.cocycleClass_eq_zero_iff
    (SingularCohomologyFree.singularCochainComplex p.Torus) 2 c).mp hclass
  refine ⟨a.toAddMonoidHom, ?_⟩
  ext z
  exact DFunLike.congr_fun ha z

end Wikipedia.HopfProblem.PeriodTorusExponentialChern.Coefficients
