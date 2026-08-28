import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularIntegralClasses
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Actual integral evaluation detects a complex singular class

If the literal complex coefficient image of an integral cohomology
class vanished, its actual cocycle would be an actual coboundary.
Evaluation on a genuine integral cycle then vanishes. This proves the
needed detection without a tensor or universal-coefficient assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open FirstHurewicz ConstantSheafSingularComparison
open SheafSingularCupComparison.Singular

private theorem shortClass_projection (S : ShortComplex AddCommGrpCat.{0}) :
    S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
  change S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
    S.abLeftHomologyData.homologyIso.hom = S.abLeftHomologyData.π
  rw [S.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A vanishing original class has a preimage under its actual incoming differential. -/
theorem shortClass_zero_preimage (S : ShortComplex AddCommGrpCat.{0})
    (a : S.g.hom.ker) (h : shortClass S a = 0) : ∃ b : S.X₁, S.f b = a.val := by
  have hq : (QuotientAddGroup.mk' S.abToCycles.range) a = 0 :=
    (ConcreteCategory.congr_hom (shortClass_projection S) a).symm.trans
      ((congrArg S.abHomologyIso.hom h).trans (map_zero S.abHomologyIso.hom.hom))
  have ha : a ∈ S.abToCycles.range := (QuotientAddGroup.eq_zero_iff a).mp hq
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, congrArg Subtype.val hb⟩

variable (X : Type) [TopologicalSpace X]

/-- A zero complex coefficient image annihilates every original integral two-cycle. -/
theorem integralToComplex_two_zero_evaluation
    (a : SingularCohomologyFree.SingularCohomology X 2)
    (ha : integralToComplexCohomologyHom X 2 a = 0)
    (z : SingularMayerVietoris.SingularHomology X 2) :
    SingularCohomologyFree.singularEvaluation X 2 a z = 0 := by
  obtain ⟨c, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective
    (SingularCohomologyFree.singularCochainComplex X) 2 a
  obtain ⟨b, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective
    (singularComplex X) 2 z
  rw [integralToComplexCohomologyHom_class] at ha
  obtain ⟨u, hu⟩ := shortClass_zero_preimage
    ((singularCochainComplex X (AddCommGrpCat.of ℂ)).sc 2)
    (integralToComplexCocycle X 2 c) ha
  let u' : Cochains X (AddCommGrpCat.of ℂ) ((ComplexShape.up ℕ).prev 2) := u
  have hval := congrArg (fun φ : Cochains X (AddCommGrpCat.of ℂ) 2 => φ b.val) hu
  change u' (((singularComplex X).d 2 ((ComplexShape.up ℕ).prev 2)).hom b.val) =
    (c.val b.val : ℂ) at hval
  have hb : ((singularComplex X).d 2 ((ComplexShape.up ℕ).prev 2)).hom b.val = 0 := by
    rw [SingularCohomologyFree.prev_nat]
    exact SingularMayerVietoris.ModuleHomology.cycle_condition (singularComplex X) 2 b
  rw [hb, map_zero] at hval
  rw [SingularCohomologyFree.singularEvaluation_cocycle_cycle]
  exact (Int.cast_injective (α := ℂ))
    (hval.symm.trans (show ((0 : ℤ) : ℂ) = 0 from Int.cast_zero).symm)

/-- Nonzero literal evaluation survives the original coefficient map to complex numbers. -/
theorem integralToComplex_two_ne_zero_of_evaluation
    (a : SingularCohomologyFree.SingularCohomology X 2)
    (z : SingularMayerVietoris.SingularHomology X 2)
    (h : SingularCohomologyFree.singularEvaluation X 2 a z ≠ 0) :
    integralToComplexCohomologyHom X 2 a ≠ 0 :=
  fun ha => h (integralToComplex_two_zero_evaluation X a ha z)

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
