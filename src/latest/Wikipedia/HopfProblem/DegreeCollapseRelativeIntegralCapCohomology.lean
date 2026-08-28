import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapHomology
import Wikipedia.HopfProblem.SingularCohomologyCupDescent

/-!
# The cap product on actual relative integral cohomology and homology

The incoming-coboundary primitive has coefficient `-(-1)^p`.
After checking that primitive, the actual cap map descends through
both original cycle quotients. No fundamental class or duality theorem
is assumed or asserted here.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris
open NoExoticSixSphere.RelativeSingularHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev Cohomology (p : ℕ) := (cochainComplex U).homology p

abbrev Cocycle (p : ℕ) := SingularCohomologyFree.Cocycle (cochainComplex U) p

theorem cocycle_coboundary_zero (p : ℕ) (α : Cocycle U p) : coboundary U α.val = 0 :=
  SingularCohomologyFree.cocycle_condition (cochainComplex U) p α

theorem coboundary_squared (p : ℕ) (α : Cochain U p) :
    coboundary U (coboundary U α) = 0 :=
  congrArg (fun f : (cochainComplex U).X p ⟶ (cochainComplex U).X (p + 2) => f.hom α)
    ((cochainComplex U).d_comp_d p (p + 1) (p + 2))

theorem homologyCap_zero (p q : ℕ) (h0 : coboundary U (0 : Cochain U p) = 0) :
    homologyCap U p q (0 : Cochain U p) h0 = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (complex U) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  have he : capCycles U p q (0 : Cochain U p) h0 c = 0 := by
    apply Subtype.ext
    change capInDegree U (p := p) (q := q) rfl (0 : Cochain U p) c.val = 0
    rw [capInDegree_zero, LinearMap.zero_apply]
  rw [he, map_zero]

theorem homologyCap_add (p q : ℕ) (α β : Cochain U p)
    (hα : coboundary U α = 0) (hβ : coboundary U β = 0)
    (hαβ : coboundary U (α + β) = 0) :
    homologyCap U p q (α + β) hαβ = homologyCap U p q α hα + homologyCap U p q β hβ := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (complex U) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.add_apply,
    homologyCap_cycleClass, homologyCap_cycleClass]
  have he : capCycles U p q (α + β) hαβ c =
      capCycles U p q α hα c + capCycles U p q β hβ c := by
    apply Subtype.ext
    exact LinearMap.congr_fun (capInDegree_add U (p := p) (q := q) rfl α β) c.val
  exact (congrArg (ModuleHomology.cycleClass (singularComplex X) q) he).trans (map_add _ _ _)

/-- An incoming relative coboundary caps to an explicit signed absolute boundary. -/
theorem homologyCap_coboundary (p q : ℕ) (β : Cochain U p) :
    homologyCap U (p + 1) q (coboundary U β) (coboundary_squared U p β) = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (complex U) ((p + 1) + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) q _).mpr
  refine ⟨-((-1 : ℤ) ^ p) •
    capInDegree U (p := p) (q := q + 1) (n := (p + 1) + q) (by omega) β c.val, ?_⟩
  have hc := ModuleHomology.cycle_condition (complex U) ((p + 1) + q) c
  rw [show ((p + 1) + q) - 1 = p + q by omega] at hc
  have he := cap_boundary_inDegree U (p := p) (q := q) (n := (p + 1) + q)
    (by omega) β c.val
  rw [hc, map_zero] at he
  rw [map_zsmul, neg_zsmul]
  exact (eq_neg_of_add_eq_zero_left he.symm).symm

/-- Cap varies linearly with the original relative integral cocycle. -/
def capCocycles (p q : ℕ) : Cocycle U p →ₗ[ℤ]
    ((complex U).homology (p + q) →ₗ[ℤ] (singularComplex X).homology q) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun α => homologyCap U p q α.val (cocycle_coboundary_zero U p α)
      map_zero' := homologyCap_zero U p q _
      map_add' α β := homologyCap_add U p q α.val β.val _ _ _ }

theorem capCocycles_apply (p q : ℕ) (α : Cocycle U p) :
    capCocycles U p q α = homologyCap U p q α.val (cocycle_coboundary_zero U p α) := rfl

theorem capCocycles_coboundary (p q : ℕ) (β : (cochainComplex U).X (p - 1)) :
    capCocycles U p q
      (SingularCohomologyFree.coboundaryCocycle (cochainComplex U) p β) = 0 := by
  cases p with
  | zero =>
      have he : SingularCohomologyFree.coboundaryCocycle (cochainComplex U) 0 β = 0 := by
        apply Subtype.ext
        change ((cochainComplex U).d 0 0).hom β = 0
        rw [(cochainComplex U).shape 0 0 (by simp)]
        rfl
      rw [he, map_zero]
  | succ p =>
      exact homologyCap_coboundary U p q β

/-- The actual integral cap product, with relative inputs and absolute output. -/
def capProduct (p q : ℕ) : Cohomology U p →ₗ[ℤ]
    ((complex U).homology (p + q) →ₗ[ℤ] (singularComplex X).homology q) :=
  SingularCohomologyCup.cohomologyDesc (cochainComplex U) p (capCocycles U p q)
    (capCocycles_coboundary U p q)

theorem capProduct_cocycleClass (p q : ℕ) (α : Cocycle U p) :
    capProduct U p q (SingularCohomologyFree.cocycleClass (cochainComplex U) p α) =
      homologyCap U p q α.val (cocycle_coboundary_zero U p α) :=
  SingularCohomologyCup.cohomologyDesc_cocycleClass (cochainComplex U) p
    (capCocycles U p q) (capCocycles_coboundary U p q) α

/-- The original cap chain represents the product of the original two classes. -/
theorem capProduct_cocycle_cycle (p q : ℕ) (α : Cocycle U p)
    (c : ModuleHomology.Cycle (complex U) (p + q)) :
    capProduct U p q (SingularCohomologyFree.cocycleClass (cochainComplex U) p α)
        (ModuleHomology.cycleClass (complex U) (p + q) c) =
      ModuleHomology.cycleClass (singularComplex X) q
        (capCycles U p q α.val (cocycle_coboundary_zero U p α) c) := by
  rw [capProduct_cocycleClass, homologyCap_cycleClass]

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
