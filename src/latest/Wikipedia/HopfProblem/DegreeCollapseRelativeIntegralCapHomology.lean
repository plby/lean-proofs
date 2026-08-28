import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapChains
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic

/-!
# Relative integral cap descends to actual homology

The signed boundary formula sends relative cycles to absolute cycles.
For an incoming relative boundary the primitive is the capped chain
multiplied by `(-1)^p`. This gives descent to the original homology
quotients over the integers, without a duality assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris
open NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem boundary_cap_closed (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : (complex U).X (p + q + 1)) :
    ((singularComplex X).d (q + 1) q).hom
      (capInDegree U (p := p) (q := q + 1) (by omega) α c) =
        (-1 : ℤ) ^ p • capInDegree U rfl α
          (((complex U).d (p + q + 1) (p + q)).hom c) := by
  have he := cap_boundary U p q α c
  rw [hα, capInDegree_zero, LinearMap.zero_apply, zero_add] at he
  have hs := congrArg (fun z : Chains X q ↦ (-1 : ℤ) ^ p • z) he
  rw [← mul_zsmul, IntegralCap.sign_mul_self, one_zsmul] at hs
  exact hs.symm

theorem cap_is_cycle (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (complex U) (p + q)) :
    ((singularComplex X).d q (q - 1)).hom (capInDegree U (q := q) rfl α c.val) = 0 := by
  cases q with
  | zero =>
      change ((singularComplex X).d 0 0).hom _ = 0
      rw [(singularComplex X).shape 0 0 (by simp)]
      rfl
  | succ q =>
      have hc := ModuleHomology.cycle_condition (complex U) (p + (q + 1)) c
      change ((complex U).d (p + q + 1) ((p + q + 1) - 1)).hom c.val = 0 at hc
      rw [show (p + q + 1) - 1 = p + q by omega] at hc
      have he := boundary_cap_closed U p q α hα c.val
      rw [hc, map_zero, zsmul_zero] at he
      exact he

/-- The cap operation on the genuine cycle kernels. -/
def capCycles (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    ModuleHomology.Cycle (complex U) (p + q) →ₗ[ℤ]
      ModuleHomology.Cycle (singularComplex X) q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun c => ModuleHomology.mkCycle (singularComplex X) q
        (capInDegree U (q := q) rfl α c.val) (cap_is_cycle U p q α hα c)
      map_zero' := Subtype.ext (map_zero (capInDegree U (q := q) rfl α))
      map_add' c d := Subtype.ext (map_add (capInDegree U (q := q) rfl α) c.val d.val) }

theorem capCycles_val (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (complex U) (p + q)) :
    (capCycles U p q α hα c).val = capInDegree U (q := q) rfl α c.val := rfl

/-- The sign is part of the actual integral boundary witness. -/
theorem capCycles_boundary_class_zero (p q : ℕ) (α : Cochain U p)
    (hα : coboundary U α = 0) (b : (complex U).X (p + q + 1)) :
    ModuleHomology.cycleClass (singularComplex X) q
      (capCycles U p q α hα (ModuleHomology.boundaryCycle (complex U) (p + q) b)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) q _).mpr
  refine ⟨(-1 : ℤ) ^ p •
    capInDegree U (p := p) (q := q + 1) (n := p + q + 1) (by omega) α b, ?_⟩
  rw [map_zsmul, boundary_cap_closed U p q α hα b,
    ← mul_zsmul, IntegralCap.sign_mul_self, one_zsmul]
  rfl

def capCycleClass (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    ModuleHomology.Cycle (complex U) (p + q) →ₗ[ℤ] (singularComplex X).homology q :=
  (ModuleHomology.cycleClass (singularComplex X) q).comp (capCycles U p q α hα)

/-- Relative homology capped with a relative integral cocycle. -/
def homologyCap (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    (complex U).homology (p + q) →ₗ[ℤ] (singularComplex X).homology q :=
  PeriodTorusHigherHomology.homologyDesc (complex U) (p + q)
    (capCycleClass U p q α hα) (capCycles_boundary_class_zero U p q α hα)

theorem homologyCap_cycleClass (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (complex U) (p + q)) :
    homologyCap U p q α hα (ModuleHomology.cycleClass (complex U) (p + q) c) =
      ModuleHomology.cycleClass (singularComplex X) q (capCycles U p q α hα c) :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (complex U) (p + q)
    (capCycleClass U p q α hα) (capCycles_boundary_class_zero U p q α hα) c

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
