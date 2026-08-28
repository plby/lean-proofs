import Wikipedia.NoExoticSixSphere.RelativeModTwoCapChains

/-!
# Relative homology capped with a relative cocycle

The actual relative differential formula sends cycles to absolute cycles.
Every relative boundary has the explicit capped-chain primitive. Thus the
operation descends to the original relative homology, without choosing a
homology model or assuming any duality theorem.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cochain coboundary)

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- A relative cocycle sends actual relative cycles to actual absolute cycles. -/
theorem cap_is_cycle (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q)) :
    ((modComplex 2 X).d q (q - 1)).hom (capInDegree U (q := q) rfl α c.val) = 0 := by
  cases q with
  | zero =>
      change ((modComplex 2 X).d 0 0).hom _ = 0
      rw [(modComplex 2 X).shape 0 0 (by simp)]
      rfl
  | succ q =>
      have hc := ModuleHomology.cycle_condition
        (RelativeCoefficients.complex Coefficient U) (p + (q + 1)) c
      change ((RelativeCoefficients.complex Coefficient U).d
        (p + q + 1) ((p + q + 1) - 1)).hom c.val = 0 at hc
      rw [show (p + q + 1) - 1 = p + q by omega] at hc
      have he := boundary_capInDegree U (p := p) (q := q) rfl α c.val
      rw [hc, map_zero, hα, capInDegree_zero, LinearMap.zero_apply, add_zero] at he
      exact he

/-- Cap on the original relative and absolute cycle kernels. -/
def capCycles (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q) →ₗ[ℤ]
      ModuleHomology.Cycle (modComplex 2 X) q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun c => ModuleHomology.mkCycle (modComplex 2 X) q
        (capInDegree U (q := q) rfl α c.val) (cap_is_cycle U p q α hα c)
      map_zero' := Subtype.ext (map_zero (capInDegree U (q := q) rfl α))
      map_add' c d := Subtype.ext (map_add (capInDegree U (q := q) rfl α) c.val d.val) }

theorem capCycles_val (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q)) :
    (capCycles U p q α hα c).val = capInDegree U (q := q) rfl α c.val := rfl

/-- An actual relative boundary has an explicit absolute capped-chain primitive. -/
theorem capCycles_boundary_class_zero (p q : ℕ) (α : Cochain U p)
    (hα : coboundary U α = 0)
    (b : (RelativeCoefficients.complex Coefficient U).X (p + q + 1)) :
    ModuleHomology.cycleClass (modComplex 2 X) q
      (capCycles U p q α hα
        (ModuleHomology.boundaryCycle (RelativeCoefficients.complex Coefficient U) (p + q) b)) =
      0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (modComplex 2 X) q _).mpr
  refine ⟨capInDegree U (p := p) (q := q + 1) (n := p + q + 1) (by omega) α b, ?_⟩
  have he := boundary_capInDegree U (p := p) (q := q) rfl α b
  rw [hα, capInDegree_zero, LinearMap.zero_apply, add_zero] at he
  exact he

/-- The class of an actual capped relative cycle. -/
def capCycleClass (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q) →ₗ[ℤ]
      ModHomology 2 X q :=
  (ModuleHomology.cycleClass (modComplex 2 X) q).comp (capCycles U p q α hα)

/-- Cap with a relative cocycle on the actual relative homology groups. -/
def homologyCap (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0) :
    (RelativeCoefficients.complex Coefficient U).homology (p + q) →ₗ[ℤ] ModHomology 2 X q :=
  PeriodTorusHigherHomology.homologyDesc (RelativeCoefficients.complex Coefficient U) (p + q)
    (capCycleClass U p q α hα) (capCycles_boundary_class_zero U p q α hα)

/-- Every actual relative cycle retains its capped-chain representative. -/
theorem homologyCap_cycleClass (p q : ℕ) (α : Cochain U p) (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q)) :
    homologyCap U p q α hα
        (ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient U) (p + q) c) =
      ModuleHomology.cycleClass (modComplex 2 X) q (capCycles U p q α hα c) :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass
    (RelativeCoefficients.complex Coefficient U) (p + q)
    (capCycleClass U p q α hα) (capCycles_boundary_class_zero U p q α hα) c

end NoExoticSixSphere.RelativeModTwoCap
