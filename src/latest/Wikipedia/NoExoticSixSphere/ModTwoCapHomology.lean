import Wikipedia.NoExoticSixSphere.ModTwoCapBoundary
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent

/-!
# Capping actual homology classes with a closed mod-two cochain

The proved boundary formula sends actual cycles to cycles and gives an
explicit primitive for the cap of every actual boundary. Canonical
cycle-quotient descent therefore gives a map on the native singular
homology groups. Cochain-class independence is a separate next step.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- A closed cochain caps every original cycle to an original cycle. -/
theorem cap_is_cycle (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    ((modComplex 2 X).d q (q - 1)).hom (cap (q := q) α c.val) = 0 := by
  cases q with
  | zero =>
      change ((modComplex 2 X).d 0 0).hom _ = 0
      rw [(modComplex 2 X).shape 0 0 (by simp)]
      rfl
  | succ q =>
      have hc := ModuleHomology.cycle_condition (modComplex 2 X) (p + (q + 1)) c
      change ((modComplex 2 X).d (p + q + 1) ((p + q + 1) - 1)).hom c.val = 0 at hc
      rw [show (p + q + 1) - 1 = p + q by omega] at hc
      have he := boundary_cap p q α c.val
      rw [hc, map_zero, hα, capInDegree_zero, LinearMap.zero_apply, add_zero] at he
      exact he

/-- The original cap map on the genuine cycle kernels. -/
def capCycles (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0) :
    ModuleHomology.Cycle (modComplex 2 X) (p + q) →ₗ[ℤ]
      ModuleHomology.Cycle (modComplex 2 X) q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun c => ModuleHomology.mkCycle (modComplex 2 X) q (cap (q := q) α c.val)
        (cap_is_cycle p q α hα c)
      map_zero' := Subtype.ext (map_zero (cap (q := q) α))
      map_add' c d := Subtype.ext (map_add (cap (q := q) α) c.val d.val) }

theorem capCycles_val (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    (capCycles p q α hα c).val = cap (q := q) α c.val := rfl

/-- The cap of an original boundary has the explicit capped-chain primitive. -/
theorem capCycles_boundary_class_zero (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0)
    (b : ModTwoChains.Chains X (p + q + 1)) :
    ModuleHomology.cycleClass (modComplex 2 X) q
      (capCycles p q α hα (ModuleHomology.boundaryCycle (modComplex 2 X) (p + q) b)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (modComplex 2 X) q _).mpr
  refine ⟨capInDegree (p := p) (q := q + 1) (n := p + q + 1) (by omega) α b, ?_⟩
  have he := boundary_cap p q α b
  rw [hα, capInDegree_zero, LinearMap.zero_apply, add_zero] at he
  exact he

/-- The actual homology class of the capped original cycle. -/
def capCycleClass (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0) :
    ModuleHomology.Cycle (modComplex 2 X) (p + q) →ₗ[ℤ] ModHomology 2 X q :=
  (ModuleHomology.cycleClass (modComplex 2 X) q).comp (capCycles p q α hα)

/-- Capping with a closed cochain on the native singular homology groups. -/
def homologyCap (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0) :
    ModHomology 2 X (p + q) →ₗ[ℤ] ModHomology 2 X q :=
  PeriodTorusHigherHomology.homologyDesc (modComplex 2 X) (p + q)
    (capCycleClass p q α hα) (capCycles_boundary_class_zero p q α hα)

/-- The descended cap map is represented by the cap of each actual cycle representative. -/
theorem homologyCap_cycleClass (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    homologyCap p q α hα (ModuleHomology.cycleClass (modComplex 2 X) (p + q) c) =
      ModuleHomology.cycleClass (modComplex 2 X) q (capCycles p q α hα c) :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (modComplex 2 X) (p + q)
    (capCycleClass p q α hα) (capCycles_boundary_class_zero p q α hα) c

end NoExoticSixSphere.ModTwoCapProduct
