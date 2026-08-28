import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexAxes
import Mathlib.Algebra.Exact.Basic

/-!
# The actual branch-to-axis-to-point analytic-germ differentials

The three pairwise intersections are ordered as `(01,02,12)`, hence as
ambient axes `(2,1,0)`.  The differentials are actual restrictions with
alternating signs.  A cocycle of axis germs has an explicit preimage made
from analytic coordinate extensions and constant germs.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open Germs ToricCharts

local notation "εA" => Germs.eval (0 : ℂ)
local notation "cA" => Germs.constant (0 : ℂ)
local notation "cB" => Germs.constant (0 : CoordinateSpace 2)

/-- Differences on the three actual pairwise intersection axes. -/
def tripleDifference : (Fin 3 → BranchGerm) →+ (Fin 3 → AxisGerm) where
  toFun f := ![axisRestriction 1 (f 0) - axisRestriction 1 (f 1),
    axisRestriction 0 (f 0) - axisRestriction 1 (f 2),
    axisRestriction 0 (f 1) - axisRestriction 0 (f 2)]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' f g := by
    funext i
    fin_cases i <;> simp [sub_add_sub_comm]

@[simp] theorem tripleDifference_apply_0 (f : Fin 3 → BranchGerm) :
    tripleDifference f 0 = axisRestriction 1 (f 0) - axisRestriction 1 (f 1) := rfl

@[simp] theorem tripleDifference_apply_1 (f : Fin 3 → BranchGerm) :
    tripleDifference f 1 = axisRestriction 0 (f 0) - axisRestriction 1 (f 2) := rfl

@[simp] theorem tripleDifference_apply_2 (f : Fin 3 → BranchGerm) :
    tripleDifference f 2 = axisRestriction 0 (f 1) - axisRestriction 0 (f 2) := rfl

theorem tripleDifference_eq_zero_iff (f : Fin 3 → BranchGerm) :
    tripleDifference f = 0 ↔
      axisRestriction 1 (f 0) = axisRestriction 1 (f 1) ∧
      axisRestriction 0 (f 0) = axisRestriction 1 (f 2) ∧
      axisRestriction 0 (f 1) = axisRestriction 0 (f 2) := by
  constructor
  · intro h
    exact ⟨sub_eq_zero.mp (congrFun h 0), sub_eq_zero.mp (congrFun h 1),
      sub_eq_zero.mp (congrFun h 2)⟩
  · rintro ⟨h01, h02, h12⟩
    funext i
    fin_cases i
    · exact sub_eq_zero.mpr h01
    · exact sub_eq_zero.mpr h02
    · exact sub_eq_zero.mpr h12

/-- Alternating evaluation of the actual axis germs at the triple point. -/
def tripleAugmentation : (Fin 3 → AxisGerm) →+ ℂ where
  toFun g := εA (g 0) - εA (g 1) + εA (g 2)
  map_zero' := by simp
  map_add' f g := by
    simp only [Pi.add_apply, map_add]
    abel

@[simp] theorem tripleAugmentation_apply (g : Fin 3 → AxisGerm) :
    tripleAugmentation g = εA (g 0) - εA (g 1) + εA (g 2) := rfl

/-- The two actual analytic restriction differentials compose to zero. -/
theorem tripleAugmentation_difference (f : Fin 3 → BranchGerm) :
    tripleAugmentation (tripleDifference f) = 0 := by
  change εA (axisRestriction 1 (f 0) - axisRestriction 1 (f 1)) -
    εA (axisRestriction 0 (f 0) - axisRestriction 1 (f 2)) +
    εA (axisRestriction 0 (f 1) - axisRestriction 0 (f 2)) = 0
  simp only [map_sub, eval_axisRestriction]
  abel

theorem tripleAugmentation_comp_difference :
    tripleAugmentation.comp tripleDifference = 0 := by
  apply AddMonoidHom.ext
  exact tripleAugmentation_difference

/-- Explicit analytic plane germs lifting a compatible axis cocycle. -/
def tripleAxisLift (g : Fin 3 → AxisGerm) : Fin 3 → BranchGerm :=
  ![0, -axisExtension 1 (g 0),
    -axisExtension 0 (g 2) - cB (εA (g 0)) - axisExtension 1 (g 1) + cB (εA (g 1))]

/-- The lift is an actual preimage of every cocycle, including its values
at the triple intersection. -/
theorem tripleDifference_axisLift (g : Fin 3 → AxisGerm)
    (hg : tripleAugmentation g = 0) : tripleDifference (tripleAxisLift g) = g := by
  have hc : cA (εA (g 0)) - cA (εA (g 1)) + cA (εA (g 2)) = 0 := by
    have h := congrArg cA hg
    simpa only [tripleAugmentation_apply, map_add, map_sub, map_zero] using h
  funext i
  fin_cases i
  · change axisRestriction 1 0 - axisRestriction 1 (-axisExtension 1 (g 0)) = g 0
    simp only [map_zero, map_neg, axisRestriction_extension, zero_sub, neg_neg]
  · change axisRestriction 0 0 - axisRestriction 1
      (-axisExtension 0 (g 2) - cB (εA (g 0)) - axisExtension 1 (g 1) +
        cB (εA (g 1))) = g 1
    simp only [map_zero, map_add, map_sub, map_neg, axisRestriction_constant,
      axisRestriction_extension,
      axisRestriction_extension_ne (show (1 : Fin 2) ≠ 0 by decide)]
    calc
      _ = g 1 + (cA (εA (g 0)) - cA (εA (g 1)) + cA (εA (g 2))) := by abel
      _ = g 1 := by rw [hc, add_zero]
  · change axisRestriction 0 (-axisExtension 1 (g 0)) - axisRestriction 0
      (-axisExtension 0 (g 2) - cB (εA (g 0)) - axisExtension 1 (g 1) +
        cB (εA (g 1))) = g 2
    simp only [map_add, map_sub, map_neg, axisRestriction_constant,
      axisRestriction_extension,
      axisRestriction_extension_ne (show (0 : Fin 2) ≠ 1 by decide)]
    abel

/-- Exactness at the actual axis-germ term, by the explicit analytic lift. -/
theorem tripleDifference_exact : Function.Exact tripleDifference tripleAugmentation := by
  intro g
  constructor
  · intro hg
    exact ⟨tripleAxisLift g, tripleDifference_axisLift g hg⟩
  · rintro ⟨f, rfl⟩
    exact tripleAugmentation_difference f

theorem tripleAugmentation_ker :
    tripleAugmentation.ker = tripleDifference.range :=
  AddMonoidHom.exact_iff.mp tripleDifference_exact

/-- Evaluation at the triple point has an actual constant-germ preimage. -/
theorem tripleAugmentation_surjective : Function.Surjective tripleAugmentation := by
  intro c
  refine ⟨![cA c, 0, 0], ?_⟩
  change εA (cA c) - εA 0 + εA 0 = c
  simp only [Germs.eval_constant, map_zero, sub_zero, add_zero]

/-- The two-plane differential is restriction difference on their actual axis. -/
def doubleDifference : (Fin 2 → BranchGerm) →+ AxisGerm where
  toFun f := axisRestriction 1 (f 0) - axisRestriction 1 (f 1)
  map_zero' := by simp
  map_add' f g := by
    simp only [Pi.add_apply, map_add]
    abel

@[simp] theorem doubleDifference_apply (f : Fin 2 → BranchGerm) :
    doubleDifference f = axisRestriction 1 (f 0) - axisRestriction 1 (f 1) := rfl

theorem doubleDifference_eq_zero_iff (f : Fin 2 → BranchGerm) :
    doubleDifference f = 0 ↔ axisRestriction 1 (f 0) = axisRestriction 1 (f 1) :=
  sub_eq_zero

theorem doubleDifference_surjective : Function.Surjective doubleDifference := by
  intro g
  refine ⟨![axisExtension 1 g, 0], ?_⟩
  change axisRestriction 1 (axisExtension 1 g) - axisRestriction 1 0 = g
  rw [axisRestriction_extension, map_zero, sub_zero]

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex
