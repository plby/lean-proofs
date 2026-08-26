/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBounds

/-!
# Universe-polymorphic coordinate removal bounds

The original coarse bound placed host vertices and root-slot labels in one
universe.  Concrete rich applications use independent host and reduced-graph
universes, so this file records the same argument with those universes split.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral

open Finset Fintype
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds

universe u v

variable {s : ℕ} {B : Type u} {RootSlot : Type v}

/-- Universe-polymorphic form of the cleaning-budget identity. -/
theorem coordinateRemovalBudget_eq
    [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (rho : ℝ)
    (rootSlot : Fin s → RootSlot)
    (rootWhole : RootSlot → Finset B)
    (interiorWhole : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole i a =
      ((#(childSegments F i a) + #(internalTargets F i a) : ℕ) : ℝ) *
        (rho * #(rawCandidate F rootSlot rootWhole interiorWhole i a)) := by
  simp only [coordinateRemovalBudget, sum_const, nsmul_eq_mul, Nat.cast_add]
  ring

/-- The coarse removal bound with independent host and root-slot universes. -/
theorem coordinateRemovalBudget_le
    [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (rho removalBudget : ℝ)
    (rootSlot : Fin s → RootSlot)
    (rootWhole : RootSlot → Finset B)
    (interiorWhole : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (segmentBound wholeBound : ℕ)
    (hrho : 0 ≤ rho)
    (hsegment : ∀ i, F.segments.size i ≤ segmentBound)
    (hwhole : ∀ i a,
      #(rawCandidate F rootSlot rootWhole interiorWhole i a) ≤ wholeBound)
    (hbudget : ((s + segmentBound : ℕ) : ℝ) *
      (rho * wholeBound) ≤ removalBudget) :
    ∀ i a, coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole
      i a ≤ removalBudget := by
  intro i a
  rw [coordinateRemovalBudget_eq]
  have hcount : #(childSegments F i a) + #(internalTargets F i a) ≤
      s + segmentBound :=
    Nat.add_le_add (card_childSegments_le F i a)
      ((card_internalTargets_le F i a).trans (hsegment i))
  have hraw :
      rho * (#(rawCandidate F rootSlot rootWhole interiorWhole i a) : ℝ) ≤
        rho * wholeBound := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hwhole i a) hrho
  exact (mul_le_mul (by exact_mod_cast hcount) hraw
    (mul_nonneg hrho (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)).trans hbudget

end Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral

#print axioms Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral.coordinateRemovalBudget_le
