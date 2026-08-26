/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetUnifiedApplication

/-!
# Scalar bounds for coordinate cleaning budgets

The canonical target-cleaning budget charges the same source candidate once
for every later child segment and once for every forward internal neighbor.
This file records the corresponding coarse bound by the total number of
segments plus the size of the current segment.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds

open Finset Fintype
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

universe u

variable {s : ℕ} {B RootSlot : Type u}

/-- The cleaning budget is the number of later obligations multiplied by the
single-pair regularity loss at the current coordinate. -/
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

/-- At most all hierarchy segments can be later children of one coordinate. -/
theorem card_childSegments_le
    (F : HierarchicalSegmentForest 1 s)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    #(childSegments F i a) ≤ s := by
  calc
    #(childSegments F i a) ≤ #(Finset.univ : Finset (Fin s)) :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = s := by simp

/-- Forward internal targets are a subset of the current segment. -/
theorem card_internalTargets_le
    (F : HierarchicalSegmentForest 1 s)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    #(internalTargets F i a) ≤ F.segments.size i := by
  classical
  calc
    #(internalTargets F i a) ≤
        #(Finset.univ : Finset (Fin (F.segments.size i))) :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = F.segments.size i := by simp

/-- A uniform size bound for hierarchy segments and their ambient candidate
sets gives one common scalar cleaning budget at every coordinate. -/
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
    ∀ i a,
      coordinateRemovalBudget F rho rootSlot rootWhole interiorWhole i a ≤
        removalBudget := by
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

end Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds

#print axioms Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds.coordinateRemovalBudget_le
