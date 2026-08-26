/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateCanonicalNumerics
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBounds

/-!
# Scalar constructors for the remaining coordinate budgets

These small generic constructors turn coarse cardinality estimates into the
two packaged numeric facts consumed by the canonical Claim 6.16 endpoint.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateScalarBounds

open Finset Fintype
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds

universe u v

/-- A bound on the number of direct hierarchy children and on the common
source reservoir size implies the direct-root Hall inequality. -/
theorem directHallBoundOfScalar
    {s : ℕ} {Host : Type u} [Fintype Host] [DecidableEq Host]
    (F : HierarchicalSegmentForest 1 s)
    (rho : ℝ) (sourceWhole : Finset Host) (quota directBound wholeBound : ℕ)
    (hrho : 0 ≤ rho)
    (hdirect : #(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) ≤
      directBound)
    (hwhole : #sourceWhole ≤ wholeBound)
    (hscalar : (directBound : ℝ) * (rho * wholeBound) < quota) :
    DirectHallBound F rho sourceWhole quota := by
  refine ⟨?_⟩
  have hdirectReal :
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) ≤
        directBound := by
    exact_mod_cast hdirect
  have hwholeReal : rho * (#sourceWhole : ℝ) ≤ rho * wholeBound :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hwhole) hrho
  exact (mul_le_mul hdirectReal hwholeReal
    (mul_nonneg hrho (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans_lt
      hscalar

end Erdos547b.ZhaoClaim616CoordinateScalarBounds

#print axioms Erdos547b.ZhaoClaim616CoordinateScalarBounds.directHallBoundOfScalar
