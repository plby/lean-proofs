import Wikipedia.HopfProblem.HigherHurewiczHomologyDescentConstants
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedDescentAugmentation

/-!
# Coefficient sums and even-degree cycle corrections

The actual boundary formula controls the coefficient sum in every degree.
For positive even degree it preserves that sum, so a genuine cycle has
coefficient sum zero. Subtracting a fixed value from every simplex in a
linear assignment therefore leaves the assignment unchanged on these cycles.
In particular this proves the constant-four-simplex correction needed in
degree four; no vanishing coefficient sum is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable (X : Type) [TopologicalSpace X]

/-- Coefficient sums commute with the boundary up to its actual alternating sign sum. -/
theorem chainAugmentation_boundary (n : ℕ) (c : Chains X (n + 1)) :
    chainAugmentation X n (((singularComplex X).d (n + 1) n).hom c) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • chainAugmentation X (n + 1) c := by
  have h : (chainAugmentation X n).comp ((singularComplex X).d (n + 1) n).hom =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • chainAugmentation X (n + 1) := by
    apply chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      chainAugmentation_simplex, LinearMap.smul_apply, zsmul_eq_mul, mul_one, Int.cast_id]
  exact LinearMap.congr_fun h c

/-- Boundaries of positive even-dimensional chains preserve the coefficient sum. -/
theorem chainAugmentation_boundary_even (n : ℕ) (hn : Even (n + 1))
    (c : Chains X (n + 1)) :
    chainAugmentation X n (((singularComplex X).d (n + 1) n).hom c) =
      chainAugmentation X (n + 1) c := by
  rw [chainAugmentation_boundary, boundarySignSum_even n hn, one_smul]

/-- Every actual cycle in positive even degree has coefficient sum zero. -/
theorem chainAugmentation_evenCycle (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (c : ModuleHomology.Cycle (singularComplex X) n) :
    chainAugmentation X n c.1 = 0 := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ n =>
    rw [← chainAugmentation_boundary_even X n hn]
    have hc : ((singularComplex X).d (n + 1) n).hom c.1 = 0 :=
      ModuleHomology.cycle_condition (singularComplex X) (n + 1) c
    rw [hc, map_zero]

variable {M : Type} [AddCommGroup M] [Module ℤ M]

/-- Constant simplex corrections cancel exactly on actual positive even-degree cycles. -/
theorem chainLift_sub_constant_evenCycle (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (f : SingularSimplex X n → M) (m : M)
    (c : ModuleHomology.Cycle (singularComplex X) n) :
    chainLift X n (fun smp => f smp - m) c.1 = chainLift X n f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_evenCycle X n hn hpos, zero_smul, sub_zero]

end Wikipedia.HopfProblem.HigherHurewicz
