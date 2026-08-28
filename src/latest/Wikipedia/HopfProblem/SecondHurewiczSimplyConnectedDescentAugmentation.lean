import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedDescent

/-!
# Coefficient sums of actual singular two-cycles

Every singular simplex is assigned coefficient sum one. A triangle has
three faces with signs `+,-,+`, so its boundary has the same coefficient
sum. Consequently every actual two-cycle has coefficient sum zero.
Subtracting a fixed value from each simplex in a linear assignment
therefore does not change that assignment on two-cycles.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable (X : Type) [TopologicalSpace X]

/-- The integral coefficient sum on the actual singular chain group. -/
def chainAugmentation (n : ℕ) : Chains X n →ₗ[ℤ] ℤ :=
  chainLift X n fun _ => 1

@[simp] theorem chainAugmentation_simplex (n : ℕ) (smp : SingularSimplex X n) :
    chainAugmentation X n (simplexChain X n smp) = 1 :=
  chainLift_simplex X n _ smp

/-- The alternating three-edge boundary preserves the coefficient sum. -/
theorem chainAugmentation_boundaryTwo (c : Chains X 2) :
    chainAugmentation X 1 (boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (boundaryTwo X) = chainAugmentation X 2 := by
    apply chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

@[simp] theorem chainAugmentation_twoCycle
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc := ModuleHomology.cycle_condition (singularComplex X) 2 c
  change boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

variable {M : Type} [AddCommGroup M] [Module ℤ M]

/-- Subtracting a constant on every simplex changes a linear assignment by
the coefficient sum times that constant. -/
theorem chainLift_sub_constant (n : ℕ) (f : SingularSimplex X n → M) (m : M)
    (c : Chains X n) :
    chainLift X n (fun smp => f smp - m) c =
      chainLift X n f c - chainAugmentation X n c • m := by
  have h : chainLift X n (fun smp => f smp - m) =
      chainLift X n f - (LinearMap.toSpanSingleton ℤ M m).comp
        (chainAugmentation X n) := by
    apply chainMap_ext X n
    intro smp
    simp only [chainLift_simplex, LinearMap.sub_apply, LinearMap.comp_apply,
      chainAugmentation_simplex, LinearMap.toSpanSingleton_apply_one]
  exact (LinearMap.congr_fun h c).trans
    (congrArg (fun z : M => chainLift X n f c - z)
      (int_smul_eq_zsmul (inferInstance : Module ℤ M) (chainAugmentation X n c) m))

/-- A constant correction to the simplex assignment cancels on actual two-cycles. -/
theorem chainLift_sub_constant_twoCycle (f : SingularSimplex X 2 → M) (m : M)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    chainLift X 2 (fun smp => f smp - m) c.1 = chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
