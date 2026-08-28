import Wikipedia.NoExoticSixSphere.ModTwoCapCohomology

/-!
# The original cap product in a specified total degree

Only the natural-number index is transported here. The cycle formula
still uses the original `capInDegree` chain map, so this can be applied
to a constructed fundamental class in the manifold's stated dimension.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X]

/-- The original capped-cycle map with an explicitly identified total degree. -/
def capCyclesInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : coboundary α = 0) :
    ModuleHomology.Cycle (modComplex 2 X) n →ₗ[ℤ] ModuleHomology.Cycle (modComplex 2 X) q := by
  subst n
  exact capCycles p q α hα

theorem capCyclesInDegree_val {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (hα : coboundary α = 0) (c : ModuleHomology.Cycle (modComplex 2 X) n) :
    (capCyclesInDegree h α hα c).val = capInDegree h α c.val := by
  subst n
  exact capCycles_val p q α hα c

/-- The already-descended cap product, with only its total degree reindexed. -/
def capProductInDegree (X : Type) [TopologicalSpace X] {p q n : ℕ} (h : p + q = n) :
    Cohomology X p →ₗ[ℤ] (ModHomology 2 X n →ₗ[ℤ] ModHomology 2 X q) := by
  subst n
  exact capProduct X p q

/-- Actual representatives still give the original capped-cycle class in this degree. -/
theorem capProductInDegree_cocycle_cycle {p q n : ℕ} (h : p + q = n) (α : Cocycle X p)
    (c : ModuleHomology.Cycle (modComplex 2 X) n) :
    capProductInDegree X h (SingularCohomologyFree.cocycleClass (cochainComplex X) p α)
        (ModuleHomology.cycleClass (modComplex 2 X) n c) =
      ModuleHomology.cycleClass (modComplex 2 X) q
        (capCyclesInDegree h α.val (cocycle_coboundary_zero X p α) c) := by
  subst n
  exact capProduct_cocycle_cycle X p q α c

end NoExoticSixSphere.ModTwoCapProduct
