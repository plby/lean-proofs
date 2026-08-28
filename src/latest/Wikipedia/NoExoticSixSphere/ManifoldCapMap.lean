import Wikipedia.NoExoticSixSphere.ManifoldFundamentalClass
import Wikipedia.NoExoticSixSphere.ModTwoCapUnit

/-!
# The actual cap map with the constructed fundamental class

This is the genuine candidate for Poincaré duality: cap the original
cohomology class with the constructed native fundamental class. Its
cycle formula and unit normalization are proved here. Bijectivity and
comparison with geometric intersection are not asserted.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ManifoldCapMap

open ModTwoCapProduct

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]

/-- Cap with the constructed fundamental class, not an assumed duality isomorphism. -/
def dualityMap (p q : ℕ) (h : p + q = n + 3) :
    Cohomology M p →ₗ[ℤ] ModHomology 2 M q :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun a => capProductInDegree M h a
        (ManifoldFundamentalClass.fundamentalClass (E := E) n M)
      map_zero' := congrArg
        (fun f => f (ManifoldFundamentalClass.fundamentalClass (E := E) n M))
        (capProductInDegree M h).map_zero
      map_add' a b := congrArg
        (fun f => f (ManifoldFundamentalClass.fundamentalClass (E := E) n M))
        ((capProductInDegree M h).map_add a b) }

theorem dualityMap_apply (p q : ℕ) (h : p + q = n + 3) (a : Cohomology M p) :
    dualityMap (E := E) n M p q h a =
      capProductInDegree M h a (ManifoldFundamentalClass.fundamentalClass (E := E) n M) := rfl

/-- Every actual fundamental cycle gives the original front/back representative formula. -/
theorem dualityMap_cocycle_cycle (p q : ℕ) (h : p + q = n + 3) (α : Cocycle M p)
    (c : ModuleHomology.Cycle (modComplex 2 M) (n + 3))
    (hc : ModuleHomology.cycleClass (modComplex 2 M) (n + 3) c =
      ManifoldFundamentalClass.fundamentalClass (E := E) n M) :
    dualityMap (E := E) n M p q h
        (SingularCohomologyFree.cocycleClass (cochainComplex M) p α) =
      ModuleHomology.cycleClass (modComplex 2 M) q
        (capCyclesInDegree h α.val (cocycle_coboundary_zero M p α) c) := by
  exact (congrArg (capProductInDegree M h
    (SingularCohomologyFree.cocycleClass (cochainComplex M) p α)) hc).symm.trans
      (capProductInDegree_cocycle_cycle h α c)

/-- The genuine cohomology unit maps to the constructed fundamental class. -/
theorem dualityMap_unit :
    dualityMap (E := E) n M 0 (n + 3) (Nat.zero_add (n + 3)) (unitClass M) =
      ManifoldFundamentalClass.fundamentalClass (E := E) n M :=
  LinearMap.congr_fun (capProductInDegree_unit M (n + 3))
    (ManifoldFundamentalClass.fundamentalClass (E := E) n M)

end NoExoticSixSphere.ManifoldCapMap
