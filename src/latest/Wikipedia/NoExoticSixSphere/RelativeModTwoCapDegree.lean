import Wikipedia.NoExoticSixSphere.RelativeModTwoCapNaturality

/-!
# Relative cap in a specified total degree

Only the natural-number degree is transported. The original relative cap
operation and its pair-map naturality are unchanged.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cochain Cocycle Cohomology complex coboundary
  cocycle_coboundary_zero cohomologyPullback)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X] (U : Set X)

def capCyclesInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain U p)
    (hα : coboundary U α = 0) :
    ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) n →ₗ[ℤ]
      ModuleHomology.Cycle (modComplex 2 X) q := by
  subst n
  exact capCycles U p q α hα

theorem capCyclesInDegree_val {p q n : ℕ} (h : p + q = n) (α : Cochain U p)
    (hα : coboundary U α = 0)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) n) :
    (capCyclesInDegree U h α hα c).val = capInDegree U h α c.val := by
  subst n
  exact capCycles_val U p q α hα c

/-- The genuine relative cap product with only its total degree reindexed. -/
def capProductInDegree {p q n : ℕ} (h : p + q = n) : Cohomology U p →ₗ[ℤ]
    ((RelativeCoefficients.complex Coefficient U).homology n →ₗ[ℤ] ModHomology 2 X q) := by
  subst n
  exact capProduct U p q

theorem capProductInDegree_cocycle_cycle {p q n : ℕ} (h : p + q = n) (α : Cocycle U p)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) n) :
    capProductInDegree U h (SingularCohomologyFree.cocycleClass (complex U) p α)
        (ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient U) n c) =
      ModuleHomology.cycleClass (modComplex 2 X) q
        (capCyclesInDegree U h α.val (cocycle_coboundary_zero U p α) c) := by
  subst n
  exact capProduct_cocycle_cycle U p q α c

variable {U} {Y : Type} [TopologicalSpace Y] {V : Set Y}

theorem capProductInDegree_naturality (f : C(X, Y)) (hf : Set.MapsTo f U V)
    {p q n : ℕ} (h : p + q = n) (a : Cohomology V p)
    (c : (RelativeCoefficients.complex Coefficient U).homology n) :
    modHomologyMap 2 f q (capProductInDegree U h (cohomologyPullback f hf p a) c) =
      capProductInDegree V h a
        ((HomologicalComplex.homologyMap (RelativeCoefficients.mapChain Coefficient f hf)
          n).hom c) := by
  subst n
  exact capProduct_naturality f hf p q a c

end NoExoticSixSphere.RelativeModTwoCap
