import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullback
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactUniformBasic

/-!
# The genuine boundary differential in actual analytic-germ coordinates

The stalk of the actual global direct-sum arrow is first projected to
each actual curve stalk. The actual positive and negative pullback
computations identify each coordinate with the oriented axis difference.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryStalk

open CuspQuotient ToricCharts ToricSpace ToricFan
open CuspQuotient.NormalizationLocalCoordinates SheafResolution SheafCurveStalk
open SheafNormalizationStalk

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual global boundary arrow evaluated by the actual stalk functor. -/
def deltaZeroStalkMap (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x →+
      (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x :=
  ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
    (deltaZero C ε hε hε1 hC hR)).hom

/-- Projecting the global actual stalk differential gives the actual
signed double-curve stalk map. -/
theorem deltaZeroStalkMap_component (x : CentralSpace C ε) (k : Fin 3)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
        (biproduct.π (curveSheaf C ε hε hε1 hC hR) k)
        (deltaZeroStalkMap C ε hε hε1 hC hR x φ) =
      boundaryStalkMap C ε hε hε1 hC hR k x φ := by
  let F := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  exact ConcreteCategory.congr_hom
    ((F.map_comp (deltaZero C ε hε hε1 hC hR)
      (biproduct.π (curveSheaf C ε hε hε1 hC hR) k)).symm.trans
      (congrArg F.map (deltaZero_component C ε hε hε1 hC hR k))) φ

variable (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The entire actual second arrow becomes the actual oriented
analytic axis-difference homomorphism in every adapted cusp chart. -/
theorem deltaZeroStalkMap_conjugacy (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx
        (deltaZeroStalkMap C ε hε hε1 hC hR x φ) =
      orientedDifference s (Germs.activeBranches ((e) x.val))
        (normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx φ) := by
  funext k
  rw [boundaryStalkEquivAt_apply, deltaZeroStalkMap_component]
  exact boundaryStalkMap_conjugacyAt C ε hε hε1 hC hR a s x hx k.val k.property φ

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryStalk
