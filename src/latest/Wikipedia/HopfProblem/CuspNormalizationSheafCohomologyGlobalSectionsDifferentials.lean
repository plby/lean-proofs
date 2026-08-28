import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBoundary
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsEvaluation
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspDifferentials

/-!
# The literal global differentials of the actual normalization resolution

The first map is zero because actual global normalization functions are
constant. Both coordinates of the last map are the literal source-signed
sum a₀ - a₁ + a₂, proved from the actual evaluation morphisms at P and Q.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual first global-section differential is the zero morphism. -/
theorem deltaZero_global_eq_zero :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (deltaZero C ε hε hε1 hC hR) = 0 := by
  let Γ := globalSectionsFunctor (TopCat.of (CentralSpace C ε))
  ext s
  apply (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).injective
  apply funext
  intro k
  change boundaryGlobalLinearEquiv C ε hε hε1 hC hR
      (Γ.map (deltaZero C ε hε hε1 hC hR) s) k =
    boundaryGlobalLinearEquiv C ε hε hε1 hC hR 0 k
  rw [map_zero, Pi.zero_apply, boundaryGlobalLinearEquiv_apply]
  have hcomp : Γ.map (deltaZero C ε hε hε1 hC hR) ≫
        Γ.map (biproduct.π (curveSheaf C ε hε hε1 hC hR) k) =
      Γ.map (boundaryDifference C ε hε hε1 hC hR k) :=
    (Γ.map_comp _ _).symm.trans
      (congrArg Γ.map (deltaZero_component C ε hε hε1 hC hR k))
  exact (congrArg (curveGlobalLinearEquiv C ε hε hε1 hC hR k)
    (ConcreteCategory.congr_hom hcomp s)).trans
      (boundaryDifference_global_scalar_zero C ε hε hε1 hC hR k s)

/-- The actual last differential at either specified endpoint is the
source's signed sum of actual global curve scalars. -/
theorem deltaOneAt_global_scalar (t : Fin 2)
    (s : Sections (boundarySheaf C ε hε hε1 hC hR)) :
    triplePointGlobalLinearEquiv C ε hε t
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (deltaOneAt C ε hε hε1 hC hR t) s) =
      boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 0 -
        boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 1 +
        boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 2 := by
  let Γ := globalSectionsFunctor (TopCat.of (CentralSpace C ε))
  change triplePointGlobalLinearEquiv C ε hε t
    (Γ.map (curveEvaluation C ε hε hε1 hC hR 0 t)
        (Γ.map (biproduct.π (curveSheaf C ε hε hε1 hC hR) 0) s) -
      Γ.map (curveEvaluation C ε hε hε1 hC hR 1 t)
        (Γ.map (biproduct.π (curveSheaf C ε hε hε1 hC hR) 1) s) +
      Γ.map (curveEvaluation C ε hε hε1 hC hR 2 t)
        (Γ.map (biproduct.π (curveSheaf C ε hε hε1 hC hR) 2) s)) = _
  simp only [Γ, map_add, map_sub, curveEvaluation_global_scalar, boundaryGlobalLinearEquiv_apply]

/-- In the actual source-ordered coordinates, the global last
differential has the same a₀ - a₁ + a₂ entry at actual P and Q. -/
theorem deltaOne_global_scalar (s : Sections (boundarySheaf C ε hε hε1 hC hR)) (t : Fin 2) :
    tripleGlobalLinearEquiv C ε hε
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (deltaOne C ε hε hε1 hC hR) s) t =
      boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 0 -
        boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 1 +
        boundaryGlobalLinearEquiv C ε hε hε1 hC hR s 2 := by
  let Γ := globalSectionsFunctor (TopCat.of (CentralSpace C ε))
  rw [tripleGlobalLinearEquiv_apply]
  have hcomp : Γ.map (deltaOne C ε hε hε1 hC hR) ≫
        Γ.map (biproduct.π (triplePointSheaf C ε hε) t) =
      Γ.map (deltaOneAt C ε hε hε1 hC hR t) :=
    (Γ.map_comp _ _).symm.trans
      (congrArg Γ.map (deltaOne_component C ε hε hε1 hC hR t))
  exact (congrArg (triplePointGlobalLinearEquiv C ε hε t)
    (ConcreteCategory.congr_hom hcomp s)).trans
      (deltaOneAt_global_scalar C ε hε hε1 hC hR t s)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
