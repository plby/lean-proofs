import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapNaturality
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular

/-!
# Forgetting the actual relative class commutes with its original pullback

The original quotient projection square dualizes to the original cochain
square. Passing to the original cohomology maps retains both forgetting
maps and the actual singular pullback, including the ambient identity case.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris NoExoticSixSphere

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)

theorem pullbackMap_toAbsolute :
    pullbackMap f hf ≫ toAbsoluteMap U = toAbsoluteMap V ≫ singularPullback f :=
  (dualMap_comp (RelativeSingularHomology.projection U)
    (RelativeSingularHomology.mapChain f hf)).symm.trans
      ((congrArg dualMap (RelativeSingularHomology.projection_mapChain f hf)).trans
        (dualMap_comp (singularChainMap f) (RelativeSingularHomology.projection V)))

theorem cohomologyForget_pullback (p : ℕ) (a : Cohomology V p) :
    (HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom (cohomologyPullback f hf p a) =
      singularCohomologyPullback f p
        ((HomologicalComplex.homologyMap (toAbsoluteMap V) p).hom a) := by
  have he := congrArg (fun g : cochainComplex V ⟶ singularCochainComplex X ↦
    (HomologicalComplex.homologyMap g p).hom) (pullbackMap_toAbsolute f hf)
  have hl := congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp
    (pullbackMap f hf) (toAbsoluteMap U) p)
  have hr := congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp
    (toAbsoluteMap V) (singularPullback f) p)
  exact LinearMap.congr_fun (hl.symm.trans (he.trans hr)) a

theorem cohomologyForget_pullback_id {U V : Set X} (h : U ⊆ V) (p : ℕ) (a : Cohomology V p) :
    (HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom
      (cohomologyPullback (ContinuousMap.id X) h p a) =
    (HomologicalComplex.homologyMap (toAbsoluteMap V) p).hom a := by
  have he := cohomologyForget_pullback (ContinuousMap.id X) h p a
  rw [singularCohomologyPullback_id] at he
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
