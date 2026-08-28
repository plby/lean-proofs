import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtFunctorConnecting

/-!
# Exact-functor naturality of the degree-one Ext comparison

The proof follows actual connecting representatives and the actual
inclusion of the intermediate kernel into the degree-zero Ext complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor

open CuspNormalization.SheafCohomologyResolution

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{0} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{0} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {V : C} {A : D} (η : A ⟶ G.obj V) (R : AugmentedResolution C)

/-- The Ext comparison of intermediate kernels respects their actual
inclusions, in every degree. -/
@[reassoc] theorem kernelExtComparison_ι (n : ℕ) :
    kernelExtComparison G η R n ≫
        (extFunctorObj A n).map (kernel.ι (mappedResolution G R).complex.g) =
      (extFunctorObj V n).map (kernel.ι R.complex.g) ≫
        comparisonHom G η R.complex.X₂ n := by
  let E := extFunctorObj A n
  change (comparisonHom G η R.K n ≫ E.map (kernelComparisonMap G R)) ≫
      E.map (kernel.ι (mappedResolution G R).complex.g) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => comparisonHom G η R.K n ≫ f)
      (E.map_comp (kernelComparisonMap G R)
        (kernel.ι (mappedResolution G R).complex.g)).symm).trans
        ((congrArg (fun f => comparisonHom G η R.K n ≫ E.map f)
          (kernelComparisonMap_ι G R)).trans
            (comparisonHom_naturality G η (kernel.ι R.complex.g) n).symm))

/-- The actual kernel sections give the same cycles after applying
the exact-functor comparison. -/
@[reassoc] theorem extCycleMap_naturality :
    kernelExtComparison G η R 0 ≫ (mappedResolution G R).extCycleMap A =
      R.extCycleMap V ≫ ShortComplex.cyclesMap (extZeroMap G η R) := by
  apply (cancel_mono ((mappedResolution G R).extZeroComplex A).iCycles).mp
  have hleft :
      (kernelExtComparison G η R 0 ≫ (mappedResolution G R).extCycleMap A) ≫
          ((mappedResolution G R).extZeroComplex A).iCycles =
        kernelExtComparison G η R 0 ≫
          (extFunctorObj A 0).map (kernel.ι (mappedResolution G R).complex.g) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => kernelExtComparison G η R 0 ≫ f)
        ((mappedResolution G R).extCycleMap_i A))
  have hright :
      (R.extCycleMap V ≫ ShortComplex.cyclesMap (extZeroMap G η R)) ≫
          ((mappedResolution G R).extZeroComplex A).iCycles =
        (extFunctorObj V 0).map (kernel.ι R.complex.g) ≫
          comparisonHom G η R.complex.X₂ 0 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => R.extCycleMap V ≫ f)
        (ShortComplex.cyclesMap_i (extZeroMap G η R))).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ (extZeroMap G η R).τ₂) (R.extCycleMap_i V))))
  exact hleft.trans ((kernelExtComparison_ι G η R 0).trans hright.symm)

/-- Genuine degree-one Ext and the actual homology of the degree-zero
Ext complex commute with the native exact-functor Ext comparison. -/
@[reassoc] theorem extOneIso_naturality
    [Subsingleton (Ext.{0} V R.complex.X₁ 1)]
    [Subsingleton (Ext.{0} A (mappedResolution G R).complex.X₁ 1)] :
    comparisonHom G η R.F 1 ≫ ((mappedResolution G R).extOneIso A).hom =
      (R.extOneIso V).hom ≫ ShortComplex.homologyMap (extZeroMap G η R) := by
  have : Epi (AddCommGrpCat.ofHom (connecting V R.first_shortExact 0)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (connecting_surjective V R.first_shortExact 0)
  refine comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (connecting V R.first_shortExact 0))
    (AddCommGrpCat.ofHom (connecting A (mappedResolution G R).first_shortExact 0))
    (R.extOneIso V).hom ((mappedResolution G R).extOneIso A).hom
    (R.extCycleMap V ≫ (R.extZeroComplex V).homologyπ)
    ((mappedResolution G R).extCycleMap A ≫
      ((mappedResolution G R).extZeroComplex A).homologyπ)
    (kernelExtComparison G η R 0) (comparisonHom G η R.F 1)
    (ShortComplex.homologyMap (extZeroMap G η R))
    (connectingOne_naturality G η R) (R.extOneIso_connecting_cycle V)
    ((mappedResolution G R).extOneIso_connecting_cycle A) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ ((mappedResolution G R).extZeroComplex A).homologyπ)
      (extCycleMap_naturality G η R)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => R.extCycleMap V ≫ f)
            (ShortComplex.homologyπ_naturality (extZeroMap G η R)).symm).trans
              (Category.assoc _ _ _).symm)))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor
