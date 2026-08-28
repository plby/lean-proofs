import Wikipedia.HopfProblem.PeriodTorusExponentialChernBasic
import Wikipedia.HopfProblem.PeriodTorusExponentialChernCoefficients
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientExt

/-!
# The original exponential coefficient square on the period torus

The native integral comparison, the literal coefficient homomorphism
`n ↦ n * (2 * π * I)`, and the genuine constant-sheaf comparison form the
existing coefficient-naturality square.  Postcomposition with the actual
global cochain unit gives the original resolution comparison, including
its degree-two truncation and actual cycle cokernel.

No equality of independently constructed Chern classes is assumed here.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open ConstantSheafSingularComparison HolomorphicExponentialSheaf

private theorem square_apply {P Q R S : AddCommGrpCat.{0}}
    (f : P ⟶ Q) (g : Q ⟶ S) (u : P ⟶ R) (v : R ⟶ S)
    (h : f ≫ g = u ≫ v) (a : P) : v (u a) = g (f a) :=
  (AddCommGrpCat.comp_apply u v a).symm.trans
    ((ConcreteCategory.congr_hom h a).symm.trans (AddCommGrpCat.comp_apply f g a))

private theorem coefficient_naturality_apply (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (hLC : LocallyContractibleSpace X)
    {A B : AddCommGrpCat.{0}} (α : A ⟶ B)
    (a : CategoryTheory.Sheaf.H.{0} (ConstantSheafFirstCohomology.Constant.sheaf X A) 2) :
    HomologicalComplex.homologyMap (coefficientMap X α) 2
        ((constantSheafH2Iso X A hLC).hom a) =
      (constantSheafH2Iso X B hLC).hom
        (CategoryTheory.Sheaf.H.map.{0}
          ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{0}).map α) 2 a) :=
  square_apply
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map α))
    (constantSheafH2Iso X B hLC).hom (constantSheafH2Iso X A hLC).hom
    (HomologicalComplex.homologyMap (coefficientMap X α) 2)
    (constantSheafH2Iso_coefficient_naturality X hLC α) a

private theorem exponentialH2Hom_integralH2Comparison_as_additive (p : PeriodDomain)
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of p.Torus)) 2) :
    Coefficients.exponentialH2Hom p (integralH2Comparison p a) =
      HomologicalComplex.homologyMap
        (coefficientMap p.Torus Coefficients.exponentialCoefficient) 2
        ((constantSheafH2Iso (TopCat.of p.Torus) (AddCommGrpCat.of ℤ)
          (torusLocallyContractible p)).hom a) := by
  change HomologicalComplex.homologyMap
      (coefficientMap p.Torus Coefficients.exponentialCoefficient) 2
      ((integralCohomologyEquiv p.Torus 2).symm
        (integralCohomologyEquiv p.Torus 2
          ((constantSheafH2Iso (TopCat.of p.Torus) (AddCommGrpCat.of ℤ)
            (torusLocallyContractible p)).hom a))) = _
  rw [AddEquiv.symm_apply_apply]

/-- Coefficient change of the original integral comparison is the
original complex comparison of the actual coefficient-induced Ext map. -/
theorem exponentialH2Hom_integralH2Comparison (p : PeriodDomain)
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of p.Torus)) 2) :
    Coefficients.exponentialH2Hom p (integralH2Comparison p a) =
      (constantSheafH2Iso (TopCat.of p.Torus) (AddCommGrpCat.of ℂ)
        (torusLocallyContractible p)).hom
        (CategoryTheory.Sheaf.H.map.{0}
          ((CategoryTheory.constantSheaf (Opens.grothendieckTopology p.Torus)
            AddCommGrpCat.{0}).map (AddCommGrpCat.ofHom integerScalarHom)) 2 a) := by
  rw [exponentialH2Hom_integralH2Comparison_as_additive]
  exact coefficient_naturality_apply (TopCat.of p.Torus)
    (torusLocallyContractible p) Coefficients.exponentialCoefficient a

/-- The actual singular-to-global cochain map identifies this same
class with the original full cochain-resolution comparison. -/
theorem exponentialH2Hom_integralH2Comparison_global (p : PeriodDomain)
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of p.Torus)) 2) :
    HomologicalComplex.homologyMap
        (globalCochainComparison (TopCat.of p.Torus) (AddCommGrpCat.of ℂ)) 2
        (Coefficients.exponentialH2Hom p (integralH2Comparison p a)) =
      (constantSheafGlobalH2Iso (TopCat.of p.Torus) (AddCommGrpCat.of ℂ)
        (torusLocallyContractible p)).hom
        (CategoryTheory.Sheaf.H.map.{0}
          ((CategoryTheory.constantSheaf (Opens.grothendieckTopology p.Torus)
            AddCommGrpCat.{0}).map (AddCommGrpCat.ofHom integerScalarHom)) 2 a) := by
  rw [exponentialH2Hom_integralH2Comparison]
  exact ConcreteCategory.congr_hom
    (constantSheafH2Iso_global (TopCat.of p.Torus) (AddCommGrpCat.of ℂ)
      (torusLocallyContractible p)) _

/-- The same global comparison is literally the original truncated
resolution's `h2Iso`, followed by its genuine cycle-cokernel comparison. -/
theorem exponentialH2Hom_integralH2Comparison_truncation (p : PeriodDomain)
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of p.Torus)) 2) :
    let X := TopCat.of p.Torus
    let R := singularSheafResolution X (AddCommGrpCat.of ℂ) (torusLocallyContractible p)
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
      FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 0
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) :=
      FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 1
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) :=
      FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 1 0
    HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
        (Coefficients.exponentialH2Hom p (integralH2Comparison p a)) =
      R.globalSecondHomologyIso.hom
        (R.truncation.h2Iso.hom
          (CategoryTheory.Sheaf.H.map.{0}
            ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
              AddCommGrpCat.{0}).map (AddCommGrpCat.ofHom integerScalarHom)) 2 a)) := by
  exact exponentialH2Hom_integralH2Comparison_global p a

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
