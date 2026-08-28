import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapPieceMaps
import Wikipedia.HopfProblem.DegreeCollapseIntegralMayerVietorisRepresentatives
import Wikipedia.NoExoticSixSphere.ChainBiproductDifferential

/-!
# The signed integral cap lift in the original Mayer--Vietoris sequence

The two localized caps give a genuine biproduct element with signs
(+,-). Its boundary is the original intersection map of -(-1)^p times
the overlap cap. All chains, inclusions, and differentials are integral.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SmallRelativeIntegralCochains (Cochain)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Representatives with the same ambient image have the same ambient boundary image. -/
theorem boundary_smallRepresentative (T D : Set X) (i j : ℕ)
    (c : (complex U A V B).X i) (t : SmallChains Coefficient T D i)
    (ht : smallInclusionMap Coefficient T D i t = ((inclusion U A V B).f i).hom c) :
    smallInclusionMap Coefficient T D j (((SmallIntegralCap.complex T D).d i j).hom t) =
      ((inclusion U A V B).f j).hom (((complex U A V B).d i j).hom c) :=
  (SmallIntegralCap.boundary_smallInclusion T D i j t).symm.trans
    ((congrArg ((singularComplex X).d i j).hom ht).trans (boundary_inclusion U A V B i j c))

/-- The original biproduct lift has the two actual localized caps with signs (+,-). -/
def capLift (p q : ℕ) (β : RelativeIntegralCap.Cochain A p)
    (γ : RelativeIntegralCap.Cochain B p) (cU : SmallChains Coefficient U A (p + q + 1))
    (cV : SmallChains Coefficient V B (p + q + 1)) :
    (IntegralMayerVietoris.smallSequence U V).X₂.X (q + 1) :=
  ChainBiproduct.pair (q + 1)
    (SmallIntegralCap.capInDegree U A (p := p) (q := q + 1) (by omega) β cU)
    (-(SmallIntegralCap.capInDegree V B (p := p) (q := q + 1) (by omega) γ cV))

/-- The boundary is exactly the original intersection map of the signed overlap cap. -/
theorem intersection_cap_eq_boundary_lift (p q : ℕ)
    (β : RelativeIntegralCap.Cochain A p) (γ : RelativeIntegralCap.Cochain B p)
    (η : Cochain A B (p + 1))
    (hβ : ((IntegralRelativeCohomologyMayerVietoris.smallRestrictionLeft A B).f (p + 1)).hom η =
      RelativeIntegralCap.coboundary A β)
    (hγ : ((IntegralRelativeCohomologyMayerVietoris.smallRestrictionRight A B).f (p + 1)).hom η =
      RelativeIntegralCap.coboundary B γ)
    (c : (complex U A V B).X (p + q + 1))
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d (p + q + 1) (p + q)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion (A ∩ B)) (p + q)))
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c) :
    ((IntegralMayerVietoris.smallSequence U V).f.f q).hom
        (-((-1 : ℤ) ^ p) • capInDegree U A V B (p := p + 1) (q := q) (by omega) η c) =
      ((IntegralMayerVietoris.smallSequence U V).X₂.d (q + 1) q).hom
        (capLift U A V B p q β γ cU cV) := by
  have hcAB := (SingularSubcomplex.inclusion_range_inter Coefficient A B (p + q)).le hc
  have hcA : smallInclusionMap Coefficient U A (p + q)
      (((SmallIntegralCap.complex U A).d (p + q + 1) (p + q)).hom cU) ∈
      LinearMap.range (inducedChain (subtypeInclusion A) (p + q)) :=
    (boundary_smallRepresentative U A V B U A (p + q + 1) (p + q) c cU hcU).symm ▸ hcAB.1
  have hcB : smallInclusionMap Coefficient V B (p + q)
      (((SmallIntegralCap.complex V B).d (p + q + 1) (p + q)).hom cV) ∈
      LinearMap.range (inducedChain (subtypeInclusion B) (p + q)) :=
    (boundary_smallRepresentative U A V B V B (p + q + 1) (p + q) c cV hcV).symm ▸ hcAB.2
  have hL := (leftChainMap_capInDegree U A V B (p := p + 1) (q := q)
    (by omega) η c cU hcU).trans
      (congrArg (fun δ => SmallIntegralCap.capInDegree U A (p := p + 1) (q := q)
        (by omega) δ cU) hβ)
  have hR := (rightChainMap_capInDegree U A V B (p := p + 1) (q := q)
    (by omega) η c cV hcV).trans
      (congrArg (fun δ => SmallIntegralCap.capInDegree V B (p := p + 1) (q := q)
        (by omega) δ cV) hγ)
  have hsL := (map_zsmul ((leftChainMap U V).f q).hom (-((-1 : ℤ) ^ p))
    (capInDegree U A V B (p := p + 1) (q := q) (by omega) η c)).trans
      ((congrArg (fun x => -((-1 : ℤ) ^ p) • x) hL).trans
        (SmallIntegralCap.boundary_capInDegree_of_relative_cycle U A rfl β cU hcA).symm)
  have hsR := (map_zsmul ((rightChainMap U V).f q).hom (-((-1 : ℤ) ^ p))
    (capInDegree U A V B (p := p + 1) (q := q) (by omega) η c)).trans
      ((congrArg (fun x => -((-1 : ℤ) ^ p) • x) hR).trans
        (SmallIntegralCap.boundary_capInDegree_of_relative_cycle V B rfl γ cV hcB).symm)
  apply (ChainBiproduct.lift_eq_pair (leftChainMap U V) (-rightChainMap U V) q _).trans
  apply Eq.trans _ (ChainBiproduct.boundary_pair (q + 1) q _ _).symm
  apply congrArg₂ (ChainBiproduct.pair q) hsL
  exact (congrArg (fun x => -x) hsR).trans
    (((singularComplex V).d (q + 1) q).hom.map_neg _).symm

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap
