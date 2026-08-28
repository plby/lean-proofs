import Wikipedia.NoExoticSixSphere.CommonSmallCapPieceMaps
import Wikipedia.NoExoticSixSphere.ChainBiproductDifferential
import Wikipedia.NoExoticSixSphere.ModTwoMayerVietoris
import Wikipedia.NoExoticSixSphere.SmallModTwoCapDifference

/-!
# The actual Mayer--Vietoris lift of the cap chain

The two localized cochains give an element of the original native
biproduct. Its boundary is the original intersection map applied to
the overlap cap of the lifted coboundary. Both identities retain the
native coefficient complexes and the actual chain inclusions.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SmallRelativeModTwoCochains (Cochain)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Two representatives with the same original image have the same original boundary image. -/
theorem boundary_smallRepresentative (T D : Set X) (i j : ℕ)
    (c : (complex U A V B).X i) (t : SmallChains Coefficient T D i)
    (ht : smallInclusionMap Coefficient T D i t = ((inclusion U A V B).f i).hom c) :
    smallInclusionMap Coefficient T D j (((SmallModTwoCap.complex T D).d i j).hom t) =
      ((inclusion U A V B).f j).hom (((complex U A V B).d i j).hom c) :=
  (SmallModTwoCap.boundary_smallInclusion T D i j t).symm.trans
    ((congrArg ((modComplex 2 X).d i j).hom ht).trans (boundary_inclusion U A V B i j c))

/-- The original biproduct lift consists of the two localized caps with signs `(+,-)`. -/
def capLift (p q : ℕ) (β : RelativeModTwoCochains.Cochain A p)
    (γ : RelativeModTwoCochains.Cochain B p) (cU : SmallChains Coefficient U A (p + q + 1))
    (cV : SmallChains Coefficient V B (p + q + 1)) :
    (ModTwoMayerVietoris.smallSequence U V).X₂.X (q + 1) :=
  ChainBiproduct.pair (q + 1)
    (SmallModTwoCap.capInDegree U A (p := p) (q := q + 1) (by omega) β cU)
    (-(SmallModTwoCap.capInDegree V B (p := p) (q := q + 1) (by omega) γ cV))

/-- The original intersection map of the overlap cap is exactly the boundary of the lift. -/
theorem intersection_cap_eq_boundary_lift (p q : ℕ)
    (β : RelativeModTwoCochains.Cochain A p) (γ : RelativeModTwoCochains.Cochain B p)
    (η : Cochain A B (p + 1))
    (hβ : ((RelativeModTwoMayerVietoris.smallRestrictionLeft A B).f (p + 1)).hom η =
      RelativeModTwoCochains.coboundary A β)
    (hγ : ((RelativeModTwoMayerVietoris.smallRestrictionRight A B).f (p + 1)).hom η =
      RelativeModTwoCochains.coboundary B γ)
    (c : (complex U A V B).X (p + q + 1))
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d (p + q + 1) (p + q)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient (A ∩ B)).f (p + q)).hom)
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c) :
    ((ModTwoMayerVietoris.smallSequence U V).f.f q).hom
        (capInDegree U A V B (p := p + 1) (q := q) (by omega) η c) =
      ((ModTwoMayerVietoris.smallSequence U V).X₂.d (q + 1) q).hom
        (capLift U A V B p q β γ cU cV) := by
  have hcAB := (SingularSubcomplex.inclusion_range_inter Coefficient A B (p + q)).le hc
  have hcA : smallInclusionMap Coefficient U A (p + q)
      (((SmallModTwoCap.complex U A).d (p + q + 1) (p + q)).hom cU) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (p + q)).hom :=
    (boundary_smallRepresentative U A V B U A (p + q + 1) (p + q) c cU hcU).symm ▸ hcAB.1
  have hcB : smallInclusionMap Coefficient V B (p + q)
      (((SmallModTwoCap.complex V B).d (p + q + 1) (p + q)).hom cV) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient B).f (p + q)).hom :=
    (boundary_smallRepresentative U A V B V B (p + q + 1) (p + q) c cV hcV).symm ▸ hcAB.2
  have hL := (leftChainMap_capInDegree U A V B (p := p + 1) (q := q)
    (by omega) η c cU hcU).trans
      ((congrArg (fun δ => SmallModTwoCap.capInDegree U A (p := p + 1) (q := q)
        (by omega) δ cU) hβ).trans
          (SmallModTwoCap.boundary_capInDegree_of_relative_cycle U A rfl β cU hcA).symm)
  have hR := (rightChainMap_capInDegree U A V B (p := p + 1) (q := q)
    (by omega) η c cV hcV).trans
      ((congrArg (fun δ => SmallModTwoCap.capInDegree V B (p := p + 1) (q := q)
        (by omega) δ cV) hγ).trans
          (SmallModTwoCap.boundary_capInDegree_of_relative_cycle V B rfl γ cV hcB).symm)
  apply (ChainBiproduct.lift_eq_pair (leftChainMap U V) (-rightChainMap U V) q _).trans
  apply Eq.trans _ (ChainBiproduct.boundary_pair (q + 1) q _ _).symm
  apply congrArg₂ (ChainBiproduct.pair q) hL
  exact (congrArg (fun x => -x) hR).trans (((modComplex 2 V).d (q + 1) q).hom.map_neg _).symm

end NoExoticSixSphere.CommonSmallModTwoCap
