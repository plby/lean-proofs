import Wikipedia.HopfProblem.DegreeCollapseSmallRelativeIntegralCochains

/-!
# Original integral union-relative representatives of the connecting map

The original small-to-union quotient induces the actual cochain pullback.
It takes a union-relative representative of the connecting class to
the original small-relative connecting class, retaining the absolute
cochain and all original cohomology maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallRelativeIntegralCochains

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (A B : Set X)

def unionCocycle (p : ℕ) (α : RelativeIntegralCap.Cocycle (A ∪ B) p) :
    Cocycle (complex A B) p :=
  mapCocycles (dualMap (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)) p α

theorem unionCocycle_val (p : ℕ) (α : RelativeIntegralCap.Cocycle (A ∪ B) p) :
    (unionCocycle A B p α).val =
      ((dualMap
        (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).f p).hom α.val :=
  mapCocycles_val _ _ _

theorem toAbsolute_unionCocycle (p : ℕ) (α : RelativeIntegralCap.Cocycle (A ∪ B) p) :
    toAbsolute A B p (unionCocycle A B p α).val =
      RelativeIntegralCap.toAbsolute (A ∪ B) p α.val :=
  (congrArg (toAbsolute A B p) (unionCocycle_val A B p α)).trans (toAbsolute_union A B p α.val)

end Wikipedia.HopfProblem.DegreeCollapse.SmallRelativeIntegralCochains

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)

theorem smallUnionEquiv_cocycleClass (p : ℕ)
    (θ : RelativeIntegralCap.Cocycle (A ∪ B) p) :
    smallUnionEquiv A B hA hB p
        (cocycleClass (RelativeIntegralCap.cochainComplex (A ∪ B)) p θ) =
      cocycleClass (SmallRelativeIntegralCochains.complex A B) p
        (SmallRelativeIntegralCochains.unionCocycle A B p θ) :=
  homologyMap_cocycleClass
    (dualMap (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)) p θ

/-- The two original representatives of connecting agree in actual small-relative cohomology. -/
theorem unionCocycle_class_of_connecting (p : ℕ)
    (a : RelativeIntegralCap.Cohomology (A ∩ B) p)
    (η : Cocycle (SmallRelativeIntegralCochains.complex A B) (p + 1))
    (hη : smallConnecting A B p a = cocycleClass _ (p + 1) η)
    (θ : RelativeIntegralCap.Cocycle (A ∪ B) (p + 1))
    (hθ : cocycleClass _ (p + 1) θ = connecting A B hA hB p a) :
    cocycleClass (SmallRelativeIntegralCochains.complex A B) (p + 1)
        (SmallRelativeIntegralCochains.unionCocycle A B (p + 1) θ) =
      cocycleClass (SmallRelativeIntegralCochains.complex A B) (p + 1) η :=
  (smallUnionEquiv_cocycleClass A B hA hB (p + 1) θ).symm.trans
    ((congrArg (smallUnionEquiv A B hA hB (p + 1)) hθ).trans
      (((smallUnionEquiv A B hA hB (p + 1)).apply_symm_apply
        (smallConnecting A B p a)).trans hη))

/-- Every value of the actual integral connecting map has an original union-relative cocycle. -/
theorem exists_connecting_union_cocycle (p : ℕ)
    (a : RelativeIntegralCap.Cohomology (A ∩ B) p) :
    ∃ θ : RelativeIntegralCap.Cocycle (A ∪ B) (p + 1),
      cocycleClass _ (p + 1) θ = connecting A B hA hB p a :=
  cocycleClass_surjective _ (p + 1) (connecting A B hA hB p a)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
