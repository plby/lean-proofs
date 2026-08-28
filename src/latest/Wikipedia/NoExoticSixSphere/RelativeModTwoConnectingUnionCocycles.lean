import Wikipedia.NoExoticSixSphere.SmallRelativeModTwoCochains

/-!
# Original union-relative representatives of the cohomological connecting map

Pullback along the actual small-to-union quotient map sends a union
representative of connecting to the original small connecting class.
This supplies the actual cohomology equality used by overlap cap.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularCohomologyFree

namespace NoExoticSixSphere.SmallRelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (A B : Set X)

/-- The original cochain pullback of a union-relative cocycle. -/
def unionCocycle (p : ℕ) (α : RelativeModTwoCochains.Cocycle (A ∪ B) p) :
    Cocycle (complex A B) p :=
  mapCocycles (ModTwoDualComplex.map
    (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)) p α

theorem unionCocycle_val (p : ℕ) (α : RelativeModTwoCochains.Cocycle (A ∪ B) p) :
    (unionCocycle A B p α).val = ((ModTwoDualComplex.map
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).f p).hom α.val :=
  mapCocycles_val _ _ _

theorem toAbsolute_unionCocycle (p : ℕ) (α : RelativeModTwoCochains.Cocycle (A ∪ B) p) :
    toAbsolute A B p (unionCocycle A B p α).val =
      RelativeModTwoCochains.toAbsolute (A ∪ B) p α.val :=
  (congrArg (toAbsolute A B p) (unionCocycle_val A B p α)).trans (toAbsolute_union A B p α.val)

end NoExoticSixSphere.SmallRelativeModTwoCochains

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)

/-- The actual union-to-small equivalence sends a cocycle class to its actual pullback class. -/
theorem smallUnionEquiv_cocycleClass (p : ℕ)
    (θ : RelativeModTwoCochains.Cocycle (A ∪ B) p) :
    smallUnionEquiv A B hA hB p
        (cocycleClass (RelativeModTwoCochains.complex (A ∪ B)) p θ) =
      cocycleClass (SmallRelativeModTwoCochains.complex A B) p
        (SmallRelativeModTwoCochains.unionCocycle A B p θ) :=
  homologyMap_cocycleClass (ModTwoDualComplex.map
    (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)) p θ

/-- Two representatives of the genuine connecting map agree in actual small-relative cohomology. -/
theorem unionCocycle_class_of_connecting (p : ℕ)
    (a : RelativeModTwoCochains.Cohomology (A ∩ B) p)
    (η : Cocycle (SmallRelativeModTwoCochains.complex A B) (p + 1))
    (hη : smallConnecting A B p a = cocycleClass _ (p + 1) η)
    (θ : RelativeModTwoCochains.Cocycle (A ∪ B) (p + 1))
    (hθ : cocycleClass _ (p + 1) θ = connecting A B hA hB p a) :
    cocycleClass (SmallRelativeModTwoCochains.complex A B) (p + 1)
        (SmallRelativeModTwoCochains.unionCocycle A B (p + 1) θ) =
      cocycleClass (SmallRelativeModTwoCochains.complex A B) (p + 1) η :=
  (smallUnionEquiv_cocycleClass A B hA hB (p + 1) θ).symm.trans
    ((congrArg (smallUnionEquiv A B hA hB (p + 1)) hθ).trans
      (((smallUnionEquiv A B hA hB (p + 1)).apply_symm_apply (smallConnecting A B p a)).trans hη))

/-- The original union-relative complex supplies a cocycle representing actual connecting. -/
theorem exists_connecting_union_cocycle (p : ℕ)
    (a : RelativeModTwoCochains.Cohomology (A ∩ B) p) :
    ∃ θ : RelativeModTwoCochains.Cocycle (A ∪ B) (p + 1),
      cocycleClass _ (p + 1) θ = connecting A B hA hB p a :=
  cocycleClass_surjective _ (p + 1) (connecting A B hA hB p a)

end NoExoticSixSphere.RelativeModTwoMayerVietoris
