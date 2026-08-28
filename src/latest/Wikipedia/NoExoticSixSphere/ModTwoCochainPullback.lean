import Wikipedia.NoExoticSixSphere.ModTwoCochainComplex

/-!
# Original continuous-map pullback on the mod-two cochain complex

The integer-enriched cochain map is still literal precomposition with
the original singular-chain map. Its differential and cocycle-class
formulas are those of the actual cochain complexes.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Original pullback with the unique compatible integer-linear structure. -/
def pullback (f : C(X, Y)) (p : ℕ) : Cochain Y p →ₗ[ℤ] Cochain X p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((ConstantSheafSingularComparison.singularPullback (AddCommGrpCat.of (ZMod 2)) f).f p).hom

theorem pullback_simplex (f : C(X, Y)) (p : ℕ) (α : Cochain Y p)
    (σ : SingularSimplex X p) :
    pullback f p α (simplexChain X p σ) = α (simplexChain Y p (f.comp σ)) :=
  ConstantSheafSingularComparison.singularPullback_simplex (AddCommGrpCat.of (ZMod 2)) f p α σ

/-- The actual cochain map on the integer-enriched native cochains. -/
def cochainPullback (f : C(X, Y)) : cochainComplex Y ⟶ cochainComplex X where
  f p := ModuleCat.ofHom (pullback f p)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change Cochain Y i at α
    apply AddMonoidHom.ext
    intro c
    change α (inducedChain f i (((singularComplex X).d j i).hom c)) =
      α (((singularComplex Y).d j i).hom (inducedChain f j c))
    exact congrArg α (congrArg (fun g : Chains X j ⟶ Chains Y i => g.hom c)
      ((singularChainMap f).comm j i).symm)

theorem pullback_coboundary (f : C(X, Y)) (p : ℕ) (α : Cochain Y p) :
    pullback f (p + 1) (coboundary α) = coboundary (pullback f p α) :=
  (congrArg (fun g => g.hom α) ((cochainPullback f).comm p (p + 1))).symm

/-- Pullback on the actual cohomology objects of the native mod-two cochain complex. -/
abbrev cohomologyPullback (f : C(X, Y)) (p : ℕ) : Cohomology Y p →ₗ[ℤ] Cohomology X p :=
  (HomologicalComplex.homologyMap (cochainPullback f) p).hom

theorem cohomologyPullback_cocycleClass (f : C(X, Y)) (p : ℕ) (α : Cocycle Y p) :
    cohomologyPullback f p (SingularCohomologyFree.cocycleClass (cochainComplex Y) p α) =
      SingularCohomologyFree.cocycleClass (cochainComplex X) p
        (SingularCohomologyFree.mapCocycles (cochainPullback f) p α) :=
  SingularCohomologyFree.homologyMap_cocycleClass (cochainPullback f) p α

end NoExoticSixSphere.ModTwoCapProduct
