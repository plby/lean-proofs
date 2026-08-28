import Wikipedia.HopfProblem.OrbitPairNerveChainNaturality

/-!
# A comparison from native subdivision to the nondegenerate-simplex nerve

On each standard simplex, the comparison sends a face to its native
nondegenerate simplex. This construction commutes with all simplex
operators, including degeneracies. The actual left Kan extension then
gives a natural transformation from `SSet.sd` to the nerve-poset functor.
No realization equivalence is assumed in constructing this map.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset

def standardFace (n : ℕ) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) →o (SSet.stdSimplex.obj ⦋n⦌).N :=
  (map (SSet.stdSimplex.isoNerve n).inv).comp
    (nerveChainsOrderIso (ULift.{u} (Fin (n + 1)))).symm.toOrderEmbedding.toOrderHom

theorem standardNerve_inv_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (SSet.stdSimplex.isoNerve m.len).inv ≫ SSet.stdSimplex.map f =
      nerveMap (SimplexCategory.toPartOrd.{u}.map f).hom.monotone.functor ≫
        (SSet.stdSimplex.isoNerve n.len).inv := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  rfl

theorem standardFace_naturality {m n : SimplexCategory} (f : m ⟶ n)
    (A : NonemptyFiniteChains (ULift.{u} (Fin (m.len + 1)))) :
    map (SSet.stdSimplex.map f) (standardFace m.len A) =
      standardFace n.len (A.map (SimplexCategory.toPartOrd.{u}.map f).hom) := by
  change map (SSet.stdSimplex.map f)
    (map (SSet.stdSimplex.isoNerve m.len).inv
      (chainNondegenerate (ULift.{u} (Fin (m.len + 1))) A)) =
      map (SSet.stdSimplex.isoNerve n.len).inv
        (chainNondegenerate (ULift.{u} (Fin (n.len + 1)))
          (A.map (SimplexCategory.toPartOrd.{u}.map f).hom))
  let c := chainNondegenerate (ULift.{u} (Fin (m.len + 1))) A
  exact (map_comp (SSet.stdSimplex.isoNerve m.len).inv (SSet.stdSimplex.map f) c).symm.trans
    ((congrArg (fun g ↦ map g c) (standardNerve_inv_naturality f)).trans
      ((map_comp (nerveMap (SimplexCategory.toPartOrd.{u}.map f).hom.monotone.functor)
        (SSet.stdSimplex.isoNerve n.len).inv c).trans
          (congrArg (map (SSet.stdSimplex.isoNerve n.len).inv)
            (chainNondegenerate_map (ULift.{u} (Fin (m.len + 1)))
              (SimplexCategory.toPartOrd.{u}.map f).hom A))))

def standardComparison (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ nerveFunctor.obj (SSet.stdSimplex.obj n) :=
  nerveMap (standardFace n.len).monotone.functor

theorem standardComparison_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.sd.{u}.map f ≫ standardComparison n =
      standardComparison m ≫ nerveFunctor.map (SSet.stdSimplex.map f) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext i
  exact (standardFace_naturality f (x.obj i)).symm

def standardComparisonNat :
    SimplexCategory.sd.{u} ⟶ SSet.stdSimplex ⋙ nerveFunctor where
  app := standardComparison
  naturality _ _ f := standardComparison_naturality f

def subdivisionComparison : SSet.sd.{u} ⟶ nerveFunctor :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv nerveFunctor standardComparisonNat

theorem subdivisionComparison_stdSimplex (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫ subdivisionComparison.app (SSet.stdSimplex.obj n) =
      standardComparison n :=
  SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv nerveFunctor
    standardComparisonNat n

theorem subdivisionComparison_simplex (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌) :
    SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫ SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
        subdivisionComparison.app X =
      standardComparison ⦋n⦌ ≫ nerveFunctor.map (SSet.yonedaEquiv.symm x) := by
  rw [subdivisionComparison.naturality, ← Category.assoc, subdivisionComparison_stdSimplex]

end Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset
