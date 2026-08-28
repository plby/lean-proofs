import Wikipedia.HopfProblem.OrbitPairFinitePosetStarRefinement
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit

/-!
# The native nondegenerate-simplex poset as a functor

A simplicial map need not preserve nondegeneracy. Its map on the poset of
nondegenerate simplices therefore takes the nondegenerate core of each
image. Equality of generated subcomplexes proves functoriality without
assuming that either the source or target is nonsingular.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset

variable {X Y Z : SSet.{u}}

def map (f : X ⟶ Y) : X.N →o Y.N where
  toFun x := (x.toS.map f).toN
  monotone' x y h := by
    change (x.toS.map f).toN.subcomplex ≤ (y.toS.map f).toN.subcomplex
    rw [SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    change SSet.Subcomplex.ofSimplex (f.app _ x.simplex) ≤
      SSet.Subcomplex.ofSimplex (f.app _ y.simplex)
    rw [← SSet.Subcomplex.image_ofSimplex, ← SSet.Subcomplex.image_ofSimplex]
    exact SSet.Subcomplex.image_monotone f h

theorem map_subcomplex (f : X ⟶ Y) (x : X.N) :
    (map f x).subcomplex = x.subcomplex.image f :=
  (SSet.S.subcomplex_toN (x.toS.map f)).trans
    (SSet.Subcomplex.image_ofSimplex x.simplex f).symm

theorem map_toN (f : X ⟶ Y) (x : X.S) :
    map f x.toN = (x.map f).toN := by
  apply SSet.N.subcomplex_injective
  rw [map_subcomplex, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
  exact SSet.Subcomplex.image_ofSimplex x.simplex f

theorem map_id (x : X.N) : map (𝟙 X) x = x := by
  apply SSet.N.subcomplex_injective
  rw [map_subcomplex, SSet.Subcomplex.image_id]

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.N) :
    map (f ≫ g) x = map g (map f x) := by
  apply SSet.N.subcomplex_injective
  rw [map_subcomplex, map_subcomplex, map_subcomplex, SSet.Subcomplex.image_comp]

def functor : SSet.{u} ⥤ PartOrd.{u} where
  obj X := PartOrd.of X.N
  map f := PartOrd.ofHom (map f)
  map_id X := PartOrd.ext (fun x ↦ map_id x)
  map_comp f g := PartOrd.ext (fun x ↦ map_comp f g x)

def nerveFunctor : SSet.{u} ⥤ SSet.{u} := functor ⋙ PartOrd.nerveFunctor

instance nerveFunctor_finite (X : SSet.{u}) [X.Finite] :
    (nerveFunctor.obj X).Finite :=
  inferInstanceAs (SSet.Finite (nerve X.N))

end Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset
