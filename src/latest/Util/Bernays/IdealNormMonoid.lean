import Util.Bernays.IdealNormMultiplicative

/-!
# Norm and class homomorphisms for integral invertible ideals
-/

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

noncomputable def normHom : InvertibleIdeal R →* ℕ where
  toFun I := (I : Ideal R).cardQuot
  map_one' := Submodule.cardQuot_top R R
  map_mul' := cardQuot_mul

noncomputable def classHom : InvertibleIdeal R →* ClassGroup R where
  toFun := idealClass
  map_one' := idealClass_one
  map_mul' := idealClass_mul

theorem cardQuot_list_prod (l : List (InvertibleIdeal R)) :
    ((l.prod : InvertibleIdeal R) : Ideal R).cardQuot =
      (l.map fun I : InvertibleIdeal R => (I : Ideal R).cardQuot).prod :=
  map_list_prod (normHom (R := R)) l

theorem idealClass_list_prod (l : List (InvertibleIdeal R)) :
    l.prod.idealClass = (l.map idealClass).prod := map_list_prod classHom l

theorem cardQuot_prod {ι : Type*} (s : Finset ι) (I : ι → InvertibleIdeal R) :
    ((∏ i ∈ s, I i : InvertibleIdeal R) : Ideal R).cardQuot = ∏ i ∈ s, (I i : Ideal R).cardQuot :=
  map_prod (normHom (R := R)) _ _

theorem idealClass_prod {ι : Type*} (s : Finset ι) (I : ι → InvertibleIdeal R) :
    (∏ i ∈ s, I i).idealClass = ∏ i ∈ s, (I i).idealClass := map_prod classHom _ _

end Bernays.InvertibleIdeal
