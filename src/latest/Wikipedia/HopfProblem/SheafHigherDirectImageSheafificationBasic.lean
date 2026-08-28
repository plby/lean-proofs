import Wikipedia.HopfProblem.SheafHigherDirectImageHomology

/-!
# Sheafification of the homology presheaf

Abelian sheafification is exact, and sheafifying the underlying
presheaf of a sheaf recovers that sheaf.  Applied degreewise, these
native comparisons identify the homology sheaf of any complex with
the sheafification of its actual presheaf homology.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

/-- The native abelian sheafification functor on the open-set site. -/
abbrev sheafification (X : TopCat.{0}) :
    TopCat.Presheaf AddCommGrpCat.{0} X ⥤ AbelianSheaf X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

instance sheafification_additive (X : TopCat.{0}) : (sheafification X).Additive :=
  inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).Additive

instance sheafification_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (sheafification X) :=
  inferInstanceAs (PreservesFiniteLimits
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))

instance sheafification_preservesFiniteColimits (X : TopCat.{0}) :
    PreservesFiniteColimits (sheafification X) :=
  inferInstanceAs (PreservesFiniteColimits
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))

/-- The actual native sheafification comparison for an existing sheaf. -/
def sheafificationUnderlyingIso (X : TopCat.{0}) :
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ sheafification X ≅ 𝟭 (AbelianSheaf X) :=
  (sheafificationNatIso (Opens.grothendieckTopology X) AddCommGrpCat).symm

variable {X : TopCat.{0}}

/-- Sheafification recovers an actual sheaf complex, including its differentials. -/
def sheafificationComplexIso (K : CochainComplex (AbelianSheaf X) ℕ) :
    ((sheafification X).mapHomologicalComplex _).obj (underlyingPresheafComplex K) ≅ K :=
  (Functor.mapHomologicalComplexCompIso (sheafificationUnderlyingIso X) _).app K ≪≫
    (Functor.mapHomologicalComplexIdIso (AbelianSheaf X) _).app K

/-- The homology sheaf is the native sheafification of presheaf homology. -/
def sheafHomologyIsoSheafification (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    K.homology n ≅ (sheafification X).obj (homologyPresheaf K n) :=
  HomologicalComplex.homologyMapIso (sheafificationComplexIso K).symm n ≪≫
    mapComplexHomologyIso (underlyingPresheafComplex K) (sheafification X) n

end Wikipedia.HopfProblem.SheafHigherDirectImage
