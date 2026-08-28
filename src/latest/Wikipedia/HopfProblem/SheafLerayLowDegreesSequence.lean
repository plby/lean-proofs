import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstract
import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforward
import Wikipedia.HopfProblem.SheafLerayLowDegreesTransport

/-!
# The genuine low-degree Leray exact sequence

For every continuous map and every abelian sheaf, the actual pushed-
forward injective resolution gives the sequence

`0 → H¹(Y,f_*F) → H¹(X,F) → H⁰(Y,R¹f_*F) → H²(Y,f_*F)`.

Every term is Mathlib's native Ext-defined sheaf cohomology, and `R¹f_*`
is its actual right-derived sheaf pushforward.  Exactness is proved
through the cycle and boundary short exact sequences of the resolution;
no Leray theorem, vanishing, or geometric premise is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)

local instance canonicalPushedInjectiveZero :
    Injective ((pushedResolution f (injectiveResolution F)).X 0) :=
  pushedResolution_term_injective f (injectiveResolution F) 0

/-- The first three genuine sheaf-cohomology terms, with the maps
induced by the actual resolution comparison. -/
def firstComplex : ShortComplex AddCommGrpCat.{0} :=
  transportComplex
    (Abstract.firstComplex (integerSheaf Y) (pushedResolution f (injectiveResolution F)))
    (homologyZeroCohomologyIso f (injectiveResolution F) 1)
    (sourceCohomologyIso f F (injectiveResolution F) 1).symm
    (homologyOneExtZeroIso f (injectiveResolution F)).symm

/-- The last three terms use the same edge map and the actual
connecting-map transgression into degree two. -/
def secondComplex : ShortComplex AddCommGrpCat.{0} :=
  transportComplex
    (Abstract.secondComplex (integerSheaf Y) (pushedResolution f (injectiveResolution F)))
    (sourceCohomologyIso f F (injectiveResolution F) 1).symm
    (homologyOneExtZeroIso f (injectiveResolution F)).symm
    (homologyZeroCohomologyIso f (injectiveResolution F) 2)

/-- The two complexes contain the very same edge map. -/
theorem secondComplex_f_eq_firstComplex_g : (secondComplex f F).f = (firstComplex f F).g := rfl

theorem firstComplex_exact : (firstComplex f F).Exact :=
  transportComplex_exact _ _ _ _
    (Abstract.firstComplex_exact (integerSheaf Y) (pushedResolution f (injectiveResolution F)))

theorem secondComplex_exact : (secondComplex f F).Exact :=
  transportComplex_exact _ _ _ _
    (Abstract.secondComplex_exact (integerSheaf Y) (pushedResolution f (injectiveResolution F)))

instance firstComplex_f_mono : Mono (firstComplex f F).f := by
  let : Mono (Abstract.firstComplex (integerSheaf Y)
      (pushedResolution f (injectiveResolution F))).f :=
    Abstract.firstMap_mono (integerSheaf Y) (pushedResolution f (injectiveResolution F))
  exact transportComplex_f_mono _ _ _ _

/-- Inflation from the ordinary pushforward is a map of actual Ext groups. -/
def inflation :
    CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1 →+
      CategoryTheory.Sheaf.H.{0} F 1 := (firstComplex f F).f.hom

/-- The actual edge map into global sections of the first higher direct image. -/
def edge :
    CategoryTheory.Sheaf.H.{0} F 1 →+
      CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 := (firstComplex f F).g.hom

/-- The actual low-degree transgression, induced by the two boundary
maps for cycles and boundaries of the pushed-forward resolution. -/
def transgression :
    CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 →+
      CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 2 := (secondComplex f F).g.hom

/-- Exactness at the initial term means genuine injectivity of inflation. -/
theorem inflation_injective : Function.Injective (inflation f F) :=
  (AddCommGrpCat.mono_iff_injective (firstComplex f F).f).mp inferInstance

/-- Exactness at genuine degree-one cohomology of the source. -/
theorem exact_inflation_edge : Function.Exact (inflation f F) (edge f F) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (firstComplex_exact f F)

/-- Exactness at genuine global sections of the first higher direct image. -/
theorem exact_edge_transgression : Function.Exact (edge f F) (transgression f F) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (secondComplex_exact f F)

/-- The complete requested low-degree Leray exactness assertion. -/
theorem lowDegree_exact :
    Function.Injective (inflation f F) ∧
      Function.Exact (inflation f F) (edge f F) ∧
        Function.Exact (edge f F) (transgression f F) :=
  ⟨inflation_injective f F, exact_inflation_edge f F, exact_edge_transgression f F⟩

end Wikipedia.HopfProblem.SheafLerayLowDegrees
