import Wikipedia.HopfProblem.SheafLerayCurveBasic
import Wikipedia.HopfProblem.SheafLerayCurveAbstract

/-!
# Genuine higher-degree curve-type Leray short exact sequences

For every actual continuous map and abelian sheaf, the finite stated
vanishings of the genuine higher direct images imply

`0 → H¹(Y,Rⁿ⁺¹f_*F) → Hⁿ⁺²(X,F) → H⁰(Y,Rⁿ⁺²f_*F) → 0`.

The proof uses the actual pushed injective resolution, its proved cycle
and boundary Ext vanishings, and its genuine native section-complex
comparison. There is no spectral-sequence or termwise-acyclicity premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

attribute [local irreducible] Abstract.curveFirstMap

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X) (n : ℕ)

/-- The original right edge on genuine source cohomology. It exists
without any vanishing hypotheses and uses the actual cycle quotient. -/
def edgeMorphism : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} F (n + 2)) ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 2)) 0) :=
  (SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)).hom ≫
    Abstract.curveEdgeMap (integerSheaf Y) (canonicalComplex f F) n ≫
      (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).inv

/-- The actual curve-type complex, with every term compared to the original
native sheaf-cohomology group by its proved resolution isomorphism. -/
def sequence (h : CohomologyVanishing f F (n + 3)) : ShortComplex AddCommGrpCat.{0} :=
  SheafLerayLowDegrees.transportComplex
    (Abstract.curveComplex (integerSheaf Y) (canonicalComplex f F)
      (canonicalComplex_term_injective f F) n (canonicalComplex_higherVanishing f F _ h))
    (resolutionCohomologyIso f (injectiveResolution F) (n + 1) 1)
    (SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)).symm
    (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).symm

/-- The right arrow is exactly the original edge, independent of the proof
that the relevant higher-direct-image cohomology vanishes. -/
@[simp] theorem sequence_g (h : CohomologyVanishing f F (n + 3)) :
    (sequence f F n h).g = edgeMorphism f F n := rfl

/-- Genuine short exactness, with only the stated actual cohomology
vanishings as input. Injectivity of resolution terms is proved above. -/
theorem sequence_shortExact (h : CohomologyVanishing f F (n + 3)) :
    (sequence f F n h).ShortExact :=
  ShortComplex.shortExact_of_iso
    (SheafLerayLowDegrees.transportComplexIso _ _ _ _)
    (Abstract.curveComplex_shortExact (integerSheaf Y) (canonicalComplex f F)
      (canonicalComplex_term_injective f F) n (canonicalComplex_higherVanishing f F _ h))

/-- The original left map from genuine cohomology of the actual derived image. -/
def inflation (h : CohomologyVanishing f F (n + 3)) :
    CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 1)) 1 →+
      CategoryTheory.Sheaf.H.{0} F (n + 2) := (sequence f F n h).f.hom

/-- The original right Leray edge, with no vanishing hypothesis in its definition. -/
def edge : CategoryTheory.Sheaf.H.{0} F (n + 2) →+
    CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 2)) 0 := (edgeMorphism f F n).hom

/-- The forward map is precisely the actual section-complex comparison,
the original cycle quotient, and the genuine derived-image comparison. -/
@[simp] theorem edge_apply (x : CategoryTheory.Sheaf.H.{0} F (n + 2)) :
    edge f F n x = (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).inv
      (Abstract.curveEdgeMap (integerSheaf Y) (canonicalComplex f F) n
        ((SheafLerayLowDegrees.sourceCohomologyIso f F
          (injectiveResolution F) (n + 2)).hom x)) := rfl

/-- The left map uses the original quotient-induced Ext inverse and the
actual cycles injection, via the canonical native term comparisons. -/
@[simp] theorem inflation_apply (h : CohomologyVanishing f F (n + 3))
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 1)) 1) :
    inflation f F n h x =
      (SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)).inv
        (Abstract.curveFirstMap (integerSheaf Y) (canonicalComplex f F)
          (canonicalComplex_term_injective f F) n (canonicalComplex_higherVanishing f F _ h)
          ((resolutionCohomologyIso f (injectiveResolution F) (n + 1) 1).inv x)) := by
  dsimp only [inflation, sequence, SheafLerayLowDegrees.transportComplex,
    Abstract.curveComplex, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply, AddCommGrpCat.Hom.hom, Iso.symm]
  apply congrArg
    ((SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)).inv.hom)
  apply congrArg
    ((Abstract.curveFirstMap (integerSheaf Y) (canonicalComplex f F)
      (canonicalComplex_term_injective f F) n
      (canonicalComplex_higherVanishing f F _ h)).hom)
  rfl

theorem inflation_injective (h : CohomologyVanishing f F (n + 3)) :
    Function.Injective (inflation f F n h) :=
  (AddCommGrpCat.mono_iff_injective (sequence f F n h).f).mp
    (sequence_shortExact f F n h).mono_f

theorem exact_inflation_edge (h : CohomologyVanishing f F (n + 3)) :
    Function.Exact (inflation f F n h) (edge f F n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (sequence_shortExact f F n h).exact

theorem edge_surjective (h : CohomologyVanishing f F (n + 3)) :
    Function.Surjective (edge f F n) :=
  (AddCommGrpCat.epi_iff_surjective (sequence f F n h).g).mp
    (sequence_shortExact f F n h).epi_g

/-- The complete native short exact assertion, with original maps and
no further geometric, injectivity, or spectral-sequence assumptions. -/
theorem short_exact (h : CohomologyVanishing f F (n + 3)) :
    Function.Injective (inflation f F n h) ∧
      Function.Exact (inflation f F n h) (edge f F n) ∧
        Function.Surjective (edge f F n) :=
  ⟨inflation_injective f F n h, exact_inflation_edge f F n h, edge_surjective f F n h⟩

end Wikipedia.HopfProblem.SheafLerayCurve
