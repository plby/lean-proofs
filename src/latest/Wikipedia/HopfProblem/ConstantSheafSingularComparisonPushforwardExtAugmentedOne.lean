import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedBasic

/-!
# Native sheaf cohomology of the actual pushed augmented resolution

The canonical finite-pushforward Ext map commutes with both original
resolution comparisons, as follows from its connecting-map compatibility
and its literal degree-zero global-section action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

private theorem composition_equal {C : Type*} [Category C]
    {A B D A' B' : C} (a : A ⟶ B) (b : B ⟶ D)
    (a' : A' ⟶ B') (b' : B' ⟶ D) (x : A ⟶ A') (y : B ⟶ B')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b) :
    x ≫ (a' ≫ b') = a ≫ b := by
  rw [← Category.assoc, ha, Category.assoc, hb]

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : AugmentedResolution (AbelianSheaf X))

/-- Native degree-one sheaf cohomology and the canonical resolution
comparison commute with the genuine finite closed pushforward map. -/
theorem augmented_h1_forward
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)] :
    forwardHom f hf hfinite R.F 1 ≫
        (pushforwardAugmentedResolution f hf hfinite R).h1Iso.hom = R.h1Iso.hom := by
  let : PreservesFiniteLimits (pushforward f) :=
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let : PreservesFiniteColimits (pushforward f) :=
    pushforward_preservesFiniteColimits f hf hfinite
  let Q := pushforwardAugmentedResolution f hf hfinite R
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf Y)
      (PushforwardExtFunctor.mappedResolution (pushforward f) R).complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf Y) Q.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)›
  have hext : forwardHom f hf hfinite R.F 1 ≫ (Q.extOneIso (unitSheaf Y)).hom =
      (R.extOneIso (unitSheaf X)).hom ≫
        ShortComplex.homologyMap (extZeroForwardMap f hf hfinite R) :=
    PushforwardExtFunctor.extOneIso_naturality (pushforward f) (integerUnit f) R
  have hglobal : ShortComplex.homologyMap (extZeroForwardMap f hf hfinite R) ≫
        ShortComplex.homologyMap Q.extZeroGlobalIso.hom =
      ShortComplex.homologyMap R.extZeroGlobalIso.hom :=
    (ShortComplex.homologyMap_comp (extZeroForwardMap f hf hfinite R)
      Q.extZeroGlobalIso.hom).symm.trans
        (congrArg (fun k : R.extZeroComplex (unitSheaf X) ⟶ R.globalComplex =>
          ShortComplex.homologyMap k) (extZeroGlobal_forward f hf hfinite R))
  change forwardHom f hf hfinite R.F 1 ≫
      ((Q.extOneIso (unitSheaf Y)).hom ≫ ShortComplex.homologyMap Q.extZeroGlobalIso.hom) =
    (R.extOneIso (unitSheaf X)).hom ≫ ShortComplex.homologyMap R.extZeroGlobalIso.hom
  exact composition_equal
    (R.extOneIso (unitSheaf X)).hom (ShortComplex.homologyMap R.extZeroGlobalIso.hom)
    (Q.extOneIso (unitSheaf Y)).hom (ShortComplex.homologyMap Q.extZeroGlobalIso.hom)
    (forwardHom f hf hfinite R.F 1)
    (ShortComplex.homologyMap (extZeroForwardMap f hf hfinite R)) hext hglobal


end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
