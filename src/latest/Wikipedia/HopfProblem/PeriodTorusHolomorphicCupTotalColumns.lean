import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalColumnsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalExactTwo

/-!
# Genuine stalk exactness of the Dolbeault total columns

The smooth columns are the original Godement resolution. The pair
column is exact by its actual two-coordinate stalk comparison. Its
native Dolbeault source is identified by the literal pair isomorphism,
not by an assumed exactness property of the total complex.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total

open SheafCupProduct SheafSingularCupComparison

variable {X : TopCat.{0}}

/-- Actual exact sheaf maps remain exact on each original stalk. -/
theorem stalk_exact (S : ShortComplex (Pairs.AbSheaf X)) (h : S.Exact) (x : X) :
    Function.Exact ((GodementExact.additiveStalk x).map S.f).hom
      ((GodementExact.additiveStalk x).map S.g).hom :=
  (S.map (GodementExact.additiveStalk x)).ab_exact_iff_function_exact.mp
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp h x)

private theorem exact_precomp {A A' B C : Type*} [Zero C]
    {f : A → B} {g : B → C} (e : A' → A) (he : Function.Surjective e)
    (h : Function.Exact f g) : Function.Exact (f ∘ e) g := by
  intro y
  rw [h y]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := he a
    exact ⟨b, by rw [Function.comp_apply, hb, ha]⟩
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩

private theorem map_square {A B B' C : Pairs.AbSheaf X}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C)
    (h : f ≫ g = f' ≫ g') (x : X) :
    ((GodementExact.additiveStalk x).map g).hom.comp
        ((GodementExact.additiveStalk x).map f).hom =
      ((GodementExact.additiveStalk x).map g').hom.comp
        ((GodementExact.additiveStalk x).map f').hom := by
  change ((GodementExact.additiveStalk x).map f ≫
    (GodementExact.additiveStalk x).map g).hom =
      ((GodementExact.additiveStalk x).map f' ≫
        (GodementExact.additiveStalk x).map g').hom
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- The original germ map is injective by the genuine stalk evaluation retraction. -/
theorem augmentation_stalk_injective (F : GodementRing.RingSheaf X) (x : X) :
    Function.Injective ((GodementExact.additiveStalk x).map
      (GodementExact.augmentation F)).hom := by
  intro a b hab
  exact (ConcreteCategory.congr_hom
      (GodementExact.augmentation_stalkRetraction F x) a).symm.trans
    ((congrArg (GodementExact.stalkRetraction F x) hab).trans
      (ConcreteCategory.congr_hom
        (GodementExact.augmentation_stalkRetraction F x) b))

private theorem iso_hom_injective {A B : AddCommGrpCat.{0}} (e : A ≅ B) :
    Function.Injective e.hom.hom := (ConcreteCategory.bijective_of_isIso e.hom).1

private theorem iso_hom_surjective {A B : AddCommGrpCat.{0}} (e : A ≅ B) :
    Function.Surjective e.hom.hom := (ConcreteCategory.bijective_of_isIso e.hom).2

/-- The actual stalk functor, with the original period-torus topology fixed. -/
abbrev nativeStalk (p : PeriodDomain) (x : p.Torus) :=
  GodementExact.additiveStalk (X := TopCat.of p.Torus) x

namespace CompatibleOperators

variable {p : PeriodDomain} (D : CompatibleOperators p)

/-- Apply the actual stalk functor to the genuine categorical total diagram. -/
abbrev stalkData (x : p.Torus) :=
  D.categoryData.mapData (nativeStalk p x)

/-- The actual native pair augmentation is injective on stalks. -/
theorem columnUnit1_stalk_injective (x : p.Torus) :
    Function.Injective ((nativeStalk p x).map (columnUnit1 p)).hom := by
  change Function.Injective ((nativeStalk p x).map
    ((nativePairIso p).hom ≫ Pairs.map (columnUnit0 p))).hom
  rw [Functor.map_comp]
  exact (Pairs.stalk_map_injective (columnUnit0 p) x
    (augmentation_stalk_injective (Derivation.smoothRingSheaf p) x)).comp
      (iso_hom_injective ((nativeStalk p x).mapIso (nativePairIso p)))

/-- Exactness of the actual native pair-augmented stalk column. -/
theorem column01_exact (x : p.Torus) : Function.Exact
    ((nativeStalk p x).map (columnUnit1 p)).hom
    ((nativeStalk p x).map
      (Pairs.map (GodementExact.d0 (Derivation.smoothRingSheaf p)))).hom := by
  change Function.Exact ((nativeStalk p x).map
    ((nativePairIso p).hom ≫ Pairs.map (columnUnit0 p))).hom _
  rw [Functor.map_comp]
  have hp : Function.Exact
      ((nativeStalk p x).map (Pairs.map (columnUnit0 p))).hom
      ((nativeStalk p x).map
        (Pairs.map (GodementExact.d0 (Derivation.smoothRingSheaf p)))).hom :=
    stalk_exact _ (Pairs.map_exact
      (GodementExact.complex0 (Derivation.smoothRingSheaf p))
      (GodementExact.exact0 (Derivation.smoothRingSheaf p))) x
  exact exact_precomp
    ((nativeStalk p x).map (nativePairIso p).hom).hom
    (iso_hom_surjective ((nativeStalk p x).mapIso (nativePairIso p))) hp

/-- All exactness and injectivity data for the original augmented stalk columns. -/
def stalkColumns (x : p.Torus) : TotalComplex.AugmentedColumns (D.stalkData x)
    ((nativeStalk p x).obj (Row.partialResolution p).I₀)
    ((nativeStalk p x).obj (Row.partialResolution p).I₁)
    ((nativeStalk p x).obj (Row.partialResolution p).I₂)
    ((nativeStalk p x).obj (Row.partialResolution p).I₃) where
  i0 := ((nativeStalk p x).map (columnUnit0 p)).hom
  i1 := ((nativeStalk p x).map (columnUnit1 p)).hom
  i2 := ((nativeStalk p x).map (columnUnit2 p)).hom
  i3 := ((nativeStalk p x).map (columnUnit3 p)).hom
  d0 := ((nativeStalk p x).map (Row.partialResolution p).d₀).hom
  d1 := ((nativeStalk p x).map (Row.partialResolution p).d₁).hom
  d2 := ((nativeStalk p x).map (Row.partialResolution p).d₂).hom
  comm0 := map_square _ _ _ _ D.columnUnit_d0 x
  comm1 := map_square _ _ _ _ D.columnUnit_d1 x
  comm2 := map_square _ _ _ _ D.columnUnit_d2 x
  column00 := stalk_exact _ (GodementExact.exact0 (Derivation.smoothRingSheaf p)) x
  column01 := column01_exact x
  column02 := stalk_exact _ (GodementExact.exact0 (Derivation.smoothRingSheaf p)) x
  column10 := stalk_exact _ (GodementExact.exact1 (Derivation.smoothRingSheaf p)) x
  column20 := stalk_exact _ (GodementExact.exact2 (Derivation.smoothRingSheaf p)) x
  column11 := stalk_exact _ (Pairs.map_exact
    (GodementExact.complex1 (Derivation.smoothRingSheaf p))
    (GodementExact.exact1 (Derivation.smoothRingSheaf p))) x
  injective0 := augmentation_stalk_injective (Derivation.smoothRingSheaf p) x
  injective1 := columnUnit1_stalk_injective x
  injective2 := augmentation_stalk_injective (Derivation.smoothRingSheaf p) x
  injective3 := iso_hom_injective ((nativeStalk p x).mapIso
    (zeroSheafIso (TopCat.of p.Torus)).symm)

end CompatibleOperators

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total
