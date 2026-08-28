import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryComplex
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryProducts
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalComplex

/-!
# Literal images of the triangular double-complex maps

An actual additive functor sends the original twelve maps to additive
group homomorphisms. The resulting group total complex is the one whose
exactness and product computations have been proved separately.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]

private theorem map_comp_zero {A B E : C} (f : A ⟶ B) (g : B ⟶ E)
    (h : f ≫ g = 0) : (F.map g).hom.comp (F.map f).hom = 0 := by
  change (F.map f ≫ F.map g).hom = (0 : F.obj A ⟶ F.obj E).hom
  rw [← F.map_comp, h, F.map_zero]

omit [Preadditive C] [F.Additive] in
private theorem map_comp_eq {A B B' E : C} (f : A ⟶ B) (g : B ⟶ E)
    (f' : A ⟶ B') (g' : B' ⟶ E) (h : f ≫ g = f' ≫ g') :
    (F.map g).hom.comp (F.map f).hom =
      (F.map g').hom.comp (F.map f').hom := by
  change (F.map f ≫ F.map g).hom = (F.map f' ≫ F.map g').hom
  rw [← F.map_comp, h, F.map_comp]

private theorem prodCongr_apply {A B E G : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup E] [AddCommGroup G]
    (f : A ≃+ E) (g : B ≃+ G) (s : A × B) :
    f.prodCongr g s = (f s.1, g s.2) := rfl

namespace Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

/-- The actual additive-group diagram obtained by the original functor. -/
def mapData : TotalComplex.Data (F.obj R00) (F.obj R10) (F.obj R01)
    (F.obj R20) (F.obj R11) (F.obj R02) (F.obj R30) (F.obj R21)
    (F.obj R12) (F.obj R03) where
  v00 := (F.map D.v00).hom
  h00 := (F.map D.h00).hom
  v10 := (F.map D.v10).hom
  h10 := (F.map D.h10).hom
  v01 := (F.map D.v01).hom
  h01 := (F.map D.h01).hom
  v20 := (F.map D.v20).hom
  h20 := (F.map D.h20).hom
  v11 := (F.map D.v11).hom
  h11 := (F.map D.h11).hom
  v02 := (F.map D.v02).hom
  h02 := (F.map D.h02).hom
  vertical00 := map_comp_zero F _ _ D.vertical00
  vertical10 := map_comp_zero F _ _ D.vertical10
  vertical01 := map_comp_zero F _ _ D.vertical01
  horizontal00 := map_comp_zero F _ _ D.horizontal00
  horizontal01 := map_comp_zero F _ _ D.horizontal01
  horizontal10 := map_comp_zero F _ _ D.horizontal10
  mixed00 := map_comp_eq F _ _ _ _ D.mixed00
  mixed10 := map_comp_eq F _ _ _ _ D.mixed10
  mixed01 := map_comp_eq F _ _ _ _ D.mixed01

variable [HasBinaryBiproducts C]

/-- The degree-one functor image as the actual pair of its components. -/
def oneEquiv : F.obj D.oneTerm ≃+ (D.mapData F).One :=
  binaryEquiv F R10 R01

/-- The degree-two functor image as the actual three components. -/
def twoEquiv : F.obj D.twoTerm ≃+ (D.mapData F).Two :=
  (binaryEquiv F R20 (R11 ⊞ R02)).trans
    (AddEquiv.prodCongr (AddEquiv.refl _) (binaryEquiv F R11 R02))

/-- The degree-three functor image as the actual four components. -/
def threeEquiv : F.obj D.threeTerm ≃+ (D.mapData F).Three :=
  (binaryEquiv F R30 (R21 ⊞ (R12 ⊞ R03))).trans
    (AddEquiv.prodCongr (AddEquiv.refl _)
      ((binaryEquiv F R21 (R12 ⊞ R03)).trans
        (AddEquiv.prodCongr (AddEquiv.refl _) (binaryEquiv F R12 R03))))

@[simp] theorem oneEquiv_apply (s : F.obj D.oneTerm) :
    D.oneEquiv F s = (F.map biprod.fst s, F.map biprod.snd s) :=
  binaryEquiv_apply F R10 R01 s

@[simp] theorem twoEquiv_apply (s : F.obj D.twoTerm) :
    D.twoEquiv F s = (F.map biprod.fst s,
      F.map (biprod.snd ≫ biprod.fst) s, F.map (biprod.snd ≫ biprod.snd) s) := by
  simp only [twoEquiv, AddEquiv.trans_apply, prodCongr_apply,
    AddEquiv.refl_apply, binaryEquiv_apply, F.map_comp, AddCommGrpCat.comp_apply]

@[simp] theorem threeEquiv_apply (s : F.obj D.threeTerm) :
    D.threeEquiv F s = (F.map biprod.fst s,
      F.map (biprod.snd ≫ biprod.fst) s,
      F.map (biprod.snd ≫ biprod.snd ≫ biprod.fst) s,
      F.map (biprod.snd ≫ biprod.snd ≫ biprod.snd) s) := by
  simp only [threeEquiv, AddEquiv.trans_apply, prodCongr_apply,
    AddEquiv.refl_apply, binaryEquiv_apply, F.map_comp, AddCommGrpCat.comp_apply]

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory
