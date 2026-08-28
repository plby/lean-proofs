import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryMap

/-!
# Actual coordinate formulas for mapped total differentials

These formulas identify the original categorical maps under any actual
additive functor with the literal signed total maps on pairs and triples.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]

theorem oneEquiv_map_d0 (s : F.obj R00) :
    D.oneEquiv F (F.map D.d0 s) = (D.mapData F).d0 s := by
  rw [oneEquiv_apply, TotalComplex.Data.d0_apply]
  apply Prod.ext
  · change F.map biprod.fst (F.map D.d0 s) = F.map D.v00 s
    rw [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d0_fst]
  · change F.map biprod.snd (F.map D.d0 s) = F.map D.h00 s
    rw [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d0_snd]

theorem twoEquiv_map_d1 (s : F.obj D.oneTerm) :
    D.twoEquiv F (F.map D.d1 s) = (D.mapData F).d1 (D.oneEquiv F s) := by
  rw [twoEquiv_apply, TotalComplex.Data.d1_apply, oneEquiv_apply]
  apply Prod.ext
  · change F.map biprod.fst (F.map D.d1 s) =
      F.map D.v10 (F.map biprod.fst s)
    rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply,
      ← F.map_comp, ← F.map_comp, D.d1_fst]
  · apply Prod.ext
    · change F.map (biprod.snd ≫ biprod.fst) (F.map D.d1 s) =
        -F.map D.h10 (F.map biprod.fst s) + F.map D.v01 (F.map biprod.snd s)
      simp only [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d1_snd_fst,
        F.map_add, F.map_neg]
      rfl
    · change F.map (biprod.snd ≫ biprod.snd) (F.map D.d1 s) =
        F.map D.h01 (F.map biprod.snd s)
      rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply,
        ← F.map_comp, ← F.map_comp, D.d1_snd_snd]

theorem threeEquiv_map_d2 (s : F.obj D.twoTerm) :
    D.threeEquiv F (F.map D.d2 s) = (D.mapData F).d2 (D.twoEquiv F s) := by
  rw [threeEquiv_apply, TotalComplex.Data.d2_apply, twoEquiv_apply]
  apply Prod.ext
  · change F.map biprod.fst (F.map D.d2 s) =
      F.map D.v20 (F.map biprod.fst s)
    rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply,
      ← F.map_comp, ← F.map_comp, D.d2_fst]
  · apply Prod.ext
    · change F.map (biprod.snd ≫ biprod.fst) (F.map D.d2 s) =
        F.map D.h20 (F.map biprod.fst s) +
          F.map D.v11 (F.map (biprod.snd ≫ biprod.fst) s)
      simp only [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d2_snd_fst,
        F.map_add, Category.assoc]
      rfl
    · apply Prod.ext
      · change F.map (biprod.snd ≫ biprod.snd ≫ biprod.fst) (F.map D.d2 s) =
          -F.map D.h11 (F.map (biprod.snd ≫ biprod.fst) s) +
            F.map D.v02 (F.map (biprod.snd ≫ biprod.snd) s)
        simp only [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d2_snd_snd_fst,
          F.map_add, F.map_neg, Category.assoc]
        rfl
      · change F.map (biprod.snd ≫ biprod.snd ≫ biprod.snd) (F.map D.d2 s) =
          F.map D.h02 (F.map (biprod.snd ≫ biprod.snd) s)
        simp only [← AddCommGrpCat.comp_apply, ← F.map_comp, D.d2_snd_snd_snd,
          Category.assoc]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data
