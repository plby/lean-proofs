import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExt
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtOriginal

/-!
# Naturality for the manuscript's original constant complex sheaf

The source is the original ring-sheafification with multiplication
forgotten, its native Ext cohomology, and its original pullback map.
The proved original/native constant comparison transports the genuine
finite-closed-map comparison to exactly these original objects and maps.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

open CuspNormalization.SheafConstants

private theorem composite_square {C : Type*} [Category C]
    {A B D A' B' D' : C}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

variable {X Y : TopCat.{0}} [CompactSpace X] [T2Space X]
  [CompactSpace Y] [T2Space Y] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The original constant-complex-sheaf H¹ comparison intertwines
the original Ext pullback and the actual singular cohomology pullback. -/
theorem complex_h1_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    complexCohomologyPullback f hf hfinite 1 ≫ (complexSheafH1Iso X hX).hom =
      (complexSheafH1Iso Y hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f.hom) 1 :=
  composite_square
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) 1).map
      (complexAdditiveSheafIso Y).hom)
    (constantSheafH1Iso Y (AddCommGrpCat.of ℂ) hY).hom
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
      (complexAdditiveSheafIso X).hom)
    (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hX).hom
    (complexCohomologyPullback f hf hfinite 1)
    (constantCohomologyPullback f hf hfinite (AddCommGrpCat.of ℂ) 1)
    (HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f.hom) 1)
    (complexCohomologyPullback_native f hf hfinite 1)
    (h1_naturality f hf hfinite (AddCommGrpCat.of ℂ) hX hY)

/-- The same literal original-sheaf comparison square in degree two. -/
theorem complex_h2_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    complexCohomologyPullback f hf hfinite 2 ≫ (complexSheafH2Iso X hX).hom =
      (complexSheafH2Iso Y hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f.hom) 2 :=
  composite_square
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) 2).map
      (complexAdditiveSheafIso Y).hom)
    (constantSheafH2Iso Y (AddCommGrpCat.of ℂ) hY).hom
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      (complexAdditiveSheafIso X).hom)
    (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hX).hom
    (complexCohomologyPullback f hf hfinite 2)
    (constantCohomologyPullback f hf hfinite (AddCommGrpCat.of ℂ) 2)
    (HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f.hom) 2)
    (complexCohomologyPullback_native f hf hfinite 2)
    (h2_naturality f hf hfinite (AddCommGrpCat.of ℂ) hX hY)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
