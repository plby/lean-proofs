import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothCovers
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothLifts

/-!
# The native full elliptic product is a real smooth diffeomorphism

The exact frozen homeomorphism and its exact inverse are smooth for the
original complex quotient atlases, with scalars restricted to the real
field.  The proof uses the actual complex vector coverings and the smooth
mutually inverse vector formulas.  No product atlas is imposed on a filling.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic SpecialPeriods EllipticFullProduct

local notation "IR" => modelWithCornersSelf ℝ FamilyModel

variable {j : Kind} (D : Equivariant.Data j)

attribute [local instance] vectorProductChartedSpace surfaceProductChartedSpace

/-- The original full filling atlas, after restriction of scalars, is real smooth. -/
theorem filling_isRealManifold :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    IsManifold IR ∞ (D.Space j.twist (mainTwist_admissible j)) := by
  let := D.chartedSpace j.twist (mainTwist_admissible j)
  let := D.isManifold j.twist (mainTwist_admissible j)
  exact complexManifold_isRealManifold _ ∞

/-- The target uses the actual product of the disc and native central-surface atlases. -/
theorem centralProduct_isRealManifold : IsManifold IR ∞
    (Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)) := by
  have : IsManifold (modelWithCornersSelf ℂ FamilyModel) ω
      (Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ComplexPlane₂)) Disc
      (Surface j D.centralPeriod j.twist (mainTwist_admissible j))
  exact complexManifold_isRealManifold _ ∞

/-- Smoothness of the unchanged forward product map in the original filling atlas. -/
theorem fillingProductHomeomorph_contMDiff :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    ContMDiff IR IR ∞ (fillingProductHomeomorph D) := by
  let := D.chartedSpace j.twist (mainTwist_admissible j)
  apply contMDiff_of_comp_real_localDiffeomorph
    (fillingCover_real_isLocalDiffeomorph D) (fillingCover_surjective D)
  have hc : ContMDiff IR IR ∞ (centralCover D) :=
    (centralCover_real_isLocalDiffeomorph D).contMDiff.of_le le_top
  exact (hc.comp (forwardLift_contMDiff D)).congr
    (fun p => (centralCover_forwardLift D p).symm)

/-- Smoothness of the unchanged inverse in the original central-surface product atlas. -/
theorem fillingProductHomeomorph_symm_contMDiff :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    ContMDiff IR IR ∞ (fillingProductHomeomorph D).symm := by
  let := D.chartedSpace j.twist (mainTwist_admissible j)
  apply contMDiff_of_comp_real_localDiffeomorph
    (centralCover_real_isLocalDiffeomorph D) (centralCover_surjective D)
  have hc : ContMDiff IR IR ∞ (fillingCover D) :=
    (fillingCover_real_isLocalDiffeomorph D).contMDiff.of_le le_top
  exact (hc.comp (inverseLift_contMDiff D)).congr
    (fun p => (fillingCover_inverseLift D p).symm)

/-- Upgrade of the exact original full-cap homeomorphism, without changing either atlas. -/
def fillingProductDiffeomorph :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    Diffeomorph IR IR (D.Space j.twist (mainTwist_admissible j))
      (Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)) ∞ := by
  letI := D.chartedSpace j.twist (mainTwist_admissible j)
  exact {
    toEquiv := (fillingProductHomeomorph D).toEquiv
    contMDiff_toFun := fillingProductHomeomorph_contMDiff D
    contMDiff_invFun := fillingProductHomeomorph_symm_contMDiff D }

@[simp] theorem fillingProductDiffeomorph_apply
    (y : D.Space j.twist (mainTwist_admissible j)) :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    fillingProductDiffeomorph D y = fillingProductHomeomorph D y := rfl

@[simp] theorem fillingProductDiffeomorph_symm_apply
    (p : Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)) :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    (fillingProductDiffeomorph D).symm p = (fillingProductHomeomorph D).symm p := rfl

section Special

open SpecialPeriods.EllipticFilling ThreefoldOverlapMappingTorus.Elliptic
open TrianglePeriodFamily.Boundary.EllipticCapProduct

/-- Real smoothness of the actual special-period full product, with its original chosen atlas. -/
theorem specialFillingProductHomeomorph_contMDiff (j : Kind) :
    letI := specialFullFillingChartedSpace j
    ContMDiff IR IR ∞ (specialFillingProductHomeomorph j) :=
  fillingProductHomeomorph_contMDiff (specialLocalData j)

/-- Real smoothness of the exact inverse for the actual special-period full product. -/
theorem specialFillingProductHomeomorph_symm_contMDiff (j : Kind) :
    letI := specialFullFillingChartedSpace j
    ContMDiff IR IR ∞ (specialFillingProductHomeomorph j).symm :=
  fillingProductHomeomorph_symm_contMDiff (specialLocalData j)

/-- The two actual full elliptic fillings are real smoothly their original disc-surface products. -/
def specialFillingProductDiffeomorph (j : Kind) :
    letI := specialFullFillingChartedSpace j
    Diffeomorph IR IR (SpecialFullFilling j) (Disc × BoundaryCentralSurface j) ∞ :=
  fillingProductDiffeomorph (specialLocalData j)

@[simp] theorem specialFillingProductDiffeomorph_apply (j : Kind) (y : SpecialFullFilling j) :
    letI := specialFullFillingChartedSpace j
    specialFillingProductDiffeomorph j y = specialFillingProductHomeomorph j y := rfl

@[simp] theorem specialFillingProductDiffeomorph_symm_apply (j : Kind)
    (p : Disc × BoundaryCentralSurface j) :
    letI := specialFullFillingChartedSpace j
    (specialFillingProductDiffeomorph j).symm p =
      (specialFillingProductHomeomorph j).symm p := rfl

/-- The smooth upgrade retains the exact original boundary product and its specified radius. -/
theorem specialFillingProductDiffeomorph_boundary (j : Kind) (q : SpecialBoundary j) :
    letI := specialFullFillingChartedSpace j
    specialFillingProductDiffeomorph j (specialBoundaryToFullFilling j q) =
      (ThreefoldOverlapMappingTorus.root j.order
        (Threefold.specialBaseCover.radius (some j)) (specialRootRadius j)
        (boundaryProductHomeomorph j q).2, (boundaryProductHomeomorph j q).1) :=
  specialFillingProductHomeomorph_boundary j q

end Special

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
