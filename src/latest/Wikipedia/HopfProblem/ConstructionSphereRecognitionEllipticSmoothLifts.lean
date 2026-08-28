import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothFormula
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothForward

/-!
# Real smoothness of the original vector-coordinate product maps

The actual inverse period matrix and forward period matrix are jointly
smooth in the original open-disc charts.  The primitive gamma coordinate
enters through its literal complex exponential.  This proves smoothness
of both vector lifts of the previously constructed full-cap product.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "I₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℝ ℂ
local notation "IV" => modelWithCornersSelf ℝ RealPlane₄

local instance vectorLiftChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance realVectorLiftChartedSpace :
    ChartedSpace (ℂ × RealPlane₄) (Disc × RealPlane₄) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ RealPlane₄) (Disc × RealPlane₄))

local instance complexRealContMDiffMul : ContMDiffMul I₁ ∞ ℂ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    refine ⟨continuous_mul, fun x y => ?_⟩
    simp only [mfld_simps, chartAt_self_eq]
    rw [contDiffOn_univ]
    exact contDiff_mul

private theorem disc_fst_contMDiff :
    ContMDiff IR I₁ ∞ (fun p : Disc × ComplexPlane₂ => p.1) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem vector_snd_contMDiff :
    ContMDiff IR I₂ ∞ (fun p : Disc × ComplexPlane₂ => p.2) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

private theorem exponential_real_contMDiff :
    ContMDiff I₁ I₁ ∞ CuspUniformization.exponential :=
  ((CuspUniformization.exponential_holomorphic.restrict_scalars ℝ).of_le le_top).contMDiff

private theorem ofReal_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) I₁ ∞ (fun t : ℝ => (t : ℂ)) :=
  Complex.ofRealCLM.contDiff.contMDiff

/-- Smoothness of the exact phase-rotated root, in the unchanged open-disc atlas. -/
theorem forwardLift_fst_contMDiff :
    ContMDiff IR I₁ ∞ (fun p : Disc × ComplexPlane₂ => (forwardLift D p).1) := by
  have ha := PeriodFamilyHolomorphicCohomology.Smooth.inversePeriodCoordinates_native_contMDiff
    D.periods
  have hγ : ContMDiff IR 𝓘(ℝ, ℝ) ∞
      (fun p : Disc × ComplexPlane₂ =>
        (j.twist 0 : ℝ) * ((D.periods.periodEquiv p.1).symm p.2) 0) :=
    contMDiff_const.mul ((contDiff_apply ℝ ℝ (0 : Fin 4)).contMDiff.comp ha)
  have h := (exponential_real_contMDiff.comp (ofReal_contMDiff.comp hγ)).mul
    (contMDiff_subtype_val.comp disc_fst_contMDiff)
  apply (ContMDiff.subtypeVal_comp_iff unitDisc _).mp
  exact h.congr (forwardLift_fst_val D)

/-- Both components of the genuine forward vector lift are real smooth. -/
theorem forwardLift_contMDiff : ContMDiff IR IR ∞ (forwardLift D) := by
  have hz : ContMDiff IR I₂ ∞ (fun p : Disc × ComplexPlane₂ => (forwardLift D p).2) :=
    (Elliptic.periodEquiv D.centralPeriod.val).contDiff.contMDiff.comp
      (PeriodFamilyHolomorphicCohomology.Smooth.inversePeriodCoordinates_native_contMDiff
        D.periods)
  rw [modelWithCornersSelf_prod]
  exact (forwardLift_fst_contMDiff D).prodMk hz

private theorem centralInverse_contMDiff :
    ContMDiff IR IV ∞ (fun p : Disc × ComplexPlane₂ =>
      (Elliptic.periodEquiv D.centralPeriod.val).symm p.2) :=
  (Elliptic.periodEquiv D.centralPeriod.val).symm.contDiff.contMDiff.comp vector_snd_contMDiff

/-- The inverse phase is smooth in the same original open-disc atlas. -/
theorem inverseLift_fst_contMDiff :
    ContMDiff IR I₁ ∞ (fun p : Disc × ComplexPlane₂ => (inverseLift D p).1) := by
  have hγ : ContMDiff IR 𝓘(ℝ, ℝ) ∞
      (fun p : Disc × ComplexPlane₂ =>
        (j.twist 0 : ℝ) * ((Elliptic.periodEquiv D.centralPeriod.val).symm p.2) 0) :=
    contMDiff_const.mul
      ((contDiff_apply ℝ ℝ (0 : Fin 4)).contMDiff.comp (centralInverse_contMDiff D))
  have h := (exponential_real_contMDiff.comp (ofReal_contMDiff.comp hγ).neg).mul
    (contMDiff_subtype_val.comp disc_fst_contMDiff)
  apply (ContMDiff.subtypeVal_comp_iff unitDisc _).mp
  exact h.congr (inverseLift_fst_val D)

/-- The actual inverse reconstructs the varying period vector smoothly at the rotated base. -/
theorem inverseLift_contMDiff : ContMDiff IR IR ∞ (inverseLift D) := by
  have hp : ContMDiff IR (modelWithCornersSelf ℝ (ℂ × RealPlane₄)) ∞
      (fun p : Disc × ComplexPlane₂ =>
        ((inverseLift D p).1, (Elliptic.periodEquiv D.centralPeriod.val).symm p.2)) := by
    rw [modelWithCornersSelf_prod]
    exact (inverseLift_fst_contMDiff D).prodMk (centralInverse_contMDiff D)
  have hz := (PeriodFamilyHolomorphicCohomology.Smooth.periodCoordinates_native_contMDiff
    D.periods).comp hp
  rw [modelWithCornersSelf_prod]
  exact (inverseLift_fst_contMDiff D).prodMk hz

/-- An actual real smooth equivalence of the original complex vector-cover manifolds. -/
def vectorLiftDiffeomorph : Diffeomorph IR IR
    (Disc × ComplexPlane₂) (Disc × ComplexPlane₂) ∞ where
  toFun := forwardLift D
  invFun := inverseLift D
  left_inv := inverseLift_forwardLift D
  right_inv := forwardLift_inverseLift D
  contMDiff_toFun := forwardLift_contMDiff D
  contMDiff_invFun := inverseLift_contMDiff D

@[simp] theorem vectorLiftDiffeomorph_apply (p : Disc × ComplexPlane₂) :
    vectorLiftDiffeomorph D p = forwardLift D p := rfl

@[simp] theorem vectorLiftDiffeomorph_symm_apply (p : Disc × ComplexPlane₂) :
    (vectorLiftDiffeomorph D).symm p = inverseLift D p := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
