import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopy
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps

/-!
# The supported isotopy on the original global elliptic patch

The already constructed native patch biholomorphism is merely regarded
as a real smooth diffeomorphism.  Conjugating the actual cap isotopy by
this map gives the family on the literal open subset of the original
global threefold.  Both atlases and all point formulas are unchanged.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy
open TrianglePeriodFamily.Boundary

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace
  smallCollarTimeChartedSpace

/-- The actual full inverse image of the original elliptic base patch. -/
abbrev capPatch (j : Kind) : Opens Threefold.Space :=
  Threefold.liftedPatch (some (some j))

/-- The ordinary product atlas of real time and the original global manifold. -/
@[instance_reducible] def globalTimeChartedSpace :
    ChartedSpace (ℝ × FamilyModel) (ℝ × Threefold.Space) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ FamilyModel) (ℝ × Threefold.Space))

/-- The ordinary product atlas on time and the native open global patch. -/
@[instance_reducible] def patchTimeChartedSpace (j : Kind) :
    ChartedSpace (ℝ × FamilyModel) (ℝ × capPatch j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ FamilyModel) (ℝ × capPatch j))

attribute [local instance] globalTimeChartedSpace patchTimeChartedSpace

/-- Restriction of scalars on the actual native patch biholomorphism. -/
def capPatchDiffeomorph (j : Kind) :
    Diffeomorph IR IR (SpecialEllipticPiece j) (capPatch j) ∞ where
  toEquiv := (EllipticGeometry.nativePatchBiholomorph j).toEquiv
  contMDiff_toFun := (CuspCircleNormalTrivialization.contMDiff_real_of_complex
    (EllipticGeometry.nativePatchBiholomorph j).contMDiff).of_le le_top
  contMDiff_invFun := (CuspCircleNormalTrivialization.contMDiff_real_of_complex
    (EllipticGeometry.nativePatchBiholomorph j).symm.contMDiff).of_le le_top

@[simp] theorem capPatchDiffeomorph_val (j : Kind) (y : SpecialEllipticPiece j) :
    (capPatchDiffeomorph j y).val = EllipticGeometry.inclusion j y := rfl

@[simp] theorem inclusion_capPatchDiffeomorph_symm (j : Kind) (x : capPatch j) :
    EllipticGeometry.inclusion j ((capPatchDiffeomorph j).symm x) = x.val :=
  congrArg Subtype.val ((capPatchDiffeomorph j).apply_symm_apply x)

theorem nativeLocalizedCollar_add (j : Kind) (τ s t : ℝ) (y : SpecialEllipticPiece j) :
    nativeLocalizedCollarDiffeomorph j τ (s + t) y =
      nativeLocalizedCollarDiffeomorph j τ s (nativeLocalizedCollarDiffeomorph j τ t y) :=
  localizedCollarTranslation_add j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) s t y

/-- The literal conjugation of the original cap map into its original global open patch. -/
def patchMap (j : Kind) (τ s : ℝ) (x : capPatch j) : capPatch j :=
  capPatchDiffeomorph j
    (nativeLocalizedCollarDiffeomorph j τ s ((capPatchDiffeomorph j).symm x))

@[simp] theorem patchMap_on_cap (j : Kind) (τ s : ℝ) (y : SpecialEllipticPiece j) :
    patchMap j τ s (capPatchDiffeomorph j y) =
      capPatchDiffeomorph j (nativeLocalizedCollarDiffeomorph j τ s y) := by
  rw [patchMap, Diffeomorph.symm_apply_apply]

@[simp] theorem patchMap_zero (j : Kind) (τ : ℝ) (x : capPatch j) :
    patchMap j τ 0 x = x := by
  rw [patchMap, nativeLocalizedCollar_zero, Diffeomorph.apply_symm_apply]

theorem patchMap_add (j : Kind) (τ s t : ℝ) (x : capPatch j) :
    patchMap j τ (s + t) x = patchMap j τ s (patchMap j τ t x) := by
  simp only [patchMap, Diffeomorph.symm_apply_apply, nativeLocalizedCollar_add]

private def patchTimeInverse (j : Kind) (p : ℝ × capPatch j) :
    ℝ × SpecialEllipticPiece j := (p.1, (capPatchDiffeomorph j).symm p.2)

private theorem patchTimeInverse_contMDiff (j : Kind) :
    ContMDiff IT IT ∞ (patchTimeInverse j) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk ((capPatchDiffeomorph j).symm.contMDiff.comp contMDiff_snd)

private theorem patchMap_eq_comp (j : Kind) (τ : ℝ) :
    (fun p : ℝ × capPatch j => patchMap j τ p.1 p.2) =
      (capPatchDiffeomorph j : SpecialEllipticPiece j → capPatch j) ∘
        ((fun p : ℝ × SpecialEllipticPiece j =>
          nativeLocalizedCollarDiffeomorph j τ p.1 p.2) ∘ patchTimeInverse j) := rfl

/-- Joint smoothness uses only the given real smooth maps in their native atlases. -/
theorem patchMap_joint_contMDiff (j : Kind) (τ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × capPatch j => patchMap j τ p.1 p.2) := by
  rw [patchMap_eq_comp]
  apply (capPatchDiffeomorph j).contMDiff.comp
  exact ContMDiff.comp (I := IT) (I' := IT) (I'' := IR)
    (nativeLocalizedCollar_joint_contMDiff j τ) (patchTimeInverse_contMDiff j)

theorem patchMap_projection (j : Kind) (τ s : ℝ) (x : capPatch j) :
    Threefold.projection (patchMap j τ s x).val = Threefold.projection x.val := by
  rw [patchMap, capPatchDiffeomorph_val, EllipticGeometry.projection_inclusion,
    nativeLocalizedCollar_projectionToBase]
  rw [← EllipticGeometry.projection_inclusion, inclusion_capPatchDiffeomorph_symm]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
