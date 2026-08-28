import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeExtensionSmooth
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugePatch
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeSupport

/-!
# The actual global supported elliptic gauge diffeomorphisms

The literal extension is the original cap map on its actual open image
and the identity elsewhere.  The proved closed support lies strictly
inside that image, so the generic local smoothness proof applies with
all geometric hypotheses discharged.  The global atlas is the original
one; only the scalar field of differentiation is real.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace
  globalTimeChartedSpace patchTimeChartedSpace

theorem patchMap_eq_self_of_not_mem_support (j : Kind) (τ s : ℝ) (x : capPatch j)
    (hx : x.val ∉ ellipticSupport j) : patchMap j τ s x = x := by
  have hy : EllipticGeometry.inclusion j ((capPatchDiffeomorph j).symm x) ∉
      ellipticSupport j := by rwa [inclusion_capPatchDiffeomorph_symm]
  rw [patchMap, nativeLocalizedCollar_eq_self_of_not_mem_support j τ s _ hy,
    Diffeomorph.apply_symm_apply]

private theorem patchMap_joint_prod (j : Kind) (τ : ℝ) :
    ContMDiff ((modelWithCornersSelf ℝ ℝ).prod IR) IR ∞
      (fun p : ℝ × capPatch j => patchMap j τ p.1 p.2) := by
  simpa only [modelWithCornersSelf_prod] using patchMap_joint_contMDiff j τ

/-- The original cap map extended by the identity on the original global space. -/
def globalMap (j : Kind) (τ s : ℝ) : Threefold.Space → Threefold.Space :=
  Extension.extend (capPatch j) (patchMap j τ s)

@[simp] theorem globalMap_inclusion (j : Kind) (τ s : ℝ) (y : SpecialEllipticPiece j) :
    globalMap j τ s (EllipticGeometry.inclusion j y) =
      EllipticGeometry.inclusion j (nativeLocalizedCollarDiffeomorph j τ s y) := by
  change Extension.extend (capPatch j) (patchMap j τ s) (capPatchDiffeomorph j y).val = _
  rw [Extension.extend_coe, patchMap_on_cap, capPatchDiffeomorph_val]

theorem globalMap_eq_self_of_not_mem_patch (j : Kind) (τ s : ℝ) {x : Threefold.Space}
    (hx : x ∉ capPatch j) : globalMap j τ s x = x :=
  Extension.extend_of_notMem (capPatch j) (patchMap j τ s) hx

/-- One actual closed support works for every phase and every real time. -/
theorem globalMap_eq_self_of_not_mem_support (j : Kind) (τ s : ℝ)
    {x : Threefold.Space} (hx : x ∉ ellipticSupport j) : globalMap j τ s x = x :=
  Extension.extend_eq_self_of_notMem (capPatch j) (patchMap j τ s)
    (patchMap_eq_self_of_not_mem_support j τ s) hx

@[simp] theorem globalMap_mem_patch_iff (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    globalMap j τ s x ∈ capPatch j ↔ x ∈ capPatch j :=
  Extension.extend_mem_iff (capPatch j) (patchMap j τ s) x

@[simp] theorem globalMap_zero (j : Kind) (τ : ℝ) (x : Threefold.Space) :
    globalMap j τ 0 x = x :=
  Extension.extend_family_zero (capPatch j) (patchMap j τ) (patchMap_zero j τ) x

theorem globalMap_add (j : Kind) (τ s t : ℝ) (x : Threefold.Space) :
    globalMap j τ (s + t) x = globalMap j τ s (globalMap j τ t x) :=
  Extension.extend_family_add (capPatch j) (patchMap j τ) (patchMap_add j τ) s t x

/-- Joint real smoothness in the unchanged global and ordinary product atlases. -/
theorem globalMap_joint_contMDiff (j : Kind) (τ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × Threefold.Space => globalMap j τ p.1 p.2) := by
  simpa only [modelWithCornersSelf_prod, globalMap] using
    Extension.extend_joint_contMDiff IR (capPatch j) (patchMap j τ)
      (patchMap_joint_prod j τ) (ellipticSupport j) (ellipticSupport_isClosed j)
      (ellipticSupport_subset_patch j) (patchMap_eq_self_of_not_mem_support j τ)

theorem globalMap_contMDiff (j : Kind) (τ s : ℝ) :
    ContMDiff IR IR ∞ (globalMap j τ s) :=
  Extension.extend_contMDiff IR (capPatch j) (patchMap j τ)
    (patchMap_joint_prod j τ) (ellipticSupport j) (ellipticSupport_isClosed j)
    (ellipticSupport_subset_patch j) (patchMap_eq_self_of_not_mem_support j τ) s

/-- The original global threefold carries the resulting actual real smooth diffeomorphism. -/
def globalDiffeomorph (j : Kind) (τ s : ℝ) :
    Diffeomorph IR IR Threefold.Space Threefold.Space ∞ :=
  Extension.extendDiffeomorph IR (capPatch j) (patchMap j τ)
    (patchMap_zero j τ) (patchMap_add j τ) (patchMap_joint_prod j τ)
    (ellipticSupport j) (ellipticSupport_isClosed j) (ellipticSupport_subset_patch j)
    (patchMap_eq_self_of_not_mem_support j τ) s

@[simp] theorem globalDiffeomorph_apply (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    globalDiffeomorph j τ s x = globalMap j τ s x := rfl

/-- The inverse is precisely the same supported global construction at negative time. -/
@[simp] theorem globalDiffeomorph_symm_apply (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    (globalDiffeomorph j τ s).symm x = globalDiffeomorph j τ (-s) x := rfl

@[simp] theorem globalDiffeomorph_inclusion (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j) :
    globalDiffeomorph j τ s (EllipticGeometry.inclusion j y) =
      EllipticGeometry.inclusion j (nativeLocalizedCollarDiffeomorph j τ s y) :=
  globalMap_inclusion j τ s y

@[simp] theorem globalMap_projection (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    Threefold.projection (globalMap j τ s x) = Threefold.projection x :=
  Extension.extend_preserves (capPatch j) Threefold.projection (patchMap j τ s)
    (patchMap_projection j τ s) x

@[simp] theorem globalMap_projectionSphere (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    Threefold.projectionSphere (globalMap j τ s x) = Threefold.projectionSphere x := by
  simp only [Threefold.projectionSphere, Function.comp_def, globalMap_projection]

theorem globalMap_mem_support_iff (j : Kind) (τ s : ℝ) (x : Threefold.Space) :
    globalMap j τ s x ∈ ellipticSupport j ↔ x ∈ ellipticSupport j := by
  change Threefold.projection (globalMap j τ s x) ∈ ellipticBaseSupport j ↔ _
  rw [globalMap_projection]
  rfl

/-- Outside the closed support, a single original neighborhood is fixed at all times and phases. -/
theorem globalMap_eventually_identity (j : Kind) {x : Threefold.Space}
    (hx : x ∉ ellipticSupport j) :
    ∀ᶠ y in 𝓝 x, ∀ τ s : ℝ, globalMap j τ s y = y := by
  filter_upwards [ellipticSupport_compl_mem_nhds j hx] with y hy τ s
  exact globalMap_eq_self_of_not_mem_support j τ s hy

private theorem globalMap_unit_continuous (j : Kind) (τ : ℝ) :
    Continuous (fun p : unitInterval × Threefold.Space => globalMap j τ (p.1 : ℝ) p.2) := by
  have hi : Continuous (fun p : unitInterval × Threefold.Space => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ℝ × Threefold.Space => globalMap j τ p.1 p.2) ∘
    (fun p : unitInterval × Threefold.Space => ((p.1 : ℝ), p.2)))
  exact (globalMap_joint_contMDiff j τ).continuous.comp hi

/-- A genuine global isotopy with jointly smooth real-time extension
and explicit smooth inverses. -/
def globalIsotopy (j : Kind) (τ : ℝ) :
    (ContinuousMap.id Threefold.Space).Homotopy
      ((globalDiffeomorph j τ 1).toHomeomorph : C(_, _)) where
  toFun p := globalMap j τ p.1 p.2
  continuous_toFun := globalMap_unit_continuous j τ
  map_zero_left x := globalMap_zero j τ x
  map_one_left _ := rfl

@[simp] theorem globalIsotopy_apply (j : Kind) (τ : ℝ)
    (s : unitInterval) (x : Threefold.Space) :
    globalIsotopy j τ (s, x) = globalDiffeomorph j τ s x := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
