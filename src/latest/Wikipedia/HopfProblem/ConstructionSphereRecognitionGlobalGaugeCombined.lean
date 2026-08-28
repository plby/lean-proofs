import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeCombinedCommutation
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeFlow

/-!
# Simultaneous native elliptic gauge isotopy on the actual global threefold

The two supported original cap diffeomorphisms commute.  Their direct
composition is therefore an additive real-time family with inverse at
negative time, jointly smooth in the unchanged original global atlas.
It restricts to precisely the native collar map on each original cap,
fixes the whole original cusp piece, and preserves the actual projection
and every parameter of the original global complex vertical flow.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace
  globalTimeChartedSpace

/-- Apply the original fourth-order cap map, followed by the original third-order cap map. -/
def combinedDiffeomorph (τ₃ τ₄ s : ℝ) :
    Diffeomorph IR IR Threefold.Space Threefold.Space ∞ :=
  (globalDiffeomorph .four τ₄ s).trans (globalDiffeomorph .three τ₃ s)

@[simp] theorem combinedDiffeomorph_apply (τ₃ τ₄ s : ℝ) (x : Threefold.Space) :
    combinedDiffeomorph τ₃ τ₄ s x = globalMap .three τ₃ s (globalMap .four τ₄ s x) := rfl

/-- The third-order cap sees exactly its original native map,
with no contribution from the other cap. -/
@[simp] theorem combinedDiffeomorph_inclusion_three (τ₃ τ₄ s : ℝ)
    (y : SpecialEllipticPiece .three) :
    combinedDiffeomorph τ₃ τ₄ s (EllipticGeometry.inclusion .three y) =
      EllipticGeometry.inclusion .three (nativeLocalizedCollarDiffeomorph .three τ₃ s y) := by
  rw [combinedDiffeomorph_apply,
    globalMap_other_inclusion .four .three (by decide), globalMap_inclusion]

/-- The fourth-order cap likewise retains its exact original point formula. -/
@[simp] theorem combinedDiffeomorph_inclusion_four (τ₃ τ₄ s : ℝ)
    (y : SpecialEllipticPiece .four) :
    combinedDiffeomorph τ₃ τ₄ s (EllipticGeometry.inclusion .four y) =
      EllipticGeometry.inclusion .four (nativeLocalizedCollarDiffeomorph .four τ₄ s y) := by
  rw [combinedDiffeomorph_apply, globalMap_inclusion,
    globalMap_other_inclusion .three .four (by decide)]

/-- Every point of the whole original cusp piece is fixed. -/
@[simp] theorem combinedDiffeomorph_cusp (τ₃ τ₄ s : ℝ) (y : CuspGeometry.LocalSpace) :
    combinedDiffeomorph τ₃ τ₄ s (CuspGeometry.inclusion y) = CuspGeometry.inclusion y := by
  rw [combinedDiffeomorph_apply, globalMap_cusp, globalMap_cusp]

@[simp] theorem combinedDiffeomorph_projection (τ₃ τ₄ s : ℝ) (x : Threefold.Space) :
    Threefold.projection (combinedDiffeomorph τ₃ τ₄ s x) = Threefold.projection x := by
  rw [combinedDiffeomorph_apply, globalMap_projection, globalMap_projection]

@[simp] theorem combinedDiffeomorph_projectionSphere (τ₃ τ₄ s : ℝ)
    (x : Threefold.Space) :
    Threefold.projectionSphere (combinedDiffeomorph τ₃ τ₄ s x) =
      Threefold.projectionSphere x := by
  rw [combinedDiffeomorph_apply, globalMap_projectionSphere, globalMap_projectionSphere]

/-- Outside the two actual closed supports, the combined map is literally the identity. -/
theorem combinedDiffeomorph_eq_self_of_not_mem_support (τ₃ τ₄ s : ℝ)
    {x : Threefold.Space} (hx : x ∉ ellipticSupport .three ∪ ellipticSupport .four) :
    combinedDiffeomorph τ₃ τ₄ s x = x := by
  rw [combinedDiffeomorph_apply,
    globalMap_eq_self_of_not_mem_support .four τ₄ s (fun h => hx (Or.inr h)),
    globalMap_eq_self_of_not_mem_support .three τ₃ s (fun h => hx (Or.inl h))]

@[simp] theorem combinedDiffeomorph_zero (τ₃ τ₄ : ℝ) (x : Threefold.Space) :
    combinedDiffeomorph τ₃ τ₄ 0 x = x := by
  rw [combinedDiffeomorph_apply, globalMap_zero, globalMap_zero]

/-- Commuting original cap actions give an additive action of the same real time parameter. -/
theorem combinedDiffeomorph_add (τ₃ τ₄ s t : ℝ) (x : Threefold.Space) :
    combinedDiffeomorph τ₃ τ₄ (s + t) x =
      combinedDiffeomorph τ₃ τ₄ s (combinedDiffeomorph τ₃ τ₄ t x) := by
  simp only [combinedDiffeomorph_apply, globalMap_add]
  rw [globalMap_commute_apply .three .four (by decide) τ₃ τ₄ t s]

/-- The inverse is exactly the same simultaneous native construction at negative time. -/
@[simp] theorem combinedDiffeomorph_symm_apply (τ₃ τ₄ s : ℝ) (x : Threefold.Space) :
    (combinedDiffeomorph τ₃ τ₄ s).symm x = combinedDiffeomorph τ₃ τ₄ (-s) x := by
  change globalMap .four τ₄ (-s) (globalMap .three τ₃ (-s) x) =
    globalMap .three τ₃ (-s) (globalMap .four τ₄ (-s) x)
  exact globalMap_commute_apply .four .three (by decide) τ₄ τ₃ (-s) (-s) x

private theorem combinedTimeFourth_contMDiff (τ₄ : ℝ) :
    ContMDiff IT IT ∞ (fun p : ℝ × Threefold.Space =>
      (p.1, globalMap .four τ₄ p.1 p.2)) := by
  have ht : ContMDiff IT 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × Threefold.Space => p.1) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hp := ht.prodMk (globalMap_joint_contMDiff .four τ₄)
  rw [← modelWithCornersSelf_prod] at hp
  exact hp

/-- Joint real-time smoothness uses the original global atlas and its ordinary product atlas. -/
theorem combinedDiffeomorph_joint_contMDiff (τ₃ τ₄ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × Threefold.Space =>
      combinedDiffeomorph τ₃ τ₄ p.1 p.2) :=
  ((globalMap_joint_contMDiff .three τ₃).comp (combinedTimeFourth_contMDiff τ₄)).congr
    (fun p => combinedDiffeomorph_apply τ₃ τ₄ p.1 p.2)

theorem combinedDiffeomorph_joint_continuous (τ₃ τ₄ : ℝ) :
    Continuous (fun p : ℝ × Threefold.Space => combinedDiffeomorph τ₃ τ₄ p.1 p.2) :=
  (combinedDiffeomorph_joint_contMDiff τ₃ τ₄).continuous

private theorem combinedNegTime_contMDiff :
    ContMDiff IT IT ∞ (fun p : ℝ × Threefold.Space => (-p.1, p.2)) := by
  have ht : ContMDiff IT 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × Threefold.Space => p.1) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hx : ContMDiff IT IR ∞ (fun p : ℝ × Threefold.Space => p.2) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hn : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => -s) :=
    (contDiff_neg : ContDiff ℝ ∞ (fun s : ℝ => -s)).contMDiff
  have hp := (hn.comp ht).prodMk hx
  rw [← modelWithCornersSelf_prod] at hp
  exact hp

/-- The literal negative-time inverse is jointly smooth in the same original atlases. -/
theorem combinedDiffeomorph_symm_joint_contMDiff (τ₃ τ₄ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × Threefold.Space =>
      (combinedDiffeomorph τ₃ τ₄ p.1).symm p.2) :=
  ((combinedDiffeomorph_joint_contMDiff τ₃ τ₄).comp combinedNegTime_contMDiff).congr
    (fun p => combinedDiffeomorph_symm_apply τ₃ τ₄ p.1 p.2)

/-- Every original complex vertical-flow parameter commutes with the simultaneous map. -/
theorem combinedDiffeomorph_flow (τ₃ τ₄ s : ℝ) (u : ℂ) (x : Threefold.Space) :
    combinedDiffeomorph τ₃ τ₄ s (VerticalAction.flow u x) =
      VerticalAction.flow u (combinedDiffeomorph τ₃ τ₄ s x) := by
  simp only [combinedDiffeomorph_apply, globalMap_flow]

theorem combinedDiffeomorph_commute_flow (τ₃ τ₄ s : ℝ) (u : ℂ) :
    Function.Commute (combinedDiffeomorph τ₃ τ₄ s) (VerticalAction.flow u) :=
  combinedDiffeomorph_flow τ₃ τ₄ s u

theorem combinedDiffeomorph_symm_flow (τ₃ τ₄ s : ℝ) (u : ℂ) (x : Threefold.Space) :
    (combinedDiffeomorph τ₃ τ₄ s).symm (VerticalAction.flow u x) =
      VerticalAction.flow u ((combinedDiffeomorph τ₃ τ₄ s).symm x) := by
  simp only [combinedDiffeomorph_symm_apply]
  exact combinedDiffeomorph_flow τ₃ τ₄ (-s) u x

private theorem combinedDiffeomorph_unit_continuous (τ₃ τ₄ : ℝ) :
    Continuous (fun p : unitInterval × Threefold.Space =>
      combinedDiffeomorph τ₃ τ₄ (p.1 : ℝ) p.2) := by
  have hi : Continuous (fun p : unitInterval × Threefold.Space => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ℝ × Threefold.Space =>
    combinedDiffeomorph τ₃ τ₄ p.1 p.2) ∘
      (fun p : unitInterval × Threefold.Space => ((p.1 : ℝ), p.2)))
  exact (combinedDiffeomorph_joint_continuous τ₃ τ₄).comp hi

/-- A genuine simultaneous global isotopy with jointly smooth real-time extension. -/
def combinedIsotopy (τ₃ τ₄ : ℝ) :
    (ContinuousMap.id Threefold.Space).Homotopy
      ((combinedDiffeomorph τ₃ τ₄ 1).toHomeomorph : C(_, _)) where
  toFun p := combinedDiffeomorph τ₃ τ₄ p.1 p.2
  continuous_toFun := combinedDiffeomorph_unit_continuous τ₃ τ₄
  map_zero_left x := combinedDiffeomorph_zero τ₃ τ₄ x
  map_one_left _ := rfl

@[simp] theorem combinedIsotopy_apply (τ₃ τ₄ : ℝ) (s : unitInterval)
    (x : Threefold.Space) :
    combinedIsotopy τ₃ τ₄ (s, x) = combinedDiffeomorph τ₃ τ₄ s x := rfl

/-- On each original cap, the global isotopy retains the native local isotopy pointwise. -/
theorem combinedIsotopy_inclusion_three (τ₃ τ₄ : ℝ) (s : unitInterval)
    (y : SpecialEllipticPiece .three) :
    combinedIsotopy τ₃ τ₄ (s, EllipticGeometry.inclusion .three y) =
      EllipticGeometry.inclusion .three (nativeLocalizedCollarIsotopy .three τ₃ (s, y)) :=
  combinedDiffeomorph_inclusion_three τ₃ τ₄ (s : ℝ) y

theorem combinedIsotopy_inclusion_four (τ₃ τ₄ : ℝ) (s : unitInterval)
    (y : SpecialEllipticPiece .four) :
    combinedIsotopy τ₃ τ₄ (s, EllipticGeometry.inclusion .four y) =
      EllipticGeometry.inclusion .four (nativeLocalizedCollarIsotopy .four τ₄ (s, y)) :=
  combinedDiffeomorph_inclusion_four τ₃ τ₄ (s : ℝ) y

@[simp] theorem combinedIsotopy_cusp (τ₃ τ₄ : ℝ) (s : unitInterval)
    (y : CuspGeometry.LocalSpace) :
    combinedIsotopy τ₃ τ₄ (s, CuspGeometry.inclusion y) = CuspGeometry.inclusion y :=
  combinedDiffeomorph_cusp τ₃ τ₄ (s : ℝ) y

theorem combinedIsotopy_projection (τ₃ τ₄ : ℝ) (s : unitInterval)
    (x : Threefold.Space) :
    Threefold.projection (combinedIsotopy τ₃ τ₄ (s, x)) = Threefold.projection x :=
  combinedDiffeomorph_projection τ₃ τ₄ (s : ℝ) x

theorem combinedIsotopy_flow (τ₃ τ₄ : ℝ) (s : unitInterval) (u : ℂ)
    (x : Threefold.Space) :
    combinedIsotopy τ₃ τ₄ (s, VerticalAction.flow u x) =
      VerticalAction.flow u (combinedIsotopy τ₃ τ₄ (s, x)) :=
  combinedDiffeomorph_flow τ₃ τ₄ (s : ℝ) u x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
