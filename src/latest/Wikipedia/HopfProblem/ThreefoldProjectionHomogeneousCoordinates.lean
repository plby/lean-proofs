import Wikipedia.HopfProblem.ThreefoldLineBundleTrivialization
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBasePullback

/-!
# Continuous homogeneous coordinates for the original threefold projection

The two sections of the original pulled-back positive point line vanish
over zero and one respectively. The proved continuous trivialization of
that same native bundle turns them into actual continuous complex-valued
functions with no common zero. This file does not yet take their cubic
and quartic roots.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy

open Canonical.PowersBase
open CanonicalGlobal.BaseTwist
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Local coefficients of the section of `O(1)` vanishing at zero. -/
def zeroCoefficient : Bool → RiemannSphere → ℂ
  | false, p => finiteCoordinate p
  | true, _ => 1

theorem zeroCoefficient_compatible :
    Canonical.PowersBase.data.IsCompatible zeroCoefficient := by
  intro a b p hp
  cases a <;> cases b
  · change (↑((CanonicalGlobal.BaseTwist.data.transition false false p)⁻¹) : ℂ) *
      zeroCoefficient false p = zeroCoefficient false p
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      transition_self, inv_one, Units.val_one, one_mul]
  · rw [Canonical.PowersBase.transition_false_true hp]
    exact infinityCoordinate_mul_finiteCoordinate hp
  · rw [Canonical.PowersBase.transition_true_false ⟨hp.2, hp.1⟩]
    exact mul_one _
  · change (↑((CanonicalGlobal.BaseTwist.data.transition true true p)⁻¹) : ℂ) * 1 = 1
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      transition_self, inv_one, Units.val_one, one_mul]

theorem zeroCoefficient_holomorphic (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (zeroCoefficient b)
      (Canonical.PowersBase.data.baseSet b) := by
  cases b
  · exact finiteCoordinate_holomorphicOn
  · exact contMDiffOn_const

def zeroPullbackCoefficient (b : Bool) (x : Space) : ℂ :=
  zeroCoefficient b (projectionSphere x)

theorem zeroPullbackCoefficient_compatible :
    pullbackData.IsCompatible zeroPullbackCoefficient :=
  fun a b x hx => zeroCoefficient_compatible a b (projectionSphere x) hx

theorem zeroPullbackCoefficient_holomorphic (b : Bool) :
    ContMDiffOn IF 𝓘(ℂ) ω (zeroPullbackCoefficient b) (pullbackData.baseSet b) :=
  (zeroCoefficient_holomorphic b).comp projectionSphere_holomorphic.contMDiffOn
    (fun _ hx => hx)

/-- The genuine section of the native pulled-back line vanishing over zero. -/
def zeroSection (x : Space) : pullbackBundle.Fiber x :=
  pullbackData.sectionFromLocal zeroPullbackCoefficient x

theorem zeroSection_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω
      (fun x => (⟨x, zeroSection x⟩ : pullbackBundle.TotalSpace)) :=
  pullbackData.sectionFromLocal_holomorphic IF zeroPullbackCoefficient
    zeroPullbackCoefficient_compatible zeroPullbackCoefficient_holomorphic

theorem zeroSection_eq_zero_iff (x : Space) :
    zeroSection x = 0 ↔ projectionSphere x = ((0 : ℂ) : RiemannSphere) := by
  change zeroCoefficient (CanonicalGlobal.BaseTwist.indexAt (projectionSphere x))
    (projectionSphere x) = 0 ↔ _
  generalize projectionSphere x = p
  induction p using OnePoint.rec with
  | infty => simp [CanonicalGlobal.BaseTwist.indexAt, zeroCoefficient]
  | coe z => simp [CanonicalGlobal.BaseTwist.indexAt, zeroCoefficient]

attribute [local instance] pullbackBundle_holomorphic

/-- This trivializes the original bundle; its total-space topology is unchanged. -/
def pointLineTrivialization : HolomorphicPicard.ContinuousTrivialization pullbackBundle.Fiber :=
  LineBundleTrivialization.continuousTrivialization pullbackBundle.Fiber

/-- First homogeneous coordinate, with zero locus the order-three fibre. -/
def zeroCoordinate (x : Space) : ℂ :=
  pointLineTrivialization.fiberEquiv x (zeroSection x)

/-- Second homogeneous coordinate, with zero locus the order-four fibre. -/
def oneCoordinate (x : Space) : ℂ :=
  pointLineTrivialization.fiberEquiv x (pullbackSection x)

theorem zeroCoordinate_continuous : Continuous zeroCoordinate := by
  unfold zeroCoordinate
  have h := (pointLineTrivialization.homeomorph.continuous.comp
    zeroSection_holomorphic.continuous).snd
  simpa only [Function.comp_def, HolomorphicPicard.ContinuousTrivialization.map_fiber] using h

theorem oneCoordinate_continuous : Continuous oneCoordinate := by
  unfold oneCoordinate
  have h := (pointLineTrivialization.homeomorph.continuous.comp
    pullbackSectionMap_holomorphic.continuous).snd
  simpa only [Function.comp_def, pullbackSectionMap,
    HolomorphicPicard.ContinuousTrivialization.map_fiber] using h

@[simp] theorem zeroCoordinate_eq_zero_iff (x : Space) :
    zeroCoordinate x = 0 ↔ projectionSphere x = ((0 : ℂ) : RiemannSphere) := by
  rw [zeroCoordinate, LinearEquiv.map_eq_zero_iff, zeroSection_eq_zero_iff]

@[simp] theorem oneCoordinate_eq_zero_iff (x : Space) :
    oneCoordinate x = 0 ↔ projectionSphere x = ((1 : ℂ) : RiemannSphere) := by
  rw [oneCoordinate, LinearEquiv.map_eq_zero_iff, pullbackSection_eq_zero_iff]

theorem coordinates_no_common_zero (x : Space) :
    zeroCoordinate x ≠ 0 ∨ oneCoordinate x ≠ 0 := by
  by_cases h : zeroCoordinate x = 0
  · right
    intro h'
    have he := (zeroCoordinate_eq_zero_iff x).mp h
    have he' := (oneCoordinate_eq_zero_iff x).mp h'
    exact zero_ne_one (OnePoint.coe_injective (he.symm.trans he'))
  · exact Or.inl h

theorem coordinates_pair_ne_zero (x : Space) :
    (zeroCoordinate x, oneCoordinate x) ≠ (0 : ℂ × ℂ) := by
  intro h
  rcases coordinates_no_common_zero x with h0 | h1
  · exact h0 (congrArg Prod.fst h)
  · exact h1 (congrArg Prod.snd h)

/-- An actual map to the punctured complex plane pair, not only a cohomology class. -/
def homogeneousLift : C(Space, {z : ℂ × ℂ // z ≠ 0}) where
  toFun x := ⟨(zeroCoordinate x, oneCoordinate x), coordinates_pair_ne_zero x⟩
  continuous_toFun := (zeroCoordinate_continuous.prodMk oneCoordinate_continuous).subtype_mk
    coordinates_pair_ne_zero

/-- The scalar of the chosen fibrewise linear trivialization in its selected chart.
No continuity across changes of the selected chart is asserted for this scalar. -/
def selectedFiberEquiv (x : Space) : ℂ ≃ₗ[ℂ] ℂ :=
  pointLineTrivialization.fiberEquiv x

def coordinateScale (x : Space) : ℂ := selectedFiberEquiv x 1

theorem coordinateScale_ne_zero (x : Space) : coordinateScale x ≠ 0 := by
  exact (selectedFiberEquiv x).map_eq_zero_iff.not.mpr one_ne_zero

theorem fiberCoordinate_eq_mul (x : Space) (z : ℂ) :
    selectedFiberEquiv x z = z * coordinateScale x := by
  have h := (selectedFiberEquiv x).map_smul z (1 : ℂ)
  simpa only [smul_eq_mul, mul_one, coordinateScale] using h

theorem zeroCoordinate_of_finite (x : Space) (z : ℂ)
    (hx : projectionSphere x = (z : RiemannSphere)) :
    zeroCoordinate x = z * coordinateScale x := by
  change selectedFiberEquiv x
    (zeroCoefficient (CanonicalGlobal.BaseTwist.indexAt (projectionSphere x))
      (projectionSphere x)) = _
  rw [fiberCoordinate_eq_mul]
  congr 1
  simp [hx, CanonicalGlobal.BaseTwist.indexAt, zeroCoefficient]

theorem oneCoordinate_of_finite (x : Space) (z : ℂ)
    (hx : projectionSphere x = (z : RiemannSphere)) :
    oneCoordinate x = (z - 1) * coordinateScale x := by
  change selectedFiberEquiv x
    (pointCoefficient (CanonicalGlobal.BaseTwist.indexAt (projectionSphere x))
      (projectionSphere x)) = _
  rw [fiberCoordinate_eq_mul]
  congr 1
  simp [hx, CanonicalGlobal.BaseTwist.indexAt, pointCoefficient]

theorem coordinates_of_infty (x : Space) (hx : projectionSphere x = (∞ : RiemannSphere)) :
    zeroCoordinate x = coordinateScale x ∧ oneCoordinate x = coordinateScale x := by
  have hs0 : (show ℂ from zeroSection x) = 1 := by
    change zeroCoefficient (CanonicalGlobal.BaseTwist.indexAt (projectionSphere x))
      (projectionSphere x) = 1
    simp [hx, CanonicalGlobal.BaseTwist.indexAt, zeroCoefficient]
  have hs1 : (show ℂ from pullbackSection x) = 1 := by
    change pointCoefficient (CanonicalGlobal.BaseTwist.indexAt (projectionSphere x))
      (projectionSphere x) = 1
    simp [hx, CanonicalGlobal.BaseTwist.indexAt, pointCoefficient]
  exact ⟨congrArg (selectedFiberEquiv x) hs0,
    congrArg (selectedFiberEquiv x) hs1⟩

theorem coordinate_difference_eq_zero_iff (x : Space) :
    zeroCoordinate x - oneCoordinate x = 0 ↔ projectionSphere x = (∞ : RiemannSphere) := by
  generalize hp : projectionSphere x = p
  induction p using OnePoint.rec with
  | infty =>
      obtain ⟨h0, h1⟩ := coordinates_of_infty x hp
      simp [h0, h1]
  | coe z =>
      rw [zeroCoordinate_of_finite x z hp, oneCoordinate_of_finite x z hp]
      have h : z * coordinateScale x - (z - 1) * coordinateScale x = coordinateScale x := by
        ring
      simp [h, coordinateScale_ne_zero]

/-- The original projection is recovered exactly, including its infinity fibre. -/
theorem projectionSphere_reconstruction (x : Space) :
    projectionSphere x =
      if zeroCoordinate x - oneCoordinate x = 0 then (∞ : RiemannSphere)
      else ((zeroCoordinate x / (zeroCoordinate x - oneCoordinate x) : ℂ) : RiemannSphere) := by
  classical
  generalize hp : projectionSphere x = p
  induction p using OnePoint.rec with
  | infty =>
      rw [if_pos ((coordinate_difference_eq_zero_iff x).mpr hp)]
  | coe z =>
      rw [zeroCoordinate_of_finite x z hp, oneCoordinate_of_finite x z hp]
      have h : z * coordinateScale x - (z - 1) * coordinateScale x = coordinateScale x := by
        ring
      rw [h, if_neg (coordinateScale_ne_zero x), mul_div_cancel_right₀ _ (coordinateScale_ne_zero x)]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy
