import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFourCircle

/-!
# Standard real rotations for the original period-one circle

The real four-dimensional rotation is evaluated at the manuscript's unchanged
normalized delta-circle parameter. The resulting continuous representation
intertwines the literal complex normal action with the standard real blocks.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour

open SpecialPeriods.Threefold.Homology
open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

local notation "Circle" => AddCircle (1 : ℝ)

/-- The actual delta-circle parameter acting in standard real four-space. -/
def circleRotation (t : Circle) : Space ≃ₗᵢ[ℝ] Space :=
  rotation (DeltaSweep.circleParameter t) (CircleOrbit.circleParameter_norm t)

theorem circleRotation_toFun (t : Circle) :
    (circleRotation t : Space → Space) =
      rotationMap (DeltaSweep.circleParameter t : ℂ) := rfl

/-- The original scalar circle action has exactly these real coordinates. -/
theorem coordinateEquiv_circleParameter_smul (t : Circle) (v : Fibre) :
    coordinateEquiv ((DeltaSweep.circleParameter t : ℂ) • v) =
      circleRotation t (coordinateEquiv v) :=
  coordinateEquiv_smul_rotation _ _ _

theorem coordinateEquiv_symm_circleRotation (t : Circle) (x : Space) :
    coordinateEquiv.symm (circleRotation t x) =
      (DeltaSweep.circleParameter t : ℂ) • coordinateEquiv.symm x :=
  coordinateEquiv_symm_rotation _ _ _

@[simp] theorem circleRotation_zero :
    circleRotation 0 = (1 : Space ≃ₗᵢ[ℝ] Space) := by
  apply LinearIsometryEquiv.ext
  intro x
  change rotationMap (DeltaSweep.circleParameter 0 : ℂ) x = x
  rw [DeltaSweep.circleParameter_zero, Units.val_one, rotationMap_one]

theorem circleRotation_add (s t : Circle) :
    circleRotation (s + t) = circleRotation s * circleRotation t := by
  apply LinearIsometryEquiv.ext
  intro x
  change rotationMap (DeltaSweep.circleParameter (s + t) : ℂ) x =
    rotationMap (DeltaSweep.circleParameter s : ℂ)
      (rotationMap (DeltaSweep.circleParameter t : ℂ) x)
  rw [DeltaSweep.circleParameter_add, Units.val_mul, rotationMap_mul]

@[simp] theorem circleRotation_neg (t : Circle) :
    circleRotation (-t) = (circleRotation t).symm := by
  have h : circleRotation (-t) * circleRotation t = 1 := by
    rw [← circleRotation_add, neg_add_cancel, circleRotation_zero]
  have hi : (circleRotation t).symm * circleRotation t = 1 :=
    inv_mul_cancel (circleRotation t)
  exact mul_right_cancel (h.trans hi.symm)

/-- The period-one circle gives an actual additive-to-multiplicative representation. -/
def circleRotationAddHom : Circle →+ Additive (Space ≃ₗᵢ[ℝ] Space) where
  toFun t := Additive.ofMul (circleRotation t)
  map_zero' := circleRotation_zero
  map_add' := circleRotation_add

@[simp] theorem circleRotationAddHom_apply (t : Circle) :
    circleRotationAddHom t = Additive.ofMul (circleRotation t) := rfl

/-- Continuity is joint in the original circle parameter and the actual vector. -/
theorem continuous_circleRotation :
    Continuous (fun p : Circle × Space => circleRotation p.1 p.2) := by
  change Continuous (fun p : Circle × Space =>
    rotationMap (DeltaSweep.circleParameter p.1 : ℂ) p.2)
  exact continuous_rotationMap.comp
    (((Units.continuous_val.comp DeltaSweep.circleParameter_continuous).comp
      continuous_fst).prodMk continuous_snd)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour
