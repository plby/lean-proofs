import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeCylinder
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupPath
import Wikipedia.HopfProblem.EllipticFundamentalGroupAffine

/-!
# The exact real lift of the original elliptic logarithmic gauge

The actual normalized logarithm along the real boundary cylinder gives a
continuous real four-dimensional translation lift.  Period covariance
proves its recurrence as an equality of real vectors, without passing to
the lattice quotient.  This exact recurrence is the prerequisite for an
equivariant straight-line homotopy to the linear translation.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic Elliptic.LogGauge SpecialPeriods SpecialPeriods.EllipticFilling
open SpecialPeriods.Threefold.EllipticGeometry CuspUniformization

/-- Positive logarithmic period translation in the actual real period coordinates. -/
def positiveLogFlat {j : Kind} (D : Equivariant.Data j) (v : Lattice)
    (z : Disc) (s : ℂ) : RealCoordinates :=
  (D.periods.periodEquiv z).symm (s • periodVector D.periods v z)

theorem positiveLogFlat_continuous {j : Kind} (D : Equivariant.Data j) (v : Lattice) :
    Continuous (fun p : Disc × ℂ => positiveLogFlat D v p.1 p.2) := by
  change Continuous ((fun q : Disc × ComplexPlane₂ => (D.periods.periodEquiv q.1).symm q.2) ∘
    (fun p : Disc × ℂ => (p.1, p.2 • periodVector D.periods v p.1)))
  apply D.periods.continuous_periodEquiv_symm.comp
  exact continuous_fst.prodMk (continuous_snd.smul
    ((periodVector_holomorphic D.periods v).continuous.comp continuous_fst))

/-- The jointly continuous real logarithmic translation before specializing its base curve. -/
def positiveLogFlatMap {j : Kind} (D : Equivariant.Data j) (v : Lattice) :
    C(Disc × ℂ, RealCoordinates) :=
  ⟨fun p => positiveLogFlat D v p.1 p.2, positiveLogFlat_continuous D v⟩

/-- Exact period covariance gives the real rotation formula, with no integral error term. -/
theorem positiveLogFlat_rotation {j : Kind} (D : Equivariant.Data j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (z : Disc) (s : ℂ) :
    positiveLogFlat D v (familyRotation j z) (s - 1 / (j.order : ℂ)) =
      flatLinear j (positiveLogFlat D v z s) - (1 / (j.order : ℝ)) • realCast v := by
  apply (D.periods.periodEquiv (familyRotation j z)).injective
  simp only [positiveLogFlat, LinearEquiv.apply_symm_apply, map_sub,
    D.periodEquiv_flatLinear, complexLift_translation, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  exact sub_smul _ _ _

/-- Any genuine normalized logarithm gives exactly the original quotient gauge coordinate. -/
theorem sectionCoordinate_eq_positiveLogFlat {j : Kind} (D : Equivariant.Data j)
    (v : Lattice) (z : Disc) (hz : (z : ℂ) ≠ 0) (s : ℂ)
    (hs : exponential s = (z : ℂ)) :
    sectionCoordinate D.periods v z = standardLattice.mkQ (positiveLogFlat D v z s) := by
  have h := sectionMap_formula_of_exponential D.periods v ⟨z, hz⟩ s hs
  have h' := congrArg Prod.snd h
  change 0 + sectionCoordinate D.periods v z =
    standardLattice.mkQ (positiveLogFlat D v z s) at h'
  exact (zero_add _).symm.trans h'

/-- The original continuous positive logarithm, including the native initial point and phase. -/
def nativeLogParameter (j : Kind) (τ : ℝ) : C(ℝ, ℂ) where
  toFun t := nativeClockwiseParameter j (-(t + τ))
  continuous_toFun := by unfold nativeClockwiseParameter; fun_prop

/-- The unchanged original positive root curve at that same phase. -/
def nativeLogRoot (j : Kind) (τ : ℝ) : C(ℝ, Disc) :=
  (nativeClockwiseRoot j).comp ⟨fun t => -(t + τ), (continuous_id.add continuous_const).neg⟩

@[simp] theorem nativeLogParameter_apply (j : Kind) (τ t : ℝ) :
    nativeLogParameter j τ t = nativeClockwiseParameter j (-(t + τ)) := rfl

@[simp] theorem nativeLogRoot_apply (j : Kind) (τ t : ℝ) :
    nativeLogRoot j τ t = nativeClockwiseRoot j (-(t + τ)) := rfl

theorem nativeLogRoot_ne_zero (j : Kind) (τ t : ℝ) :
    (nativeLogRoot j τ t : ℂ) ≠ 0 := nativeClockwiseRoot_ne_zero j _

theorem nativeLogRoot_exponential (j : Kind) (τ t : ℝ) :
    exponential (nativeLogParameter j τ t) = (nativeLogRoot j τ t : ℂ) := rfl

/-- Increasing positive boundary time reverses the original clockwise root rotation. -/
theorem nativeLogRoot_rotation (j : Kind) (τ t : ℝ) :
    familyRotation j (nativeLogRoot j τ (t + 1)) = nativeLogRoot j τ t := by
  have h := nativeClockwiseRoot_add_one j (-(t + 1 + τ))
  rw [show -(t + 1 + τ) + 1 = -(t + τ) by ring] at h
  exact h.symm

/-- The chosen real-cylinder logarithm increases by precisely `1/m`. -/
theorem nativeLogParameter_step (j : Kind) (τ t : ℝ) :
    nativeLogParameter j τ (t + 1) - 1 / (j.order : ℂ) = nativeLogParameter j τ t := by
  simp only [nativeLogParameter_apply, nativeClockwiseParameter]
  push_cast
  ring

/-- A continuous real lift of the full original time-dependent logarithmic translation. -/
def nativeGaugeRealLift (j : Kind) (τ : ℝ) : C(ℝ, RealCoordinates) :=
  (positiveLogFlatMap (specialLocalData j) j.twist).comp
    ((nativeLogRoot j τ).prodMk (nativeLogParameter j τ))

@[simp] theorem nativeGaugeRealLift_apply (j : Kind) (τ t : ℝ) :
    nativeGaugeRealLift j τ t =
      ((specialLocalData j).periods.periodEquiv (nativeLogRoot j τ t)).symm
        (nativeLogParameter j τ t •
          periodVector (specialLocalData j).periods j.twist (nativeLogRoot j τ t)) := rfl

/-- The exact real recurrence before applying any quotient projection. -/
theorem nativeGaugeRealLift_forward (j : Kind) (τ t : ℝ) :
    flatLinear j (nativeGaugeRealLift j τ (t + 1)) =
      nativeGaugeRealLift j τ t + (1 / (j.order : ℝ)) • realCast j.twist := by
  have h := positiveLogFlat_rotation (specialLocalData j) j.twist j.matrix_fixes_twist
    (nativeLogRoot j τ (t + 1)) (nativeLogParameter j τ (t + 1))
  rw [nativeLogRoot_rotation, nativeLogParameter_step] at h
  change nativeGaugeRealLift j τ t =
    flatLinear j (nativeGaugeRealLift j τ (t + 1)) -
      (1 / (j.order : ℝ)) • realCast j.twist at h
  exact sub_eq_iff_eq_add.mp h.symm

/-- In the positive-time convention the exact recurrence uses the actual inverse linear map. -/
theorem nativeGaugeRealLift_recurrence (j : Kind) (τ t : ℝ) :
    nativeGaugeRealLift j τ (t + 1) =
      (flatLinearEquiv j).symm (nativeGaugeRealLift j τ t) +
        (1 / (j.order : ℝ)) • realCast j.twist := by
  apply (flatLinearEquiv j).injective
  rw [(flatLinearEquiv j).map_add, LinearEquiv.apply_symm_apply,
    (flatLinearEquiv j).map_smul]
  change flatLinear j (nativeGaugeRealLift j τ (t + 1)) =
    nativeGaugeRealLift j τ t + (1 / (j.order : ℝ)) • flatLinear j (realCast j.twist)
  rw [flatLinear_fixes_realCast j j.twist j.matrix_fixes_twist,
    nativeGaugeRealLift_forward]

/-- The original full gauge cylinder is precisely translation by the quotient
of this continuous real lift; no winding has been discarded. -/
theorem nativeGaugeCylinder_realLift (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeGaugeCylinder j τ (t, x) = x + standardLattice.mkQ (nativeGaugeRealLift j τ t) := by
  rw [nativeGaugeCylinder_apply]
  apply congrArg (fun y : RealTorus₄ => x + y)
  exact sectionCoordinate_eq_positiveLogFlat (specialLocalData j) j.twist
    (nativeLogRoot j τ t) (nativeLogRoot_ne_zero j τ t) (nativeLogParameter j τ t)
    (nativeLogRoot_exponential j τ t)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
