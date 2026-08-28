import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGaugeForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticBaseChangeCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover

/-!
# The original upper-half-plane coordinates on the elliptic regular cover

The inverse elliptic chart changes only the base coordinate. The complex
fibre vectors keep their original period marking. The two actual maps to
the global threefold agree, so the genuine derivative pullback changes
the coefficient of each base differential by the actual chart derivative.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling HolomorphicDifferentialForms
  HolomorphicDifferentialForms.Coordinates

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace starCoverChartedSpace Threefold.chartedSpace
  cover_isManifold starCover_isManifold Threefold.space_isManifold
  RegularCover.coverChartedSpace RegularCover.cover_isManifold

/-- The genuine original source coordinate, retaining both fibre vectors. -/
def regularCoverToSource (j : Kind) (x : CoverStar j) : RegularCover.Cover :=
  (regularBase j x.1, x.2)

@[simp] theorem regularCoverToSource_apply (j : Kind) (x : CoverStar j) :
    regularCoverToSource j x = (regularBase j x.1, x.2) := rfl

theorem regularCoverToSource_holomorphic (j : Kind) :
    ContMDiff IF IF ω (regularCoverToSource j) := by
  rw [modelWithCornersSelf_prod]
  exact (regularBase_holomorphic j).prodMap contMDiff_id

/-- The actual period-vector quotient maps agree without a fibre-coordinate change. -/
theorem regularCover_eq_sourceCover (j : Kind) (x : CoverStar j) :
    regularCover j x = RegularCover.globalCover (regularCoverToSource j x) := rfl

/-- The base factor is the actual native derivative of the inverse elliptic chart. -/
def regularBaseJacobian (j : Kind) (z : RootStar j) : ℂ :=
  (mfderiv I₁ I₁ (regularBase j) z : ℂ →L[ℂ] ℂ) (1 : ℂ)

theorem mfderiv_regularCoverToSource (j : Kind) (x : CoverStar j) :
    mfderiv IF IF (regularCoverToSource j) x =
      EllipticBaseChange.baseChange (regularBaseJacobian j x.1) := by
  have hb := (regularBase_holomorphic j x.1).mdifferentiableAt (by simp)
  have hi : MDifferentiableAt I₂ I₂ (id : ComplexPlane₂ → ComplexPlane₂) x.2 :=
    mdifferentiableAt_id
  have hp := mfderiv_prodMap hb hi
  rw [mfderiv_id] at hp
  rw [modelWithCornersSelf_prod]
  change mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (Prod.map (regularBase j) id) x = _
  refine hp.trans ?_
  apply ContinuousLinearMap.ext
  intro v
  let L : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (regularBase j) x.1
  let w : FamilyModel := v
  change (L w.1, w.2) = (L (1 : ℂ) * w.1, w.2)
  apply Prod.ext
  · simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul w.1 (1 : ℂ)
  · rfl

/-- The two descriptions of the regular form are actual derivative
pullbacks of the same global form. -/
theorem regularCoverPullback_eq_sourceNative (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : CoverStar j) :
    regularCoverPullback j θ x =
      (RegularCover.nativeCoefficients θ (regularCoverToSource j x)).compContinuousLinearMap
        (EllipticBaseChange.baseChange (regularBaseJacobian j x.1)) := by
  have hm : regularCover j = RegularCover.globalCover ∘ regularCoverToSource j :=
    funext (regularCover_eq_sourceCover j)
  have hpc := pullback_congr (p := p) (regularCover_holomorphic j)
    (RegularCover.globalCover_holomorphic.comp (regularCoverToSource_holomorphic j)) hm
  have hp := (congrArg
    (fun A : Form FamilyModel Threefold.Space p →ₗ[ℂ] Form FamilyModel (CoverStar j) p => A θ)
    hpc).trans
      (pullback_comp (regularCoverToSource j) (regularCoverToSource_holomorphic j)
        RegularCover.globalCover RegularCover.globalCover_holomorphic θ)
  ext v
  have hv := congrArg (fun η : Form FamilyModel (CoverStar j) p => η x v) hp
  change regularCoverPullback j θ x v =
    RegularCover.globalCoverPullback θ (regularCoverToSource j x)
      (fun i => mfderiv IF IF (regularCoverToSource j) x (v i)) at hv
  change regularCoverPullback j θ x v =
    RegularCover.nativeCoefficients θ (regularCoverToSource j x)
      (fun i => EllipticBaseChange.baseChange (regularBaseJacobian j x.1) (v i))
  rw [RegularCover.nativeCoefficients_apply]
  apply hv.trans
  apply congrArg (RegularCover.globalCoverPullback θ (regularCoverToSource j x))
  funext i
  exact DFunLike.congr_fun (mfderiv_regularCoverToSource j x) (v i)

/-- The fibre one-form coefficient does not acquire a base factor. -/
theorem oneFibreCoefficient_source (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) (x : CoverStar j) :
    oneFibreCoefficient (regularCoverPullback j θ x) =
      oneFibreCoefficient (RegularCover.nativeCoefficients θ (regularCoverToSource j x)) := by
  rw [regularCoverPullback_eq_sourceNative]
  exact EllipticBaseChange.oneFibreCoefficient_pullback _ _

theorem oneBaseCoefficient_source (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) (x : CoverStar j) :
    oneBaseCoefficient (regularCoverPullback j θ x) =
      regularBaseJacobian j x.1 *
        oneBaseCoefficient (RegularCover.nativeCoefficients θ (regularCoverToSource j x)) := by
  rw [regularCoverPullback_eq_sourceNative]
  exact EllipticBaseChange.oneBaseCoefficient_pullback _ _

theorem twoVerticalCoefficient_source (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j) :
    twoVerticalCoefficient (regularCoverPullback j θ x) =
      twoVerticalCoefficient (RegularCover.nativeCoefficients θ (regularCoverToSource j x)) := by
  rw [regularCoverPullback_eq_sourceNative]
  exact EllipticBaseChange.twoVerticalCoefficient_pullback _ _

theorem twoMixedCoefficient_source (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j) :
    twoMixedCoefficient (regularCoverPullback j θ x) =
      regularBaseJacobian j x.1 •
        twoMixedCoefficient (RegularCover.nativeCoefficients θ (regularCoverToSource j x)) := by
  rw [regularCoverPullback_eq_sourceNative]
  exact EllipticBaseChange.twoMixedCoefficient_pullback _ _

theorem topCoefficient_source (j : Kind)
    (θ : Form FamilyModel Threefold.Space 3) (x : CoverStar j) :
    topCoefficient (regularCoverPullback j θ x) =
      regularBaseJacobian j x.1 *
        topCoefficient (RegularCover.nativeCoefficients θ (regularCoverToSource j x)) := by
  rw [regularCoverPullback_eq_sourceNative]
  exact EllipticBaseChange.topCoefficient_pullback _ _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
