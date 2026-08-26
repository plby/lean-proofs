import ErdosProblems.Erdos520.AlignedHarperConcentrationAssembly
import ErdosProblems.Erdos520.CaichAlignedScheduledCleanup
import ErdosProblems.Erdos520.CaichConcreteAuxiliaryAssembly
import ErdosProblems.Erdos520.PublishedInterpolation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Granular final endpoint for Erdős #520

This file replaces the historical catch-all `CaichPublishedTailCompletion`
at the active endpoint.  Harper's exact low-moment specialization and the
exact Lau--Tenenbaum--Wu interpolation specialization are named separately.
The sole intervening premise is an eventual bound for the *concrete*
smoothing remainder defined in `CaichConcreteSmoothingReduction`, on the
literal aligned `1/350` test mesh.

Thus there is no hidden generic decomposition, concentration, smooth-term,
or interpolation hook in the theorem below.  Those pieces are all proved by
the imported modules.
-/

/-- Exact remaining aligned auxiliary statement after the equation-(16)
repair, Harper block maximum, unconditional smooth contribution, concrete
first smoothing inequality, and stopped concentration have all been wired.

For each positive exponent we may choose a sufficiently large integer `K`
and a positive smoothing parameter at each selected test point.  The
remainder in the conclusion is the displayed arithmetic function, not an
abstract error term. -/
def AlignedConcreteSmoothingAuxiliaryStatement
    (hHarper : HarperRademacherInitialMomentStatement) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ K : ℕ, ∃ hK : 9 ≤ K,
      10 < 2 * (K : ℝ) * η ∧
      ∃ X : ℕ → ℕ → ℝ,
        (∀ ell i, i ∈ alignedRootExpTests K ltwRootExpDenominator ell →
          0 < X ell i) ∧
        ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
          auxiliaryRemainderGoodAtScale
            (alignedRootExpTests K ltwRootExpDenominator)
            (selectedAlignedHarperConcreteSmoothingRemainder
              hK hHarper ltwRootExpDenominator X)
            (selectedClampedAlignedHarperBlockCertificate
              hK hHarper).blockConstant
            K ell omega

/-! ## Expansion into the five source components -/

/-- Exact five-component spelling of the remaining Caich auxiliary input.
It exposes separately the deterministic main-term cleanup and the summable
failure probabilities for `lambda2`, `lambda3`, `L12`, `L2`, and the literal
short-interval error `W/x`. -/
def AlignedCaichFiveAuxiliaryStatement
    (hHarper : HarperRademacherInitialMomentStatement) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ K : ℕ, ∃ hK : 9 ≤ K,
      10 < 2 * (K : ℝ) * η ∧
      ∃ X : ℕ → ℕ → ℝ,
      ∃ lambda2 lambda3 L12 L2 : ℕ → ℕ → Omega → ℝ,
        (∀ ell i, i ∈ alignedRootExpTests K ltwRootExpDenominator ell →
          0 < X ell i) ∧
        (∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
          caichUnaccountedMainDominatedAtScale
            (alignedRootExpTests K ltwRootExpDenominator)
            (fun _ell i => alignedRootExpTestPoint ltwRootExpDenominator i)
            (selectedAlignedHarperInitialCutoff hK hHarper)
            (fun _ell i => alignedRootExpTestPoint ltwRootExpDenominator i)
            X
            (selectedClampedAlignedHarperBlockCertificate
              hK hHarper).schedule.J
            (selectedClampedAlignedHarperBlockCertificate
              hK hHarper).schedule.toThinBlockData.U
            lambda2 lambda3 L12 L2 ell omega) ∧
        Summable (fun ell ↦ μ.real
          (caichAuxiliaryComponentFailure
            (alignedRootExpTests K ltwRootExpDenominator) lambda2
            (caichLambdaAuxThreshold K) ell)) ∧
        Summable (fun ell ↦ μ.real
          (caichAuxiliaryComponentFailure
            (alignedRootExpTests K ltwRootExpDenominator) lambda3
            (caichLambdaAuxThreshold K) ell)) ∧
        Summable (fun ell ↦ μ.real
          (caichAuxiliaryComponentFailure
            (alignedRootExpTests K ltwRootExpDenominator) L12
            (caichLargeAuxThreshold K) ell)) ∧
        Summable (fun ell ↦ μ.real
          (caichAuxiliaryComponentFailure
            (alignedRootExpTests K ltwRootExpDenominator) L2
            (caichLargeAuxThreshold K) ell)) ∧
        Summable (fun ell ↦ μ.real
          (caichAuxiliaryComponentFailure
            (alignedRootExpTests K ltwRootExpDenominator)
            (caichConcreteWoverX X
              (fun _ell i =>
                alignedRootExpTestPoint ltwRootExpDenominator i)
              (selectedAlignedHarperInitialCutoff hK hHarper)
              (fun _ell i =>
                alignedRootExpTestPoint ltwRootExpDenominator i))
            (caichWAuxThreshold K) ell))

/-- The five explicit component estimates imply the single concrete
smoothing-remainder statement used by the final concentration theorem. -/
theorem alignedConcreteSmoothingAuxiliary_of_fiveComponents
    (hHarper : HarperRademacherInitialMomentStatement)
    (hFive : AlignedCaichFiveAuxiliaryStatement hHarper) :
    AlignedConcreteSmoothingAuxiliaryStatement hHarper := by
  intro η hη
  obtain ⟨K, hK, hgap, X, lambda2, lambda3, L12, L2,
      hX, hmain, hlambda2, hlambda3, hL12, hL2, hW⟩ := hFive η hη
  refine ⟨K, hK, hgap, X, hX, ?_⟩
  let tests : ℕ → Finset ℕ :=
    alignedRootExpTests K ltwRootExpDenominator
  let x : ℕ → ℕ → ℕ := fun _ell i =>
    alignedRootExpTestPoint ltwRootExpDenominator i
  let a : ℕ → ℕ → ℕ := selectedAlignedHarperInitialCutoff hK hHarper
  let b : ℕ → ℕ → ℕ := fun _ell i =>
    alignedRootExpTestPoint ltwRootExpDenominator i
  let w : ClampedAlignedHarperBlockCertificate K :=
    selectedClampedAlignedHarperBlockCertificate hK hHarper
  have haux5 := ae_eventually_auxiliaryRemainderGood_caichConcrete
    tests x a b X w.schedule.J w.schedule.toThinBlockData.U
    lambda2 lambda3 L12 L2 K
    (by simpa only [tests, x, a, b, w] using! hmain)
    (by simpa only [tests] using! hlambda2)
    (by simpa only [tests] using! hlambda3)
    (by simpa only [tests] using! hL12)
    (by simpa only [tests] using! hL2)
    (by simpa only [tests, x, a, b] using! hW)
  have hauxB : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale tests
        (fun ell r omega =>
          caichConcreteSmoothingRemainder (X ell r)
            w.schedule.J w.schedule.toThinBlockData.U ell omega
            (x ell r) (a ell r) (b ell r))
        w.blockConstant K ell omega := by
    filter_upwards [haux5] with omega hauxOmega
    filter_upwards [hauxOmega] with ell hauxEll
    exact auxiliaryRemainderGoodAtScale_mono_constant tests _
      w.five_le_blockConstant hauxEll
  simpa only [tests, x, a, b, w,
    selectedAlignedHarperConcreteSmoothingRemainder,
    selectedAlignedHarperInitialCutoff] using! hauxB

/-- The exact auxiliary statement gives every repaired critical test-point
bound on the LTW mesh. -/
theorem aeTestPointBound_ltw_of_alignedConcreteSmoothingAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    ∀ η : ℝ, 0 < η →
      AETestPointBound μ partialSum (criticalScale η)
        ltwRademacherTestPoint := by
  intro η hη
  obtain ⟨K, hK, hgap, X, hX, haux⟩ := hAux η hη
  have hpoints :=
    aeTestPointBound_partialSum_of_alignedHarper_concreteSmoothing
      hK ltwRootExpDenominator_pos hη hgap hHarper X hX haux
  simpa only [ltwRademacherTestPoint] using! hpoints

/-- Granular repaired upper bound.  The only external mathematical results
are now the exact Harper and LTW propositions, plus the concrete aligned
auxiliary estimate displayed above. -/
theorem criticalUpperBound_of_harper_ltw_concreteAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    CriticalUpperBound μ partialSum :=
  criticalUpperBound_of_ltwRademacherTestPoints
    (aeTestPointBound_ltw_of_alignedConcreteSmoothingAuxiliary
      hHarper hAux)
    hLTW

/-- Zero at the proposed LIL normalization from the granular inputs. -/
theorem zeroLIL_of_harper_ltw_concreteAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    ZeroLIL μ partialSum :=
  zeroLIL_of_criticalUpperBound
    (criticalUpperBound_of_harper_ltw_concreteAuxiliary
      hHarper hLTW hAux)

/-- The corresponding explicit negative answer to a positive limiting LIL
constant. -/
theorem noPositiveLILConstant_of_harper_ltw_concreteAuxiliary
    (hHarper : HarperRademacherInitialMomentStatement)
    (hLTW : LauTenenbaumWuRademacherInterpolation)
    (hAux : AlignedConcreteSmoothingAuxiliaryStatement hHarper) :
    NoPositiveLILConstant μ partialSum :=
  noPositiveLILConstant_of_zeroLIL
    (zeroLIL_of_harper_ltw_concreteAuxiliary hHarper hLTW hAux)

end Problem520
end Erdos
