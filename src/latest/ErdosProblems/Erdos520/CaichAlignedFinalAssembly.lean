import ErdosProblems.Erdos520.CaichAlignedScheduledCleanup
import ErdosProblems.Erdos520.CaichAlignedScheduledMainPNTSpecialization
import ErdosProblems.Erdos520.CaichConcreteAuxiliaryAssembly
import ErdosProblems.Erdos520.CaichWPiecewiseArithmetic
import ErdosProblems.Erdos520.CaichAlignedResidualL2
import ErdosProblems.Erdos520.AlignedSmoothConcentrationAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Final concentration assembly for the honestly scaled aligned energy

The literal near family has size `O(K * ell * log ell)`.  Consequently the
main cleanup uses a fixed scale factor `D0` on the Harper block energies.
This file inserts that scaled family directly into the already proved
concentration and smoothing reductions.  It contains no new analytic input.
-/

/-- A sufficiently large integer schedule degree exists for every positive
target exponent. -/
theorem exists_alignedDegree_for_criticalGap
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, 9 ≤ K ∧ 10 < 2 * (K : ℝ) * η := by
  obtain ⟨K, hK⟩ := exists_nat_gt (5 / η + 9)
  have hdivpos : 0 < (5 : ℝ) / η := div_pos (by norm_num) hη
  have hK9R : (9 : ℝ) < K := by linarith
  have hK9 : 9 ≤ K := by exact_mod_cast hK9R.le
  have hdiv : 5 / η < (K : ℝ) := by linarith
  have hfive : 5 < (K : ℝ) * η :=
    (div_lt_iff₀ hη).mp hdiv
  exact ⟨K, hK9, by nlinarith⟩

/-- One fixed natural degree large enough for the unconditional `W/x`
finite-test estimate. -/
def selectedCaichAuxiliaryMomentDegree (K m : ℕ) : ℕ :=
  12 * (2 ^ K) * (2 * m + 2) +
    (4 * m + 2 * K + 8) * 2 ^ (K + 1) + 2

theorem one_le_selectedCaichAuxiliaryMomentDegree (K m : ℕ) :
    1 ≤ selectedCaichAuxiliaryMomentDegree K m := by
  unfold selectedCaichAuxiliaryMomentDegree
  omega

theorem two_le_selectedCaichAuxiliaryMomentDegree (K m : ℕ) :
    2 ≤ selectedCaichAuxiliaryMomentDegree K m := by
  unfold selectedCaichAuxiliaryMomentDegree
  omega

theorem caichWGap_selectedCaichAuxiliaryMomentDegree (K m : ℕ) :
    12 * (2 ^ K) * (2 * m + 2) ≤
      selectedCaichAuxiliaryMomentDegree K m := by
  unfold selectedCaichAuxiliaryMomentDegree
  omega

theorem caichL2RawGap_selectedCaichAuxiliaryMomentDegree (K m : ℕ) :
    (4 * m + 2 * K + 8) * 2 ^ (K + 1) ≤
      selectedCaichAuxiliaryMomentDegree K m := by
  unfold selectedCaichAuxiliaryMomentDegree
  omega

theorem self_le_caichWSmoothingExponent
    {q : ℕ} (hq : 2 ≤ q) :
    q ≤ caichWSmoothingExponent q := by
  have hsq : 2 * q ≤ q ^ 2 := by nlinarith
  unfold caichWSmoothingExponent
  omega

theorem caichL2Gap_selectedCaichAuxiliaryMomentDegree (K m : ℕ) :
    (4 * m + 2 * K + 8) * 2 ^ (K + 1) ≤
      caichWSmoothingExponent
        (selectedCaichAuxiliaryMomentDegree K m) := by
  exact (caichL2RawGap_selectedCaichAuxiliaryMomentDegree K m).trans
    (self_le_caichWSmoothingExponent
      (two_le_selectedCaichAuxiliaryMomentDegree K m))

/-- The concrete smoothing remainder formed with the scaled aligned Harper
energy family. -/
noncomputable def selectedScaledAlignedHarperConcreteSmoothingRemainder
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (D0 : ℝ) (q m : ℕ) : ℕ → ℕ → Omega → ℝ :=
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  fun ell i omega ↦
    caichConcreteSmoothingRemainder
      (selectedAlignedCaichSmoothingParameter q m ell i)
      w.schedule.J (selectedScaledAlignedHarperEnergy hK hHarper D0)
      ell omega (selectedAlignedTestPoint m ell i)
      (selectedAlignedHarperInitialCutoff hK hHarper ell i)
      (selectedAlignedTestPoint m ell i)

/-- Complete aligned test-point estimate with the honestly scaled Harper
energy.  The only premise left here is the eventual bound for the displayed
concrete auxiliary remainder. -/
theorem aeTestPointBound_partialSum_of_scaledAlignedHarper_concreteSmoothing
    {K m q : ℕ} (hK : 9 ≤ K) (hm : 0 < m)
    {D0 η : ℝ} (hD0 : 0 < D0) (hη : 0 < η)
    (hgap : 10 < 2 * (K : ℝ) * η)
    (hHarper : HarperRademacherInitialMomentStatement)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m)
        (selectedScaledAlignedHarperConcreteSmoothingRemainder
          hK hHarper D0 q m)
        (D0 *
          (selectedClampedAlignedHarperBlockCertificate
            hK hHarper).blockConstant)
        K ell omega) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  let w : ClampedAlignedHarperBlockCertificate K :=
    selectedClampedAlignedHarperBlockCertificate hK hHarper
  let X : ℕ → ℕ → ℝ := selectedAlignedCaichSmoothingParameter q m
  let U : ℕ → ℕ → Omega → ℝ :=
    selectedScaledAlignedHarperEnergy hK hHarper D0
  let E : ℕ → ℕ → Omega → ℝ :=
    selectedScaledAlignedHarperConcreteSmoothingRemainder
      hK hHarper D0 q m
  have hX : ∀ ell i, i ∈ alignedRootExpTests K m ell → 0 < X ell i := by
    intro ell i hi
    exact caichWSmoothingParameterNatCast_pos q
      (alignedRootExpTestPoint m i)
  have hx : ∀ ell i, i ∈ alignedRootExpTests K m ell →
      0 < selectedAlignedTestPoint m ell i := by
    intro ell i hi
    exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi)
  have hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale
        (alignedRootExpTests K m)
        (selectedAlignedTestPoint m)
        (selectedAlignedHarperInitialCutoff hK hHarper)
        (selectedAlignedTestPoint m)
        w.schedule.J U E 2 ell omega := by
    have h := ae_eventually_qvSmoothingGood_caichConcrete
      (alignedRootExpTests K m)
      (selectedAlignedTestPoint m)
      (selectedAlignedHarperInitialCutoff hK hHarper)
      (selectedAlignedTestPoint m)
      X w.schedule.J U hX hx
    simpa only [E, X, U,
      selectedScaledAlignedHarperConcreteSmoothingRemainder, w] using! h
  have hblock : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale w.schedule.J U
        (D0 * w.blockConstant) K ell omega := by
    simpa only [U, w] using!
      (ae_eventually_selectedScaledAlignedHarper_blockGood
        hK hHarper hD0.le)
  have hB : 0 < D0 * w.blockConstant :=
    mul_pos hD0 w.blockConstant_pos
  exact aeTestPointBound_partialSum_clampedAligned_of_components
    (D := 2) (B := D0 * w.blockConstant) (η := η)
    w.clamp w.schedule.J U E (by norm_num) hB hη (by omega) hm hgap
    (by simpa only [w] using! hsmoothing)
    hblock
    (by simpa only [E, w] using! haux)

/-! ## Assembly of the literal residual components -/

theorem caichLambdaAuxThreshold_nonneg (K ell : ℕ) :
    0 ≤ caichLambdaAuxThreshold K ell := by
  rcases ell with _ | ell
  · simp [caichLambdaAuxThreshold, caichAuxiliaryPower,
      caichAuxiliaryLogFactor]
  · have hone : (1 : ℝ) ≤ (ell + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le ell)
    have hlog : 0 ≤ Real.log ((ell + 1 : ℕ) : ℝ) :=
      Real.log_nonneg hone
    unfold caichLambdaAuxThreshold caichAuxiliaryPower
      caichAuxiliaryLogFactor
    positivity

/-- An identically zero lambda component has no exceptional set. -/
theorem summable_selectedAlignedZeroAuxiliary_failure
    (tests : ℕ → Finset ℕ) (K : ℕ) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests selectedAlignedZeroAuxiliary
        (caichLambdaAuxThreshold K) ell) := by
  have hzero : (fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests selectedAlignedZeroAuxiliary
        (caichLambdaAuxThreshold K) ell)) = fun _ell ↦ 0 := by
    funext ell
    have hthreshold := caichLambdaAuxThreshold_nonneg K ell
    simp [caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale, selectedAlignedZeroAuxiliary,
      hthreshold]
  rw [hzero]
  exact summable_zero

/-- The unconditional piecewise `W/x` theorem, rewritten in the exact
notation used by the concrete smoothing assembly. -/
theorem summable_selectedAlignedHarperConcreteW_failure
    {q K m : ℕ} (hq : 1 ≤ q) (hK : 1 ≤ K)
    (hgap : 12 * (2 ^ K) * (2 * m + 2) ≤ q)
    (hK9 : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (caichConcreteWoverX
          (selectedAlignedCaichSmoothingParameter q m)
          (selectedAlignedTestPoint m)
          (selectedAlignedHarperInitialCutoff hK9 hHarper)
          (selectedAlignedTestPoint m))
        (caichWAuxThreshold K) ell) := by
  have h := summable_measureReal_caichAlignedConcreteWoverXNat_failure
    hq hK hgap (selectedAlignedHarperInitialCutoff hK9 hHarper)
  simpa only [caichAlignedConcreteWoverXNat, caichConcreteWoverX,
    selectedAlignedCaichSmoothingParameter, selectedAlignedTestPoint,
    caichWSmoothingParameterNatCast] using! h

/-- The selected main geometry together with summable `L12`, `L2`, and
`W/x` failures gives the eventual concrete auxiliary estimate for the
honestly scaled energy.  The two lambda components vanish identically. -/
theorem ae_eventually_selectedScaledAlignedHarper_auxiliary_of_mainGeometry
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hgeometry : ∀ᶠ ell : ℕ in atTop,
      SelectedAlignedHarperMainGeometryAtScale
        hK hHarper q m 9 ((1200 * K : ℕ) : ℝ) ell)
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hW : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (caichConcreteWoverX
          (selectedAlignedCaichSmoothingParameter q m)
          (selectedAlignedTestPoint m)
          (selectedAlignedHarperInitialCutoff hK hHarper)
          (selectedAlignedTestPoint m))
        (caichWAuxThreshold K) ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m)
        (selectedScaledAlignedHarperConcreteSmoothingRemainder
          hK hHarper ((1200 * K : ℕ) : ℝ) q m)
        (((1200 * K : ℕ) : ℝ) *
          (selectedClampedAlignedHarperBlockCertificate
            hK hHarper).blockConstant)
        K ell omega := by
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let x : ℕ → ℕ → ℕ := selectedAlignedTestPoint m
  let a : ℕ → ℕ → ℕ :=
    selectedAlignedHarperInitialCutoff hK hHarper
  let X : ℕ → ℕ → ℝ := selectedAlignedCaichSmoothingParameter q m
  let w : ClampedAlignedHarperBlockCertificate K :=
    selectedClampedAlignedHarperBlockCertificate hK hHarper
  let D0 : ℝ := ((1200 * K : ℕ) : ℝ)
  let U : ℕ → ℕ → Omega → ℝ :=
    selectedScaledAlignedHarperEnergy hK hHarper D0
  have hmain := ae_eventually_selectedAlignedHarper_mainDominatedAtScale
    hK hHarper (C := 9) (D0 := D0) (by norm_num)
      (by dsimp [D0]; positivity) (by simpa only [D0] using! hgeometry)
  have hzero : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests selectedAlignedZeroAuxiliary
        (caichLambdaAuxThreshold K) ell) :=
    summable_selectedAlignedZeroAuxiliary_failure tests K
  have haux5 := ae_eventually_auxiliaryRemainderGood_caichConcrete
    tests x a x X w.schedule.J U
    selectedAlignedZeroAuxiliary selectedAlignedZeroAuxiliary
    (selectedAlignedHarperL12 hK hHarper q m)
    (selectedAlignedHarperL2 hK hHarper q m) K
    (by simpa only [tests, x, a, X, w, U, D0] using! hmain)
    hzero hzero
    (by simpa only [tests] using! hL12)
    (by simpa only [tests] using! hL2)
    (by simpa only [tests, x, a, X] using! hW)
  have hscale : (5 : ℝ) ≤ D0 * w.blockConstant := by
    have hD0 : (1 : ℝ) ≤ D0 := by
      dsimp [D0]
      exact_mod_cast (show 1 ≤ 1200 * K by omega)
    nlinarith [w.five_le_blockConstant]
  filter_upwards [haux5] with omega hauxOmega
  filter_upwards [hauxOmega] with ell hauxEll
  have henlarge := auxiliaryRemainderGoodAtScale_mono_constant
    tests _ hscale hauxEll
  simpa only [tests, x, a, X, w, U, D0,
    selectedScaledAlignedHarperConcreteSmoothingRemainder] using! henlarge

/-- Backwards-compatible assembly using the effective-PNT interface. -/
theorem ae_eventually_selectedScaledAlignedHarper_auxiliary_of_components
    (hPNT : EffectivePrimeCountingStatement)
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hW : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (caichConcreteWoverX
          (selectedAlignedCaichSmoothingParameter q m)
          (selectedAlignedTestPoint m)
          (selectedAlignedHarperInitialCutoff hK hHarper)
          (selectedAlignedTestPoint m))
        (caichWAuxThreshold K) ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m)
        (selectedScaledAlignedHarperConcreteSmoothingRemainder
          hK hHarper ((1200 * K : ℕ) : ℝ) q m)
        (((1200 * K : ℕ) : ℝ) *
          (selectedClampedAlignedHarperBlockCertificate
            hK hHarper).blockConstant)
        K ell omega := by
  exact ae_eventually_selectedScaledAlignedHarper_auxiliary_of_mainGeometry
    hK hHarper q m
      (eventually_selectedAlignedHarperMainGeometry_of_effectivePNT
        hPNT hK hHarper q m)
      hL12 hL2 hW

/-- Premise-free auxiliary assembly using the verified Brun--Titchmarsh
sieve for the main geometry. -/
theorem ae_eventually_selectedScaledAlignedHarper_auxiliary_unconditional
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hW : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (caichConcreteWoverX
          (selectedAlignedCaichSmoothingParameter q m)
          (selectedAlignedTestPoint m)
          (selectedAlignedHarperInitialCutoff hK hHarper)
          (selectedAlignedTestPoint m))
        (caichWAuxThreshold K) ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale
        (alignedRootExpTests K m)
        (selectedScaledAlignedHarperConcreteSmoothingRemainder
          hK hHarper ((1200 * K : ℕ) : ℝ) q m)
        (((1200 * K : ℕ) : ℝ) *
          (selectedClampedAlignedHarperBlockCertificate
            hK hHarper).blockConstant)
        K ell omega := by
  exact ae_eventually_selectedScaledAlignedHarper_auxiliary_of_mainGeometry
    hK hHarper q m
      (eventually_selectedAlignedHarperMainGeometry_unconditional
        hK hHarper q m)
      hL12 hL2 hW

/-- The final aligned test-point estimate after the unconditional `W/x`
theorem has been inserted.  Only the two literal residual failure series are
parameters of this assembly lemma. -/
theorem aeTestPointBound_partialSum_of_selectedAlignedResiduals
    (hPNT : EffectivePrimeCountingStatement)
    {K q m : ℕ} (hK : 9 ≤ K) (hm : 0 < m)
    (hq : 1 ≤ q)
    (hWgap : 12 * (2 ^ K) * (2 * m + 2) ≤ q)
    {η : ℝ} (hη : 0 < η)
    (hcriticalGap : 10 < 2 * (K : ℝ) * η)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell)) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  have hW := summable_selectedAlignedHarperConcreteW_failure
    hq (by omega : 1 ≤ K) hWgap hK hHarper
  have haux :=
    ae_eventually_selectedScaledAlignedHarper_auxiliary_of_components
      hPNT hK hHarper q m hL12 hL2 hW
  exact
    aeTestPointBound_partialSum_of_scaledAlignedHarper_concreteSmoothing
      hK hm
      (D0 := ((1200 * K : ℕ) : ℝ))
      (by positivity) hη hcriticalGap hHarper haux

/-- The final aligned test-point estimate with no prime-counting premise. -/
theorem aeTestPointBound_partialSum_of_selectedAlignedResiduals_unconditional
    {K q m : ℕ} (hK : 9 ≤ K) (hm : 0 < m)
    (hq : 1 ≤ q)
    (hWgap : 12 * (2 ^ K) * (2 * m + 2) ≤ q)
    {η : ℝ} (hη : 0 < η)
    (hcriticalGap : 10 < 2 * (K : ℝ) * η)
    (hHarper : HarperRademacherInitialMomentStatement)
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure
        (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell)) :
    AETestPointBound μ partialSum (criticalScale η)
      (alignedRootExpTestPoint m) := by
  have hW := summable_selectedAlignedHarperConcreteW_failure
    hq (by omega : 1 ≤ K) hWgap hK hHarper
  have haux :=
    ae_eventually_selectedScaledAlignedHarper_auxiliary_unconditional
      hK hHarper q m hL12 hL2 hW
  exact
    aeTestPointBound_partialSum_of_scaledAlignedHarper_concreteSmoothing
      hK hm
      (D0 := ((1200 * K : ℕ) : ℝ))
      (by positivity) hη hcriticalGap hHarper haux

end Problem520
end Erdos
