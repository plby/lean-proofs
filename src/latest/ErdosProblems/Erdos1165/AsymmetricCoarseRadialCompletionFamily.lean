/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedSuccessfulTailRow
import ErdosProblems.Erdos1165.AsymmetricCoarseHighTailUpper
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionScale
import ErdosProblems.Erdos1165.BufferedStoppedSuccessfulPointUpper
import ErdosProblems.Erdos1165.AsymmetricDirectFarPairCompletionConstructor
import ErdosProblems.Erdos1165.AsymmetricLiteralPairEndpoint

/-!
# The concrete coarse radial completion at separated scales

This file assembles the reference-free padded successful-row estimate into
the normalized coarse completion family.  It also records the resulting
literal far-pair datum at every separation level at least three.  The padded
right-hand row itself is uniform in the separation level.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCoarseRadialCompletionFamily

open AnnularRadialSequentialUpperFamily AppendixPair AppendixPairMoment
open AnnularProfileClocks
open AsymmetricActualFarPairData AsymmetricCoarseCompletionScale
open AsymmetricCoarseCompletionCode
open AsymmetricCoarseNormalizedCompletionRows
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricCoarseHighTailUpper
open AsymmetricCompatibleRadialCompletionFamily
open AsymmetricDirectFarPairCompletionConstructor
open AsymmetricLiteralPairEndpoint
open AsymmetricPaddedSuccessfulTailRow
open BufferedStoppedSuccessfulPointEvent BufferedStoppedSuccessfulPointUpper
open GaussianGeometricCutoff ProfileWeightUpper
open MarkedBridgeFactorization
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open ThickPoint
open SharedPrefixPairExtraction

noncomputable section

/-- The checked bridge-product row is exactly the quantitative input of the
concrete normalized coarse completion. -/
def compatibleRadialCompletionFamilyOfPaddedRow
    {start q l : ℕ} (hn : 2 ≤ q) (hk : l + 1 ≤ q)
    (hseparation : l = separationLevel q x y)
    (hlevel : l ≤ q) (hthree : 3 ≤ l)
    (hrow : ∀ code : CoarseSplitCompletionCode start q l hk
        profileUpperDelta x y (profileInnerBoundary q l y)
        (discBoundary (0, 0) (outerScale q)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
          ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
            profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
          ∏ j, (coarseAtom code).kernel j) :
    CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent start q profileUpperDelta x y)
      (coarseRetainedEvent (start := start) hk profileUpperDelta x y
        (profileInnerBoundary q l y)
        (discBoundary (0, 0) (outerScale q)) (0, 0))
      (stoppedBufferedSuccessfulPointEvent start q (l - 3) (l + 1)
        profileUpperDelta x)
      (Real.exp 1 *
        Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
          profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) := by
  subst l
  let rows := coarseCompletionTailRowsOfBridgeProduct
    hn rfl hlevel hrow
  exact CoarseCompletionTailRows.toCompatibleRadialCompletionFamily rows
    (stoppedBufferedSuccessfulPointEvent start q
      (separationLevel q x y - 3) (separationLevel q x y + 1)
      profileUpperDelta x)
    (iUnion_coarseRetainedAtom_subset_buffered_of_three
      hn (by omega) hlevel (by omega))

/-- At separation one or two, the same normalized successful tail row is
retained, while the left upper event is the self-centred constrained
high-tail event. -/
def compatibleRadialCompletionFamilyOfPaddedRow_low
    {start q l : ℕ} (hn : 2 ≤ q) (hself : 2 + 1 ≤ q)
    (hk : l + 1 ≤ q)
    (hseparation : l = separationLevel q x y)
    (hlevel : l ≤ q) (htwo : l ≤ 2)
    (hrow : ∀ code : CoarseSplitCompletionCode start q l hk
        profileUpperDelta x y (profileInnerBoundary q l y)
        (discBoundary (0, 0) (outerScale q)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
          ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
            profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
          ∏ j, (coarseAtom code).kernel j) :
    CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent start q profileUpperDelta x y)
      (coarseRetainedEvent (start := start) hk profileUpperDelta x y
        (profileInnerBoundary q l y)
        (discBoundary (0, 0) (outerScale q)) (0, 0))
      (coarseConstrainedHighTailEvent
        (start := start) hself profileUpperDelta x)
      (Real.exp 1 *
        Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
          profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) := by
  subst l
  let rows := coarseCompletionTailRowsOfBridgeProduct
    hn rfl hlevel hrow
  exact CoarseCompletionTailRows.toCompatibleRadialCompletionFamily rows
    (coarseConstrainedHighTailEvent
      (start := start) hself profileUpperDelta x)
    (coarseRetainedEvent_subset_highTail_of_separation_le_two
      hn hself (by omega) hlevel (by omega))

/-- The selected profile terminal lower window is strictly positive from
scale two onward. -/
lemma terminalLower_chosenProfileDelta_pos
    {q : ℕ} (hq : 2 ≤ q) :
    0 < terminalLower q chosenProfileDelta := by
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpow : (q : ℝ) ^ (1 + chosenProfileDelta) ≤
      (q : ℝ) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hqOne
    norm_num [chosenProfileDelta]
  have hsq : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hnum : 0 < 2 * (q : ℝ) ^ 2 -
      (q : ℝ) ^ (1 + chosenProfileDelta) := by
    rw [Real.rpow_two] at hpow
    nlinarith
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  unfold terminalLower
  exact div_pos hnum (by positivity)

/-- At all sufficiently large selected scales, every far pair whose
separation level is at least three has the complete literal far-pair datum.
This is the source-facing assembly of the coarse padded row. -/
theorem eventually_nonempty_actualMarkedFarPairData_of_three_le_separation
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop,
      ∀ (i : Fin (chosenBlockCount delta blockIndex)) (x y : Point),
        separationLevel (scaleIndex delta blockIndex) x y ≤
            decorrelationCutoff (scaleIndex delta blockIndex) →
        3 ≤ separationLevel (scaleIndex delta blockIndex) x y →
        Nonempty (ActualMarkedFarPairData delta blockIndex
          (Real.exp (1 / 4)) i x y) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hscaleFive := hscaleNat.eventually (eventually_ge_atTop 5)
  have htailScale := hscaleNat.eventually
    (eventually_ge_atTop profileUpperTailStart)
  have hpadding := hscaleNat.eventually
    eventually_geometricCutoff_le_decorrelationPadding
  have hpaddingLt := hscaleNat.eventually
    eventually_decorrelationPadding_lt
  have hsuccessfulScale := hscaleNat.eventually
    eventually_successfulBridgeMass_le_radialTail_mul_kernel_all
  have hbufferedScale := hscaleNat.eventually
    eventually_fairSteps_stoppedBufferedSuccessfulPointEvent_le_exactCostTsum
  filter_upwards
      [hscaleFive, htailScale, hpadding, hpaddingLt,
       eventually_coarseSeparationLevel_bounds,
       eventually_geometricCutoff_le_pairPrefixScale,
       hsuccessfulScale, hbufferedScale]
      with blockIndex hqFive htailQ hpadding hpaddingLt hbounds hprefix
        hsuccessfulRow hbufferedRow
  intro i x y hlevel hthree
  let q := scaleIndex delta blockIndex
  let l := separationLevel q x y
  let start := (i : ℕ) * chosenBlockLength delta blockIndex
  have hqTwo : 2 ≤ q := by simpa only [q] using hbounds.1
  have hlOne : 1 ≤ l :=
    Nat.one_le_iff_ne_zero.mpr (separationLevel_ne_zero q x y)
  have hlSucc : l + 1 ≤ q := by
    simpa only [q, l] using (hbounds.2 x y hlevel).1
  have hlq : l ≤ q := by omega
  have hpaddingPos : 2 ≤ decorrelationPadding q := by
    exact (show 2 ≤ geometricCutoff by
      norm_num [geometricCutoff, geometricCutoffBase]).trans
        (by simpa only [q] using hpadding)
  have hpaddingLe : decorrelationPadding q ≤ q := by
    exact (by simpa only [q] using hpaddingLt.le)
  have hadd : l + decorrelationPadding q ≤ q := by
    unfold decorrelationCutoff at hlevel
    exact Nat.add_le_of_le_sub hpaddingLe hlevel
  have hprefEq : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  have hlPrefix : l + 1 < pairPrefixScale q l := by
    rw [hprefEq]
    omega
  have hcutoff : geometricCutoff ≤ pairPrefixScale q l := by
    exact hprefix l (Finset.mem_Icc.mpr ⟨hlOne, hlevel⟩)
  have htailPrefix : profileUpperTailStart ≤ pairPrefixScale q l :=
    (show profileUpperTailStart ≤ geometricCutoff by
      norm_num [profileUpperTailStart, geometricCutoff,
        geometricCutoffBase]).trans hcutoff
  let radial : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne (by
      simpa only [q, l] using hcutoff)
  let retained := coarseRetainedEvent (start := start) hlSucc
    profileUpperDelta x y (profileInnerBoundary q l y)
    (discBoundary (0, 0) (outerScale q)) (0, 0)
  let gammaX := stoppedBufferedSuccessfulPointEvent
    start q (l - 3) (l + 1) profileUpperDelta x
  have hbridge : ∀ code : CoarseSplitCompletionCode start q l hlSucc
      profileUpperDelta x y (profileInnerBoundary q l y)
      (discBoundary (0, 0) (outerScale q)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
          ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal radial.radialTail *
          ∏ j, (coarseAtom code).kernel j := by
    intro code
    have h := hsuccessfulRow l (by simpa only [q, l] using hlevel)
      hlSucc (by omega) hlPrefix htailPrefix code
    have hword (tail : CoarseSuccessfulReturnTuple code)
        (j : Fin code.1.returnCount) :
        (coarseAtom code).bridgeWord j (tail.1 j) = (tail.1 j).1.1 := rfl
    simp_rw [hword]
    simpa only [radial, ProfileRadialTailCertificate.radialTail,
      ProfileRadialTailCertificate.expOne,
      ProfileRadialTailCertificate.of_geometricCutoff, q, l] using h
  let family : CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent start q profileUpperDelta x y)
      retained gammaX radial.radialTail := by
    simpa only [retained, gammaX, radial,
      ProfileRadialTailCertificate.radialTail,
      ProfileRadialTailCertificate.expOne,
      ProfileRadialTailCertificate.of_geometricCutoff] using
        (compatibleRadialCompletionFamilyOfPaddedRow
          hqTwo hlSucc rfl hlq hthree hbridge)
  have hgammaUpper : fairSteps.real gammaX ≤
      pairPointEnvelope delta blockIndex := by
    have hmeasure := hbufferedRow hqTwo start (l - 3) (l + 1)
      profileUpperDelta x (terminalLower_chosenProfileDelta_pos hqTwo)
    exact fairSteps_real_stoppedBufferedSuccessfulPointEvent_le_pairPointEnvelope
      (delta := delta) (blockIndex := blockIndex) hqFive hlOne hlSucc
        (by simpa only [q] using htailQ) rfl hmeasure
  have hretainedUpper : fairSteps.real retained ≤
      pairPointEnvelope delta blockIndex := by
    have hm : fairSteps retained ≤ fairSteps gammaX :=
      measure_mono family.retained_subset
    have hreal := ENNReal.toReal_mono (measure_ne_top fairSteps gammaX) hm
    have hreal' : fairSteps.real retained ≤ fairSteps.real gammaX := by
      simpa only [Measure.real] using hreal
    exact hreal'.trans hgammaUpper
  refine ⟨of_pairSuccessfulCompletion_with_retainedUpper
    radial retained gammaX family hretainedUpper⟩

/-- The remaining far separation levels one and two use the normalized
self-centred high-tail upper event. -/
theorem eventually_nonempty_actualMarkedFarPairData_of_separation_le_two
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop,
      ∀ (i : Fin (chosenBlockCount delta blockIndex)) (x y : Point),
        separationLevel (scaleIndex delta blockIndex) x y ≤
            decorrelationCutoff (scaleIndex delta blockIndex) →
        separationLevel (scaleIndex delta blockIndex) x y ≤ 2 →
        Nonempty (ActualMarkedFarPairData delta blockIndex
          (Real.exp (1 / 4)) i x y) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hscaleFive := hscaleNat.eventually (eventually_ge_atTop 5)
  have htailScale := hscaleNat.eventually
    (eventually_ge_atTop profileUpperTailStart)
  have hpadding := hscaleNat.eventually
    eventually_geometricCutoff_le_decorrelationPadding
  have hpaddingLt := hscaleNat.eventually
    eventually_decorrelationPadding_lt
  have hsuccessfulScale := hscaleNat.eventually
    eventually_successfulBridgeMass_le_radialTail_mul_kernel_all
  filter_upwards
      [hscaleFive, htailScale, hpadding, hpaddingLt,
       eventually_coarseSeparationLevel_bounds,
       eventually_geometricCutoff_le_pairPrefixScale,
       hsuccessfulScale,
       eventually_fairSteps_real_coarseConstrainedHighTailEvent_le_pairPointEnvelope]
      with blockIndex hqFive htailQ hpadding hpaddingLt hbounds hprefix
        hsuccessfulRow hhighUpper
  intro i x y hlevel htwo
  let q := scaleIndex delta blockIndex
  let l := separationLevel q x y
  let start := (i : ℕ) * chosenBlockLength delta blockIndex
  have hqTwo : 2 ≤ q := by simpa only [q] using hbounds.1
  have hqThree : 2 + 1 ≤ q := by
    exact (by omega : 2 + 1 ≤ 5).trans (by simpa only [q] using hqFive)
  have hlOne : 1 ≤ l :=
    Nat.one_le_iff_ne_zero.mpr (separationLevel_ne_zero q x y)
  have hlSucc : l + 1 ≤ q := by
    simpa only [q, l] using (hbounds.2 x y hlevel).1
  have hlq : l ≤ q := by omega
  have hpaddingPos : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ geometricCutoff by
      norm_num [geometricCutoff, geometricCutoffBase]).trans
        (by simpa only [q] using hpadding)
  have hpaddingLe : decorrelationPadding q ≤ q := by
    exact (by simpa only [q] using hpaddingLt.le)
  have hadd : l + decorrelationPadding q ≤ q := by
    unfold decorrelationCutoff at hlevel
    exact Nat.add_le_of_le_sub hpaddingLe hlevel
  have hprefEq : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  have hlPrefix : l + 1 < pairPrefixScale q l := by
    rw [hprefEq]
    omega
  have hcutoff : geometricCutoff ≤ pairPrefixScale q l := by
    exact hprefix l (Finset.mem_Icc.mpr ⟨hlOne, hlevel⟩)
  have htailPrefix : profileUpperTailStart ≤ pairPrefixScale q l :=
    (show profileUpperTailStart ≤ geometricCutoff by
      norm_num [profileUpperTailStart, geometricCutoff,
        geometricCutoffBase]).trans hcutoff
  let radial : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne (by
      simpa only [q, l] using hcutoff)
  let retained := coarseRetainedEvent (start := start) hlSucc
    profileUpperDelta x y (profileInnerBoundary q l y)
    (discBoundary (0, 0) (outerScale q)) (0, 0)
  let gammaX := coarseConstrainedHighTailEvent
    (start := start) hqThree profileUpperDelta x
  have hbridge : ∀ code : CoarseSplitCompletionCode start q l hlSucc
      profileUpperDelta x y (profileInnerBoundary q l y)
      (discBoundary (0, 0) (outerScale q)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
          ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal radial.radialTail *
          ∏ j, (coarseAtom code).kernel j := by
    intro code
    have h := hsuccessfulRow l (by simpa only [q, l] using hlevel)
      hlSucc (by omega) hlPrefix htailPrefix code
    have hword (tail : CoarseSuccessfulReturnTuple code)
        (j : Fin code.1.returnCount) :
        (coarseAtom code).bridgeWord j (tail.1 j) = (tail.1 j).1.1 := rfl
    simp_rw [hword]
    simpa only [radial, ProfileRadialTailCertificate.radialTail,
      ProfileRadialTailCertificate.expOne,
      ProfileRadialTailCertificate.of_geometricCutoff, q, l] using h
  let family : CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent start q profileUpperDelta x y)
      retained gammaX radial.radialTail := by
    simpa only [retained, gammaX, radial,
      ProfileRadialTailCertificate.radialTail,
      ProfileRadialTailCertificate.expOne,
      ProfileRadialTailCertificate.of_geometricCutoff] using
        (compatibleRadialCompletionFamilyOfPaddedRow_low
          hqTwo hqThree hlSucc rfl hlq htwo hbridge)
  have hgammaUpper : fairSteps.real gammaX ≤
      pairPointEnvelope delta blockIndex := by
    simpa only [gammaX, q, start] using hhighUpper hqThree start x
  have hretainedUpper : fairSteps.real retained ≤
      pairPointEnvelope delta blockIndex := by
    have hm : fairSteps retained ≤ fairSteps gammaX :=
      measure_mono family.retained_subset
    have hreal := ENNReal.toReal_mono (measure_ne_top fairSteps gammaX) hm
    have hreal' : fairSteps.real retained ≤ fairSteps.real gammaX := by
      simpa only [Measure.real] using hreal
    exact hreal'.trans hgammaUpper
  refine ⟨of_pairSuccessfulCompletion_with_retainedUpper
    radial retained gammaX family hretainedUpper⟩

/-- All far separation levels now have the literal marked pair datum. -/
theorem eventually_nonempty_actualMarkedFarPairData
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop,
      ∀ (i : Fin (chosenBlockCount delta blockIndex)) (x y : Point),
        separationLevel (scaleIndex delta blockIndex) x y ≤
            decorrelationCutoff (scaleIndex delta blockIndex) →
        Nonempty (ActualMarkedFarPairData delta blockIndex
          (Real.exp (1 / 4)) i x y) := by
  filter_upwards
      [eventually_nonempty_actualMarkedFarPairData_of_three_le_separation,
       eventually_nonempty_actualMarkedFarPairData_of_separation_le_two]
      with blockIndex hthree htwo
  intro i x y hlevel
  by_cases h : 3 ≤ separationLevel (scaleIndex delta blockIndex) x y
  · exact hthree i x y hlevel h
  · exact htwo i x y hlevel (by omega)

/-- The concrete one-point rows and the now complete far-pair construction
form the exact eventual source record consumed by the final lower theorem. -/
theorem eventually_nonempty_asymmetricPairSourceData (delta : ℝ) :
    ∀ᶠ blockIndex : ℕ in atTop,
      Nonempty (AsymmetricPairSourceData delta blockIndex) := by
  filter_upwards
      [eventually_nonempty_chosenSequentialProfileUpperFamily delta,
       eventually_nonempty_actualMarkedFarPairData]
      with blockIndex hone hfar
  refine ⟨{
    onePointFamily := ?_
    farPairData := ?_ }⟩
  · intro i x _hx
    exact Classical.choice (hone i x)
  · intro _terminal i x _hx y _hy hlevel _radial
    exact Classical.choice (hfar i x y hlevel)

end

end Erdos1165.AsymmetricCoarseRadialCompletionFamily
