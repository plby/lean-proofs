/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredActiveProjectedDyadicDataCertificate
import ErdosProblems.Erdos186.CFP.CenteredCorePopulationNumerics
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingFromDyadicFamily
import ErdosProblems.Erdos186.CFP.DyadicRangeWindowNumerics
import ErdosProblems.Erdos186.CFP.DyadicScaleSplit
import ErdosProblems.Erdos186.CFP.FixedScaleWitnessSource
import ErdosProblems.Erdos186.CFP.FixedScaleWitnessScale
import ErdosProblems.Erdos186.CFP.IntegerTheoremLogLossLargeAssembly
import ErdosProblems.Erdos186.CFP.ProjectedColorSourceScaleNumerics
import ErdosProblems.Erdos186.CFP.ProjectedDyadicCrossingNumerics
import ErdosProblems.Erdos186.CFP.ScaleDyadicPreprocessingWindow
import ErdosProblems.Erdos186.CFP.SharpColorCapacityMonotone
import ErdosProblems.Erdos186.CFP.TrivialEnhancedWitness
import ErdosProblems.Erdos186.CFP.TrivialPreprocessedCertificate

/-!
# The unconditional centered projected large-input coverage theorem

This is the final quantitative selector in the CFP proof.  It fixes all
finite geometric constants before the source set, chooses the exact dyadic
preprocessing fold and the colour-greedy range from the source scale, and
then joins the retained preprocessing data to the projected physical-density
certificate.  The empty-relevant branch is handled by the rank-zero witness.
-/

namespace Erdos186.CFP

noncomputable section

set_option autoImplicit false

namespace RandomPartition

/-- Quantifier-reordered form of the projected retained-data theorem.  The
geometric constants, and hence the public scale denominator, are selected
before the source and its preprocessing data. -/
theorem exists_uniform_centeredActiveProjectedDyadicDataCertificateConstants
    (D M propernessDenominator : ℕ)
    (hpropernessDenominator : 0 < propernessDenominator) :
    ∃ corWidthMax denseMax denseEllMax denseWidthMax : ℕ,
      0 < denseMax ∧
      ∀ {source : Finset ℤ} {stableBudget n C0 fold : ℕ}
        (data : Preprocessing.DyadicCenteredPreprocessingData source
          stableBudget D n C0 1
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) fold),
        data.relevant.Nonempty →
        ∀ {q cap low terminal s block : ℕ},
          PreprocessingBilu.DyadicRangeSourceHApproximationFamily
            source low terminal D 1
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) →
          0 < q → 2 ≤ n → D ≤ n → low < terminal →
          (∀ h, low ≤ h → h ≤ terminal → 2 ^ h ≤ n) →
          (∀ h, low ≤ h → h ≤ terminal →
            PreprocessingBilu.preprocessingIndexBound D
                propernessDenominator ≤ 2 ^ h) →
          (∀ z ∈ source, 0 ≤ z ∧ z < (n : ℤ)) →
          (2 * q + 1) *
              ((cap + 1) +
                (Nat.log 2
                  ((n ^ obstaclePolynomialExponent D + 1) * (q + 1)) +
                    1)) ≤
            stableBudget / C0 + 1 →
          (2 * q + 1) *
              ((cap + 1) +
                (Nat.log 2
                  ((n ^ obstaclePolynomialExponent D + 1) * (q + 1)) +
                    1)) ≤ data.core.card →
          2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
              16 * Greedy.stableDyadicRatio D
                (PreprocessingBilu.preprocessingScaleDen
                  propernessDenominator) * 2 ^ terminal + 1 < cap →
          fold ≤ M * 2 ^ terminal →
          rankFlexiblePhysicalComparisonCoefficient D M
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ≤ fold + 1 →
          cap ≤ 2 * stableBudget →
          0 < block → denseEllMax ≤ q + 1 →
          max corWidthMax denseWidthMax ≤
            blockedColorSourceScale s q block →
          denseMax ≤ q + 1 →
          cap + rankFlexiblePhysicalDensityDenominator D M
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ≤
            blockedColorSourceScale s q block →
          2 * block * (q + 1) ≤ s →
          blockedColorSourceScale s q block ≤ fold →
          ProjectedProperization.projectionFactor D ≤
            blockedColorSourceScale s q block * ((q + 1) / denseMax) →
          ∃ k : ℕ, Nonempty (FixedScaleWitness
            (Stability.integerPoints data.core) s D k 0 1
              ((4 * denseMax * block) *
                ProjectedProperization.projectionFactor D)) := by
  obtain ⟨corWidthMax, denseMax, denseEllMax, denseWidthMax,
      hdenseMax, hcertificate⟩ :=
    exists_centeredActiveProjectedPopulatedDyadicCertificateConstants D M
      propernessDenominator hpropernessDenominator
  refine ⟨corWidthMax, denseMax, denseEllMax, denseWidthMax,
    hdenseMax, ?_⟩
  intro source stableBudget n C0 fold data hrelevant q cap low terminal s
    block hfamily hq hn hDn hlowTerminal hleveln hindex hinterval hcapacity
    hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable hblock hell
    hwidth hCell hcapSource hroom hsFold hprojection
  obtain ⟨d, hdrel⟩ := hrelevant
  let rd : {e // e ∈ data.relevant} := ⟨d, hdrel⟩
  let V : HDimension.HApproximation data.weakCore fold d 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) := by
    have hV := data.approximation rd
    rw [data.hAt_eq_fold rd] at hV
    exact Classical.choice hV
  have hfoldn : fold ≤ n := by
    have hle := data.horizon_le rd
    simpa only [data.hAt_eq_fold rd] using hle
  have hfoldLarge : PreprocessingBilu.preprocessingNoCarryIndexBound D
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) ≤
        fold := by
    have hlarge := data.horizon_large rd
    simpa only [data.hAt_eq_fold rd,
      PreprocessingBilu.preprocessingNoCarryIndexBound] using hlarge
  apply hcertificate data.boxesProper hdrel data.weakCore_subset_source
    data.core_subset_weakCore data.zero_mem_weakCore data.zero_mem_core
    (fun e he ↦ data.rank_le ⟨e, he⟩)
    data.stable data.weakCore_stable hfamily V hq hn hDn hfoldn
    hlowTerminal hleveln hindex
    (fun z hz ↦ hinterval z (data.weakCore_subset_source hz))
    hcapacity hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable
    hfoldLarge hblock hell hwidth hCell hcapSource hroom hsFold hprojection

end RandomPartition

/-- The public scale inequality implies that the reserve scale is no larger
than the source cardinality. -/
theorem scale_le_card_of_fixedScaleInequality
    {m s scaleDen : ℕ} (hm : 2 ≤ m) (hden : 0 < scaleDen)
    (hscale : (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (m : ℝ) ≤
      (m : ℝ)) :
    s ≤ m := by
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : 1 ≤ Real.logb 2 (m : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    simpa using Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2)
      (zero_lt_two.trans_le hmReal) hmReal
  have hdenReal : (1 : ℝ) ≤ (scaleDen : ℝ) := by
    exact_mod_cast hden
  have hsReal : (s : ℝ) ≤ (m : ℝ) := by
    calc
      (s : ℝ) = 1 * (s : ℝ) * 1 := by ring
      _ ≤ (scaleDen : ℝ) * (s : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdenReal (by positivity)) (by positivity)
      _ ≤ (scaleDen : ℝ) * (s : ℝ) *
          Real.logb 2 (m : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (m : ℝ) := hscale
  exact_mod_cast hsReal

/-- The ambient endpoint used by exact-fold preprocessing has one fixed
dyadic logarithm more than the source endpoint. -/
theorem scaleDyadicAmbient_log_le
    {m n s horizonFactor horizonCoefficient : ℕ}
    (hm : 2 ≤ m) (hhorizonFactor : 0 < horizonFactor)
    (hn : n + 1 ≤ m ^ horizonCoefficient) (hs : s ≤ m) :
    Nat.log 2
          (max (n + 1)
            (PreprocessingBilu.scaleDyadicFold horizonFactor s)) + 1 ≤
      (horizonCoefficient + horizonFactor + 6) *
        (Nat.log 2 m + 1) := by
  let ell := Nat.log 2 m + 1
  let H₀ := horizonCoefficient + horizonFactor + 5
  let H := horizonCoefficient + horizonFactor + 6
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hmPow : m < 2 ^ ell := by
    simpa only [ell] using Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hnPow : n + 1 ≤ 2 ^ (horizonCoefficient * ell) := by
    calc
      n + 1 ≤ m ^ horizonCoefficient := hn
      _ ≤ (2 ^ ell) ^ horizonCoefficient :=
        Nat.pow_le_pow_left hmPow.le _
      _ = 2 ^ (horizonCoefficient * ell) := by
        rw [← pow_mul]
        congr 1
        ring
  have hfoldWindow :=
    PreprocessingBilu.scaleDyadic_window (s := s) hhorizonFactor
  have hfoldPow :
      PreprocessingBilu.scaleDyadicFold horizonFactor s ≤ 2 ^ (H₀ * ell) := by
    have hsOne : s + 1 ≤ 2 * m := by omega
    have hfactorPow : horizonFactor ≤ 2 ^ horizonFactor :=
      PreprocessingBilu.self_le_two_pow horizonFactor
    calc
      PreprocessingBilu.scaleDyadicFold horizonFactor s ≤
          4 * horizonFactor * (s + 1) := hfoldWindow.2.2.2.le
      _ ≤ 8 * horizonFactor * m := by
        calc
          4 * horizonFactor * (s + 1) ≤
              4 * horizonFactor * (2 * m) :=
            Nat.mul_le_mul_left (4 * horizonFactor) hsOne
          _ = 8 * horizonFactor * m := by ring
      _ ≤ 2 ^ 3 * 2 ^ horizonFactor * 2 ^ ell := by
        calc
          8 * horizonFactor * m ≤ 8 * 2 ^ horizonFactor * m := by
            gcongr
          _ ≤ 8 * 2 ^ horizonFactor * 2 ^ ell := by
            gcongr
          _ = 2 ^ 3 * 2 ^ horizonFactor * 2 ^ ell := by norm_num
      _ = 2 ^ (horizonFactor + 3 + ell) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (H₀ * ell) := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp only [H₀]
        have : 1 ≤ ell := hell
        nlinarith
  have hnPow' : n + 1 ≤ 2 ^ (H₀ * ell) := by
    exact hnPow.trans (Nat.pow_le_pow_right (by omega) (by
      dsimp only [H₀]
      have : 1 ≤ ell := hell
      nlinarith))
  have hmax : max (n + 1)
      (PreprocessingBilu.scaleDyadicFold horizonFactor s) ≤
        2 ^ (H₀ * ell) := max_le hnPow' hfoldPow
  have hlog : Nat.log 2
      (max (n + 1) (PreprocessingBilu.scaleDyadicFold horizonFactor s)) ≤
        H₀ * ell := by
    calc
      Nat.log 2
          (max (n + 1) (PreprocessingBilu.scaleDyadicFold horizonFactor s)) ≤
          Nat.log 2 (2 ^ (H₀ * ell)) := Nat.log_mono_right hmax
      _ = H₀ * ell := Nat.log_pow Nat.one_lt_two _
  have hH : H = H₀ + 1 := by
    dsimp only [H, H₀]
  calc
    Nat.log 2
          (max (n + 1)
            (PreprocessingBilu.scaleDyadicFold horizonFactor s)) + 1 ≤
        H₀ * ell + 1 := Nat.add_le_add_right hlog 1
    _ ≤ H₀ * ell + ell := by omega
    _ = H * ell := by rw [hH]; ring

/-- Rounding a positive source scale up to a power of two preserves the
source-polynomial ambient endpoint. -/
theorem ceilDyadicAmbient_bounds
    {n s sourceScale D : ℕ} (hs : 0 < s) (hsource : 0 < sourceScale)
    (hsourceLe : sourceScale ≤ s) (hD : 3 ≤ D)
    (hn : n ≤ s ^ (D - 2)) :
    let fold := 2 ^ Nat.clog 2 sourceScale
    let N := max (n + 1) fold
    fold ≤ N ∧ N ≤ 2 * s ^ (D - 2) := by
  intro fold N
  have hfold : fold < 2 * sourceScale := by
    simpa only [fold] using
      (PreprocessingBilu.le_two_pow_clog_lt_two_mul hsource).2
  have hsPower : s ≤ s ^ (D - 2) := by
    have hsOne : 1 ≤ s := hs
    have hpow : s ^ 1 ≤ s ^ (D - 2) :=
      Nat.pow_le_pow_right hsOne (by omega)
    simpa only [pow_one] using hpow
  have hnSucc : n + 1 ≤ 2 * s ^ (D - 2) := by
    have hp : 1 ≤ s ^ (D - 2) := Nat.one_le_pow _ _ hs
    omega
  have hfoldBound : fold ≤ 2 * s ^ (D - 2) := by
    calc
      fold ≤ 2 * sourceScale := hfold.le
      _ ≤ 2 * s := Nat.mul_le_mul_left 2 hsourceLe
      _ ≤ 2 * s ^ (D - 2) := Nat.mul_le_mul_left 2 hsPower
  exact ⟨le_max_right _ _, max_le hnSucc hfoldBound⟩

/-- The rounded source-scale ambient endpoint has a uniform logarithmic
bound in the original source cardinality. -/
theorem ceilDyadicAmbient_log_le
    {m n s sourceScale horizonCoefficient : ℕ}
    (hm : 2 ≤ m) (hn : n + 1 ≤ m ^ horizonCoefficient)
    (hs : s ≤ m) (hsource : 0 < sourceScale)
    (hsourceLe : sourceScale ≤ s) :
    Nat.log 2 (max (n + 1) (2 ^ Nat.clog 2 sourceScale)) + 1 ≤
      (horizonCoefficient + 3) * (Nat.log 2 m + 1) := by
  let ell := Nat.log 2 m + 1
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hmPow : m < 2 ^ ell := by
    simpa only [ell] using Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hnPow : n + 1 ≤ 2 ^ (horizonCoefficient * ell) := by
    calc
      n + 1 ≤ m ^ horizonCoefficient := hn
      _ ≤ (2 ^ ell) ^ horizonCoefficient :=
        Nat.pow_le_pow_left hmPow.le _
      _ = 2 ^ (horizonCoefficient * ell) := by
        rw [← pow_mul]
        congr 1
        ring
  have hfold : 2 ^ Nat.clog 2 sourceScale < 2 * sourceScale :=
    (PreprocessingBilu.le_two_pow_clog_lt_two_mul hsource).2
  have hfoldPow : 2 ^ Nat.clog 2 sourceScale ≤ 2 ^ (2 * ell) := by
    calc
      2 ^ Nat.clog 2 sourceScale ≤ 2 * sourceScale := hfold.le
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 (hsourceLe.trans hs)
      _ ≤ 2 * 2 ^ ell :=
        Nat.mul_le_mul_left 2 hmPow.le
      _ = 2 ^ (ell + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * ell) := by
        apply Nat.pow_le_pow_right (by omega)
        omega
  have hmax : max (n + 1) (2 ^ Nat.clog 2 sourceScale) ≤
      2 ^ ((horizonCoefficient + 2) * ell) := by
    apply max_le
    · exact hnPow.trans (Nat.pow_le_pow_right (by omega) (by
        have : 1 ≤ ell := hell
        nlinarith))
    · exact hfoldPow.trans (Nat.pow_le_pow_right (by omega) (by
        have : 1 ≤ ell := hell
        nlinarith))
  have hlog : Nat.log 2
      (max (n + 1) (2 ^ Nat.clog 2 sourceScale)) ≤
        (horizonCoefficient + 2) * ell := by
    calc
      Nat.log 2 (max (n + 1) (2 ^ Nat.clog 2 sourceScale)) ≤
          Nat.log 2 (2 ^ ((horizonCoefficient + 2) * ell)) :=
        Nat.log_mono_right hmax
      _ = (horizonCoefficient + 2) * ell :=
        Nat.log_pow Nat.one_lt_two _
  calc
    Nat.log 2 (max (n + 1) (2 ^ Nat.clog 2 sourceScale)) + 1 ≤
        (horizonCoefficient + 2) * ell + 1 := Nat.add_le_add_right hlog 1
    _ ≤ (horizonCoefficient + 2) * ell + ell := by omega
    _ = (horizonCoefficient + 3) *
        (Nat.log 2 m + 1) := by dsimp only [ell]; ring

/-- The canonical sharp-colouring population cap occupies at most half of
one colour's source scale. -/
theorem colorCap_le_half_colorSourceScale
    {s q C0 : ℕ} (hC0 : 0 < C0) :
    RandomPartition.colorCap s q C0 ≤
      RandomPartition.blockedColorSourceScale s q 1 / 2 := by
  have hden : 2 * (q + 1) ≤ 4 * C0 * (2 * q + 1) := by
    nlinarith
  have hdiv : s / (4 * C0 * (2 * q + 1)) ≤ s / (2 * (q + 1)) := by
    exact Nat.div_le_div (Nat.le_refl s) hden (by positivity)
  simpa only [RandomPartition.colorCap,
    RandomPartition.blockedColorSourceScale, Nat.one_mul,
    Nat.div_div_eq_div_mul, Nat.mul_comm] using hdiv

/-- A fixed density margin and the half-scale cap fit simultaneously in the
per-colour source scale. -/
theorem colorCap_add_le_blockedColorSourceScale
    {s q C0 density : ℕ} (hC0 : 0 < C0)
    (hdensity : 2 * density ≤
      RandomPartition.blockedColorSourceScale s q 1) :
    RandomPartition.colorCap s q C0 + density ≤
      RandomPartition.blockedColorSourceScale s q 1 := by
  have hcap := colorCap_le_half_colorSourceScale (s := s) (q := q) hC0
  have hdensityHalf : density ≤
      RandomPartition.blockedColorSourceScale s q 1 / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    simpa only [Nat.mul_comm] using hdensity
  have htwice : 2 *
      (RandomPartition.blockedColorSourceScale s q 1 / 2) ≤
        RandomPartition.blockedColorSourceScale s q 1 := by
    simpa only [Nat.mul_comm] using
      Nat.div_mul_le_self (RandomPartition.blockedColorSourceScale s q 1) 2
  omega

/-- The dyadic ceiling of the per-colour source scale is controlled by the
terminal level selected a fixed factor farther down. -/
theorem ceilColorSourceScale_le_terminal
    {s q terminalBase : ℕ} (hs : 0 < s) (hbase : 0 < terminalBase)
    (hlog : Nat.clog 2 ((q + 1) * terminalBase) ≤ Nat.log 2 s) :
    2 ^ Nat.clog 2 (RandomPartition.blockedColorSourceScale s q 1) ≤
      (8 * terminalBase) *
        2 ^ dyadicTerminalBelow s ((q + 1) * terminalBase) := by
  let sourceScale := RandomPartition.blockedColorSourceScale s q 1
  let terminal := dyadicTerminalBelow s ((q + 1) * terminalBase)
  have hsource : 0 < sourceScale := by
    have hden : q + 1 ≤ s := by
      have hdivisor : (q + 1) * terminalBase ≤ s := by
        calc
          (q + 1) * terminalBase ≤
              2 ^ Nat.clog 2 ((q + 1) * terminalBase) :=
            (PreprocessingBilu.le_two_pow_clog_lt_two_mul
              (Nat.mul_pos (by omega) hbase)).1
          _ ≤ 2 ^ Nat.log 2 s := Nat.pow_le_pow_right (by omega) hlog
          _ ≤ s := Nat.pow_log_le_self 2 (Nat.ne_of_gt hs)
      exact (Nat.le_mul_of_pos_right (q + 1) hbase).trans hdivisor
    dsimp only [sourceScale, RandomPartition.blockedColorSourceScale]
    simpa only [Nat.one_mul] using Nat.div_pos hden (by omega : 0 < q + 1)
  have hceil : 2 ^ Nat.clog 2 sourceScale < 2 * sourceScale :=
    (PreprocessingBilu.le_two_pow_clog_lt_two_mul hsource).2
  have hwindow := (dyadicTerminalBelow_window hs
    (Nat.mul_pos (by omega) hbase) hlog).2
  have hsourceUpper : sourceScale < 4 * terminalBase * 2 ^ terminal := by
    dsimp only [sourceScale, RandomPartition.blockedColorSourceScale]
    simp only [Nat.one_mul]
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)]
    calc
      s < 4 * ((q + 1) * terminalBase) * 2 ^ terminal := by
        simpa only [terminal] using hwindow
      _ = (4 * terminalBase * 2 ^ terminal) * (q + 1) := by ring
  calc
    2 ^ Nat.clog 2
        (RandomPartition.blockedColorSourceScale s q 1) ≤
        2 * sourceScale := by simpa only [sourceScale] using hceil.le
    _ ≤ 2 * (4 * terminalBase * 2 ^ terminal) :=
      Nat.mul_le_mul_left 2 hsourceUpper.le
    _ = (8 * terminalBase) *
        2 ^ dyadicTerminalBelow s ((q + 1) * terminalBase) := by
      dsimp only [terminal]
      ring

/-- The concrete centered projected reserve construction supplies the last
remaining large-input coverage proposition. -/
theorem uniformCenteredLargeInputLogLossCoverage :
    UniformCenteredLargeInputLogLossCoverage := by
  intro D first horizonFactor propernessDenominator _C0 horizonCoefficient
    eta hD hfirst hhorizonFactor hpropernessDenominator _hC0
    hhorizonCoefficient heta heta1
  let preprocessingScaleDen :=
    PreprocessingBilu.preprocessingScaleDen propernessDenominator
  let robustDen :=
    PreprocessingBilu.preprocessingRobustnessDenominator D
      propernessDenominator
  let ratio := Greedy.stableDyadicRatio D preprocessingScaleDen
  let terminalBase := 4096 * robustDen * ratio + 1
  let M := 8 * terminalBase
  have hrobustDen : 0 < robustDen := by
    dsimp only [robustDen,
      PreprocessingBilu.preprocessingRobustnessDenominator]
    omega
  have hratio : 0 < ratio := Greedy.stableDyadicRatio_pos _ _
  have hterminalBase : 0 < terminalBase := by
    dsimp only [terminalBase]
    omega
  have hterminalBaseLarge : 4096 * robustDen * ratio ≤ terminalBase := by
    dsimp only [terminalBase]
    omega
  obtain ⟨corWidthMax, denseMax, denseEllMax, denseWidthMax,
      hdenseMax, hcertificate⟩ :=
    RandomPartition.exists_uniform_centeredActiveProjectedDyadicDataCertificateConstants
      D M propernessDenominator hpropernessDenominator
  let q := max denseMax denseEllMax
  have hq : 0 < q := hdenseMax.trans_le (le_max_left _ _)
  have hdenseMaxQ : denseMax ≤ q + 1 :=
    (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hdenseEllMaxQ : denseEllMax ≤ q + 1 :=
    (le_max_right _ _).trans (Nat.le_add_right _ _)
  let H := horizonCoefficient + 3
  let densityDen := rankFlexiblePhysicalDensityDenominator D M
    preprocessingScaleDen
  let comparison := rankFlexiblePhysicalComparisonCoefficient D M
    preprocessingScaleDen
  let baseScaleDen := (4 * denseMax) *
    ProjectedProperization.projectionFactor D
  let finalScaleDen := max baseScaleDen (4 * (6 * D * H + 2))
  let preprocessingLossCoefficient := 6 * D * H + 1
  let smallLossCoefficient := D * Nat.log 2
    (4 * (6 * preprocessingScaleDen) ^ D *
      (4 * preprocessingScaleDen) ^ D) + 2
  let lossCoefficient := preprocessingLossCoefficient + smallLossCoefficient
  let offset := Nat.clog 2 horizonFactor
  let lastRequirement :=
    (2 * D + 1) * first + 2 * horizonFactor * (D - 1)
  let indexBound :=
    PreprocessingBilu.preprocessingIndexBound D propernessDenominator
  let minimumLevel := offset + first + lastRequirement + indexBound + D + 1
  obtain ⟨lowCoefficient, crossingCutoff, hlowCoefficient,
      hcrossingCutoff, hcrossing⟩ :=
    exists_cutoff_projectedDyadicCrossing q robustDen ratio H minimumLevel
      terminalBase eta hrobustDen hterminalBase hterminalBaseLarge heta
  obtain ⟨capacityCutoff, hcapacityCutoff, hcapacity⟩ :=
    RandomPartition.exists_cutoff_sharpColorCapacity_of_le q robustDen
      (RandomPartition.obstaclePolynomialExponent D) H eta hq hrobustDen heta
  let scaleK := max (max corWidthMax denseWidthMax)
    (max (2 * densityDen)
      (max comparison (ProjectedProperization.projectionFactor D)))
  let scaleCutoff := projectedBlockedColorSourceScaleCutoff q 1 scaleK
  let horizonK :=
    2 * (2 * lowCoefficient * 2 ^ offset) ^ (D - 1)
  let largeK := max scaleCutoff horizonK
  obtain ⟨largeCutoff, hlargeCutoff, hlarge⟩ :=
    exists_cutoff_logPolynomial_le_rpow eta heta largeK (D - 1)
  let cutoff := max crossingCutoff (max capacityCutoff largeCutoff)
  have hcutoff : 2 ≤ cutoff := by
    exact hcrossingCutoff.trans
      (le_max_left crossingCutoff (max capacityCutoff largeCutoff))
  have hbaseScaleDen : 0 < baseScaleDen := by
    dsimp only [baseScaleDen]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hdenseMax)
      (ProjectedProperization.projectionFactor_pos D)
  have hfinalScaleDen : 0 < finalScaleDen :=
    hbaseScaleDen.trans_le (le_max_left _ _)
  have hlossCoefficient : 0 < lossCoefficient := by
    dsimp only [lossCoefficient, preprocessingLossCoefficient]
    omega
  refine ⟨1, finalScaleDen, lossCoefficient, cutoff, by omega,
    hfinalScaleDen, by omega, hlossCoefficient, hcutoff, ?_⟩
  intro A n s hA hcutoffA hAinterval hnCard hnScale hslow hscale hproducer
  let m := A.card
  let ell := Nat.log 2 m + 1
  have hmTwo : 2 ≤ m := by
    exact hcutoff.trans hcutoffA
  have hmPos : 0 < m := by omega
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hsCard : s ≤ m := by
    apply scale_le_card_of_fixedScaleInequality hmTwo hfinalScaleDen
    simpa only [m, Nat.cast_one, one_mul] using hscale
  have hlargeInput : largeK * ell ^ (D - 1) ≤ s := by
    have hreal : ((largeK * ell ^ (D - 1) : ℕ) : ℝ) ≤ (s : ℝ) := by
      calc
        ((largeK * ell ^ (D - 1) : ℕ) : ℝ) =
            ((largeK * (Nat.log 2 m + 1) ^ (D - 1) : ℕ) : ℝ) := by
          simp only [ell]
        _ ≤ Real.rpow (m : ℝ) eta := hlarge
          ((le_max_right capacityCutoff largeCutoff).trans
            ((le_max_right crossingCutoff
              (max capacityCutoff largeCutoff)).trans hcutoffA))
        _ ≤ (s : ℝ) := by simpa only [m] using hslow
    exact_mod_cast hreal
  have hsPos : 0 < s := by
    have hscaleCutoffPos : 0 < scaleCutoff := by
      dsimp only [scaleCutoff, projectedBlockedColorSourceScaleCutoff]
      have : 0 < 2 * 1 * (q + 1) := by positivity
      exact this.trans_le (le_max_left _ _)
    have hscaleCutoffLe : scaleCutoff ≤ s := by
      calc
        scaleCutoff ≤ largeK := le_max_left _ _
        _ ≤ largeK * ell ^ (D - 1) := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left largeK
            (Nat.one_le_pow _ _ (by omega : 1 ≤ ell))
        _ ≤ s := hlargeInput
    exact hscaleCutoffPos.trans_le hscaleCutoffLe
  have hzeroA : 0 ∉ A := by
    intro hz
    have := hAinterval hz
    simp only [Finset.mem_Icc] at this
    omega
  have hscaleCutoffLe : scaleCutoff ≤ s := by
    calc
      scaleCutoff ≤ largeK := le_max_left _ _
      _ ≤ largeK * ell ^ (D - 1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left largeK
          (Nat.one_le_pow _ _ (by omega : 1 ≤ ell))
      _ ≤ s := hlargeInput
  have hscaleBounds := projectedBlockedColorSourceScale_bounds
    (q := q) (block := 1) (denseConstant := denseMax) (D := D)
    (K := scaleK) (s := s) (by omega) hdenseMax hdenseMaxQ
    (by
      exact (le_max_right comparison
        (ProjectedProperization.projectionFactor D)).trans
          ((le_max_right (2 * densityDen)
            (max comparison (ProjectedProperization.projectionFactor D))).trans
              (le_max_right (max corWidthMax denseWidthMax)
                (max (2 * densityDen)
                  (max comparison
                    (ProjectedProperization.projectionFactor D))))))
    hscaleCutoffLe
  let sourceScale := RandomPartition.blockedColorSourceScale s q 1
  let globalLevel := Nat.clog 2 sourceScale
  let fold := 2 ^ globalLevel
  let N := max (n + 1) fold
  let low := dyadicLevelBelow s (lowCoefficient * ell)
  let terminal := dyadicTerminalBelow s ((q + 1) * terminalBase)
  have hsourceScale : 0 < sourceScale := by
    simpa only [sourceScale] using hscaleBounds.1
  have hsourceScaleLe : sourceScale ≤ s := by
    calc
      sourceScale ≤ (q + 1) * sourceScale := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right sourceScale (show 1 ≤ q + 1 by omega)
      _ ≤ s := by
        simpa only [sourceScale] using hscaleBounds.2.2.2.2.1
  have hfoldBounds := ceilDyadicAmbient_bounds hsPos hsourceScale
    hsourceScaleLe hD hnScale
  have hfoldN : fold ≤ N := by simpa only [fold, N, globalLevel] using hfoldBounds.1
  have hNPower : N ≤ 2 * s ^ (D - 2) := by
    simpa only [fold, N, globalLevel] using hfoldBounds.2
  have hlogN : Nat.log 2 N + 1 ≤ H * ell := by
    simpa only [N, fold, globalLevel, H, ell, m] using
      (ceilDyadicAmbient_log_le hmTwo hnCard hsCard hsourceScale
        hsourceScaleLe)
  have hcross := hcrossing
    ((le_max_left crossingCutoff (max capacityCutoff largeCutoff)).trans
      hcutoffA) hlogN (by simpa only [m] using hslow) hsCard
  have hminimumLow : minimumLevel ≤ low := by
    simpa only [low, ell] using hcross.1
  have hlowTerminal : low < terminal := by
    simpa only [low, terminal, ell] using hcross.2.1
  have hcrossNumeric :
      2 ^ (low + 1) * (Nat.log 2 (2 ^ low * N + 1) + 1) +
          16 * ratio * 2 ^ terminal + 1 <
        RandomPartition.colorCap s q robustDen := by
    simpa only [low, terminal, ell] using hcross.2.2
  have hterminalPos : 0 < terminal := (Nat.zero_le low).trans_lt hlowTerminal
  have hterminalLog : Nat.clog 2 ((q + 1) * terminalBase) ≤
      Nat.log 2 s := by
    dsimp only [terminal, dyadicTerminalBelow] at hterminalPos
    omega
  have hlowDivisor : 0 < lowCoefficient * ell :=
    Nat.mul_pos hlowCoefficient hell
  have hlowPos : 0 < low := by
    have hminimumPos : 0 < minimumLevel := by
      dsimp only [minimumLevel]
      omega
    exact hminimumPos.trans_le hminimumLow
  have hlowLog : Nat.log 2 (lowCoefficient * ell) ≤ Nat.log 2 s := by
    dsimp only [low, dyadicLevelBelow] at hlowPos
    omega
  have hsourceFold : sourceScale ≤ fold := by
    simpa only [fold, globalLevel] using
      (PreprocessingBilu.le_two_pow_clog_lt_two_mul hsourceScale).1
  have hfoldLevel : fold ≤ M * 2 ^ terminal := by
    simpa only [fold, globalLevel, M, terminal] using
      (ceilColorSourceScale_le_terminal hsPos hterminalBase hterminalLog)
  have hterminalScale : 2 ^ terminal ≤ sourceScale := by
    have hterminalWindow :=
      (dyadicTerminalBelow_window hsPos
        (Nat.mul_pos (by omega) hterminalBase) hterminalLog).1
    dsimp only [sourceScale, RandomPartition.blockedColorSourceScale]
    simp only [Nat.one_mul]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < q + 1)]
    calc
      2 ^ terminal * (q + 1) ≤
          ((q + 1) * terminalBase) * 2 ^ terminal := by
        calc
          2 ^ terminal * (q + 1) = (q + 1) * 2 ^ terminal := by ring
          _ ≤ (q + 1) * terminalBase * 2 ^ terminal := by
            exact Nat.mul_le_mul_right _
              (by
                simpa only [Nat.mul_one] using
                  Nat.mul_le_mul_left (q + 1)
                    (show 1 ≤ terminalBase by omega))
          _ = ((q + 1) * terminalBase) * 2 ^ terminal := by ring
      _ ≤ s := by simpa only [terminal] using hterminalWindow
  have hterminalGlobal : terminal ≤ globalLevel := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
    exact hterminalScale.trans hsourceFold
  have hlowGlobal : low ≤ globalLevel := hlowTerminal.le.trans hterminalGlobal
  have hsourceInterval : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (N : ℤ) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have hNpos : 0 < N :=
        (show 0 < n + 1 by omega).trans_le (le_max_left _ _)
      exact ⟨by omega, by exact_mod_cast hNpos⟩
    · have hzBounds := Finset.mem_Icc.mp (hAinterval hz)
      have hnN : n + 1 ≤ N := le_max_left _ _
      have hnNInt : (n : ℤ) < (N : ℤ) := by exact_mod_cast (show n < N by omega)
      exact ⟨by omega, hzBounds.2.trans_lt hnNInt⟩
  have hanchoredInterval : insert 0 A ⊆
      Finset.Icc (0 : ℤ) ((N : ℤ) - 1) := by
    intro z hz
    exact Finset.mem_Icc.mpr ⟨(hsourceInterval z hz).1, by
      have := (hsourceInterval z hz).2
      omega⟩
  have hlowOffset : offset ≤ low := by
    dsimp only [minimumLevel] at hminimumLow
    omega
  have hfirstLow : first < low - offset := by
    dsimp only [minimumLevel] at hminimumLow
    omega
  have hlastLow : lastRequirement < low - offset := by
    dsimp only [minimumLevel] at hminimumLow
    omega
  have hindexLow : indexBound ≤ 2 ^ low := by
    have hindexLevel : indexBound ≤ low := by
      dsimp only [minimumLevel] at hminimumLow
      omega
    exact hindexLevel.trans (PreprocessingBilu.self_le_two_pow low)
  have hNLowPower : N ≤
      (horizonFactor * 2 ^ (low - offset)) ^ (D - 1) := by
    apply dyadicLevelBelow_horizon_power hsPos hlowDivisor
      hhorizonFactor (by omega) hlowLog
    · exact hlowOffset
    · exact hNPower
    · have hhor : horizonK * ell ^ (D - 1) ≤ s := by
        calc
          horizonK * ell ^ (D - 1) ≤ largeK * ell ^ (D - 1) := by
            gcongr
            exact le_max_right _ _
          _ ≤ s := hlargeInput
      convert hhor using 1 <;>
        simp only [horizonK, offset, Nat.mul_pow] <;> ring
  have hwindow : PreprocessingBilu.DyadicRangeWindow N low globalLevel
      first horizonFactor D propernessDenominator := by
    apply PreprocessingBilu.DyadicRangeWindow.of_endpoints hlowOffset
    · simpa only [fold, globalLevel] using hfoldN
    · simpa only [offset] using hNLowPower
    · simpa only [offset] using hfirstLow
    · simpa only [offset, lastRequirement] using hlastLow
    · simpa only [indexBound] using hindexLow
  have hfamilyFull := hproducer hanchoredInterval hwindow
  have hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      (insert 0 A) low terminal D 1 preprocessingScaleDen := by
    intro level hlow hhigh
    exact hfamilyFull level hlow (hhigh.trans hterminalGlobal)
  have hexact : PreprocessingBilu.DyadicSourceHApproximationFamily
      (insert 0 A) fold D 1 preprocessingScaleDen := by
    intro S hS hzeroS hneS
    have hglobal : PreprocessingBilu.DyadicSourceHApproximationFamily
        (insert 0 A) (2 ^ globalLevel) D 1
          (PreprocessingBilu.preprocessingScaleDen
            propernessDenominator) :=
      hfamilyFull globalLevel hlowGlobal le_rfl
    have hresult := hglobal hS hzeroS hneS
    simpa only [fold, preprocessingScaleDen] using hresult
  have hfoldIndex : indexBound ≤ fold := by
    calc
      indexBound ≤ 2 ^ low := hindexLow
      _ ≤ 2 ^ globalLevel := Nat.pow_le_pow_right (by omega) hlowGlobal
      _ = fold := rfl
  let data := Classical.choice
    (Preprocessing.exists_dyadicCenteredPreprocessingData_of_dyadicSourceFamily
      (A := insert 0 A) (stableBudget := s) (D := D) (n := N)
      (propernessDenominator := propernessDenominator) (fold := fold)
      (Finset.mem_insert_self 0 A) hpropernessDenominator hsourceInterval
      hexact hfoldN (by simpa only [indexBound] using hfoldIndex))
  have hdataC0 :
      PreprocessingBilu.preprocessingRobustnessDenominator D
        propernessDenominator = robustDen := rfl
  have hcapacityBound :
      (2 * q + 1) *
          ((RandomPartition.colorCap s q robustDen + 1) +
            (Nat.log 2
              ((N ^ RandomPartition.obstaclePolynomialExponent D + 1) *
                (q + 1)) + 1)) ≤
        s / robustDen + 1 := by
    exact hcapacity
      ((le_max_left capacityCutoff largeCutoff).trans
        ((le_max_right crossingCutoff
          (max capacityCutoff largeCutoff)).trans hcutoffA))
      hlogN (by simpa only [m] using hslow) (Nat.le_refl _)
  have hfinalPopulation : 4 * (6 * D * H + 2) ≤ finalScaleDen :=
    le_max_right _ _
  have hcorePopulation : s + 1 ≤ data.core.card := by
    apply centeredPreprocessingCore_succ_scale_le_card data hzeroA
      hsourceInterval hlogN hmTwo hfinalPopulation
    simpa only [finalScaleDen, m, Nat.cast_one, one_mul] using hscale
  have hpopulation :
      (2 * q + 1) *
          ((RandomPartition.colorCap s q robustDen + 1) +
            (Nat.log 2
              ((N ^ RandomPartition.obstaclePolynomialExponent D + 1) *
                (q + 1)) + 1)) ≤
        data.core.card := by
    exact hcapacityBound.trans ((Nat.add_le_add_right
      (Nat.div_le_self s robustDen) 1).trans hcorePopulation)
  have hcomparison : comparison ≤ fold + 1 := by
    have hcomparisonScale : comparison ≤ sourceScale := by
      calc
        comparison ≤ scaleK := by
          exact (le_max_left comparison
            (ProjectedProperization.projectionFactor D)).trans
              ((le_max_right (2 * densityDen)
                (max comparison
                  (ProjectedProperization.projectionFactor D))).trans
                (le_max_right (max corWidthMax denseWidthMax)
                  (max (2 * densityDen)
                    (max comparison
                      (ProjectedProperization.projectionFactor D)))))
        _ ≤ sourceScale := by simpa only [sourceScale] using hscaleBounds.2.1
    omega
  have hcapStable : RandomPartition.colorCap s q robustDen ≤ 2 * s :=
    (Nat.div_le_self _ _).trans (by omega)
  have hwidth : max corWidthMax denseWidthMax ≤ sourceScale := by
    calc
      max corWidthMax denseWidthMax ≤ scaleK := le_max_left _ _
      _ ≤ sourceScale := by simpa only [sourceScale] using hscaleBounds.2.1
  have hdensity : 2 * densityDen ≤ sourceScale := by
    calc
      2 * densityDen ≤ scaleK :=
        (le_max_left (2 * densityDen)
          (max comparison (ProjectedProperization.projectionFactor D))).trans
            (le_max_right (max corWidthMax denseWidthMax) _)
      _ ≤ sourceScale := by simpa only [sourceScale] using hscaleBounds.2.1
  have hcapSource : RandomPartition.colorCap s q robustDen + densityDen ≤
      sourceScale := by
    simpa only [sourceScale] using
      colorCap_add_le_blockedColorSourceScale hrobustDen hdensity
  have hroom : 2 * 1 * (q + 1) ≤ s := by
    exact (le_max_left _ _).trans hscaleCutoffLe
  have hprojection : ProjectedProperization.projectionFactor D ≤
      sourceScale * ((q + 1) / denseMax) := by
    simpa only [sourceScale] using hscaleBounds.2.2.2.2.2.2
  have hsourceCardLoss : (insert 0 A).card ≤ data.core.card +
      preprocessingLossCoefficient * s * ell := by
    have hpreLoss := preprocessingCardinalityLoss_le_scale_mul_log
      (A := insert 0 A) (n := N) (m := m) (s := s) (D := D)
      (horizonCoefficient := H) (Finset.mem_insert_self 0 A)
      hsourceInterval hlogN
    have hsource := data.source_card_le
    have hsource' : (insert 0 A).card ≤ data.core.card +
        preprocessingCardinalityLoss (insert 0 A) s D := by
      simpa only [preprocessingCardinalityLoss, Nat.add_assoc] using hsource
    exact hsource'.trans (Nat.add_le_add_left hpreLoss _)
  have hcoreSource : data.core ⊆ insert 0 A :=
    data.core_subset_weakCore.trans data.weakCore_subset_source
  rcases data.relevant_nonempty_or_weakCore_small with hrelevant | hsmall
  · obtain ⟨k, hW⟩ := hcertificate data hrelevant hfamily hq
      (by
        have hDLow : D ≤ low := by
          dsimp only [minimumLevel] at hminimumLow
          omega
        have hDfold : D ≤ fold := by
          calc
            D ≤ low := hDLow
            _ ≤ 2 ^ low := PreprocessingBilu.self_le_two_pow low
            _ ≤ fold := by
              exact Nat.pow_le_pow_right (by omega) hlowGlobal
        exact (show 2 ≤ D by omega).trans (hDfold.trans hfoldN))
      (by
        have hDLow : D ≤ low := by
          dsimp only [minimumLevel] at hminimumLow
          omega
        exact hDLow.trans ((PreprocessingBilu.self_le_two_pow low).trans
          ((Nat.pow_le_pow_right (by omega) hlowGlobal).trans hfoldN)))
      hlowTerminal
      (fun h hlow hhigh ↦ hwindow.fold_le_n h hlow
        (hhigh.trans hterminalGlobal))
      (fun h hlow hhigh ↦ hwindow.index_le_fold h hlow
        (hhigh.trans hterminalGlobal)) hsourceInterval
      hcapacityBound hpopulation hcrossNumeric hfoldLevel
      (by simpa only [comparison] using hcomparison) hcapStable (by omega)
      hdenseEllMaxQ hwidth hdenseMaxQ
      (by simpa only [densityDen] using hcapSource) hroom hsourceFold hprojection
    let W₀ := Classical.choice hW
    let W₁ : FixedScaleWitness (Stability.integerPoints data.core) s D k 0
        1 finalScaleDen := W₀.increaseScaleDen
          (by
            simpa only [baseScaleDen, finalScaleDen, Nat.mul_one,
              Nat.mul_assoc] using
              (le_max_left baseScaleDen (4 * (6 * D * H + 2))))
          hfinalScaleDen
    let totalLoss := lossCoefficient * s * ell
    have hlargeSource : (Stability.integerPoints (insert 0 A)).card ≤
        (Stability.integerPoints data.core).card + totalLoss := by
      simp only [Stability.card_integerPoints]
      calc
        (insert 0 A).card ≤ data.core.card +
            preprocessingLossCoefficient * s * ell := hsourceCardLoss
        _ ≤ data.core.card + totalLoss := by
          gcongr
          dsimp only [totalLoss, lossCoefficient]
          exact Nat.mul_le_mul_right ell
            (Nat.mul_le_mul_right s
              (Nat.le_add_right preprocessingLossCoefficient
                smallLossCoefficient))
    refine ⟨k, totalLoss, FixedScaleWitness.nonempty_enlargeSource
      (hW := ⟨W₁⟩) (preprocessingLoss := totalLoss)
      (Stability.integerPoints_mono hcoreSource) hlargeSource, ?_⟩
    exact Nat.le_refl _
  · let smallLoss := smallLossCoefficient * s * ell
    have hcoreSmall : data.core.card ≤ smallLoss := by
      dsimp only [smallLoss, smallLossCoefficient]
      exact smallDyadicPreprocessingCore_card_le_logLoss data hsmall hsPos hell
    let W₀ : FixedScaleWitness (Stability.integerPoints data.core) s D s
        smallLoss 1 finalScaleDen :=
      discardAllFixedScaleWitness _ s D smallLoss 1 finalScaleDen hsPos
        (by omega) hfinalScaleDen (by omega)
        (by simpa only [Stability.card_integerPoints] using hcoreSmall)
    let preprocessingLoss := preprocessingLossCoefficient * s * ell
    let totalLoss := lossCoefficient * s * ell
    have htotal : preprocessingLoss + smallLoss = totalLoss := by
      dsimp only [preprocessingLoss, smallLoss, totalLoss, lossCoefficient]
      ring
    have hlargeSource : (Stability.integerPoints (insert 0 A)).card ≤
        (Stability.integerPoints data.core).card + preprocessingLoss := by
      simpa only [Stability.card_integerPoints, preprocessingLoss] using
        hsourceCardLoss
    let W₁ := W₀.enlargeSource (Stability.integerPoints_mono hcoreSource)
      hlargeSource
    refine ⟨s, totalLoss, ?_, Nat.le_refl _⟩
    rw [← htotal]
    exact ⟨W₁⟩

end

end Erdos186.CFP

#print axioms Erdos186.CFP.scale_le_card_of_fixedScaleInequality
#print axioms Erdos186.CFP.scaleDyadicAmbient_log_le
#print axioms Erdos186.CFP.ceilDyadicAmbient_bounds
#print axioms Erdos186.CFP.ceilDyadicAmbient_log_le
#print axioms Erdos186.CFP.colorCap_le_half_colorSourceScale
#print axioms Erdos186.CFP.colorCap_add_le_blockedColorSourceScale
#print axioms Erdos186.CFP.ceilColorSourceScale_le_terminal
#print axioms Erdos186.CFP.uniformCenteredLargeInputLogLossCoverage
