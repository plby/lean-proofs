import ErdosProblems.Erdos1038.HighKPlatformCertificateReduction
import ErdosProblems.Erdos1038.HighKPlatformGlobalCrossingRestriction
import ErdosProblems.Erdos1038.HighKTerminalCalibrationAssembly

/-!
# Assembly interfaces for the complete numerical high-k cover

The first two certificate families use the globally selected affine and
constant crossing branches.  The terminal family is stated directly as an
explicit calibrated platform.  Elementary rational case splitting then
produces the numerical half of the final high-k certificate.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

open HighKPlatformFormula
open HighKPlatformGlobalCrossingProbes
open HighKPlatformGlobalCrossingCertificates
open HighKPlatformGlobalCrossingRestriction

/-- Completed 264-slab affine scalar certificate on the global crossings. -/
def HighKAffineGlobalCalibrationCertificate : Prop :=
  ∀ k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
    PlatformAffineCalibration k (highKPlatformEdge .affine k)
      (affineCrossingPair.xMinus k) (affineCrossingPair.xPlus k)
      (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
        (affineCrossingPair.xMinus k))
      (1 / platformExteriorWx k (highKPlatformEdge .affine k)
        (affineCrossingPair.xPlus k))
      (platformEffectiveConstant L k (highKPlatformEdge .affine k)
        (affineCrossingPair.xMinus k) (affineCrossingPair.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (affineCrossingPair.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (affineCrossingPair.xPlus k)))

/-- Completed 840-slab constant-edge scalar certificate on the global
crossings. -/
def HighKConstantGlobalCalibrationCertificate : Prop :=
  ∀ k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ),
    PlatformConstantEdgeCalibration k (highKPlatformEdge .constant k)
      (constantCrossingPair.xMinus k) (constantCrossingPair.xPlus k)
      (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
        (constantCrossingPair.xMinus k))
      (1 / platformExteriorWx k (highKPlatformEdge .constant k)
        (constantCrossingPair.xPlus k))
      (platformEffectiveConstant L k (highKPlatformEdge .constant k)
        (constantCrossingPair.xMinus k) (constantCrossingPair.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantCrossingPair.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantCrossingPair.xPlus k)))

/-- Terminal numerical cover, beginning strictly beyond the endpoint already
included in the constant-edge range. -/
def HighKTerminalExplicitCalibrationCover : Prop :=
  ∀ k : ℝ, 21 / 5 < k →
    ∃ (platformA xMinus xPlus : ℝ)
      (_hk : 1 ≤ k) (_ha : 0 < platformA)
      (_ha1 : 1 ≤ platformA) (_ha2 : platformA < 2)
      (_hthreshold : platformThreshold k ≤ platformA),
      PlatformExplicitExteriorCrossingCertificate
          k platformA xMinus xPlus ∧
        PlatformEffectiveCalibration k platformA xMinus xPlus
          (-1 / platformExteriorWx k platformA xMinus)
          (1 / platformExteriorWx k platformA xPlus)

/-- Surjectivity of the decreasing terminal ratio parametrization over the
range not already assigned to the constant-edge cover. -/
def HighKTerminalRatioCover : Prop :=
  ∀ k : ℝ, 21 / 5 < k →
    ∃ q : ℝ, 0 < q ∧ q < qSoft ∧ terminalPlatformRatio q = k

/-- Numerical content of the terminal charts after all exact terminal
algebra has been removed: positivity of one explicit circle base. -/
def HighKTerminalBaseCertificate : Prop :=
  ∀ (q : ℝ) (_hq : 0 < q) (_hqs : q < qSoft)
    (_hk : 21 / 5 < terminalPlatformRatio q),
    0 < circleRectangleBase
      (platformCapacity (terminalPlatformEdge q))
      (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
      (platformBPi (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
      (platformReferenceCircleRadiusCap
        (terminalPlatformRatio q) (terminalPlatformEdge q))
      (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))

/-- The terminal ratio cover and scalar charts give the terminal branch of
the explicit platform cover. -/
theorem highKTerminalExplicitCalibrationCover_of_ratio_and_base
    (hratio : HighKTerminalRatioCover)
    (hbase : HighKTerminalBaseCertificate) :
    HighKTerminalExplicitCalibrationCover := by
  intro k hkHigh
  rcases hratio k hkHigh with ⟨q, hq, hqs, hratioEq⟩
  have hparams := terminalPlatform_parameters hq hqs
  have hkTerminal : 1 ≤ terminalPlatformRatio q := by
    rw [hratioEq]
    linarith
  have hcalibration := terminalPlatform_effectiveCalibration_of_base_pos
    hq hqs hkTerminal (hbase q hq hqs (by simpa [hratioEq] using! hkHigh))
  refine ⟨terminalPlatformEdge q, terminalPlatformXMinus q,
    terminalPlatformXPlus q, ?_, hparams.2.1,
    one_le_terminalPlatformEdge hq hqs, hparams.2.2.1, ?_, ?_, ?_⟩
  · rw [← hratioEq]
    exact hkTerminal
  · rw [← hratioEq]
    exact hparams.2.2.2
  · simpa only [← hratioEq] using!
      terminalPlatform_explicitCrossingCertificate hq hqs
  · simpa only [← hratioEq, terminalPlatformSigmaMinus,
      terminalPlatformSigmaPlus] using! hcalibration

/-- The three exhaustive numerical regimes give the explicit platform cover
consumed by the final reduction. -/
theorem highKExplicitPlatformCalibrationCover_of_regimes
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hconstant : HighKConstantGlobalCalibrationCertificate)
    (hterminal : HighKTerminalExplicitCalibrationCover) :
    HighKExplicitPlatformCalibrationCover := by
  intro k hkHigh
  by_cases hAffineUpper : k ≤ 21 / 10
  · have hkRange : k ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) := by
      constructor
      · norm_num [affineKBox] at hkHigh ⊢
        linarith
      · simpa [affineKBox] using! hAffineUpper
    let kp : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) := ⟨k, hkRange⟩
    have hstruct := affineHighKPlatformEdge_structural (k := k) (by
      simpa [affineKBox] using! hkRange)
    have ha1 : 1 ≤ highKPlatformEdge .affine k := by
      have hkUpper := hkRange.2
      norm_num [affineKBox, highKPlatformEdge] at hkUpper ⊢
      linarith
    refine ⟨highKPlatformEdge .affine k,
      affineCrossingPair.xMinus kp, affineCrossingPair.xPlus kp,
      hstruct.1, ?_, ha1, ?_, ?_,
      affineCrossingPair_explicitCertificate kp, ?_⟩
    · simpa [highKPlatformEdge, affineHighKPlatformEdge] using! hstruct.2.1
    · simpa [highKPlatformEdge, affineHighKPlatformEdge] using! hstruct.2.2.1
    · simpa [highKPlatformEdge, affineHighKPlatformEdge] using! hstruct.2.2.2
    · exact Or.inl (haffine kp)
  · have hConstantLower : 21 / 10 < k := lt_of_not_ge hAffineUpper
    by_cases hConstantUpper : k ≤ 21 / 5
    · have hkRange : k ∈ Icc
          (constantKBox.lo : ℝ) (constantKBox.hi : ℝ) := by
        constructor
        · simpa [constantKBox] using! hConstantLower.le
        · simpa [constantKBox] using! hConstantUpper
      let kp : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ) :=
        ⟨k, hkRange⟩
      have hstruct := constantHighKPlatformEdge_structural (k := k) (by
        simpa [constantKBox] using! hkRange)
      have ha1 : 1 ≤ highKPlatformEdge .constant k := by
        norm_num [highKPlatformEdge]
      refine ⟨highKPlatformEdge .constant k,
        constantCrossingPair.xMinus kp, constantCrossingPair.xPlus kp,
        hstruct.1, ?_, ha1, ?_, ?_,
        constantCrossingPair_explicitCertificate kp, ?_⟩
      · norm_num [highKPlatformEdge]
      · norm_num [highKPlatformEdge]
      · simpa [highKPlatformEdge, constantHighKPlatformEdge] using! hstruct.2.2.2
      · exact Or.inr (Or.inl (hconstant kp))
    · exact hterminal k (lt_of_not_ge hConstantUpper)

/-- The exact parameter-free theorem from the four complete numerical
regime certificates and the single configuration-uniform analytic
finite-jump certificate.  This is the final checker-facing reduction: once
the five arguments below are unconditional the proof of `MainTheorem` is
unconditional as well. -/
theorem mainTheorem_of_completePlatformRegimeCertificates
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hconstant : HighKConstantGlobalCalibrationCertificate)
    (hterminalRatio : HighKTerminalRatioCover)
    (hterminalBase : HighKTerminalBaseCertificate)
    (hfiniteJump : PlatformResidualMaterialUniformFiniteJumpCertificate) :
    MainTheorem := by
  apply mainTheorem_of_explicitPlatformCover_and_uniformFiniteJump
  · exact highKExplicitPlatformCalibrationCover_of_regimes haffine hconstant
      (highKTerminalExplicitCalibrationCover_of_ratio_and_base
        hterminalRatio hterminalBase)
  · exact hfiniteJump

/-- The finite-jump component of the complete regime reduction is now
unconditional; only the four scalar/numerical regime certificates remain. -/
theorem mainTheorem_of_completePlatformRegimes
    (haffine : HighKAffineGlobalCalibrationCertificate)
    (hconstant : HighKConstantGlobalCalibrationCertificate)
    (hterminalRatio : HighKTerminalRatioCover)
    (hterminalBase : HighKTerminalBaseCertificate) :
    MainTheorem := by
  apply mainTheorem_of_explicitPlatformCover
  exact highKExplicitPlatformCalibrationCover_of_regimes haffine hconstant
    (highKTerminalExplicitCalibrationCover_of_ratio_and_base
      hterminalRatio hterminalBase)

end

end Erdos1038
