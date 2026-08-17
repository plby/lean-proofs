/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AugmentationScales

/-!
# Staged outer coefficient choice

The deletion coefficient must be available before the inner augmentation
constants are chosen, while the outer window coefficient has to be chosen
after the inner partial-exposure gap is known.  Finally, the separation
coefficient is chosen only after the inner window radius is known.  This file
implements precisely that dependency order.

The key compatibility point is that a very small outer step does not force a
failure of the packing inequality.  If `s = smallStepCoeff K eta` and
`P = 512 * cW * sqrt (2 * c₀)`, we choose `sigmaCoeff = P / s`; hence
`s * sigmaCoeff = P` exactly.  The early choice makes `P` a small fixed
fraction of the motion budget.
-/

namespace Erdos636.AugmentationOuterConstants

noncomputable section

/-- Constants fixed before the inner partial-exposure gap is known.  In
particular, this structure contains no `eta`, `sigmaCoeff`, or radius
coefficient. -/
structure EarlyOuterCoefficientChoice
    (K : ℕ) (cW c aDisc bStruct : ℝ) where
  c₀ : ℝ
  lambdaCoeff : ℝ
  matchingCoeff : ℝ
  c₀_pos : 0 < c₀
  c₀_small : 6 * c₀ ≤ c
  lambdaCoeff_pos : 0 < lambdaCoeff
  matchingCoeff_pos : 0 < matchingCoeff
  matchingCoeff_eq : matchingCoeff = bStruct
  matchingCoeff_le : matchingCoeff ≤ bStruct
  endpointReserve :
    lambdaCoeff + c₀ * K * cW * Real.sqrt (2 * c₀) ≤ aDisc
  packingReserve :
    512 * cW * Real.sqrt (2 * c₀) ≤ lambdaCoeff / 4

/-- Choose the deletion, endpoint, and packing reserves before any outer
window size is specified. -/
theorem exists_earlyOuterCoefficientChoice
    {K : ℕ} {cW c aDisc bStruct : ℝ}
    (hK : 0 < K) (hcW : 0 < cW) (hc : 0 < c)
    (haDisc : 0 < aDisc) (hbStruct : 0 < bStruct) :
    Nonempty (EarlyOuterCoefficientChoice K cW c aDisc bStruct) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let lambdaCoeff : ℝ := aDisc / 2
  have hlambda : 0 < lambdaCoeff := by dsimp [lambdaCoeff]; positivity
  let T : ℝ := min (aDisc / (4096 * cW))
    (aDisc / (2 * K * cW))
  have hTleft : 0 < aDisc / (4096 * cW) := by positivity
  have hTright : 0 < aDisc / (2 * K * cW) := by positivity
  have hT : 0 < T := by
    dsimp only [T]
    exact lt_min hTleft hTright
  let c₀ : ℝ := min (c / 6) (min 1 (T ^ 2 / 2))
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hc₀c : c₀ ≤ c / 6 := by
    dsimp only [c₀]
    exact min_le_left _ _
  have hc₀one : c₀ ≤ 1 := by
    dsimp only [c₀]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hc₀T : c₀ ≤ T ^ 2 / 2 := by
    dsimp only [c₀]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsqrtT : Real.sqrt (2 * c₀) ≤ T := by
    rw [Real.sqrt_le_iff]
    exact ⟨hT.le, by nlinarith⟩
  have hTpacking : T ≤ aDisc / (4096 * cW) := by
    dsimp only [T]
    exact min_le_left _ _
  have hTendpoint : T ≤ aDisc / (2 * K * cW) := by
    dsimp only [T]
    exact min_le_right _ _
  have hpacking : 512 * cW * Real.sqrt (2 * c₀) ≤ aDisc / 8 := by
    calc
      512 * cW * Real.sqrt (2 * c₀) ≤ 512 * cW * T := by gcongr
      _ ≤ 512 * cW * (aDisc / (4096 * cW)) := by gcongr
      _ = aDisc / 8 := by field_simp; norm_num
  have hsqrtEndpoint : (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤
      aDisc / 2 := by
    calc
      (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤ (K : ℝ) * cW * T := by
        gcongr
      _ ≤ (K : ℝ) * cW * (aDisc / (2 * K * cW)) := by gcongr
      _ = aDisc / 2 := by field_simp
  have hc₀sqrtEndpoint :
      c₀ * (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤ aDisc / 2 := by
    calc
      c₀ * (K : ℝ) * cW * Real.sqrt (2 * c₀) =
          c₀ * ((K : ℝ) * cW * Real.sqrt (2 * c₀)) := by ring
      _ ≤ 1 * ((K : ℝ) * cW * Real.sqrt (2 * c₀)) := by
        exact mul_le_mul_of_nonneg_right hc₀one (by positivity)
      _ ≤ aDisc / 2 := by simpa only [one_mul] using hsqrtEndpoint
  refine ⟨{
    c₀ := c₀
    lambdaCoeff := lambdaCoeff
    matchingCoeff := bStruct
    c₀_pos := hc₀
    c₀_small := by nlinarith [hc₀c]
    lambdaCoeff_pos := hlambda
    matchingCoeff_pos := hbStruct
    matchingCoeff_eq := rfl
    matchingCoeff_le := le_rfl
    endpointReserve := ?_
    packingReserve := ?_ }⟩
  · dsimp only [lambdaCoeff]
    nlinarith [hc₀sqrtEndpoint]
  · dsimp only [lambdaCoeff]
    convert hpacking using 1
    ring

/-- A second-stage choice meeting a prescribed positive outer window
coefficient. -/
structure WindowedOuterCoefficientChoice
    {K : ℕ} {cW c aDisc bStruct : ℝ}
    (A : EarlyOuterCoefficientChoice K cW c aDisc bStruct)
    (windowCoeff : ℝ) where
  outer : AugmentationScales.OuterCoefficientChoice K cW c aDisc 0 bStruct
  c₀_eq : outer.c₀ = A.c₀
  lambdaCoeff_eq : outer.lambdaCoeff = A.lambdaCoeff
  matchingCoeff_eq : outer.matchingCoeff = A.matchingCoeff
  window_cap : outer.eta * Real.sqrt (2 / A.c₀) < windowCoeff

/-- After an arbitrary positive target window coefficient is known, choose
`eta`, `sigmaCoeff`, and the boundary coefficient without changing `c₀`.
The reciprocal choice of `sigmaCoeff` makes the packing product exact. -/
theorem exists_windowedOuterCoefficientChoice
    {K : ℕ} {cW c aDisc bStruct windowCoeff : ℝ}
    (A : EarlyOuterCoefficientChoice K cW c aDisc bStruct)
    (hK : 0 < K) (hcW : 0 < cW) (hc : 0 < c)
    (hwindowCoeff : 0 < windowCoeff) :
    Nonempty (WindowedOuterCoefficientChoice A windowCoeff) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let q : ℝ := Real.sqrt (2 / A.c₀)
  have hq : 0 < q := by
    dsimp only [q]
    exact Real.sqrt_pos.2 (div_pos (by norm_num) A.c₀_pos)
  let P : ℝ := 512 * cW * Real.sqrt (2 * A.c₀)
  have hP : 0 < P := by
    dsimp only [P]
    have hsqrt : 0 < Real.sqrt (2 * A.c₀) :=
      Real.sqrt_pos.2 (mul_pos (by norm_num) A.c₀_pos)
    exact mul_pos (mul_pos (by norm_num) hcW) hsqrt
  let D : ℝ := cW + 4 * c + 2 * K * A.c₀ * Real.sqrt (2 * A.c₀)
  have hD : 0 < D := by
    dsimp only [D]
    have hsqrtNonneg : 0 ≤ Real.sqrt (2 * A.c₀) := Real.sqrt_nonneg _
    have hextra : 0 ≤
        2 * (K : ℝ) * A.c₀ * Real.sqrt (2 * A.c₀) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hKreal.le) A.c₀_pos.le)
        hsqrtNonneg
    nlinarith
  let E : ℝ := cW + 4 * c + A.c₀ * Real.sqrt (2 * A.c₀)
  have hE : 0 < E := by
    dsimp only [E]
    have hextra : 0 ≤ A.c₀ * Real.sqrt (2 * A.c₀) :=
      mul_nonneg A.c₀_pos.le (Real.sqrt_nonneg _)
    nlinarith
  let windowStep : ℝ := windowCoeff / (4 * (1 + 4 * K) * q)
  have hwindowStep : 0 < windowStep := by
    dsimp only [windowStep]
    positivity
  let motionStep : ℝ := A.lambdaCoeff / (8 * D)
  have hmotionStep : 0 < motionStep := by
    dsimp only [motionStep]
    exact div_pos A.lambdaCoeff_pos (mul_pos (by norm_num) hD)
  let s : ℝ := min windowStep motionStep
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min hwindowStep hmotionStep
  have hsWindow : s ≤ windowStep := by
    dsimp only [s]
    exact min_le_left _ _
  have hsMotion : s ≤ motionStep := by
    dsimp only [s]
    exact min_le_right _ _
  let eta : ℝ := 2 * (1 + 4 * K) * s
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hstep : AugmentationScales.smallStepCoeff K eta = s := by
    dsimp only [AugmentationScales.smallStepCoeff, eta]
    have hden : (2 : ℝ) * (1 + 4 * K) ≠ 0 := by positivity
    field_simp
  let boundaryCoeff : ℝ := A.lambdaCoeff / (8 * E)
  have hboundary : 0 < boundaryCoeff := by
    dsimp only [boundaryCoeff]
    exact div_pos A.lambdaCoeff_pos (mul_pos (by norm_num) hE)
  let sigmaCoeff : ℝ := P / s
  have hsigma : 0 < sigmaCoeff := by
    dsimp only [sigmaCoeff]
    positivity
  have hsD : s * D ≤ A.lambdaCoeff / 8 := by
    calc
      s * D ≤ motionStep * D := by gcongr
      _ = A.lambdaCoeff / 8 := by
        dsimp only [motionStep]
        field_simp
  have hEb : E * boundaryCoeff = A.lambdaCoeff / 8 := by
    dsimp only [boundaryCoeff]
    field_simp
  have hsSigma : s * sigmaCoeff = P := by
    dsimp only [sigmaCoeff]
    field_simp
  have hwindow : eta * q < windowCoeff := by
    calc
      eta * q = 2 * (1 + 4 * K) * s * q := by rfl
      _ ≤ 2 * (1 + 4 * K) * windowStep * q := by gcongr
      _ = windowCoeff / 2 := by
        dsimp only [windowStep]
        field_simp
        ring
      _ < windowCoeff := by linarith
  let O : AugmentationScales.OuterCoefficientChoice K cW c aDisc 0
      bStruct := {
    c₀ := A.c₀
    eta := eta
    matchingCoeff := A.matchingCoeff
    boundaryCoeff := boundaryCoeff
    lambdaCoeff := A.lambdaCoeff
    sigmaCoeff := sigmaCoeff
    RCoeff := 1
    c₀_pos := A.c₀_pos
    c₀_small := A.c₀_small
    eta_pos := heta
    matchingCoeff_pos := A.matchingCoeff_pos
    matchingCoeff_eq := A.matchingCoeff_eq
    boundaryCoeff_pos := hboundary
    lambdaCoeff_pos := A.lambdaCoeff_pos
    sigmaCoeff_pos := hsigma
    RCoeff_pos := by norm_num
    endpointCoeff := A.endpointReserve
    motionCoeff := by
      rw [hstep]
      calc
        s * (cW + 4 * c + sigmaCoeff +
              2 * K * A.c₀ * Real.sqrt (2 * A.c₀)) +
            (cW + 4 * c + A.c₀ * Real.sqrt (2 * A.c₀)) *
              boundaryCoeff =
            s * D + s * sigmaCoeff + E * boundaryCoeff := by
              dsimp only [D, E]
              ring
        _ = s * D + P + A.lambdaCoeff / 8 := by
          rw [hsSigma, hEb]
        _ ≤ A.lambdaCoeff / 8 + A.lambdaCoeff / 4 +
            A.lambdaCoeff / 8 := by
          gcongr
          exact A.packingReserve
        _ ≤ A.lambdaCoeff := by linarith [A.lambdaCoeff_pos]
    packingCoeff := by
      rw [hstep]
      change P ≤ s * sigmaCoeff
      rw [hsSigma]
    radiusCoeffSmall := by norm_num }
  refine ⟨{
    outer := O
    c₀_eq := rfl
    lambdaCoeff_eq := rfl
    matchingCoeff_eq := rfl
    window_cap := ?_ }⟩
  simpa only [O, q] using hwindow

namespace WindowedOuterCoefficientChoice

/-- Complete the coefficient choice after the nonnegative radius coefficient
has been obtained from the inner augmentation construction.  No earlier
coefficient changes. -/
def withRadius
    {K : ℕ} {cW c aDisc bStruct windowCoeff radiusCoeff : ℝ}
    {A : EarlyOuterCoefficientChoice K cW c aDisc bStruct}
    (B : WindowedOuterCoefficientChoice A windowCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff) :
    AugmentationScales.OuterCoefficientChoice K cW c aDisc radiusCoeff
      bStruct where
  c₀ := B.outer.c₀
  eta := B.outer.eta
  matchingCoeff := B.outer.matchingCoeff
  boundaryCoeff := B.outer.boundaryCoeff
  lambdaCoeff := B.outer.lambdaCoeff
  sigmaCoeff := B.outer.sigmaCoeff
  RCoeff := 4 * radiusCoeff * B.outer.c₀ + 1
  c₀_pos := B.outer.c₀_pos
  c₀_small := B.outer.c₀_small
  eta_pos := B.outer.eta_pos
  matchingCoeff_pos := B.outer.matchingCoeff_pos
  matchingCoeff_eq := B.outer.matchingCoeff_eq
  boundaryCoeff_pos := B.outer.boundaryCoeff_pos
  lambdaCoeff_pos := B.outer.lambdaCoeff_pos
  sigmaCoeff_pos := B.outer.sigmaCoeff_pos
  RCoeff_pos := by
    have hnonneg : 0 ≤ 4 * radiusCoeff * B.outer.c₀ := by
      exact mul_nonneg (mul_nonneg (by norm_num) hradiusCoeff)
        B.outer.c₀_pos.le
    linarith
  endpointCoeff := B.outer.endpointCoeff
  motionCoeff := B.outer.motionCoeff
  packingCoeff := B.outer.packingCoeff
  radiusCoeffSmall := by linarith

@[simp] lemma withRadius_c₀
    {K : ℕ} {cW c aDisc bStruct windowCoeff radiusCoeff : ℝ}
    {A : EarlyOuterCoefficientChoice K cW c aDisc bStruct}
    (B : WindowedOuterCoefficientChoice A windowCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff) :
    (B.withRadius hradiusCoeff).c₀ = A.c₀ := by
  exact B.c₀_eq

@[simp] lemma withRadius_eta
    {K : ℕ} {cW c aDisc bStruct windowCoeff radiusCoeff : ℝ}
    {A : EarlyOuterCoefficientChoice K cW c aDisc bStruct}
    (B : WindowedOuterCoefficientChoice A windowCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff) :
    (B.withRadius hradiusCoeff).eta = B.outer.eta := rfl

@[simp] lemma withRadius_RCoeff
    {K : ℕ} {cW c aDisc bStruct windowCoeff radiusCoeff : ℝ}
    {A : EarlyOuterCoefficientChoice K cW c aDisc bStruct}
    (B : WindowedOuterCoefficientChoice A windowCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff) :
    (B.withRadius hradiusCoeff).RCoeff =
      4 * radiusCoeff * B.outer.c₀ + 1 := rfl

end WindowedOuterCoefficientChoice

end

end Erdos636.AugmentationOuterConstants
