/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZSourceCorrectFutureTransition
import ErdosProblems.Erdos1165.HLOZSourceCorrectFilteredTransitions
import ErdosProblems.Erdos1165.TerminalParameterBounds
import ErdosProblems.Erdos1165.TerminalExcursionPathwise
import ErdosProblems.Erdos1165.TerminalSequentialVisitLaw

/-!
# The high-spatial factor in HLOZ Proposition 4.7

For a proper mesh gap whose exponent is strictly larger than `κ₂`, the
minimality in `gapScaleOf` puts the two successive creation sites farther
apart than `exp (m^κ₂)`.  Until the new site is created, the old favorite
cannot be revisited: such a visit would create a level-`m+1` site.  Hence the
fresh walk after the old creation must cross a literal disc boundary before
its first positive return.

The final certificate below is atomwise.  Its hypotheses concern only
stopped-past measurability and deterministic containment; its probability
bound is derived from the literal escape probability and strong Markov.
There is no prefix-product screen and no transition-probability premise.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZHighSpatialTransitionFactor

open BoundaryVisitRegeneration HLOZGapStoppedCandidate HLOZPathEvents
open HLOZSourceCorrectFutureTransition PotentialEuclideanGeometry
open HLOZStoppedHistoryCandidateFuture
open HLOZSourceCorrectFilteredTransitions HLOZSpatialAdapter
open StoppedInsertion
open TerminalExcursionPathwise TerminalParameterBounds

noncomputable section

/-- A proper high mesh value is nonzero, and its predecessor exponent is
already at least `κ₂`.  This is where the exact `1/1024` mesh is used. -/
lemma highGapScale_predecessor_exponent
    {a : GapScale} (ha : a ∈ highGapMesh) :
    0 < a.1 ∧
      ScreeningInstantiation.kappaTwo ≤ meshExponent (a.1 - 1) := by
  have halpha := (mem_highGapMesh_iff.mp ha).2
  have haReal : (344 : ℝ) < (a.1 : ℝ) + 1 := by
    norm_num [ScreeningInstantiation.kappaTwo,
      ScreeningInstantiation.meshDelta, meshExponent] at halpha ⊢
    linarith
  have haNat : 344 < a.1 + 1 := by exact_mod_cast haReal
  have hapos : 0 < a.1 := by omega
  refine ⟨hapos, ?_⟩
  have hpred : a.1 - 1 + 1 = a.1 := Nat.sub_add_cancel hapos
  have hpredReal : ((a.1 - 1 : ℕ) : ℝ) + 1 = (a.1 : ℝ) := by
    exact_mod_cast hpred
  norm_num [ScreeningInstantiation.kappaTwo,
    ScreeningInstantiation.meshDelta, meshExponent]
  rw [hpredReal]
  have hcast : (344 : ℝ) ≤ (a.1 : ℝ) := by
    exact_mod_cast (show 344 ≤ a.1 by omega)
  linarith

/-- The lower edge of a proper high mesh cell is beyond
`exp (m^κ₂)`. -/
theorem exp_kappaTwo_lt_latticeDistance_of_highGapScale
    {m : ℕ} {x y : Point} {a : GapScale}
    (hm : 1 ≤ m) (ha : a ∈ highGapMesh)
    (hscale : gapScaleOf m x y = a) :
    Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) <
      latticeDistance x y := by
  have hproper := (mem_highGapMesh_iff.mp ha).1
  have hhas : HasProperGapScale m x y := by
    by_contra hnot
    have hover := (gapScaleOf_eq_overflow_iff m x y).2 hnot
    have hane : a ≠ overflowScale := by
      simpa only [properGapMesh, Finset.mem_erase, Finset.mem_univ,
        and_true] using hproper
    exact hane (hscale.symm.trans hover)
  have hvalue : Nat.find hhas = a.1 := by
    unfold gapScaleOf at hscale
    rw [dif_pos hhas] at hscale
    exact congrArg Fin.val hscale
  have hpred := highGapScale_predecessor_exponent ha
  have hpredLt : a.1 - 1 < Nat.find hhas := by omega
  have hnot := Nat.find_min hhas hpredLt
  have hpredSteps : a.1 - 1 < meshSteps := by
    have hane : a ≠ overflowScale := by
      simpa only [properGapMesh, Finset.mem_erase, Finset.mem_univ,
        and_true] using hproper
    have haBound : a.1 < meshSteps := by
      have halt : a.1 < meshSteps + 1 := a.2
      by_contra hnot
      have hval : a.1 = meshSteps := by omega
      apply hane
      apply Fin.ext
      simpa only [overflowScale] using hval
    omega
  have hdist : meshRadius m (a.1 - 1) < latticeDistance x y := by
    by_contra hle
    apply hnot
    exact ⟨hpredSteps, le_of_not_gt hle⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ ScreeningInstantiation.kappaTwo ≤
      (m : ℝ) ^ meshExponent (a.1 - 1) :=
    Real.rpow_le_rpow_of_exponent_le hmR hpred.2
  exact (Real.exp_le_exp.mpr hpow).trans_lt hdist

/-- Natural radius used for the high-spatial future event.  The factor `1/3`
leaves room for the integer ceiling while retaining the full `m^κ₂`
logarithmic scale. -/
def highSpatialRadius (m : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) / 3)

lemma highSpatialRadius_pos (m : ℕ) : 0 < highSpatialRadius m := by
  unfold highSpatialRadius
  exact Nat.ceil_pos.mpr (by positivity)

lemma highSpatialRadius_cast_lower (m : ℕ) :
    Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) / 3 ≤
      (highSpatialRadius m : ℝ) := by
  exact Nat.le_ceil _

lemma highSpatialRadius_cast_lt_exp {m : ℕ} (hm : 1 ≤ m) :
    (highSpatialRadius m : ℝ) <
      Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) := by
  have hpow : (1 : ℝ) ≤
      (m : ℝ) ^ ScreeningInstantiation.kappaTwo := by
    apply Real.one_le_rpow
    · exact_mod_cast hm
    · norm_num [ScreeningInstantiation.kappaTwo]
  have hexp : Real.exp 1 ≤
      Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) :=
    Real.exp_le_exp.mpr hpow
  have hthree : (3 : ℝ) / 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at this ⊢
    linarith
  have hlarge : (3 : ℝ) / 2 <
      Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) :=
    hthree.trans_le hexp
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) / 3 by
      positivity)
  unfold highSpatialRadius
  exact lt_of_lt_of_le hceil (by linarith)

/-! ## The one-walk potential bound -/

/-- A deliberately coarse universal error for the diagonal killed Green
lower bound.  Its size is irrelevant; only that it is independent of the
level and radius matters. -/
def highSpatialPotentialError : ℝ :=
  13000000002 + PotentialRadialGlobal.globalRadialConstant +
    |PotentialRadialAsymptotic.cPotential|

lemma highSpatialPotentialError_pos : 0 < highSpatialPotentialError := by
  unfold highSpatialPotentialError
  have hg := PotentialRadialGlobal.globalRadialConstant_pos
  have hc := abs_nonneg PotentialRadialAsymptotic.cPotential
  linarith

lemma literalBoundaryError_le_highSpatialShellConstant
    {R : ℕ} (hR : 2 ≤ R) :
    BoundaryStoppedHarnack.literalBoundaryError R ≤ 13000000002 := by
  unfold BoundaryStoppedHarnack.literalBoundaryError
    RadialHarnackSpecialization.euclideanShellError
  have hdenNat : 1 ≤ R - 1 := by omega
  have hden : (1 : ℝ) ≤ (R - 1 : ℕ) := by exact_mod_cast hdenNat
  have hpos : (0 : ℝ) < (R - 1 : ℕ) := zero_lt_one.trans_le hden
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Potential theory in the exact literal-boundary normalization: once the
logarithmic main term dominates the uniform radial errors, escape before the
first positive return is at most `π / log R`. -/
theorem literalEscapeProbability_le_pi_div_log
    {R : ℕ} (hR : 5 ≤ R)
    (hlarge : highSpatialPotentialError ≤
      (1 / Real.pi) * Real.log (R : ℝ)) :
    literalEscapeProbability R ≤ Real.pi / Real.log (R : ℝ) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRone : (1 : ℝ) < R := by exact_mod_cast (show 1 < R by omega)
  have hlogPos : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have haxisNe : TerminalParameterBounds.axisPoint R ≠ (0 : Point) := by
    intro h
    have hfirst := congrArg Prod.fst h
    simp [TerminalParameterBounds.axisPoint] at hfirst
    omega
  have hradial :=
    PotentialRadialGlobal.abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      haxisNe
  rw [TerminalParameterBounds.euclideanRadius_axisPoint] at hradial
  have hboundary := literalBoundaryError_le_highSpatialShellConstant
    (show 2 ≤ R by omega)
  have hgreen :=
    TerminalParameterBounds.abs_infiniteGreen_diagonal_sub_axisPotential_le R hR
  rw [abs_le] at hradial hgreen
  have hradialDiv :
      PotentialRadialGlobal.globalRadialConstant / (R : ℝ) ≤
        PotentialRadialGlobal.globalRadialConstant := by
    rw [div_le_iff₀ hRpos]
    have hnonneg := PotentialRadialGlobal.globalRadialConstant_pos.le
    nlinarith
  have hc : -|PotentialRadialAsymptotic.cPotential| ≤
      PotentialRadialAsymptotic.cPotential := neg_abs_le _
  have hdiagLower :
      (1 / Real.pi) * Real.log (R : ℝ) ≤
        (GreenProbability.infiniteGreen
          (BoundaryStoppedHarnack.boundaryInterior R) 0 0).toReal := by
    have hpotentialLower :
        (2 / Real.pi) * Real.log (R : ℝ) +
            PotentialRadialAsymptotic.cPotential -
              PotentialRadialGlobal.globalRadialConstant / (R : ℝ) ≤
          PotentialConvergence.planarPotentialKernel
            (TerminalParameterBounds.axisPoint R) := by
      linarith [hradial.1]
    have hgreenLower :
        PotentialConvergence.planarPotentialKernel
              (TerminalParameterBounds.axisPoint R) -
            BoundaryStoppedHarnack.literalBoundaryError R ≤
          (GreenProbability.infiniteGreen
            (BoundaryStoppedHarnack.boundaryInterior R) 0 0).toReal := by
      linarith [hgreen.1]
    unfold highSpatialPotentialError at hlarge
    have hpi : 0 < Real.pi := Real.pi_pos
    have htwo : (2 / Real.pi) * Real.log (R : ℝ) =
        2 * ((1 / Real.pi) * Real.log (R : ℝ)) := by ring
    rw [htwo] at hpotentialLower
    linarith
  rw [literalEscapeProbability_eq_inv_infiniteGreen_diagonal R
    (show 3 ≤ R by omega)]
  calc
    ((GreenProbability.infiniteGreen
        (BoundaryStoppedHarnack.boundaryInterior R) 0 0).toReal)⁻¹ ≤
        (((1 / Real.pi) * Real.log (R : ℝ))⁻¹) := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (mul_pos (one_div_pos.mpr Real.pi_pos) hlogPos) hdiagLower
    _ = Real.pi / Real.log (R : ℝ) := by
      field_simp [Real.pi_ne_zero, hlogPos.ne']

/-- The literal high-spatial future has the source `m^{-κ₂}` cost. -/
theorem eventually_literalEscapeProbability_highSpatialRadius_le :
    ∀ᶠ m : ℕ in atTop,
      literalEscapeProbability (highSpatialRadius m) ≤
        2 * Real.pi / (m : ℝ) ^ ScreeningInstantiation.kappaTwo := by
  have hkappa : 0 < ScreeningInstantiation.kappaTwo := by
    norm_num [ScreeningInstantiation.kappaTwo]
  have htend := ScreeningInstantiation.tendsto_nat_rpow_atTop hkappa
  have herror := htend.eventually (eventually_ge_atTop
    (2 * Real.pi * highSpatialPotentialError + Real.log 3))
  have hlogThree := htend.eventually
    (eventually_ge_atTop (2 * Real.log 3))
  have hfive := htend.eventually (eventually_ge_atTop (Real.log 15))
  filter_upwards [herror, hlogThree, hfive, eventually_ge_atTop 1] with
      m herrorM hlogThreeM hfiveM hm
  have hmPowPos : 0 < (m : ℝ) ^ ScreeningInstantiation.kappaTwo := by
    positivity
  have hRlower := highSpatialRadius_cast_lower m
  have hRpos : (0 : ℝ) < highSpatialRadius m := by
    exact_mod_cast highSpatialRadius_pos m
  have hscalePos : 0 <
      Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) / 3 := by positivity
  have hlogLower :
      (m : ℝ) ^ ScreeningInstantiation.kappaTwo - Real.log 3 ≤
        Real.log (highSpatialRadius m : ℝ) := by
    have hlog := Real.log_le_log hscalePos hRlower
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_exp] at hlog
    exact hlog
  have hRfive : 5 ≤ highSpatialRadius m := by
    have hexp15 : (15 : ℝ) ≤
        Real.exp ((m : ℝ) ^ ScreeningInstantiation.kappaTwo) := by
      calc
        (15 : ℝ) = Real.exp (Real.log 15) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 15)]
        _ ≤ _ := Real.exp_le_exp.mpr hfiveM
    have : (5 : ℝ) ≤ (highSpatialRadius m : ℝ) := by
      linarith
    exact_mod_cast this
  have hlarge : highSpatialPotentialError ≤
      (1 / Real.pi) * Real.log (highSpatialRadius m : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfromError : highSpatialPotentialError ≤
        (1 / Real.pi) *
          ((m : ℝ) ^ ScreeningInstantiation.kappaTwo - Real.log 3) := by
      rw [one_div_mul_eq_div, le_div_iff₀ hpi]
      linarith
    exact hfromError.trans
      (mul_le_mul_of_nonneg_left hlogLower (one_div_nonneg.mpr hpi.le))
  have hescape := literalEscapeProbability_le_pi_div_log hRfive hlarge
  have hhalf : (m : ℝ) ^ ScreeningInstantiation.kappaTwo / 2 ≤
      Real.log (highSpatialRadius m : ℝ) := by linarith
  have hhalfPos : 0 < (m : ℝ) ^ ScreeningInstantiation.kappaTwo / 2 := by
    positivity
  calc
    literalEscapeProbability (highSpatialRadius m) ≤
        Real.pi / Real.log (highSpatialRadius m : ℝ) := hescape
    _ ≤ Real.pi /
        ((m : ℝ) ^ ScreeningInstantiation.kappaTwo / 2) := by
      exact div_le_div_of_nonneg_left Real.pi_pos.le hhalfPos hhalf
    _ = 2 * Real.pi /
        (m : ℝ) ^ ScreeningInstantiation.kappaTwo := by field_simp

/-- The sharper `m^{-κ₂}` literal escape estimate fits the canonical
`m^{-κ}` transition envelope (with unit constant) at all sufficiently large
levels. -/
theorem eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m := by
  have hpower := ExternalProposition44.eventually_const_mul_nat_rpow_le
    (4 * Real.pi) ScreeningInstantiation.kappa
      ScreeningInstantiation.kappaTwo (by
        norm_num [ScreeningInstantiation.kappa,
          ScreeningInstantiation.kappaTwo,
          ScreeningInstantiation.meshDelta])
  filter_upwards [eventually_literalEscapeProbability_highSpatialRadius_le,
      hpower, eventually_ge_atTop 1] with m hescape hpowerM hm
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkappaNonneg : 0 ≤ ScreeningInstantiation.kappa := by
    norm_num [ScreeningInstantiation.kappa,
      ScreeningInstantiation.kappaTwo, ScreeningInstantiation.meshDelta]
  have hkappaLeOne : ScreeningInstantiation.kappa ≤ 1 := by
    norm_num [ScreeningInstantiation.kappa,
      ScreeningInstantiation.kappaTwo, ScreeningInstantiation.meshDelta]
  have hbase : (m + 1 : ℝ) ≤ 2 * m := by
    linarith
  have hshiftPow : (m + 1 : ℝ) ^ ScreeningInstantiation.kappa ≤
      2 * (m : ℝ) ^ ScreeningInstantiation.kappa := by
    calc
      (m + 1 : ℝ) ^ ScreeningInstantiation.kappa ≤
          (2 * m : ℝ) ^ ScreeningInstantiation.kappa :=
        Real.rpow_le_rpow (by positivity) hbase hkappaNonneg
      _ = (2 : ℝ) ^ ScreeningInstantiation.kappa *
          (m : ℝ) ^ ScreeningInstantiation.kappa := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmPos.le]
      _ ≤ 2 * (m : ℝ) ^ ScreeningInstantiation.kappa := by
        gcongr
        simpa using
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            hkappaLeOne)
  have hden :
      2 * Real.pi *
          (m + 1 : ℝ) ^ ScreeningInstantiation.kappa ≤
        (m : ℝ) ^ ScreeningInstantiation.kappaTwo := by
    calc
      2 * Real.pi *
          (m + 1 : ℝ) ^ ScreeningInstantiation.kappa ≤
          4 * Real.pi *
            (m : ℝ) ^ ScreeningInstantiation.kappa := by
        nlinarith [Real.pi_pos, Real.rpow_nonneg hmPos.le
          ScreeningInstantiation.kappa]
      _ ≤ (m : ℝ) ^ ScreeningInstantiation.kappaTwo := hpowerM
  have hquotient :
      2 * Real.pi / (m : ℝ) ^ ScreeningInstantiation.kappaTwo ≤
        1 / (m + 1 : ℝ) ^ ScreeningInstantiation.kappa := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hmPos _)
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < m + 1) _)]
    simpa only [one_mul] using hden
  have hreal : literalEscapeProbability (highSpatialRadius m) ≤
      1 / |(m : ℝ) + 1| ^ ScreeningInstantiation.kappa := by
    calc
      literalEscapeProbability (highSpatialRadius m) ≤
          2 * Real.pi / (m : ℝ) ^ ScreeningInstantiation.kappaTwo := hescape
      _ ≤ 1 / (m + 1 : ℝ) ^ ScreeningInstantiation.kappa := hquotient
      _ = 1 / |(m : ℝ) + 1| ^ ScreeningInstantiation.kappa := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  unfold UpperCanonical.hlozTransitionCost UpperAssembly.pSeriesWeight
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The same literal escape estimate fits every canonical envelope whose
constant is at least one. -/
theorem eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost_of_one_le
    (K : ℝ≥0) (hK : 1 ≤ K) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m := by
  filter_upwards
      [eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost]
      with m hm
  refine hm.trans ?_
  unfold UpperCanonical.hlozTransitionCost
  gcongr

/-- Euclidean radius of the translated displacement. -/
lemma euclideanRadius_sub_eq_latticeDistance (x y : Point) :
    euclideanRadius (y - x) = latticeDistance x y := by
  unfold euclideanRadius euclideanRadiusSq latticeDistance
  change Real.sqrt
      ((((y.1 - x.1 : ℤ) : ℝ) ^ 2) + (((y.2 - x.2 : ℤ) : ℝ) ^ 2)) =
    Real.sqrt
      ((((x.1 - y.1 : ℤ) : ℝ) ^ 2) + (((x.2 - y.2 : ℤ) : ℝ) ^ 2))
  congr 1
  push_cast
  ring

/-- A simple random-walk trajectory is nearest-neighbor at every step. -/
lemma trajectory_adjacent (omega : StepPath) (n : ℕ) :
    ThickPoint.Adjacent (trajectory omega n) (trajectory omega (n + 1)) := by
  rw [trajectory_succ]
  unfold ThickPoint.Adjacent
  generalize hd : omega n = d
  fin_cases d <;> simp [directionVector]

/-- The deterministic high-spatial creation step.  Starting at the old
creation clock, the translated walk hits the literal radius
`highSpatialRadius m` boundary before it can return to the old favorite. -/
theorem postStoppingSteps_not_positiveReturnBeforeBoundary_of_high_creation
    {omega : StepPath} {m rank nOld nNew : ℕ} {a : GapScale}
    (hm : 1 ≤ m) (hrank : 0 < rank)
    (hold : ThresholdCreation (trajectory omega) m rank nOld)
    (hnew : ThresholdCreation (trajectory omega) m (rank + 1) nNew)
    (hnext : thresholdCount (trajectory omega) nNew (m + 1) = 0)
    (ha : a ∈ highGapMesh)
    (hscale : gapScaleOf m (trajectory omega nOld)
      (trajectory omega nNew) = a) :
    postStoppingSteps (fun _ : StepPath => nOld) omega ∉
      positiveReturnBeforeBoundary
        (ThickPoint.discBoundary 0 (highSpatialRadius m : ℝ)) := by
  classical
  let tail := postStoppingSteps (fun _ : StepPath => nOld) omega
  let d := nNew - nOld
  have hOldNew : nOld < nNew :=
    creation_time_lt hrank (by omega) (by omega) hold hnew
  have hadd : nOld + d = nNew := Nat.add_sub_of_le hOldNew.le
  have htailZero : trajectory tail 0 = 0 := by simp [tail, postStoppingSteps]
  have htailEnd : trajectory tail d =
      trajectory omega nNew - trajectory omega nOld := by
    dsimp only [tail, postStoppingSteps]
    rw [← trajectory_add_sub_trajectory, hadd]
  have hdist := exp_kappaTwo_lt_latticeDistance_of_highGapScale
    hm ha hscale
  have hout : trajectory tail d ∉
      ThickPoint.disc 0 (highSpatialRadius m : ℝ) := by
    intro hmem
    change latticeDistance 0 (trajectory tail d) ≤
      (highSpatialRadius m : ℝ) at hmem
    have hradius : latticeDistance 0 (trajectory tail d) =
        latticeDistance (trajectory omega nOld) (trajectory omega nNew) := by
      rw [htailEnd]
      unfold latticeDistance
      congr 1
      simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub]
      push_cast
      ring
    rw [hradius] at hmem
    exact (not_lt_of_ge hmem)
      ((highSpatialRadius_cast_lt_exp hm).trans hdist)
  have hin : trajectory tail 0 ∈
      ThickPoint.disc 0 (highSpatialRadius m : ℝ) := by
    rw [htailZero]
    change latticeDistance 0 0 ≤ (highSpatialRadius m : ℝ)
    simp [latticeDistance]
  have hhit : ThickPoint.firstHitThrough (trajectory tail)
      (ThickPoint.discBoundary 0 (highSpatialRadius m : ℝ)) 0 d ≤ d := by
    change ThickPoint.firstHitThrough (trajectory tail)
      (ThickPoint.innerBoundary
        (ThickPoint.disc 0 (highSpatialRadius m : ℝ))) 0 d ≤ d
    apply firstHitThrough_innerBoundary_le_of_exit (trajectory tail)
      (ThickPoint.disc 0 (highSpatialRadius m : ℝ))
      (trajectory_adjacent tail) (Nat.zero_le d) hin hout
  let hit := ThickPoint.firstHitThrough (trajectory tail)
    (ThickPoint.discBoundary 0 (highSpatialRadius m : ℝ)) 0 d
  have hhitMem : trajectory tail hit ∈
      ThickPoint.discBoundary 0 (highSpatialRadius m : ℝ) :=
    ThickPoint.firstHitThrough_mem_set_of_le _ _ _ _ hhit
  have hnoReturn : ∀ q, 0 < q -> q ≤ d -> trajectory tail q ≠ 0 := by
    intro q hq hqd hzero
    have hqOld : nOld < nOld + q := by omega
    have hqNew : nOld + q ≤ nNew := by omega
    have havoid := no_oldCreation_visit_of_no_next_level
      hrank hold hnext (nOld + q) hqOld hqNew
    apply havoid
    have hshift := trajectory_add_sub_trajectory omega nOld q
    dsimp only [tail, postStoppingSteps] at hzero
    rw [hzero] at hshift
    simpa using (sub_eq_zero.mp hshift)
  intro hreturn
  obtain ⟨r, hr, havoidBoundary⟩ := Set.mem_iUnion.mp hreturn
  have hrspec := TerminalSequentialVisitLaw.firstPositiveReturnTime_spec hr
  by_cases hrd : r ≤ d
  · exact hnoReturn r hrspec.1 hrd hrspec.2.1
  · have hdlt : d < r := Nat.lt_of_not_ge hrd
    exact havoidBoundary hit (hhit.trans_lt hdlt) hhitMem

/-! ## Atomwise source-correct high factors -/

/-- The exact stopped-atom input for a high-spatial transition.  The old
creation time is fixed on the atom, so it is an honest finite stopping time.
The `next_creation` field is deterministic path data, not a probability
bound. -/
structure HighCreationAtomData
    (past next : Set WalkPath) (m rank nOld : ℕ) (a : GapScale) where
  rank_pos : 0 < rank
  high_scale : a ∈ highGapMesh
  past_observable : IsMeasurableAtStopping (fun _ : StepPath => nOld)
    (trajectory ⁻¹' past)
  next_creation : ∀ omega, trajectory omega ∈ next →
    trajectory omega ∈ past ∧ ∃ nNew,
      ThresholdCreation (trajectory omega) m rank nOld ∧
      ThresholdCreation (trajectory omega) m (rank + 1) nNew ∧
      thresholdCount (trajectory omega) nNew (m + 1) = 0 ∧
      gapScaleOf m (trajectory omega nOld) (trajectory omega nNew) = a

/-- The fixed threshold-creation atom is measurable in the deterministic
increment filtration at its creation time. -/
lemma measurableSet_trajectory_thresholdCreation_filtration
    (m rank n : ℕ) :
    MeasurableSet[incrementFiltration n]
      {omega : StepPath | ThresholdCreation (trajectory omega) m rank n} := by
  have hnow : MeasurableSet[incrementFiltration n]
      {omega : StepPath | rank ≤ thresholdCount (trajectory omega) n m} :=
    measurableSet_thresholdCount_ge n m rank
  have hprior : MeasurableSet[incrementFiltration n]
      (⋂ q : Fin n,
        {omega : StepPath | thresholdCount (trajectory omega) q m < rank}) := by
    apply MeasurableSet.iInter
    intro q
    have hge : MeasurableSet[incrementFiltration (q : ℕ)]
        {omega : StepPath | rank ≤
          thresholdCount (trajectory omega) q m} :=
      measurableSet_thresholdCount_ge q m rank
    have hlt :
        {omega : StepPath | thresholdCount (trajectory omega) q m < rank} =
          {omega : StepPath | rank ≤
            thresholdCount (trajectory omega) q m}ᶜ := by
      ext omega
      simp
    rw [hlt]
    exact incrementFiltration.mono (Nat.le_of_lt q.isLt) _ hge.compl
  have heq :
      {omega : StepPath | ThresholdCreation (trajectory omega) m rank n} =
        {omega : StepPath | rank ≤ thresholdCount (trajectory omega) n m} ∩
          ⋂ q : Fin n,
            {omega : StepPath |
              thresholdCount (trajectory omega) q m < rank} := by
    ext omega
    simp only [ThresholdCreation, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨h, fun q => hp q q.isLt⟩
    · rintro ⟨h, hp⟩
      exact ⟨h, fun q hq => hp ⟨q, hq⟩⟩
  rw [heq]
  exact hnow.inter hprior

/-! ### The concrete first high-gap stopped atoms -/

/-- Rank-one filtered transition paths whose old creation time is fixed. -/
def filteredFirstTransitionAtom
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (nOld : ℕ) : Set WalkPath :=
  filteredFirstTransitionEvent cap stagedCandidate₁ t m a ∩
    firstCreationAtom m nOld

/-- A rank-two past atom fixes the first two creation times. -/
def filteredFirstPairCreationAtom
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : PairCreationIndex) :
    Set WalkPath :=
  filteredFirstTransitionEvent cap stagedCandidate₁ t m a ∩
    pairCreationAtom t m a z

/-- The matching rank-two next atom, stopped at the old rank-two creation. -/
def filteredSecondTransitionAtom
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : PairCreationIndex) :
    Set WalkPath :=
  filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂ t m a ∩
    pairCreationAtom t m a z

/-- A rank-three past atom fixes the first three creation times. -/
def filteredSecondTripleCreationAtom
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : TripleCreationIndex) :
    Set WalkPath :=
  filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂ t m a ∩
    tripleCreationAtom t m a z

/-- The matching rank-three next atom. -/
def filteredThirdTransitionAtom
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : TripleCreationIndex) :
    Set WalkPath :=
  filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ t m a ∩
    tripleCreationAtom t m a z

/-- The concrete first-transition slice has precisely the stopped-creation
geometry required by the generic high atom. -/
theorem filteredFirstHighCreationAtomData
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (nOld : ℕ)
    (ha : a.1.1 ∈ highGapMesh) :
    HighCreationAtomData (firstCreationAtom m nOld)
      (filteredFirstTransitionAtom cap stagedCandidate₁ t m a nOld)
      m 1 nOld a.1.1 where
  rank_pos := by omega
  high_scale := ha
  past_observable := by
    change IsMeasurableAtStopping (fun _ : StepPath => nOld)
      {omega | ThresholdCreation (trajectory omega) m 1 nOld}
    apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact measurableSet_trajectory_thresholdCreation_filtration m 1 nOld
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, holdAtom⟩
    rcases Set.mem_iUnion.mp hfiltered.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hpair⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      thresholdCount (trajectory omega) n₂ (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₂) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 at hpair
    have hn₁eq : n₁ = nOld :=
      thresholdCreation_time_unique hpair.1 holdAtom
    subst n₁
    exact ⟨holdAtom, n₂, hpair.1, hpair.2.1, hpair.2.2.1,
      hpair.2.2.2.2⟩

/-- Rank-two deterministic high-gap data.  The sole premise is exactly the
stopped-past observability needed by strong Markov. -/
theorem filteredSecondHighCreationAtomData
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : PairCreationIndex)
    (ha : a.1.2 ∈ highGapMesh)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath => z.2)
      (trajectory ⁻¹'
        filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z)) :
    HighCreationAtomData
      (filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z)
      (filteredSecondTransitionAtom cap stagedCandidate₁ stagedCandidate₂
        t m a z)
      m 2 z.2 a.1.2 where
  rank_pos := by omega
  high_scale := ha
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, hpairAtom⟩
    have hpastFiltered :=
      filteredSecondTransitionEvent_subset_filteredFirst
        cap stagedCandidate₁ stagedCandidate₂ t m a hfiltered
    have hpast : trajectory omega ∈
        filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z :=
      ⟨hpastFiltered, hpairAtom⟩
    rcases Set.mem_iUnion.mp hfiltered.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
    rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, htriple⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      ThresholdCreation (trajectory omega) m 3 n₃ ∧
      thresholdCount (trajectory omega) n₃ (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₂) ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₃) ∧
      ¬Tilings.sameDomino t (trajectory omega n₂) (trajectory omega n₃) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 ∧
      gapScaleOf m (trajectory omega n₂) (trajectory omega n₃) = a.1.2 at htriple
    have hn₁ : n₁ = z.1 :=
      thresholdCreation_time_unique htriple.1 hpairAtom.1
    have hn₂ : n₂ = z.2 :=
      thresholdCreation_time_unique htriple.2.1 hpairAtom.2.1
    subst n₁
    subst n₂
    exact ⟨hpast, n₃, htriple.2.1, htriple.2.2.1,
      htriple.2.2.2.1, htriple.2.2.2.2.2.2.2.2⟩

/-- Rank-three deterministic high-gap data, again with only the precise
old-clock observability premise left to the filtered-history construction. -/
theorem filteredThirdHighCreationAtomData
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : TripleCreationIndex)
    (ha : a.2 ∈ highGapMesh)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath => z.2)
      (trajectory ⁻¹'
        filteredSecondTripleCreationAtom cap stagedCandidate₁ stagedCandidate₂
          t m a z)) :
    HighCreationAtomData
      (filteredSecondTripleCreationAtom cap stagedCandidate₁ stagedCandidate₂
        t m a z)
      (filteredThirdTransitionAtom cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a z)
      m 3 z.2 a.2 where
  rank_pos := by omega
  high_scale := ha
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, htripleAtom⟩
    have hpastFiltered :=
      filteredThirdTransitionEvent_subset_filteredSecond
        cap stagedCandidate₁ stagedCandidate₂ stagedCandidate₃
          t m a hfiltered
    have hpast : trajectory omega ∈
        filteredSecondTripleCreationAtom cap stagedCandidate₁ stagedCandidate₂
          t m a z := ⟨hpastFiltered, htripleAtom⟩
    rcases Set.mem_iUnion.mp hfiltered.1.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
    rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
    rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      ThresholdCreation (trajectory omega) m 3 n₃ ∧
      ThresholdCreation (trajectory omega) m 4 n₄ ∧
      thresholdCount (trajectory omega) n₄ (m + 1) = 0 ∧
      fourPointsSeparated t (trajectory omega n₁) (trajectory omega n₂)
        (trajectory omega n₃) (trajectory omega n₄) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 ∧
      gapScaleOf m (trajectory omega n₂) (trajectory omega n₃) = a.1.2 ∧
      gapScaleOf m (trajectory omega n₃) (trajectory omega n₄) = a.2 at hquad
    have hn₁ : n₁ = z.1.1 :=
      thresholdCreation_time_unique hquad.1 htripleAtom.1
    have hn₂ : n₂ = z.1.2 :=
      thresholdCreation_time_unique hquad.2.1 htripleAtom.2.1
    have hn₃ : n₃ = z.2 :=
      thresholdCreation_time_unique hquad.2.2.1 htripleAtom.2.2.1
    subst n₁
    subst n₂
    subst n₃
    exact ⟨hpast, n₄, hquad.2.2.1, hquad.2.2.2.1,
      hquad.2.2.2.2.1, hquad.2.2.2.2.2.2.2.2⟩

/-- On one fixed old-creation atom, high spatial separation gives the literal
boundary-escape certificate consumed by strong Markov. -/
def highCreationAtomBoundaryEscapeCertificate
    {past next : Set WalkPath} {m rank nOld : ℕ} {a : GapScale}
    (hm : 1 ≤ m) (data : HighCreationAtomData past next m rank nOld a) :
    BoundaryEscapeFutureFactorCertificate Unit past next
      (ENNReal.ofReal (literalEscapeProbability (highSpatialRadius m))) where
  stop := fun _ => nOld
  location := fun _ => ()
  boundary := fun _ =>
    ThickPoint.discBoundary 0 (highSpatialRadius m : ℝ)
  stop_isStopping := isFiniteStoppingTime_const nOld
  pastFiber_observable := by
    intro x
    cases x
    simpa using data.past_observable
  escape_le := by
    intro x _hx
    cases x
    exact le_rfl
  next_subset := by
    intro omega homega
    change trajectory omega ∈ next at homega
    obtain ⟨hpast, nNew, hold, hnew, hnext, hscale⟩ :=
      data.next_creation omega homega
    refine ⟨hpast, ?_⟩
    exact postStoppingSteps_not_positiveReturnBeforeBoundary_of_high_creation
      hm data.rank_pos hold hnew hnext data.high_scale hscale

/-- The high constructor of the source-correct transition interface,
instantiated on a stopped creation atom. -/
def highCreationAtomSourceCorrectTransitionFactor
    {History Candidate : Type*} [Countable History]
    {past next : Set WalkPath} {m rank nOld : ℕ} {a : GapScale} {q : ℝ≥0∞}
    (hm : 1 ≤ m) (data : HighCreationAtomData past next m rank nOld a)
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤ q) :
    SourceCorrectTransitionFactor History Candidate Unit past next q :=
  .high _ (highCreationAtomBoundaryEscapeCertificate hm data) hcost

/-! ## Countable creation-clock assembly -/

/-- The whole first filtered transition, decomposed over its rank-one
creation clock.  Paths which never create the first favorite need no atom:
the countable interface only asks that the stopped past pieces lie in
`univ`. -/
def filteredFirstHighCountableAtomFutureFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.1.1 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a)) :
    CountableAtomFutureFactor ℕ Unit Set.univ
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := firstCreationAtom m
  nextPiece := filteredFirstTransitionAtom cap stagedCandidate₁ t m a
  past_pairwise := firstCreationAtom_pairwiseDisjoint m
  past_measurable := measurableSet_firstCreationAtom m
  next_measurable := fun n ↦
    (measurableSet_filteredFirstTransitionEvent cap stagedCandidate₁
      t m a hcandidate₁).inter (measurableSet_firstCreationAtom m n)
  past_subset := fun _ _ ↦ Set.mem_univ _
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
      exact hn.1
    · intro s hs
      have hcreated :=
        firstTransitionEvent_subset_iUnion_firstCreationAtom t m a hs.1
      rcases Set.mem_iUnion.mp hcreated with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, hs, hn⟩
  atom := fun n ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (filteredFirstHighCreationAtomData cap stagedCandidate₁
        t m a n ha)

/-- The second filtered transition assembled over the fixed first-two
creation atoms.  Its only history premise is observability at the old
rank-two creation clock. -/
def filteredSecondHighCountableAtomFutureFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.1.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hpast : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹'
          filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z)) :
    CountableAtomFutureFactor PairCreationIndex Unit
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := filteredFirstPairCreationAtom cap stagedCandidate₁ t m a
  nextPiece := filteredSecondTransitionAtom cap stagedCandidate₁
    stagedCandidate₂ t m a
  past_pairwise := by
    intro z w hzw
    exact (pairCreationAtom_pairwiseDisjoint t m a hzw).mono
      Set.inter_subset_right Set.inter_subset_right
  past_measurable := fun z ↦
    (measurableSet_filteredFirstTransitionEvent cap stagedCandidate₁
      t m a hcandidate₁).inter (measurableSet_pairCreationAtom t m a z)
  next_measurable := fun z ↦
    (measurableSet_filteredSecondTransitionEvent cap stagedCandidate₁
      stagedCandidate₂ t m a hcandidate₁ hcandidate₂).inter
        (measurableSet_pairCreationAtom t m a z)
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
    exact hz.1
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
      exact hz.1
    · intro s hs
      have hfirst := filteredSecondTransitionEvent_subset_filteredFirst
        cap stagedCandidate₁ stagedCandidate₂ t m a hs
      have hatom : s ∈ ⋃ z : PairCreationIndex,
          pairCreationAtom t m a z := by
        rw [iUnion_pairCreationAtom t m a]
        exact hfirst.1
      rcases Set.mem_iUnion.mp hatom with ⟨z, hz⟩
      exact Set.mem_iUnion.mpr ⟨z, hs, hz⟩
  atom := fun z ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (filteredSecondHighCreationAtomData cap stagedCandidate₁
        stagedCandidate₂ t m a z ha (hpast z))

/-- The third filtered transition assembled over the fixed first-three
creation atoms. -/
def filteredThirdHighCountableAtomFutureFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hpast : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹' filteredSecondTripleCreationAtom cap
          stagedCandidate₁ stagedCandidate₂ t m a z)) :
    CountableAtomFutureFactor TripleCreationIndex Unit
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := filteredSecondTripleCreationAtom cap stagedCandidate₁
    stagedCandidate₂ t m a
  nextPiece := filteredThirdTransitionAtom cap stagedCandidate₁
    stagedCandidate₂ stagedCandidate₃ t m a
  past_pairwise := by
    intro z w hzw
    exact (tripleCreationAtom_pairwiseDisjoint t m a hzw).mono
      Set.inter_subset_right Set.inter_subset_right
  past_measurable := fun z ↦
    (measurableSet_filteredSecondTransitionEvent cap stagedCandidate₁
      stagedCandidate₂ t m a hcandidate₁ hcandidate₂).inter
        (measurableSet_tripleCreationAtom t m a z)
  next_measurable := fun z ↦
    (measurableSet_filteredThirdTransitionEvent cap stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a hcandidate₁
        hcandidate₂ hcandidate₃).inter
      (measurableSet_tripleCreationAtom t m a z)
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
    exact hz.1
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
      exact hz.1
    · intro s hs
      have hsecond := filteredThirdTransitionEvent_subset_filteredSecond
        cap stagedCandidate₁ stagedCandidate₂ stagedCandidate₃
          t m a hs
      have hatom : s ∈ ⋃ z : TripleCreationIndex,
          tripleCreationAtom t m a z := by
        rw [iUnion_tripleCreationAtom t m a]
        exact hsecond.1
      rcases Set.mem_iUnion.mp hatom with ⟨z, hz⟩
      exact Set.mem_iUnion.mpr ⟨z, hs, hz⟩
  atom := fun z ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (filteredThirdHighCreationAtomData cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a z ha (hpast z))

/-! ## Rankwise source-correct factors and the all-high branch package -/

/-- Concrete `.highAtomwise` factor for the entire first filtered event. -/
def filteredFirstHighSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : HLOZFilteredTransitionAssembly.BranchEvent)
    (K : ℝ≥0) (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.1.1 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit Set.univ
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (filteredFirstHighCountableAtomFutureFactor cap stagedCandidate₁
      t m a hm ha hcandidate₁) hcost

/-- Concrete `.highAtomwise` factor for the entire second filtered event. -/
def filteredSecondHighSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (K : ℝ≥0) (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.1.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hpast : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹'
          filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (filteredSecondHighCountableAtomFutureFactor cap stagedCandidate₁
      stagedCandidate₂ t m a hm ha hcandidate₁ hcandidate₂ hpast) hcost

/-- Concrete `.highAtomwise` factor for the entire third filtered event. -/
def filteredThirdHighSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (K : ℝ≥0) (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m) (ha : a.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hpast : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹' filteredSecondTripleCreationAtom cap
          stagedCandidate₁ stagedCandidate₂ t m a z))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (filteredThirdHighCountableAtomFutureFactor cap stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a hm ha hcandidate₁
        hcandidate₂ hcandidate₃ hpast) hcost

/-- When all three mesh gaps are high, the three literal countable-atom
factors form the concrete filtered branch package. -/
def filteredAllHighBranchTransitionFactorPackage
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (K : ℝ≥0) (t : Tilings.Tiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 1 ≤ m)
    (ha₁ : a.1.1 ∈ highGapMesh) (ha₂ : a.1.2 ∈ highGapMesh)
    (ha₃ : a.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hpast₂ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹'
          filteredFirstPairCreationAtom cap stagedCandidate₁ t m a z))
    (hpast₃ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath => z.2)
        (trajectory ⁻¹' filteredSecondTripleCreationAtom cap
          stagedCandidate₁ stagedCandidate₂ t m a z))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    FilteredBranchTransitionFactorPackage Unit Unit Unit cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a where
  stagedCandidate₁_measurable := hcandidate₁
  stagedCandidate₂_measurable := hcandidate₂
  stagedCandidate₃_measurable := hcandidate₃
  factors :=
    { firstFactor := filteredFirstHighSourceCorrectTransitionFactor cap
        stagedCandidate₁ K t m a hm ha₁ hcandidate₁ hcost
      secondFactor := filteredSecondHighSourceCorrectTransitionFactor cap
        stagedCandidate₁ stagedCandidate₂ K t m a hm ha₂ hcandidate₁
          hcandidate₂ hpast₂ hcost
      thirdFactor := filteredThirdHighSourceCorrectTransitionFactor cap
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm ha₃
          hcandidate₁ hcandidate₂ hcandidate₃ hpast₃ hcost }

/-- The all-high filtered branch package exists eventually with the
canonical constant `1`; no transition-probability estimate is assumed. -/
theorem eventually_filteredAllHighBranchTransitionFactorPackage :
    ∀ᶠ m : ℕ in atTop,
      ∀ (cap : ℕ → ℕ)
        (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
          HLOZFilteredTransitionAssembly.BranchEvent)
        (t : Tilings.Tiling)
        (a : (GapScale × GapScale) × GapScale),
        a.1.1 ∈ highGapMesh → a.1.2 ∈ highGapMesh →
        a.2 ∈ highGapMesh →
        MeasurableSet (stagedCandidate₁ t m a) →
        MeasurableSet (stagedCandidate₂ t m a) →
        MeasurableSet (stagedCandidate₃ t m a) →
        (∀ z : PairCreationIndex,
          IsMeasurableAtStopping (fun _ : StepPath => z.2)
            (trajectory ⁻¹' filteredFirstPairCreationAtom cap
              stagedCandidate₁ t m a z)) →
        (∀ z : TripleCreationIndex,
          IsMeasurableAtStopping (fun _ : StepPath => z.2)
            (trajectory ⁻¹' filteredSecondTripleCreationAtom cap
              stagedCandidate₁ stagedCandidate₂ t m a z)) →
        Nonempty (FilteredBranchTransitionFactorPackage Unit Unit Unit cap
          stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ 1 t m a) := by
  filter_upwards
      [eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost,
        eventually_ge_atTop 1] with m hcost hm
  intro cap stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t a
    ha₁ ha₂ ha₃ hcandidate₁ hcandidate₂ hcandidate₃ hpast₂ hpast₃
  exact ⟨filteredAllHighBranchTransitionFactorPackage cap
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ 1 t m a hm
      ha₁ ha₂ ha₃ hcandidate₁ hcandidate₂ hcandidate₃ hpast₂ hpast₃ hcost⟩

end

end Erdos1165.HLOZHighSpatialTransitionFactor
