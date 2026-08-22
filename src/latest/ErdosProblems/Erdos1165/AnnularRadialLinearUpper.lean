/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialReferenceEdge
import ErdosProblems.Erdos1165.AnnularProfileUniformUpperLoss

/-!
# Upper bounds for one chronological radial word

This file is deliberately linear.  It compares the literal successive-
different-boundary chain one row at a time and never identifies a nested
family of overlapping annular intervals with one stopped path event.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialLinearUpper

open AnnularProfileClocks AnnularRadialChainLower AnnularRadialLabelWord
open AnnularOffspringKernelRadial
open AnnularRadialOneStepRow AnnularRadialReferenceEdge
open AnnularRadialProfileWords AnnularProfileUniformUpperLoss
open AnnularRadialTerminalRow AppendixFirstMoment ExcursionTransition
open MarkedBoundaryVisitKernel ProfileAnnularRowRegular RealDiscFinite ThickPoint
open LiteralRealAnnulusRadialExit TerminalSpliceProfileGeometry

noncomputable section

/-- Uniform relative terminal loss used by the linear word.  The factor
`1 + 3 log n` compensates for the smaller `n -> n+1` ideal probability. -/
def terminalLinearUpperError (n : ℕ) : ℝ :=
  terminalRadialRowError n * (1 + 3 * Real.log n)

def terminalInwardMassReal (n : ℕ) (center start : Point) : ℝ :=
  (radialOneStepKernelENNReal n center ⟨n, by omega⟩
    ⟨n + 1, by omega⟩ start).toReal

def terminalOutwardMassReal (n : ℕ) (center start : Point) : ℝ :=
  (radialOneStepKernelENNReal n center ⟨n, by omega⟩
    ⟨n - 1, by omega⟩ start).toReal

lemma terminalLinearUpperError_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ terminalLinearUpperError n := by
  have hinner : 1 < scaleRadius n (n + 1) := by
    rw [scaleRadius_succ_self]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 6]
  have hmiddle : 1 < scaleRadius n n := by
    rw [scaleRadius_of_le le_rfl, regularRadius_self]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 9]
  have houter : 1 < scaleRadius n (n - 1) := by
    exact hmiddle.trans_le (scaleRadius_antitone_of_le (by omega) (by omega))
  have herr : 0 ≤ terminalRadialRowError n := by
    unfold terminalRadialRowError
    rw [terminal_outer_middle_potential_gap (by omega)]
    positivity [realBoundaryPotentialError_nonneg hinner,
      realBoundaryPotentialError_nonneg hmiddle,
      realBoundaryPotentialError_nonneg houter]
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  exact mul_nonneg herr (by positivity)

private theorem profile_terminal_rows_sum_eq_one
    {n : ℕ} (hn : 2 ≤ n) (center : Point)
    (u : ProfileCycleMiddlePoint n n center) :
    (∑ z : ProfileCycleInnerPoint n n center,
      (skeletonExitKernel
        (profileInnerBoundary n (n + 1) center ∪
          profileOuterBoundary n n center) u.1 z.1).toReal) +
      profileAnnularEscapeRowReal n n center u = 1 := by
  have houter : (profileOuterBoundary n n center).Nonempty := by
    apply discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hrenewal := profileAnnularCycle_escape_isStochasticRenewalRow
    houter (terminalRadius_le_regularRadius_self n (by omega))
      (scaleRadius_self_add_one_le_of_lt (by omega) (by omega)) u
  have hmiddle : (profileInnerBoundary n n center).Nonempty := by
    apply discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hcycle := sum_profileAnnularCycleKernelReal_eq_inwardRow hmiddle u
  rw [hcycle] at hrenewal
  simpa only [add_comm] using hrenewal.symm

/-- The two possible literal decisions from terminal regular level `n`
have total mass one. -/
theorem terminal_radial_rows_sum_toReal_eq_one
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n, by omega⟩) :
    terminalInwardMassReal n center start +
      terminalOutwardMassReal n center start = 1 := by
  let u : ProfileCycleMiddlePoint n n center :=
    ⟨start, mem_discBoundaryFinset.mpr (by
      simpa [radialBoundary] using hstart)⟩
  have hsum := profile_terminal_rows_sum_eq_one hn center u
  unfold terminalInwardMassReal terminalOutwardMassReal
  rw [radialOneStepKernelENNReal_terminal_inward_toReal_eq hn center start hstart,
    radialOneStepKernelENNReal_terminal_outward_toReal_eq hn center start hstart]
  exact hsum

/-- A common multiplicative upper comparison for both terminal directions. -/
theorem radialOneStepKernelENNReal_terminal_upper
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n, by omega⟩) :
    terminalInwardMassReal n center start ≤
          (1 + terminalLinearUpperError n) * (1 - terminalSuccess n) ∧
      terminalOutwardMassReal n center start ≤
          (1 + terminalLinearUpperError n) * terminalSuccess n := by
  let inward := terminalInwardMassReal n center start
  let outward := terminalOutwardMassReal n center start
  let e := terminalRadialRowError n
  let p := terminalSuccess n
  have hsum : inward + outward = 1 :=
    terminal_radial_rows_sum_toReal_eq_one hn center start hstart
  have hlower := radialOneStepKernelENNReal_terminal_ofReal_lower
    hn center start hstart
  have hinLower : (1 - e) * (1 - p) ≤ inward := by
    change _ ≤ terminalInwardMassReal n center start
    unfold terminalInwardMassReal
    exact (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).mp hlower.1
  have houtLower : (1 - e) * p ≤ outward := by
    change _ ≤ terminalOutwardMassReal n center start
    unfold terminalOutwardMassReal
    exact (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).mp hlower.2
  have hp0 : 0 < p := terminalSuccess_pos hn
  have hp1 : p ≤ 1 := terminalSuccess_le_one hn
  have hfailure : 0 < 1 - p := sub_pos.mpr (by
    unfold p terminalSuccess
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hden : 0 < 1 + 3 * Real.log (n : ℝ) := by positivity
    apply (div_lt_one hden).2
    linarith)
  have herr : 0 ≤ e := by
    dsimp only [e]
    have := terminalLinearUpperError_nonneg hn
    unfold terminalLinearUpperError at this
    have hfactor : 0 < 1 + 3 * Real.log (n : ℝ) := by
      have : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      positivity
    exact nonneg_of_mul_nonneg_left this hfactor
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hratio : p = 3 * Real.log (n : ℝ) * (1 - p) := by
    unfold p terminalSuccess
    have hden : 0 < 1 + 3 * Real.log (n : ℝ) := by positivity
    field_simp [ne_of_gt hden]
    ring
  have hfailure_le : 1 - p ≤ p := by
    have hlogLower : 1 ≤ 3 * Real.log (n : ℝ) := by
      nlinarith [Real.log_two_gt_d9,
        Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hn : (2 : ℝ) ≤ n)]
    rw [hratio]
    nlinarith
  have herror_le_terminal : e ≤ terminalLinearUpperError n := by
    unfold terminalLinearUpperError
    nlinarith
  constructor
  · dsimp only [inward, outward] at hsum ⊢
    dsimp only [e, p] at hinLower houtLower hratio hfailure_le herr ⊢
    rw [terminalLinearUpperError]
    nlinarith
  · dsimp only [inward, outward] at hsum ⊢
    dsimp only [e, p] at hinLower houtLower hratio hfailure_le herr
    dsimp only [e] at herror_le_terminal
    nlinarith

/-- After paying the logarithmic imbalance between the two terminal
directions, the common terminal upper error is still eventually `n⁻⁴`. -/
theorem eventually_terminalLinearUpperError_le_inv_pow_four :
    ∀ᶠ n : ℕ in atTop,
      terminalLinearUpperError n ≤ 1 / (n : ℝ) ^ 4 := by
  have hlogReal := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 6 by norm_num)
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [eventually_terminalRadialRowError_le_inv_pow_five,
      hlogNat, eventually_ge_atTop 2] with n herror hlog hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlogUpper : Real.log (n : ℝ) ≤ (n : ℝ) / 6 := by
    have hlog' : Real.log (n : ℝ) ≤ (1 / 6 : ℝ) * n := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hlog0,
        abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using hlog
    linarith
  have hfactor : 1 + 3 * Real.log (n : ℝ) ≤ n := by
    linarith
  unfold terminalLinearUpperError
  calc
    terminalRadialRowError n * (1 + 3 * Real.log (n : ℝ)) ≤
        (1 / (n : ℝ) ^ 5) * (1 + 3 * Real.log (n : ℝ)) := by
      gcongr
    _ ≤ (1 / (n : ℝ) ^ 5) * n := by
      gcongr
    _ = 1 / (n : ℝ) ^ 4 := by
      field_simp

private lemma dist_eq_one_cases {a b : ℕ} (h : Nat.dist a b = 1) :
    b = a + 1 ∨ b + 1 = a := by
  unfold Nat.dist at h
  by_cases hab : a ≤ b
  · have hzero : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hzero, Nat.zero_add] at h
    exact Or.inl (by omega)
  · have hba : b ≤ a := by omega
    have hzero : b - a = 0 := Nat.sub_eq_zero_of_le hba
    rw [hzero, Nat.add_zero] at h
    exact Or.inr (by omega)

/-- Every adjacent chronological row is eventually bounded above by one
copy of `1+n⁻⁴` times its ideal label-chain row. -/
theorem eventually_radialOneStepKernelENNReal_adjacent_upper :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (center : Point)
      (source target : Fin (n + 2)) (start : Point),
      start ∈ radialBoundary n center source →
      (source : ℕ) ≠ 0 → Nat.dist (source : ℕ) (target : ℕ) = 1 →
      radialOneStepKernelENNReal n center source target start ≤
        ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
          annularIdealEdge n source target := by
  filter_upwards [eventually_profileRegularRowError_le_inv_pow_six,
      eventually_terminalLinearUpperError_le_inv_pow_four,
      eventually_ge_atTop 2] with n hregular hterminal hn
  intro _ center source target start hstart hsource0 hadjacent
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hinvSixFour : 1 / (n : ℝ) ^ 6 ≤ 1 / (n : ℝ) ^ 4 := by
    apply one_div_le_one_div_of_le (by positivity)
    have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnR
    calc
      (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 * (n : ℝ) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hnSq
      _ = (n : ℝ) ^ 6 := by ring
  by_cases hsourceInternal : (source : ℕ) < n
  · have hsourcePos : 0 < (source : ℕ) := Nat.pos_of_ne_zero hsource0
    have hsourceBound : (source : ℕ) + 1 ≤ n := by omega
    have houter : (profileOuterBoundary n (source : ℕ) center).Nonempty := by
      apply discBoundary_center_nonempty_of_nonneg
      unfold scaleRadius regularRadius
      split_ifs <;> positivity
    have hbounds := radialOneStepKernelENNReal_internal_half_bounds
      hn hsourcePos hsourceBound center start
        (by simpa [radialBoundary] using hstart) houter
    rcases dist_eq_one_cases hadjacent with hin | hout
    · have hsourceEq : source = ⟨(source : ℕ), by omega⟩ := (Fin.eta source _).symm
      have htargetEq : target = ⟨(source : ℕ) + 1, by omega⟩ :=
        Fin.ext hin
      have hactual : radialOneStepKernelENNReal n center source target start ≤
          ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) / 2) := by
        apply (ENNReal.toReal_le_toReal (by
          unfold radialOneStepKernelENNReal
          exact measure_ne_top fairSteps _) (by simp)).mp
        rw [ENNReal.toReal_ofReal (by positivity)]
        have hrowUpper :
            (radialOneStepKernelENNReal n center source target start).toReal ≤
              (1 + literalRealAnnulusRowError
                (scaleRadius n ((source : ℕ) + 1))
                (scaleRadius n (source : ℕ))
                (scaleRadius n ((source : ℕ) - 1))) / 2 := by
          simpa only [htargetEq] using hbounds.2.1
        have herr := hregular (source : ℕ) hsourcePos hsourceBound
        linarith
      calc
        radialOneStepKernelENNReal n center source target start ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) / 2) := hactual
        _ = ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
              annularIdealEdge n source target := by
          have hideal : annularIdealEdge n source target =
              ENNReal.ofReal (1 / 2 : ℝ) := by
            simp [annularIdealEdge, hsource0, hsourceInternal, hadjacent]
          rw [hideal, ← ENNReal.ofReal_mul (by positivity :
            0 ≤ 1 + 1 / (n : ℝ) ^ 4)]
          congr
          ring
    · have hsourceEq : source = ⟨(source : ℕ), by omega⟩ := (Fin.eta source _).symm
      have htargetEq : target = ⟨(source : ℕ) - 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hactual : radialOneStepKernelENNReal n center source target start ≤
          ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) / 2) := by
        apply (ENNReal.toReal_le_toReal (by
          unfold radialOneStepKernelENNReal
          exact measure_ne_top fairSteps _) (by simp)).mp
        rw [ENNReal.toReal_ofReal (by positivity)]
        have hrowUpper :
            (radialOneStepKernelENNReal n center source target start).toReal ≤
              (1 + literalRealAnnulusRowError
                (scaleRadius n ((source : ℕ) + 1))
                (scaleRadius n (source : ℕ))
                (scaleRadius n ((source : ℕ) - 1))) / 2 := by
          simpa only [htargetEq] using hbounds.2.2.2
        have herr := hregular (source : ℕ) hsourcePos hsourceBound
        linarith
      calc
        radialOneStepKernelENNReal n center source target start ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) / 2) := hactual
        _ = ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
              annularIdealEdge n source target := by
          have hideal : annularIdealEdge n source target =
              ENNReal.ofReal (1 / 2 : ℝ) := by
            simp [annularIdealEdge, hsource0, hsourceInternal, hadjacent]
          rw [hideal, ← ENNReal.ofReal_mul (by positivity :
            0 ≤ 1 + 1 / (n : ℝ) ^ 4)]
          congr
          ring
  · have hsourceGe : n ≤ (source : ℕ) := by omega
    by_cases hsourceTerminal : (source : ℕ) = n
    · have hsourceEq : source = ⟨n, by omega⟩ := Fin.ext hsourceTerminal
      have hupper := radialOneStepKernelENNReal_terminal_upper hn center start
        (by simpa [hsourceEq] using hstart)
      rcases dist_eq_one_cases hadjacent with hin | hout
      · have htargetEq : target = ⟨n + 1, by omega⟩ := by
          apply Fin.ext
          simpa [hsourceTerminal] using hin
        have hactual : radialOneStepKernelENNReal n center source target start ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) *
              (1 - terminalSuccess n)) := by
          apply (ENNReal.toReal_le_toReal (by
            unfold radialOneStepKernelENNReal
            exact measure_ne_top fairSteps _) (by simp)).mp
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity)
            (sub_nonneg.mpr (terminalSuccess_le_one hn)))]
          have hleft :
              (radialOneStepKernelENNReal n center source target start).toReal =
                terminalInwardMassReal n center start := by
            unfold terminalInwardMassReal
            congr 3
          rw [hleft]
          exact hupper.1.trans (mul_le_mul_of_nonneg_right
            (by linarith) (sub_nonneg.mpr (terminalSuccess_le_one hn)))
        calc
          radialOneStepKernelENNReal n center source target start ≤ _ := hactual
          _ = ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
                annularIdealEdge n source target := by
            rw [ENNReal.ofReal_mul (by positivity)]
            have hideal : annularIdealEdge n source target =
                ENNReal.ofReal (1 - terminalSuccess n) := by
              simp [annularIdealEdge, hsourceTerminal, htargetEq,
                show n ≠ 0 by omega, show n - 1 + 1 = n by omega]
            rw [hideal]
      · have htargetEq : target = ⟨n - 1, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        have hactual : radialOneStepKernelENNReal n center source target start ≤
            ENNReal.ofReal ((1 + 1 / (n : ℝ) ^ 4) *
              terminalSuccess n) := by
          apply (ENNReal.toReal_le_toReal (by
            unfold radialOneStepKernelENNReal
            exact measure_ne_top fairSteps _) (by simp)).mp
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity)
            (terminalSuccess_pos hn).le)]
          have hleft :
              (radialOneStepKernelENNReal n center source target start).toReal =
                terminalOutwardMassReal n center start := by
            unfold terminalOutwardMassReal
            congr 3
          rw [hleft]
          exact hupper.2.trans (mul_le_mul_of_nonneg_right
            (by linarith) (terminalSuccess_pos hn).le)
        calc
          radialOneStepKernelENNReal n center source target start ≤ _ := hactual
          _ = ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
                annularIdealEdge n source target := by
            rw [ENNReal.ofReal_mul (by positivity)]
            have hideal : annularIdealEdge n source target =
                ENNReal.ofReal (terminalSuccess n) := by
              simp [annularIdealEdge, hsourceTerminal, htargetEq,
                show n ≠ 0 by omega, show n - 1 + 1 = n by omega]
            rw [hideal]
    · have hsourceInner : (source : ℕ) = n + 1 := by omega
      have htarget : (target : ℕ) = n := by
        rcases dist_eq_one_cases hadjacent with hin | hout
        · omega
        · omega
      have hsourceEq : source = ⟨n + 1, by omega⟩ := Fin.ext hsourceInner
      have htargetEq : target = ⟨n, by omega⟩ := Fin.ext htarget
      have hactual : radialOneStepKernelENNReal n center source target start = 1 := by
        simpa only [hsourceEq, htargetEq] using
          radialOneStepKernelENNReal_terminal_return_eq_one hn center start
            (by simpa [hsourceEq] using hstart)
      rw [hactual]
      have hideal : annularIdealEdge n source target = 1 := by
        simp [annularIdealEdge, hsource0, hsourceInternal,
          hsourceTerminal, htarget]
      rw [hideal, mul_one]
      apply ENNReal.one_le_ofReal.mpr
      have : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
      linarith

/-- Endpoint-integrated upper row bounds multiply along one exact random-
endpoint chronological chain. -/
theorem radialChainKernelENNReal_le_reference
    {n : ℕ} (center : Point)
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (hrow : ∀ source target : Fin (n + 2),
      ∀ start : Point, start ∈ radialBoundary n center source →
        (∑ endpoint : RadialBoundaryPoint n center target,
          skeletonExitKernel (otherRadialBoundaries n center source)
            start endpoint.1) ≤ edge source target) :
    ∀ source targets start, start ∈ radialBoundary n center source →
      radialChainKernelENNReal n center source targets start ≤
        radialChainReference edge source targets := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start _
      simp [radialChainReference, radialChainKernelENNReal]
  | cons target tail ih =>
      intro start hstart
      have hhead := hrow source target start hstart
      have htail (endpoint : RadialBoundaryPoint n center target) :
          radialChainKernelENNReal n center target tail endpoint.1 ≤
            radialChainReference edge target tail :=
        ih target endpoint.1 endpoint.2
      rw [radialChainReference, radialChainKernelENNReal]
      calc
        (∑ endpoint : RadialBoundaryPoint n center target,
            skeletonExitKernel (otherRadialBoundaries n center source)
                start endpoint.1 *
              radialChainKernelENNReal n center target tail endpoint.1) ≤
            ∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                radialChainReference edge target tail := by
          exact Finset.sum_le_sum fun endpoint _ ↦
            mul_le_mul le_rfl (htail endpoint) bot_le bot_le
        _ = (∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                start endpoint.1) *
              radialChainReference edge target tail := by
          rw [Finset.sum_mul]
        _ ≤ edge source target * radialChainReference edge target tail :=
          mul_le_mul hhead le_rfl bot_le bot_le

/-- A row comparison needed only along the displayed label chain is enough;
unsupported label pairs never enter the proof. -/
theorem radialChainKernelENNReal_le_pow_mul_reference_of_chain
    {n : ℕ} (center : Point) (common : ℝ≥0∞)
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))),
      List.IsChain (fun a b ↦ ∀ start : Point,
        start ∈ radialBoundary n center a →
          (∑ endpoint : RadialBoundaryPoint n center b,
            skeletonExitKernel (otherRadialBoundaries n center a)
              start endpoint.1) ≤ common * edge a b) (source :: targets) →
      ∀ start : Point, start ∈ radialBoundary n center source →
        radialChainKernelENNReal n center source targets start ≤
          common ^ targets.length *
            radialChainReference edge source targets := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro _ start _
      simp [radialChainReference, radialChainKernelENNReal]
  | cons target tail ih =>
      intro hchain start hstart
      have hparts := List.isChain_cons_cons.mp hchain
      have hhead := hparts.1 start hstart
      have htail (endpoint : RadialBoundaryPoint n center target) :
          radialChainKernelENNReal n center target tail endpoint.1 ≤
            common ^ tail.length * radialChainReference edge target tail :=
        ih target hparts.2 endpoint.1 endpoint.2
      rw [radialChainKernelENNReal, radialChainReference, List.length_cons,
        pow_succ]
      calc
        (∑ endpoint : RadialBoundaryPoint n center target,
            skeletonExitKernel (otherRadialBoundaries n center source)
                start endpoint.1 *
              radialChainKernelENNReal n center target tail endpoint.1) ≤
            ∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                (common ^ tail.length *
                  radialChainReference edge target tail) := by
          exact Finset.sum_le_sum fun endpoint _ ↦
            mul_le_mul le_rfl (htail endpoint) bot_le bot_le
        _ = (∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                start endpoint.1) *
              (common ^ tail.length *
                radialChainReference edge target tail) := by
          rw [Finset.sum_mul]
        _ ≤ (common * edge source target) *
              (common ^ tail.length *
                radialChainReference edge target tail) :=
          mul_le_mul hhead le_rfl bot_le bot_le
        _ = common ^ tail.length * common *
              (edge source target *
                radialChainReference edge target tail) := by ac_rfl

/-- Specialization to an exact admissible radial word.  This is the linear
upper comparison used below; it never introduces nested time intervals. -/
theorem eventually_fairSteps_radialLabelWordAtom_le_common_pow_mul_reference :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (L : ℕ) (center start : Point)
      (word : RadialLabelWord n L),
      start ∈ radialBoundary n center ⟨1, by omega⟩ →
      fairSteps (radialLabelWordAtom n L center start word) ≤
        ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) ^ L *
          radialChainReference (annularIdealEdge n)
            (word.level ⟨0, by omega⟩) word.toList.tail := by
  filter_upwards [eventually_radialOneStepKernelENNReal_adjacent_upper,
      eventually_ge_atTop 2] with n hrow hn
  intro _ L center start word hstart
  rw [fairSteps_radialLabelWordAtom_eq_radialWordChainKernelENNReal
    hn center start word hstart]
  change radialChainKernelENNReal n center
      (word.level ⟨0, by omega⟩) word.toList.tail start ≤ _
  have hlist : word.toList = word.level ⟨0, by omega⟩ ::
      word.toList.tail := by
    simp [RadialLabelWord.toList, List.ofFn_succ]
  have hvalid : List.IsChain
      (fun a b : Fin (n + 2) ↦ (a : ℕ) ≠ 0 ∧ Nat.dist (a : ℕ) (b : ℕ) = 1)
      word.toList := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact ⟨word.beforeFinal_ne_zero ⟨i, by omega⟩,
      word.adjacent ⟨i, by omega⟩⟩
  have hrows : List.IsChain (fun a b ↦ ∀ z : Point,
      z ∈ radialBoundary n center a →
        (∑ endpoint : RadialBoundaryPoint n center b,
          skeletonExitKernel (otherRadialBoundaries n center a)
            z endpoint.1) ≤
          ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) *
            annularIdealEdge n a b)
      (word.level ⟨0, by omega⟩ :: word.toList.tail) := by
    rw [← hlist]
    exact hvalid.imp (by
      intro a b hab z hz
      rw [sum_skeletonExitKernel_otherRadialBoundaries_eq]
      exact hrow hn center a b z hz hab.1 hab.2)
  have hbound := radialChainKernelENNReal_le_pow_mul_reference_of_chain
    center (ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4))
      (annularIdealEdge n) _ _ hrows _ (by
        rw [word.startsAtOne]
        exact hstart)
  have hlength : word.toList.tail.length = L := by
    simpa using congrArg List.length (congrArg List.tail hlist)
  simpa only [hlength] using hbound

/-- Exact-cutoff specialization of the linear word comparison.  The common
row-loss power is kept explicit so it can later be summed over profiles with
unrestricted coordinates. -/
theorem eventually_fairSteps_exactFixedProfileRadialWordFamilyAtom_le_ideal_sum :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (delta : ℝ)
      (center start : Point) (m : Profile n),
      start ∈ radialBoundary n center ⟨1, by omega⟩ →
      fairSteps (exactFixedProfileRadialWordFamilyAtom
          n delta center start m) ≤
        ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m *
          ∑ word : {word : BoundedRadialLabelWord n
              (exactProfileRadialWordMaxTransitions m) //
              IsFixedProfileRadialWordWithCutoff n
                (exactProfileRadialWordMaxTransitions m) delta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩)
              word.1.2.toList.tail := by
  filter_upwards
      [eventually_fairSteps_radialLabelWordAtom_le_common_pow_mul_reference,
        eventually_ge_atTop 2] with n hword hn
  intro _ delta center start m hstart
  rw [fairSteps_exactFixedProfileRadialWordFamilyAtom, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  have hraw := hword hn word.1.1 center start word.1.2 hstart
  have hbaseReal : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) ^ 4 :=
    le_add_of_nonneg_right (by positivity)
  have hbase : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) :=
    ENNReal.one_le_ofReal.mpr hbaseReal
  have hlength : (word.1.1 : ℕ) ≤
      exactProfileRadialWordMaxTransitions m :=
    Nat.le_of_lt_succ word.1.1.2
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hbase hlength) bot_le)

/-- The deliberately generous cutoff `8n³+1` still makes the accumulated
linear upper error at most `exp 1`. -/
theorem one_add_inv_pow_four_profileRadialWordMaxTransitions_le_exp_one
    {n : ℕ} (hn : 10 ≤ n) :
    (1 + 1 / (n : ℝ) ^ 4) ^ profileRadialWordMaxTransitions n ≤
      Real.exp 1 := by
  have hnPos : (0 : ℝ) < n := by positivity
  have hnTen : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hcost :
      (profileRadialWordMaxTransitions n : ℝ) *
          (1 / (n : ℝ) ^ 4) ≤ 1 := by
    rw [show (profileRadialWordMaxTransitions n : ℝ) =
      8 * (n : ℝ) ^ 3 + 1 by
        simp [profileRadialWordMaxTransitions]]
    have hnCube : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    have hnFour : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
    rw [show (8 * (n : ℝ) ^ 3 + 1) * (1 / (n : ℝ) ^ 4) =
      (8 * (n : ℝ) ^ 3 + 1) / (n : ℝ) ^ 4 by ring,
      div_le_one hnFour]
    have hnCubeLe : 9 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
      rw [show (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n by ring]
      calc
        9 * (n : ℝ) ^ 3 ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hnCube
        _ = (n : ℝ) ^ 3 * n := by ring
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
      exact one_le_pow₀ (by linarith)
    linarith
  exact (AppendixPairMoment.pow_one_add_le_exp_nat_mul (by positivity)
      (profileRadialWordMaxTransitions n)).trans
    (Real.exp_le_exp.mpr hcost)

theorem eventually_fairSteps_boundedRadialLabelWordAtom_le_exp_one_mul_reference :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (center start : Point)
      (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n)),
      start ∈ radialBoundary n center ⟨1, by omega⟩ →
      fairSteps (boundedRadialLabelWordAtom n
          (profileRadialWordMaxTransitions n) center start word) ≤
        ENNReal.ofReal (Real.exp 1) *
          radialChainReference (annularIdealEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail := by
  filter_upwards
      [eventually_fairSteps_radialLabelWordAtom_le_common_pow_mul_reference,
        eventually_ge_atTop 10] with n hword hn10
  intro hn center start word hstart
  have hraw := hword hn word.1 center start word.2 hstart
  have hbase : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) ^ 4 :=
    le_add_of_nonneg_right (by positivity)
  have hlength : (word.1 : ℕ) ≤ profileRadialWordMaxTransitions n := by
    exact Nat.le_of_lt_succ word.1.2
  have hpowReal : (1 + 1 / (n : ℝ) ^ 4) ^ (word.1 : ℕ) ≤
      Real.exp 1 := by
    calc
      (1 + 1 / (n : ℝ) ^ 4) ^ (word.1 : ℕ) ≤
          (1 + 1 / (n : ℝ) ^ 4) ^
            profileRadialWordMaxTransitions n :=
        pow_le_pow_right₀ hbase hlength
      _ ≤ Real.exp 1 :=
        one_add_inv_pow_four_profileRadialWordMaxTransitions_le_exp_one hn10
  have hpowENN : ENNReal.ofReal (1 + 1 / (n : ℝ) ^ 4) ^
      (word.1 : ℕ) ≤ ENNReal.ofReal (Real.exp 1) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    exact ENNReal.ofReal_le_ofReal hpowReal
  exact hraw.trans (mul_le_mul_of_nonneg_right hpowENN bot_le)

/-- Summing the disjoint literal word atoms preserves the linear comparison.
The right side is a purely finite label-chain sum; its subsequent contour
enumeration does not mention stopping times. -/
theorem eventually_fairSteps_fixedProfileRadialWordFamilyAtom_le_ideal_sum :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (delta : ℝ)
      (center start : Point) (m : Profile n),
      start ∈ radialBoundary n center ⟨1, by omega⟩ →
      fairSteps (fixedProfileRadialWordFamilyAtom n delta center start m) ≤
        ENNReal.ofReal (Real.exp 1) *
          ∑ word : {word : BoundedRadialLabelWord n
              (profileRadialWordMaxTransitions n) //
              IsFixedProfileRadialWord n delta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail := by
  filter_upwards
      [eventually_fairSteps_boundedRadialLabelWordAtom_le_exp_one_mul_reference,
        eventually_ge_atTop 10] with n hword hn10
  intro hn delta center start m hstart
  rw [fairSteps_fixedProfileRadialWordFamilyAtom, Finset.mul_sum]
  exact Finset.sum_le_sum fun word _ ↦ hword hn center start word.1 hstart

end

end Erdos1165.AnnularRadialLinearUpper
