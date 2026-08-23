/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410SourceBands
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411

/-!
# Source-scale absorption for HLOZ Lemma 4.10

This file isolates the elementary analytic part of the last union bound in
Lemma 4.10.  Proposition 4.8 supplies a tail for the number of candidates of
order
`exp (C * m^(β_j-κ₁)) * log(m+1)^2`.  The post-hit race has exponent
`m^(β_j-κ₁+δ)`.  The extra `δ` therefore absorbs both the candidate cap and
the fixed 454-band union.
-/

namespace Erdos1166.HLOZLemma410SourceAbsorption

open Filter
open scoped ENNReal BigOperators Topology

open HLOZProp47Parameters HLOZLemma411 HLOZLemma410SourceBands

/-- The first candidate exponent is exactly `κ₁`. -/
theorem sourceBeta_zero_eq_kappaOne (alpha : ℝ) :
    sourceBeta alpha (0 : SourceBetaBandIndex) = kappaOne := by
  norm_num [sourceBeta, sourceBetaNat, sourceBetaStep]

/-- Candidate exponents increase from `κ₁`. -/
theorem kappaOne_le_sourceBeta {alpha : ℝ} (halpha : alpha ≤ kappaTwo)
    (j : SourceBetaBandIndex) :
    kappaOne ≤ sourceBeta alpha j := by
  rw [← sourceBeta_zero_eq_kappaOne alpha]
  unfold sourceBeta sourceBetaNat
  have hstep := sourceBetaStep_pos halpha
  gcongr
  exact_mod_cast j.1.zero_le

/-- The exponent in the post-hit race is the candidate exponent plus the
source's spare `δ`. -/
theorem sourceBetaPrevious_sub_alpha
    (alpha : ℝ) (j : SourceBetaBandIndex) :
    sourceBetaPrevious alpha j - alpha =
      (sourceBeta alpha j - kappaOne) + delta := by
  rw [sourceBeta_eq_previous_add]
  unfold sourceBetaStep
  ring

/-- The integer radius enclosing `exp(m^α)` is nonzero. -/
theorem sourceLemma410Radius_pos (m : ℕ) (alpha : ℝ) :
    0 < sourceLemma410Radius m alpha := by
  rw [sourceLemma410Radius, Nat.ceil_pos]
  exact Real.exp_pos _

/-- Upward rounding preserves the lower logarithmic scale. -/
theorem nat_rpow_le_log_sourceLemma410Radius (m : ℕ) (alpha : ℝ) :
    (m : ℝ) ^ alpha ≤ Real.log (sourceLemma410Radius m alpha : ℝ) := by
  apply (Real.le_log_iff_exp_le (by
    exact_mod_cast sourceLemma410Radius_pos m alpha)).2
  exact Nat.le_ceil _

/-- Upward rounding costs at most `log 2` in the logarithm. -/
theorem log_sourceLemma410Radius_le_nat_rpow_add_log_two
    (m : ℕ) (alpha : ℝ) :
    Real.log (sourceLemma410Radius m alpha : ℝ) ≤
      (m : ℝ) ^ alpha + Real.log 2 := by
  apply (Real.log_le_iff_le_exp (by
    exact_mod_cast sourceLemma410Radius_pos m alpha)).2
  have hceil : (sourceLemma410Radius m alpha : ℝ) <
      Real.exp ((m : ℝ) ^ alpha) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  calc
    (sourceLemma410Radius m alpha : ℝ) ≤
        Real.exp ((m : ℝ) ^ alpha) + 1 := hceil.le
    _ ≤ 2 * Real.exp ((m : ℝ) ^ alpha) := by
      have hnonneg : 0 ≤ (m : ℝ) ^ alpha := Real.rpow_nonneg (by positivity) _
      have hone := Real.one_le_exp hnonneg
      linarith
    _ = Real.exp ((m : ℝ) ^ alpha + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

/-- On the source grid, the rounded radius has logarithm at most twice its
unrounded logarithmic scale. -/
theorem log_sourceLemma410Radius_le_two_mul_nat_rpow
    (m : ℕ) (alpha : ℝ) (hm : 1 ≤ m) (halpha : 0 ≤ alpha) :
    Real.log (sourceLemma410Radius m alpha : ℝ) ≤
      2 * (m : ℝ) ^ alpha := by
  have hpow : 1 ≤ (m : ℝ) ^ alpha :=
    Real.one_le_rpow (by exact_mod_cast hm) halpha
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  linarith [log_sourceLemma410Radius_le_nat_rpow_add_log_two m alpha]

/-- The two explicit radius side conditions required by the checked planar
race theorem hold uniformly over the finite source grid. -/
theorem eventually_sourceLemma410Radius_bounds :
    ∀ᶠ m : ℕ in atTop, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      2 ≤ sourceLemma410Radius m (alphaValue a) ∧
      2540 ≤ 2 * Real.log (sourceLemma410Radius m (alphaValue a)) := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop delta_pos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop 1270)
  filter_upwards [hlarge, eventually_ge_atTop 2] with m hlarge hm
  intro a _ha
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hdeltaAlpha : delta ≤ alphaValue a := by
    rw [alphaValue]
    have hfac : (1 : ℝ) ≤ (a.1 : ℝ) + 1 := by
      have ha0 : (0 : ℝ) ≤ (a.1 : ℝ) := Nat.cast_nonneg _
      linarith
    nlinarith [delta_pos]
  have hpowMono : (m : ℝ) ^ delta ≤ (m : ℝ) ^ alphaValue a :=
    Real.rpow_le_rpow_of_exponent_le hmReal hdeltaAlpha
  have hlogLower := nat_rpow_le_log_sourceLemma410Radius m (alphaValue a)
  constructor
  · have hpowOne : 1 ≤ (m : ℝ) ^ alphaValue a :=
      Real.one_le_rpow hmReal (alphaValue_pos a).le
    have hexp : 2 < Real.exp ((m : ℝ) ^ alphaValue a) := by
      exact Real.exp_one_gt_two.trans_le
        (Real.exp_le_exp.mpr hpowOne)
    have hceil : (2 : ℝ) ≤
        (sourceLemma410Radius m (alphaValue a) : ℝ) := by
      exact hexp.le.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  · linarith

/-- Removing one after upward rounding retains half of a real number once
that number is at least two. -/
theorem half_rpow_le_sourceBetaRaceCount
    (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex)
    (htwo : 2 ≤ (m : ℝ) ^ sourceBetaPrevious alpha j) :
    (1 / 2 : ℝ) * (m : ℝ) ^ sourceBetaPrevious alpha j ≤
      (sourceBetaRaceCount m alpha j : ℝ) := by
  let x := (m : ℝ) ^ sourceBetaPrevious alpha j
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) htwo
  have hceilpos : 0 < Nat.ceil x := Nat.ceil_pos.mpr hxpos
  have hxceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  rw [sourceBetaRaceCount, Nat.cast_sub (by omega : 1 ≤ Nat.ceil x)]
  dsimp [x] at htwo hxceil ⊢
  norm_num
  linarith

/-- The rounded race exponent dominates the source power
`m^(β_j-κ₁+δ)` with a safe factor `1/96`. -/
theorem sourceBetaRace_exponent_lower
    (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex)
    (hm : 1 ≤ m) (halpha0 : 0 < alpha)
    (htwo : 2 ≤ (m : ℝ) ^ sourceBetaPrevious alpha j) :
    (1 / 96 : ℝ) * (m : ℝ) ^
        ((sourceBeta alpha j - kappaOne) + delta) ≤
      (sourceBetaRaceCount m alpha j : ℝ) *
        (1 / (24 * Real.log (sourceLemma410Radius m alpha))) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogpos : 0 < Real.log (sourceLemma410Radius m alpha : ℝ) := by
    have hpowgt : 1 < (m : ℝ) ^ alpha := by
      have hmgt : (1 : ℝ) < m := by
        by_cases hmeq : m = 1
        · subst m
          norm_num at htwo
        · exact_mod_cast (show 1 < m by omega)
      exact Real.one_lt_rpow hmgt halpha0
    exact lt_trans (by norm_num : (0 : ℝ) < 1)
      (hpowgt.trans_le (nat_rpow_le_log_sourceLemma410Radius m alpha))
  have hlogUpper := log_sourceLemma410Radius_le_two_mul_nat_rpow
    m alpha hm halpha0.le
  have hq := half_rpow_le_sourceBetaRaceCount m alpha j htwo
  have hpowpos : 0 < (m : ℝ) ^ alpha := Real.rpow_pos_of_pos hmpos _
  have hdenpos : 0 < 24 * Real.log (sourceLemma410Radius m alpha) :=
    mul_pos (by norm_num) hlogpos
  have hmain : (1 / 96 : ℝ) * (m : ℝ) ^
        ((sourceBeta alpha j - kappaOne) + delta) ≤
      (sourceBetaRaceCount m alpha j : ℝ) /
        (24 * Real.log (sourceLemma410Radius m alpha)) := by
    apply (le_div_iff₀ hdenpos).2
    rw [← sourceBetaPrevious_sub_alpha]
    rw [Real.rpow_sub hmpos]
    have hratio :
        Real.log (sourceLemma410Radius m alpha) / (m : ℝ) ^ alpha ≤ 2 :=
      (div_le_iff₀ hpowpos).2 hlogUpper
    calc
      (1 / 96 : ℝ) *
            ((m : ℝ) ^ sourceBetaPrevious alpha j / (m : ℝ) ^ alpha) *
            (24 * Real.log (sourceLemma410Radius m alpha)) =
          (1 / 4 : ℝ) * (m : ℝ) ^ sourceBetaPrevious alpha j *
            (Real.log (sourceLemma410Radius m alpha) / (m : ℝ) ^ alpha) := by
        field_simp
        ring
      _ ≤ (1 / 4 : ℝ) * (m : ℝ) ^ sourceBetaPrevious alpha j * 2 := by
        gcongr
      _ = (1 / 2 : ℝ) * (m : ℝ) ^ sourceBetaPrevious alpha j := by ring
      _ ≤ (sourceBetaRaceCount m alpha j : ℝ) := hq
  simpa [div_eq_mul_inv] using hmain

/-! ## The Proposition 4.8 candidate cap -/

/-- The source-shaped deterministic cap for the number of candidates in
the `j`th band. -/
noncomputable def sourceBetaCandidateCap
    (C : ℝ) (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℕ :=
  Nat.ceil
    (Real.exp (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne)) *
      Real.log ((m : ℝ) + 1) ^ 2)

/-- The source-shaped per-band tail furnished by Proposition 4.8. -/
noncomputable def sourceBetaCandidateTail (d : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2))

/-- A ceiling-safe exponential upper bound for the real size of the
candidate cap. -/
theorem sourceBetaCandidateCap_cast_le_exp
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) (alpha : ℝ)
    (j : SourceBetaBandIndex) :
    (sourceBetaCandidateCap C m alpha j : ℝ) ≤
      Real.exp
        (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
          Real.log ((m : ℝ) + 1) ^ 2 + 1) := by
  let E := Real.exp (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne))
  let L := Real.log ((m : ℝ) + 1)
  have hpow : 0 ≤ (m : ℝ) ^ (sourceBeta alpha j - kappaOne) :=
    Real.rpow_nonneg (by positivity) _
  have hE : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (mul_nonneg hC hpow)
  have hL : 0 ≤ L ^ 2 := sq_nonneg L
  have hceil : (sourceBetaCandidateCap C m alpha j : ℝ) <
      E * L ^ 2 + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg (Real.exp_nonneg _) hL)
  calc
    (sourceBetaCandidateCap C m alpha j : ℝ) ≤ E * L ^ 2 + 1 := hceil.le
    _ ≤ E * (L ^ 2 + 1) := by nlinarith
    _ ≤ E * Real.exp (L ^ 2 + 1) := by
      gcongr
      exact (Real.add_one_le_exp (L ^ 2)).trans
        (Real.exp_le_exp.mpr (by linarith))
    _ = Real.exp
        (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
          Real.log ((m : ℝ) + 1) ^ 2 + 1) := by
      dsimp [E, L]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Once the spare `δ`-power dominates the explicit cap exponent, one
candidate-band race is bounded by the desired stretched-log error. -/
theorem sourceBetaCandidateCap_mul_raceBound_le
    {C c : ℝ} (hC : 0 ≤ C) (m : ℕ) (alpha : ℝ)
    (j : SourceBetaBandIndex) (hm : 1 ≤ m) (halpha0 : 0 < alpha)
    (htwo : 2 ≤ (m : ℝ) ^ sourceBetaPrevious alpha j)
    (hdom :
      C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
          Real.log ((m : ℝ) + 1) ^ 2 + 1 +
          c * Real.log ((m : ℝ) + 1) ^ 2 ≤
        (1 / 96 : ℝ) *
          (m : ℝ) ^ ((sourceBeta alpha j - kappaOne) + delta)) :
    (sourceBetaCandidateCap C m alpha j : ℝ≥0∞) *
        sourceBetaRaceBound m alpha j ≤
      ENNReal.ofReal
        (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2)) := by
  have hrace := sourceBetaRace_exponent_lower
    m alpha j hm halpha0 htwo
  have hcap := sourceBetaCandidateCap_cast_le_exp hC m alpha j
  have hreal :
      (sourceBetaCandidateCap C m alpha j : ℝ) *
          Real.exp (-((sourceBetaRaceCount m alpha j : ℝ) *
            (1 / (24 * Real.log (sourceLemma410Radius m alpha))))) ≤
        Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2) := by
    calc
      (sourceBetaCandidateCap C m alpha j : ℝ) *
          Real.exp (-((sourceBetaRaceCount m alpha j : ℝ) *
            (1 / (24 * Real.log (sourceLemma410Radius m alpha))))) ≤
          Real.exp
              (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
                Real.log ((m : ℝ) + 1) ^ 2 + 1) *
            Real.exp (-((sourceBetaRaceCount m alpha j : ℝ) *
              (1 / (24 * Real.log (sourceLemma410Radius m alpha))))) := by
        gcongr
      _ = Real.exp
          (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
            Real.log ((m : ℝ) + 1) ^ 2 + 1 -
            ((sourceBetaRaceCount m alpha j : ℝ) *
              (1 / (24 * Real.log (sourceLemma410Radius m alpha))))) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2) := by
        apply Real.exp_le_exp.mpr
        linarith
  rw [sourceBetaRaceBound]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ (sourceBetaCandidateCap C m alpha j : ℝ))]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## Eventual source-scale comparisons -/

/-- A fixed multiple of `m^b` is eventually absorbed by `m^(b+e)` for
every positive spare exponent `e`. -/
theorem eventually_const_mul_rpow_le_rpow_add
    {C d b e : ℝ} (hC : 0 ≤ C) (hd : 0 < d) (he : 0 < e) :
    ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ b ≤ d * (m : ℝ) ^ (b + e) := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hm hm1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hratio : C ≤ d * (m : ℝ) ^ e := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hm
  calc
    C * (m : ℝ) ^ b ≤ (d * (m : ℝ) ^ e) * (m : ℝ) ^ b := by
      gcongr
    _ = d * (m : ℝ) ^ (b + e) := by
      rw [Real.rpow_add hmpos]
      ring

/-- A shifted logarithmic square is eventually below any fixed positive
multiple of a positive power. -/
theorem eventually_const_mul_log_add_one_sq_le_rpow
    {A d e : ℝ} (hA : 0 ≤ A) (hd : 0 < d) (he : 0 < e)
    (heOne : e ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      A * Real.log ((m : ℝ) + 1) ^ 2 ≤ d * (m : ℝ) ^ e := by
  by_cases hAzero : A = 0
  · subst A
    exact Filter.Eventually.of_forall fun m ↦ by
      have hp : 0 ≤ (m : ℝ) ^ e := Real.rpow_nonneg (by positivity) _
      norm_num
      exact mul_nonneg hd.le hp
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  have hraw := (tendsto_add_atTop_nat 1).eventually
    (eventually_const_mul_log_sq_le_rpow
      (c := A) (c₁ := d / 2) (a := e) hApos (by positivity) he)
  have htwo : (2 : ℝ) ^ e ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) heOne
    simpa only [Real.rpow_one] using this
  filter_upwards [hraw, eventually_ge_atTop 1] with m hraw hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hbase : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hrpow : (((m + 1 : ℕ) : ℝ)) ^ e ≤
      (2 * (m : ℝ)) ^ e := Real.rpow_le_rpow (by positivity) hbase he.le
  calc
    A * Real.log ((m : ℝ) + 1) ^ 2 =
        A * Real.log (((m + 1 : ℕ) : ℝ)) ^ 2 := by norm_num
    _ ≤ (d / 2) * (((m + 1 : ℕ) : ℝ)) ^ e := hraw
    _ ≤ (d / 2) * (2 * (m : ℝ)) ^ e := by gcongr
    _ = (d / 2) * ((2 : ℝ) ^ e * (m : ℝ) ^ e) := by
      rw [Real.mul_rpow (by norm_num) hm0]
    _ ≤ (d / 2) * (2 * (m : ℝ) ^ e) := by gcongr
    _ = d * (m : ℝ) ^ e := by ring

/-- For each fixed source band, all rounding hypotheses and the complete
candidate-cap/race absorption inequality hold eventually. -/
theorem eventually_sourceBetaBand_analytic_bounds
    {C c alpha : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (halpha0 : 0 < alpha) (halpha : alpha ≤ kappaTwo)
    (j : SourceBetaBandIndex) :
    ∀ᶠ m : ℕ in atTop,
      1 ≤ m ∧
      2 ≤ (m : ℝ) ^ sourceBetaPrevious alpha j ∧
      C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne) +
          Real.log ((m : ℝ) + 1) ^ 2 + 1 +
          c * Real.log ((m : ℝ) + 1) ^ 2 ≤
        (1 / 96 : ℝ) *
          (m : ℝ) ^ ((sourceBeta alpha j - kappaOne) + delta) := by
  let b := sourceBeta alpha j - kappaOne
  have hb : 0 ≤ b := sub_nonneg.mpr (kappaOne_le_sourceBeta halpha j)
  have hprev : 0 < sourceBetaPrevious alpha j := by
    unfold sourceBetaPrevious sourceBetaNat
    have hj : 0 ≤ (j.1 : ℝ) * sourceBetaStep alpha :=
      mul_nonneg (by positivity) (sourceBetaStep_pos halpha).le
    linarith [delta_pos]
  have htwo : ∀ᶠ m : ℕ in atTop,
      2 ≤ (m : ℝ) ^ sourceBetaPrevious alpha j := by
    exact ((tendsto_rpow_atTop hprev).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop 2)
  have hCpow := eventually_const_mul_rpow_le_rpow_add
    (C := C) (d := (1 : ℝ) / 384) (b := b) (e := delta)
    hC (by norm_num) delta_pos
  have hlog := eventually_const_mul_log_add_one_sq_le_rpow
    (A := c + 1) (d := (1 : ℝ) / 768) (e := delta)
    (by linarith) (by norm_num) delta_pos (by norm_num [delta])
  have hone := eventually_const_mul_rpow_le_rpow_add
    (C := (1 : ℝ)) (d := (1 : ℝ) / 768) (b := 0) (e := delta)
    (by norm_num) (by norm_num) delta_pos
  filter_upwards [eventually_ge_atTop 1, htwo, hCpow, hlog, hone]
    with m hm htwo hCpow hlog hone
  refine ⟨hm, htwo, ?_⟩
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmb : 1 ≤ (m : ℝ) ^ b := Real.one_le_rpow hmReal hb
  have hsmall :
      (c + 1) * Real.log ((m : ℝ) + 1) ^ 2 + 1 ≤
        (1 / 384 : ℝ) * (m : ℝ) ^ (b + delta) := by
    have hone' : 1 ≤ (1 / 768 : ℝ) * (m : ℝ) ^ delta := by
      simpa only [Real.rpow_zero, one_mul, zero_add] using hone
    have hsum :
        (c + 1) * Real.log ((m : ℝ) + 1) ^ 2 + 1 ≤
          (1 / 384 : ℝ) * (m : ℝ) ^ delta := by
      linarith
    have hpoweq : (m : ℝ) ^ (b + delta) =
        (m : ℝ) ^ b * (m : ℝ) ^ delta := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < m)]
    rw [hpoweq]
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) delta]
  change
    C * (m : ℝ) ^ b + Real.log ((m : ℝ) + 1) ^ 2 + 1 +
        c * Real.log ((m : ℝ) + 1) ^ 2 ≤
      (1 / 96 : ℝ) * (m : ℝ) ^ (b + delta)
  have hlogs :
      Real.log ((m : ℝ) + 1) ^ 2 + 1 +
          c * Real.log ((m : ℝ) + 1) ^ 2 =
        (c + 1) * Real.log ((m : ℝ) + 1) ^ 2 + 1 := by ring
  nlinarith [hlogs]

/-- The fixed finite alpha/band grids let the preceding pointwise eventual
bounds be chosen with one common level threshold. -/
theorem eventually_all_sourceBetaBand_analytic_bounds
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) :
    ∀ᶠ m : ℕ in atTop, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      1 ≤ m ∧
      2 ≤ (m : ℝ) ^ sourceBetaPrevious (alphaValue a) j ∧
      C * (m : ℝ) ^ (sourceBeta (alphaValue a) j - kappaOne) +
          Real.log ((m : ℝ) + 1) ^ 2 + 1 +
          c * Real.log ((m : ℝ) + 1) ^ 2 ≤
        (1 / 96 : ℝ) *
          (m : ℝ) ^
            ((sourceBeta (alphaValue a) j - kappaOne) + delta) := by
  have hpairs : ∀ᶠ m : ℕ in atTop,
      ∀ p : AlphaIndex × SourceBetaBandIndex,
        alphaValue p.1 ≤ kappaTwo →
        1 ≤ m ∧
        2 ≤ (m : ℝ) ^ sourceBetaPrevious (alphaValue p.1) p.2 ∧
        C * (m : ℝ) ^ (sourceBeta (alphaValue p.1) p.2 - kappaOne) +
            Real.log ((m : ℝ) + 1) ^ 2 + 1 +
            c * Real.log ((m : ℝ) + 1) ^ 2 ≤
          (1 / 96 : ℝ) *
            (m : ℝ) ^
              ((sourceBeta (alphaValue p.1) p.2 - kappaOne) + delta) := by
    rw [Filter.eventually_all]
    intro p
    by_cases ha : alphaValue p.1 ≤ kappaTwo
    · filter_upwards [eventually_sourceBetaBand_analytic_bounds
        hC hc (alphaValue_pos p.1) ha p.2] with m hm
      exact fun _ ↦ hm
    · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
  filter_upwards [hpairs] with m hm
  intro a ha j
  exact hm (a, j) ha

/-- A convenient positive constant retained after both the Proposition 4.8
tail and the race error are combined. -/
noncomputable def sourceLemma410AbsorptionConstant (d : ℝ) : ℝ :=
  min d 1 / 4

theorem sourceLemma410AbsorptionConstant_pos {d : ℝ} (hd : 0 < d) :
    0 < sourceLemma410AbsorptionConstant d := by
  unfold sourceLemma410AbsorptionConstant
  positivity

theorem four_mul_sourceLemma410AbsorptionConstant_le_left (d : ℝ) :
    4 * sourceLemma410AbsorptionConstant d ≤ d := by
  unfold sourceLemma410AbsorptionConstant
  rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
  exact min_le_left _ _

theorem four_mul_sourceLemma410AbsorptionConstant_le_one (d : ℝ) :
    4 * sourceLemma410AbsorptionConstant d ≤ 1 := by
  unfold sourceLemma410AbsorptionConstant
  rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
  exact min_le_right _ _

/-- The numerical factor from two errors in each of 454 bands is absorbed
by one quarter of the smaller stretched-log exponent. -/
theorem eventually_sourceLemma410_fixed_band_sum_absorbed
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      (908 : ℝ) * Real.exp
          (-(4 * sourceLemma410AbsorptionConstant d) *
            Real.log ((m : ℝ) + 1) ^ 2) ≤
        Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2) := by
  let c := sourceLemma410AbsorptionConstant d
  have hc : 0 < c := sourceLemma410AbsorptionConstant_pos hd
  have habsorb := (tendsto_add_atTop_nat 1).eventually
    (eventually_three_rpow_mul_exp_neg_log_sq_le
      (c := 4 * c) (b := (1 : ℝ)) (by positivity) (by norm_num))
  filter_upwards [habsorb, eventually_ge_atTop 302] with m habsorb hm
  have hfactor : (908 : ℝ) ≤ 3 * (((m : ℝ) + 1) ^ (1 : ℝ)) := by
    rw [Real.rpow_one]
    exact_mod_cast (show 908 ≤ 3 * (m + 1) by omega)
  have hLnonneg : 0 ≤ Real.log (((m + 1 : ℕ) : ℝ)) ^ 2 := sq_nonneg _
  calc
    (908 : ℝ) * Real.exp
          (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2) ≤
        3 * (((m + 1 : ℕ) : ℝ) ^ (1 : ℝ)) *
          Real.exp (-(4 * c) * Real.log (((m + 1 : ℕ) : ℝ)) ^ 2) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ ≤ Real.exp (-(4 * c / 2) *
        Real.log (((m + 1 : ℕ) : ℝ)) ^ 2) := habsorb
    _ ≤ Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2) := by
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Fully checked analytic absorption of the 454-band sum.  Its only input
is the pointwise Proposition 4.8 candidate tail; the cap and race factors
are the exact source-shaped definitions above. -/
theorem eventually_sourceBetaBand_sum_absorption
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      (∑ j : SourceBetaBandIndex,
          (sourceBetaCandidateTail d m +
            (sourceBetaCandidateCap C m (alphaValue a) j : ℝ≥0∞) *
              sourceBetaRaceBound m (alphaValue a) j)) ≤
        ENNReal.ofReal
          (Real.exp
            (-sourceLemma410AbsorptionConstant d *
              Real.log ((m : ℝ) + 1) ^ 2)) := by
  let c := sourceLemma410AbsorptionConstant d
  have hc : 0 < c := sourceLemma410AbsorptionConstant_pos hd
  have hall := eventually_all_sourceBetaBand_analytic_bounds
    (C := C) (c := (1 : ℝ)) hC (by norm_num)
  filter_upwards [hall, eventually_sourceLemma410_fixed_band_sum_absorbed hd]
    with m hall habsorb
  intro a ha
  have hfourD : 4 * c ≤ d := by
    exact four_mul_sourceLemma410AbsorptionConstant_le_left d
  have hfourOne : 4 * c ≤ 1 := by
    exact four_mul_sourceLemma410AbsorptionConstant_le_one d
  have hL : 0 ≤ Real.log ((m : ℝ) + 1) ^ 2 := sq_nonneg _
  have htail : sourceBetaCandidateTail d m ≤
      ENNReal.ofReal
        (Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  have hrace (j : SourceBetaBandIndex) :
      (sourceBetaCandidateCap C m (alphaValue a) j : ℝ≥0∞) *
          sourceBetaRaceBound m (alphaValue a) j ≤
        ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2)) := by
    rcases hall a ha j with ⟨hm, htwo, hdom⟩
    apply sourceBetaCandidateCap_mul_raceBound_le
      hC m (alphaValue a) j hm (alphaValue_pos a) htwo
    have hdomOne :
        C * (m : ℝ) ^
              (sourceBeta (alphaValue a) j - kappaOne) +
            Real.log ((m : ℝ) + 1) ^ 2 + 1 +
            Real.log ((m : ℝ) + 1) ^ 2 ≤
          (1 / 96 : ℝ) *
            (m : ℝ) ^
              ((sourceBeta (alphaValue a) j - kappaOne) + delta) := by
      simpa only [one_mul] using hdom
    nlinarith
  calc
    (∑ j : SourceBetaBandIndex,
        (sourceBetaCandidateTail d m +
          (sourceBetaCandidateCap C m (alphaValue a) j : ℝ≥0∞) *
            sourceBetaRaceBound m (alphaValue a) j)) ≤
        ∑ _j : SourceBetaBandIndex,
          (ENNReal.ofReal
              (Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2)) +
            ENNReal.ofReal
              (Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2))) := by
      gcongr with j
      exact hrace j
    _ = (908 : ℕ) * ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2)) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      norm_num [SourceBetaBandIndex, mul_add, ← add_mul]
    _ = ENNReal.ofReal
          ((908 : ℝ) *
            Real.exp (-(4 * c) * Real.log ((m : ℝ) + 1) ^ 2)) := by
      rw [← ENNReal.ofReal_natCast]
      norm_num only [Nat.cast_ofNat]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 908)]
    _ ≤ ENNReal.ofReal
          (Real.exp (-c * Real.log ((m : ℝ) + 1) ^ 2)) :=
      ENNReal.ofReal_le_ofReal habsorb

end Erdos1166.HLOZLemma410SourceAbsorption
