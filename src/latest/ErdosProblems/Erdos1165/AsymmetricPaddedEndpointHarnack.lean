/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionScale
import ErdosProblems.Erdos1165.RealRadiusPoissonEndpoint

/-!
# Quantitative endpoint mixing across the asymmetric padding

The retained separation endpoint is at radius `r_{q,l}`, whereas the
recursive tail is cut immediately outside the padded radius
`r_{q,l+ceil(3 log q)}`.  This file records the elementary scale comparison
which makes the latter boundary remote from the former one.  It is kept
separate from the stopped-word disintegration so that the analytic Harnack
estimate can be reused by every retained outer skeleton.
-/

open Filter Real
open scoped ENNReal

namespace Erdos1165.AsymmetricPaddedEndpointHarnack

open AppendixPair AppendixPairMoment PotentialEuclideanGeometry
open PotentialRadialGlobal RealRadiusPoissonKernel ThickPoint

noncomputable section

/-- The radius immediately outside the padded cut is at most
`3 q^{-3}` times the retained separation radius. -/
theorem paddedPredecessorRadius_le
    {q l : ℕ} (hq : 1 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 1 ≤ decorrelationPadding q) :
    scaleRadius q (pairPrefixScale q l - 1) ≤
      3 * scaleRadius q l / (q : ℝ) ^ 3 := by
  have hadd : l + decorrelationPadding q ≤ q := by
    unfold decorrelationCutoff at hl
    exact Nat.add_le_of_le_sub hpadding hl
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  have hpadLower : 3 * Real.log (q : ℝ) ≤
      (decorrelationPadding q : ℝ) := by
    unfold decorrelationPadding
    exact Nat.le_ceil _
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hpred : pairPrefixScale q l - 1 =
      l + (decorrelationPadding q - 1) := by
    rw [hpref]
    omega
  have hlq : l ≤ q := hl.trans (Nat.sub_le _ _)
  have hpredq : pairPrefixScale q l - 1 ≤ q := by omega
  rw [scaleRadius_of_le hlq, scaleRadius_of_le hpredq, regularRadius,
    regularRadius, hpred]
  have hcast : ((l + (decorrelationPadding q - 1) : ℕ) : ℝ) =
      (l : ℝ) + (decorrelationPadding q : ℝ) - 1 := by
    rw [Nat.cast_add, Nat.cast_sub hpadPos]
    push_cast
    ring
  rw [hcast]
  have hqpow : 0 < (q : ℝ) ^ 3 := pow_pos hqpos _
  have hqpow9 : 0 < (q : ℝ) ^ 9 := pow_pos hqpos _
  have hexpBase : 0 < Real.exp ((q : ℝ) - (l : ℝ)) := Real.exp_pos _
  have hexpPad : Real.exp (1 - (decorrelationPadding q : ℝ)) ≤
      3 / (q : ℝ) ^ 3 := by
    calc
      Real.exp (1 - (decorrelationPadding q : ℝ)) =
          Real.exp 1 / Real.exp (decorrelationPadding q : ℝ) := by
            rw [Real.exp_sub]
      _ ≤ 3 / Real.exp (decorrelationPadding q : ℝ) := by
            exact div_le_div_of_nonneg_right Real.exp_one_lt_three.le
              (Real.exp_nonneg _)
      _ ≤ 3 / Real.exp (3 * Real.log (q : ℝ)) := by
            exact div_le_div_of_nonneg_left (by norm_num)
              (Real.exp_pos _) (Real.exp_le_exp.mpr hpadLower)
      _ = 3 / (q : ℝ) ^ 3 := by
            congr 1
            calc
              Real.exp (3 * Real.log (q : ℝ)) =
                  (Real.exp (Real.log (q : ℝ))) ^ (3 : ℕ) := by
                    simpa only [Nat.cast_ofNat] using
                      Real.exp_nat_mul (Real.log (q : ℝ)) 3
              _ = (q : ℝ) ^ 3 := by rw [Real.exp_log hqpos]
  have hfactor :
      Real.exp ((q : ℝ) - ((l : ℝ) +
          (decorrelationPadding q : ℝ) - 1)) =
        Real.exp ((q : ℝ) - (l : ℝ)) *
          Real.exp (1 - (decorrelationPadding q : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  calc
    Real.exp ((q : ℝ) - (l : ℝ)) *
          Real.exp (1 - (decorrelationPadding q : ℝ)) * (q : ℝ) ^ 9 ≤
        Real.exp ((q : ℝ) - (l : ℝ)) *
          (3 / (q : ℝ) ^ 3) * (q : ℝ) ^ 9 := by
            gcongr
    _ = 3 * (Real.exp ((q : ℝ) - (l : ℝ)) * (q : ℝ) ^ 9) /
          (q : ℝ) ^ 3 := by field_simp

/-- Every retained separation radius in the far range is at least `q^9`. -/
theorem pow_nine_le_retainedRadius
    {q l : ℕ} (hq : 1 ≤ q) (hl : l ≤ decorrelationCutoff q) :
    (q : ℝ) ^ 9 ≤ scaleRadius q l := by
  have hlq : l ≤ q := hl.trans (Nat.sub_le _ _)
  rw [scaleRadius_of_le hlq, regularRadius]
  have hlqR : (l : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlq
  have hexponent : 0 ≤ (q : ℝ) - (l : ℝ) := sub_nonneg.mpr hlqR
  have hexp : 1 ≤ Real.exp ((q : ℝ) - (l : ℝ)) :=
    Real.one_le_exp hexponent
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hpow : 0 ≤ (q : ℝ) ^ 9 := le_of_lt (pow_pos hqpos 9)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hpow

/-- The logarithmic padding makes the child boundary sufficiently small
relative to the retained separation boundary for the real-radius Poisson
comparison.  The deliberately generous threshold keeps the ensuing
constant bookkeeping independent of the value of the global potential
kernel constant. -/
theorem paddedPoissonParameters
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 1 ≤ decorrelationPadding q)
    (hconstant : globalRadialConstant ≤ (q : ℝ)) :
    let R := scaleRadius q l
    let inner := scaleRadius q (pairPrefixScale q l - 1)
    let S := R / 2
    0 ≤ inner ∧ inner + 2 ≤ R ∧ inner + 2 ≤ S ∧ S + 4 ≤ R ∧
      0 < realGreenPoleLower R S inner ∧
      realPoissonKernelRelativeError R S inner ≤
        1 / (6 * (q : ℝ) ^ 2) := by
  let R := scaleRadius q l
  let inner := scaleRadius q (pairPrefixScale q l - 1)
  let S := R / 2
  let Q : ℝ := q
  let C : ℝ := globalRadialConstant
  have hQ : (10000 : ℝ) ≤ Q := by
    dsimp only [Q]
    exact_mod_cast hq
  have hQpos : 0 < Q := by positivity
  have hQone : 1 ≤ Q := by linarith
  have hQ3pos : 0 < Q ^ 3 := pow_pos hQpos _
  have hQ2pos : 0 < Q ^ 2 := pow_pos hQpos _
  have hQ9pos : 0 < Q ^ 9 := pow_pos hQpos _
  have hRlower : Q ^ 9 ≤ R := by
    dsimp only [Q, R]
    exact pow_nine_le_retainedRadius (by omega) hl
  have hRpos : 0 < R := hQ9pos.trans_le hRlower
  have hR0 : 0 ≤ R := hRpos.le
  have hinner0 : 0 ≤ inner := by
    dsimp only [inner]
    exact scaleRadius_nonneg _ _
  have hinnerRaw : inner ≤ 3 * R / Q ^ 3 := by
    dsimp only [inner, R, Q]
    exact paddedPredecessorRadius_le (by omega) hl hpadding hpadPos
  have hQ3large : (1000 : ℝ) ≤ Q ^ 3 := by
    have hp : (10 : ℝ) ^ 3 ≤ Q ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith : (10 : ℝ) ≤ Q) 3
    norm_num at hp ⊢
    linarith
  have hratioSmall : 3 / Q ^ 3 ≤ (1 / 16 : ℝ) := by
    rw [div_le_iff₀ hQ3pos]
    nlinarith
  have hinnerSixteenth : inner ≤ R / 16 := by
    calc
      inner ≤ 3 * R / Q ^ 3 := hinnerRaw
      _ = (3 / Q ^ 3) * R := by ring
      _ ≤ (1 / 16 : ℝ) * R :=
        mul_le_mul_of_nonneg_right hratioSmall hR0
      _ = R / 16 := by ring
  have hRthirtyTwo : (32 : ℝ) ≤ R := by
    have hp : (2 : ℝ) ^ 9 ≤ Q ^ 9 :=
      pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ Q) 9
    norm_num at hp ⊢
    exact (by linarith : (32 : ℝ) ≤ Q ^ 9).trans hRlower
  have hsmall : inner + 2 ≤ R / 8 := by
    nlinarith
  have hinnerR : inner + 2 ≤ R := by nlinarith
  have hinnerS : inner + 2 ≤ S := by
    dsimp only [S]
    nlinarith
  have hcutOuter : S + 4 ≤ R := by
    dsimp only [S]
    nlinarith
  let B := realBoundaryPoleGap R inner
  let I := realIntermediatePoleGap S inner
  let D := S + inner + 2
  have hB : 7 * R / 8 ≤ B := by
    dsimp only [B]
    unfold realBoundaryPoleGap
    nlinarith
  have hI : 3 * R / 8 ≤ I := by
    dsimp only [I, S]
    unfold realIntermediatePoleGap
    nlinarith
  have hD : D ≤ 5 * R / 8 := by
    dsimp only [D, S]
    nlinarith
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hI
  have hDpos : 0 < D := by
    dsimp only [D, S]
    positivity
  have hratioBD : (7 / 5 : ℝ) ≤ B / D := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  have hlogSeven : (2 / 7 : ℝ) ≤ Real.log (7 / 5 : ℝ) := by
    nlinarith [Real.self_sub_one_le_mul_log
      (show (0 : ℝ) ≤ 7 / 5 by norm_num)]
  have hlogRatio : (2 / 7 : ℝ) ≤ Real.log (B / D) := by
    exact hlogSeven.trans
      (Real.log_le_log (by norm_num) hratioBD)
  have hpi : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  have hmain : (1 / 7 : ℝ) ≤
      (2 / Real.pi) * Real.log (B / D) := by
    calc
      (1 / 7 : ℝ) = (1 / 2 : ℝ) * (2 / 7 : ℝ) := by norm_num
      _ ≤ (2 / Real.pi) * (2 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right hpi (by norm_num)
      _ ≤ (2 / Real.pi) * Real.log (B / D) :=
        mul_le_mul_of_nonneg_left hlogRatio (by positivity)
  have hQ3R : Q ^ 3 ≤ R := by
    have hp : Q ^ 3 ≤ Q ^ 9 := pow_le_pow_right₀ hQone (by norm_num)
    exact hp.trans hRlower
  have hQ4Q9 : Q ^ 4 ≤ Q ^ 9 :=
    pow_le_pow_right₀ hQone (by norm_num)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact globalRadialConstant_pos.le
  have hCQ : C ≤ Q := by simpa only [C, Q] using hconstant
  have hCmul : C * Q ^ 3 ≤ R := by
    calc
      C * Q ^ 3 ≤ Q * Q ^ 3 :=
        mul_le_mul_of_nonneg_right hCQ (pow_nonneg hQpos.le _)
      _ = Q ^ 4 := by ring
      _ ≤ Q ^ 9 := hQ4Q9
      _ ≤ R := hRlower
  have hinnerMul : inner * Q ^ 3 ≤ 3 * R := by
    exact (le_div_iff₀ hQ3pos).mp (by simpa only [mul_comm] using hinnerRaw)
  have hCB : C / B ≤ 2 / Q ^ 3 := by
    rw [div_le_div_iff₀ hBpos hQ3pos]
    calc
      C * Q ^ 3 ≤ R := hCmul
      _ ≤ 2 * (7 * R / 8) := by
        calc
          R = 1 * R := by ring
          _ ≤ (7 / 4 : ℝ) * R :=
            mul_le_mul_of_nonneg_right (by norm_num) hR0
          _ = 2 * (7 * R / 8) := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hB (by norm_num)
  have hCI : C / I ≤ 4 / Q ^ 3 := by
    rw [div_le_div_iff₀ hIpos hQ3pos]
    calc
      C * Q ^ 3 ≤ R := hCmul
      _ ≤ 4 * (3 * R / 8) := by
        calc
          R = 1 * R := by ring
          _ ≤ (3 / 2 : ℝ) * R :=
            mul_le_mul_of_nonneg_right (by norm_num) hR0
          _ = 4 * (3 * R / 8) := by ring
      _ ≤ 4 * I := mul_le_mul_of_nonneg_left hI (by norm_num)
  have hboundary : realBoundaryPoleError R inner ≤ 16 / Q ^ 3 := by
    unfold realBoundaryPoleError
    change (2 * C + (2 * inner + 1)) / B ≤ 16 / Q ^ 3
    rw [div_le_div_iff₀ hBpos hQ3pos]
    calc
      (2 * C + (2 * inner + 1)) * Q ^ 3 =
          2 * (C * Q ^ 3) + 2 * (inner * Q ^ 3) + Q ^ 3 := by ring
      _ ≤ 2 * R + 2 * (3 * R) + R := by gcongr
      _ = 9 * R := by ring
      _ ≤ 14 * R := mul_le_mul_of_nonneg_right (by norm_num) hR0
      _ = 16 * (7 * R / 8) := by ring
      _ ≤ 16 * B := mul_le_mul_of_nonneg_left hB (by norm_num)
  have hreference : realReferencePoleError R inner ≤ 16 / Q ^ 3 := by
    unfold realReferencePoleError
    change (2 * C + 2 * inner) / B ≤ 16 / Q ^ 3
    rw [div_le_div_iff₀ hBpos hQ3pos]
    calc
      (2 * C + 2 * inner) * Q ^ 3 =
          2 * (C * Q ^ 3) + 2 * (inner * Q ^ 3) := by ring
      _ ≤ 2 * R + 2 * (3 * R) := by gcongr
      _ = 8 * R := by ring
      _ ≤ 14 * R := mul_le_mul_of_nonneg_right (by norm_num) hR0
      _ = 16 * (7 * R / 8) := by ring
      _ ≤ 16 * B := mul_le_mul_of_nonneg_left hB (by norm_num)
  have hintermediate : realIntermediatePoleError S inner ≤ 32 / Q ^ 3 := by
    unfold realIntermediatePoleError
    change (2 * C + 2 * inner) / I ≤ 32 / Q ^ 3
    rw [div_le_div_iff₀ hIpos hQ3pos]
    calc
      (2 * C + 2 * inner) * Q ^ 3 =
          2 * (C * Q ^ 3) + 2 * (inner * Q ^ 3) := by ring
      _ ≤ 2 * R + 2 * (3 * R) := by gcongr
      _ = 8 * R := by ring
      _ ≤ 12 * R := mul_le_mul_of_nonneg_right (by norm_num) hR0
      _ = 32 * (3 * R / 8) := by ring
      _ ≤ 32 * I := mul_le_mul_of_nonneg_left hI (by norm_num)
  have hlowerEstimate : (1 / 14 : ℝ) ≤
      realGreenPoleLower R S inner := by
    unfold realGreenPoleLower
    change (1 / 14 : ℝ) ≤
      (2 / Real.pi) * Real.log (B / D) - C / B - C / I -
        realBoundaryPoleError R inner
    have htail : 22 / Q ^ 3 ≤ (1 / 14 : ℝ) := by
      rw [div_le_iff₀ hQ3pos]
      nlinarith only [hQ3large]
    have herrors : C / B + C / I + realBoundaryPoleError R inner ≤
        22 / Q ^ 3 := by
      calc
        C / B + C / I + realBoundaryPoleError R inner ≤
            2 / Q ^ 3 + 4 / Q ^ 3 + 16 / Q ^ 3 := by
              gcongr
        _ = 22 / Q ^ 3 := by ring
    nlinarith only [hmain, htail, herrors]
  have hlower : 0 < realGreenPoleLower R S inner :=
    (by norm_num : (0 : ℝ) < 1 / 14).trans_le hlowerEstimate
  have hadditive : realGreenPoleAdditiveError R S inner ≤ 80 / Q ^ 3 := by
    unfold realGreenPoleAdditiveError
    calc
      2 * realBoundaryPoleError R inner + realReferencePoleError R inner +
          realIntermediatePoleError S inner ≤
        2 * (16 / Q ^ 3) + 16 / Q ^ 3 + 32 / Q ^ 3 := by
          gcongr
      _ = 80 / Q ^ 3 := by ring
  have hbudget : 80 / Q ^ 3 ≤
      (1 / (6 * Q ^ 2)) * (1 / 14 : ℝ) := by
    field_simp
    nlinarith only [hQ]
  have hrelative : realPoissonKernelRelativeError R S inner ≤
      1 / (6 * Q ^ 2) := by
    unfold realPoissonKernelRelativeError
    rw [div_le_iff₀ hlower]
    exact hadditive.trans (hbudget.trans
      (mul_le_mul_of_nonneg_left hlowerEstimate (by positivity)))
  exact ⟨hinner0, hinnerR, hinnerS, hcutOuter, hlower, by
    simpa only [Q] using hrelative⟩

/-- Uniform arbitrary-continuation Harnack bound at one sufficiently large
far-pair scale. -/
theorem weightedBoundaryExitMass_le_budget
    {q l : ℕ} (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 1 ≤ decorrelationPadding q)
    (hconstant : globalRadialConstant ≤ (q : ℝ))
    (center : Point) (F : Finset Point) (weight : Point → ℝ≥0∞)
    (hF : ∀ exit ∈ F,
      exit ∈ discBoundary center (scaleRadius q l))
    {u v : Point}
    (hu : u ∈ discBoundary center
      (scaleRadius q (pairPrefixScale q l - 1)))
    (hv : v ∈ discBoundary center
      (scaleRadius q (pairPrefixScale q l - 1))) :
    RealRadiusPoissonEndpoint.weightedBoundaryExitMass
        (scaleRadius q l) center F weight v ≤
      ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) *
        RealRadiusPoissonEndpoint.weightedBoundaryExitMass
          (scaleRadius q l) center F weight u := by
  let R := scaleRadius q l
  let inner := scaleRadius q (pairPrefixScale q l - 1)
  let S := R / 2
  have hp := paddedPoissonParameters hq hl hpadding hpadPos hconstant
  dsimp only at hp
  have hbudget0 : 0 ≤ 1 / (6 * (q : ℝ) ^ 2) := by positivity
  have hbudget1 : 1 / (6 * (q : ℝ) ^ 2) ≤ 1 := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hden : (1 : ℝ) ≤ 6 * (q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hqR
      nlinarith
    exact (div_le_one (by positivity)).2 hden
  have herror1 : realPoissonKernelRelativeError R S inner ≤ 1 :=
    hp.2.2.2.2.2.trans hbudget1
  have hraw := RealRadiusPoissonEndpoint.weightedBoundaryExitMass_le
    R S inner center F weight hF hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
      hu hv hp.2.2.2.2.1 herror1
  calc
    RealRadiusPoissonEndpoint.weightedBoundaryExitMass R center F weight v ≤
        ENNReal.ofReal (1 + realPoissonKernelRelativeError R S inner) *
          RealRadiusPoissonEndpoint.weightedBoundaryExitMass
            R center F weight u := hraw
    _ ≤ ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) *
          RealRadiusPoissonEndpoint.weightedBoundaryExitMass
            R center F weight u := by
      gcongr
      exact hp.2.2.2.2.2

/-- The endpoint oscillation can be paid once for every retained profile
gap at a scale.  Constrained profiles have at most `3 q^2` such gaps, so
the full product consumes at most the reserved `exp (1/2)` budget. -/
theorem endpointDistortion_pow_le_expHalf
    {q a : ℕ} (hq : 1 ≤ q) (ha : a ≤ 3 * q ^ 2) :
    ENNReal.ofReal (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ a ≤
      ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) := by
  have hqR : (0 : ℝ) < q := by
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hx0 : 0 ≤ 1 / (6 * (q : ℝ) ^ 2) := by positivity
  have hbase0 : 0 ≤ 1 + 1 / (6 * (q : ℝ) ^ 2) := by positivity
  have haR : (a : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by
    exact_mod_cast ha
  have hexponent :
      (a : ℝ) * (1 / (6 * (q : ℝ) ^ 2)) ≤ (1 / 2 : ℝ) := by
    calc
      (a : ℝ) * (1 / (6 * (q : ℝ) ^ 2)) =
          (a : ℝ) / (6 * (q : ℝ) ^ 2) := by ring
      _ ≤ (3 * (q : ℝ) ^ 2) / (6 * (q : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_right haR (by positivity)
      _ = (1 / 2 : ℝ) := by field_simp <;> norm_num
  rw [← ENNReal.ofReal_pow hbase0]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1 + 1 / (6 * (q : ℝ) ^ 2)) ^ a ≤
        (Real.exp (1 / (6 * (q : ℝ) ^ 2))) ^ a := by
      exact pow_le_pow_left₀ hbase0 (by
        simpa only [add_comm] using
          Real.add_one_le_exp (1 / (6 * (q : ℝ) ^ 2))) a
    _ = Real.exp ((a : ℝ) * (1 / (6 * (q : ℝ) ^ 2))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hexponent

/-- The padded Poisson hypotheses hold uniformly in the far separation
level once the ambient scale is large. -/
theorem eventually_paddedPoissonParameters :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      let R := scaleRadius q l
      let inner := scaleRadius q (pairPrefixScale q l - 1)
      let S := R / 2
      0 ≤ inner ∧ inner + 2 ≤ R ∧ inner + 2 ≤ S ∧ S + 4 ≤ R ∧
        0 < realGreenPoleLower R S inner ∧
        realPoissonKernelRelativeError R S inner ≤
          1 / (6 * (q : ℝ) ^ 2) := by
  have hconstant : ∀ᶠ q : ℕ in atTop,
      globalRadialConstant ≤ (q : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈globalRadialConstant⌉₊]
        with q hq
    exact (Nat.le_ceil globalRadialConstant).trans (by exact_mod_cast hq)
  filter_upwards [eventually_ge_atTop 10000,
      eventually_geometricCutoff_le_decorrelationPadding,
      eventually_decorrelationPadding_lt, hconstant]
      with q hq hpaddingLower hpaddingUpper hconstantQ
  intro l hl
  exact paddedPoissonParameters hq hl hpaddingUpper.le
    ((show 1 ≤ 32 by omega).trans
      (GaussianGeometricCutoff.geometricCutoff_ge_thirty_two.trans
        hpaddingLower)) hconstantQ

end

end Erdos1165.AsymmetricPaddedEndpointHarnack
