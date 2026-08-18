import ErdosProblems.Erdos140.ConcreteNumerics
import ErdosProblems.Erdos140.CrootSisask
import ErdosProblems.Erdos140.DensityStep
import ErdosProblems.Erdos140.BohrScaleVolume

/-!
# Scalar bookkeeping for the raw Kelley--Meka supply

This file contains numerical adapters for the q, sample-size, relative
Chang, and phase/tail bounds consumed by ConcreteSupply.
-/

open Finset
open scoped NNReal

namespace Erdos140.RawSupplyNumerics

noncomputable section

def approximationDelta : ℝ := 1 / 8192

def qQuant (alpha : ℝ) : ℕ := ⌈8192 / alpha⌉₊

def tailExponent (alpha : ℝ) : ℕ := Nat.clog 2 (qQuant alpha)

def sampleQBound (alpha : ℝ) : ℕ :=
  ⌈1 + Real.log (2 / alpha)⌉₊

def sampleKBound (alpha : ℝ) : ℕ :=
  Erdos140.crootSisaskSampleSize (sampleQBound alpha)
    ((approximationDelta / tailExponent alpha) / Real.exp 1)

def crootBeta (alpha : ℝ) (k : ℕ) : ℝ :=
  (alpha / 2) ^ k / 2

def changRankCost (alpha : ℝ) (k : ℕ) : ℕ :=
  ⌈8 * (1 + Real.log (2 / crootBeta alpha k))⌉₊

/-- Holder exponent used at dyadic scale d. -/
def holderExponent (d : ℕ) : ℕ := 4 * (d + 1)

/-- Even exponent at which the high balanced norm is tested. -/
def smoothingExponent (d : ℕ) : ℕ :=
  BalancedRestriction.stoppingExponent (1 / 8 : ℝ) (holderExponent d)

def dyadicAlphaExponent (d : ℕ) : ℕ :=
  2 + 2 * d * smoothingExponent d

/-- Conservative common lower bound for both sifted densities.  The
terminal proof gets this from the dyadic density bound and the high-norm
threshold; writing it as a reciprocal power of two makes positivity and
all later logarithms painless. -/
def dyadicSiftedAlpha (d : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ dyadicAlphaExponent d

/-- All rank increments from relative Chang are absorbed by this one
natural budget. -/
def dyadicRankCost (d : ℕ) : ℕ :=
  max 1 (changRankCost (dyadicSiftedAlpha d)
    (sampleKBound (dyadicSiftedAlpha d)))

def dyadicQQuant (d : ℕ) : ℕ := qQuant (dyadicSiftedAlpha d)

def dyadicTailExponent (d : ℕ) : ℕ :=
  tailExponent (dyadicSiftedAlpha d)

def dyadicSampleKBound (d : ℕ) : ℕ :=
  sampleKBound (dyadicSiftedAlpha d)

/-- A polynomial envelope for the Croot sample size. -/
def dyadicSamplePolynomial (d : ℕ) : ℕ :=
  2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3

def dyadicRankPolynomial (d : ℕ) : ℕ :=
  2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4

/-- The fixed coefficient after eliminating the intermediate dyadic
exponent from the rank-cost envelope. -/
def dyadicRankDegreeEightConstant : ℕ :=
  2 ^ 42 * 1720335 ^ 4

lemma approximationDelta_pos : 0 < approximationDelta := by
  norm_num [approximationDelta]

lemma approximationDelta_le_one : approximationDelta ≤ 1 := by
  norm_num [approximationDelta]

lemma holderExponent_pos (d : ℕ) : 0 < holderExponent d := by
  unfold holderExponent
  positivity

lemma smoothingExponent_pos (d : ℕ) : 0 < smoothingExponent d := by
  unfold smoothingExponent
  exact BalancedRestriction.stoppingExponent_pos (by norm_num) (holderExponent_pos d)

lemma smoothingExponent_even (d : ℕ) : Even (smoothingExponent d) := by
  unfold smoothingExponent
  exact BalancedRestriction.stoppingExponent_even _ _

lemma smoothingExponent_le (d : ℕ) :
    smoothingExponent d ≤ 860160 * (d + 1) := by
  have h :=
    BalancedRestriction.stoppingExponent_le_const_mul
      (ε := (1 / 8 : ℝ)) (p := holderExponent d) (holderExponent_pos d)
  norm_num [smoothingExponent, holderExponent, unbalancingMultiplier] at h ⊢
  omega

lemma dyadicAlphaExponent_le (d : ℕ) :
    dyadicAlphaExponent d ≤ 1720322 * (d + 1) ^ 2 := by
  unfold dyadicAlphaExponent
  have h := smoothingExponent_le d
  nlinarith [show d ≤ d + 1 by omega]

lemma dyadicSiftedAlpha_pos (d : ℕ) : 0 < dyadicSiftedAlpha d := by
  unfold dyadicSiftedAlpha
  positivity

lemma dyadicSiftedAlpha_le_one (d : ℕ) : dyadicSiftedAlpha d ≤ 1 := by
  unfold dyadicSiftedAlpha
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ dyadicAlphaExponent d := by
    exact one_le_pow₀ (by norm_num)
  exact (div_le_iff₀ (by positivity)).2
    (by simpa only [dyadicAlphaExponent, one_mul] using hpow)

lemma dyadicSiftedAlpha_le_two (d : ℕ) : dyadicSiftedAlpha d ≤ 2 :=
  (dyadicSiftedAlpha_le_one d).trans (by norm_num)

lemma dyadicRankCost_pos (d : ℕ) : 0 < dyadicRankCost d := by
  unfold dyadicRankCost
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma dyadicQQuant_eq (d : ℕ) :
    dyadicQQuant d = 8192 * 2 ^ dyadicAlphaExponent d := by
  unfold dyadicQQuant qQuant dyadicSiftedAlpha
  have hpow : (0 : ℝ) < (2 : ℝ) ^ dyadicAlphaExponent d := by positivity
  rw [show (8192 : ℝ) / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
      ((8192 * 2 ^ dyadicAlphaExponent d : ℕ) : ℝ) by
        push_cast
        field_simp]
  exact Nat.ceil_natCast _

lemma dyadicTailExponent_eq (d : ℕ) :
    dyadicTailExponent d = 13 + dyadicAlphaExponent d := by
  unfold dyadicTailExponent tailExponent
  change Nat.clog 2 (dyadicQQuant d) = 13 + dyadicAlphaExponent d
  rw [dyadicQQuant_eq]
  rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, ← pow_add,
    Nat.clog_pow 2 (13 + dyadicAlphaExponent d) (by norm_num)]

lemma sampleQBound_dyadic_le (d : ℕ) :
    sampleQBound (dyadicSiftedAlpha d) ≤ dyadicAlphaExponent d + 2 := by
  unfold sampleQBound dyadicSiftedAlpha
  apply Nat.ceil_le.mpr
  have hpow : (0 : ℝ) < (2 : ℝ) ^ dyadicAlphaExponent d := by positivity
  have harg :
      2 / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
        (2 : ℝ) ^ (dyadicAlphaExponent d + 1) := by
    field_simp
    rw [pow_succ]
    ring
  rw [harg, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ dyadicAlphaExponent d + 1 by positivity)]

lemma dyadicSampleKBound_le_polynomial (d : ℕ) :
    dyadicSampleKBound d ≤ dyadicSamplePolynomial d := by
  unfold dyadicSampleKBound sampleKBound dyadicSamplePolynomial
  unfold Erdos140.crootSisaskSampleSize
  apply Nat.ceil_le.mpr
  have hq := sampleQBound_dyadic_le d
  have htail := dyadicTailExponent_eq d
  have hqR : (sampleQBound (dyadicSiftedAlpha d) : ℝ) ≤
      dyadicAlphaExponent d + 2 := by exact_mod_cast hq
  have htailR : (tailExponent (dyadicSiftedAlpha d) : ℝ) =
      dyadicAlphaExponent d + 13 := by
    change (dyadicTailExponent d : ℝ) =
      dyadicAlphaExponent d + 13
    exact_mod_cast (by simpa [Nat.add_comm] using htail)
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hE : (0 : ℝ) ≤ dyadicAlphaExponent d := by positivity
  rw [htailR]
  unfold approximationDelta
  have hden :
      (0 : ℝ) <
        (((1 / 8192 : ℝ) / (dyadicAlphaExponent d + 13)) /
          Real.exp 1 / 2) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hE13 : (0 : ℝ) < dyadicAlphaExponent d + 13 := by positivity
  have hqE13 : (sampleQBound (dyadicSiftedAlpha d) : ℝ) ≤
      dyadicAlphaExponent d + 13 := by linarith
  have hexp2 : Real.exp 1 ^ 2 ≤ (9 : ℝ) := by
    nlinarith [Real.exp_pos (1 : ℝ)]
  field_simp
  push_cast
  calc
    64 * (sampleQBound (dyadicSiftedAlpha d) : ℝ) * 8192 ^ 2 *
        (dyadicAlphaExponent d + 13) ^ 2 * Real.exp 1 ^ 2 * 2 ^ 2 ≤
      64 * (dyadicAlphaExponent d + 13) * 8192 ^ 2 *
        (dyadicAlphaExponent d + 13) ^ 2 * 9 * 2 ^ 2 := by
          gcongr
    _ = (64 * 8192 ^ 2 * 9 * 2 ^ 2 : ℝ) *
        (dyadicAlphaExponent d + 13) ^ 3 := by ring
    _ ≤ (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 := by
      gcongr
      norm_num
    _ = (274877906944 : ℝ) *
        (dyadicAlphaExponent d + 13) ^ 3 := by norm_num

lemma qQuant_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < qQuant alpha := by
  unfold qQuant
  apply Nat.ceil_pos.2
  positivity

lemma qQuant_cast_lower {alpha : ℝ} (_halpha : 0 < alpha) :
    8192 / alpha ≤ (qQuant alpha : ℝ) := by
  exact Nat.le_ceil _

lemma one_le_qQuant {alpha : ℝ} (halpha : 0 < alpha) :
    1 ≤ qQuant alpha := by
  exact Nat.one_le_iff_ne_zero.mpr (qQuant_pos halpha).ne'

/-- If the final-to-middle cardinality ratio is at least alpha/2, the
localized Croot moment parameter is bounded by the canonical logarithmic
choice. -/
lemma sampleQ_le_sampleQBound {alpha ratio : ℝ}
    (halpha : 0 < alpha) (halpha_two : alpha ≤ 2)
    (hratio : alpha / 2 ≤ ratio) :
    ⌈1 + Real.log (min 1 ratio)⁻¹⌉₊ ≤ sampleQBound alpha := by
  have halphaHalf : 0 < alpha / 2 := by positivity
  have hhalfOne : alpha / 2 ≤ (1 : ℝ) := by linarith
  have hmin : alpha / 2 ≤ min 1 ratio := le_min hhalfOne hratio
  have hminPos : 0 < min 1 ratio := halphaHalf.trans_le hmin
  have hinv : (min 1 ratio)⁻¹ ≤ (alpha / 2)⁻¹ :=
    (inv_le_inv₀ hminPos halphaHalf).2 hmin
  have hlog : Real.log (min 1 ratio)⁻¹ ≤ Real.log (2 / alpha) := by
    have hrewrite : (alpha / 2)⁻¹ = 2 / alpha := by
      field_simp
    rw [← hrewrite]
    exact Real.log_le_log (by positivity) hinv
  unfold sampleQBound
  apply Nat.ceil_mono
  linarith

/-- Croot--Sisask's explicit sample count is monotone in its natural moment
parameter at every positive tolerance. -/
lemma crootSisaskSampleSize_mono_q {q Q : ℕ} {epsilon : ℝ}
    (hq : q ≤ Q) (hepsilon : 0 < epsilon) :
    Erdos140.crootSisaskSampleSize q epsilon ≤
      Erdos140.crootSisaskSampleSize Q epsilon := by
  unfold Erdos140.crootSisaskSampleSize
  apply Nat.ceil_mono
  have hden : 0 < (epsilon / 2) ^ 2 := by positivity
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.mul_le_mul_left 64 hq) hden.le

/-- Direct form used after the supported-popular cardinal bounds have supplied
the ratio alpha/2 ≤ |A₁|/|S|. -/
lemma localizedAPSampleK_le_sampleKBound
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (M L : Finset G) {alpha : ℝ}
    (halpha : 0 < alpha) (halpha_two : alpha ≤ 2)
    (hratio : alpha / 2 ≤ (L.card : ℝ) / M.card)
    (hm : 0 < tailExponent alpha) :
    DensityStep.localizedAPSampleK M L approximationDelta
        (tailExponent alpha) ≤ sampleKBound alpha := by
  unfold DensityStep.localizedAPSampleK sampleKBound
  apply crootSisaskSampleSize_mono_q
  · unfold DensityStep.localizedAPSampleQ
    exact sampleQ_le_sampleQBound halpha halpha_two hratio
  · have htail : (0 : ℝ) < tailExponent alpha := by exact_mod_cast hm
    exact div_pos (div_pos approximationDelta_pos htail) (Real.exp_pos _)

lemma tailExponent_pos {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) :
    0 < tailExponent alpha := by
  unfold tailExponent
  have hq : 1 < qQuant alpha := by
    have hlarge : (1 : ℝ) < 8192 / alpha := by
      have : alpha < 8192 := by
        nlinarith
      exact (lt_div_iff₀ halpha).2 (by nlinarith)
    have hceil : 8192 / alpha ≤ (qQuant alpha : ℝ) := qQuant_cast_lower halpha
    exact_mod_cast hlarge.trans_le hceil
  exact Nat.clog_pos (by norm_num) hq

lemma two_pow_tailExponent_ge_qQuant {alpha : ℝ} (_halpha : 0 < alpha) :
    qQuant alpha ≤ 2 ^ tailExponent alpha := by
  unfold tailExponent
  exact Nat.le_pow_clog (by norm_num) _

lemma inv_two_pow_tailExponent_le {alpha : ℝ} (halpha : 0 < alpha) :
    (1 / 2 : ℝ) ^ tailExponent alpha ≤ alpha / 8192 := by
  have hq : (0 : ℝ) < qQuant alpha := by
    exact_mod_cast qQuant_pos halpha
  have hpow : (0 : ℝ) < (2 : ℝ) ^ tailExponent alpha := by positivity
  have hqpow : (qQuant alpha : ℝ) ≤ (2 : ℝ) ^ tailExponent alpha := by
    exact_mod_cast two_pow_tailExponent_ge_qQuant halpha
  have hceil : 8192 / alpha ≤ (qQuant alpha : ℝ) :=
    qQuant_cast_lower halpha
  calc
    (1 / 2 : ℝ) ^ tailExponent alpha =
        ((2 : ℝ) ^ tailExponent alpha)⁻¹ := by
          rw [one_div, inv_pow]
    _ ≤ (qQuant alpha : ℝ)⁻¹ :=
      (inv_le_inv₀ hpow hq).2 hqpow
    _ ≤ (8192 / alpha)⁻¹ := by
      have hbase : (0 : ℝ) < 8192 / alpha := by positivity
      exact (inv_le_inv₀ hq hbase).2 hceil
    _ = alpha / 8192 := by
      field_simp

lemma sqrt_two_div_le_two_div {alpha : ℝ}
    (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    Real.sqrt (2 / alpha) ≤ 2 / alpha := by
  have hone : (1 : ℝ) ≤ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    nlinarith
  have hnonneg : 0 ≤ 2 / alpha := by positivity
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · nlinarith

lemma quantized_phase_mul_sqrt_le
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    (2 / (qQuant alpha : ℝ)) * Real.sqrt (2 / alpha) ≤ 1 / 2048 := by
  have hq : (0 : ℝ) < qQuant alpha := by
    exact_mod_cast qQuant_pos halpha
  have hceil := qQuant_cast_lower halpha
  have hsqrt := sqrt_two_div_le_two_div halpha halpha_one
  calc
    (2 / (qQuant alpha : ℝ)) * Real.sqrt (2 / alpha) ≤
        (2 / (qQuant alpha : ℝ)) * (2 / alpha) := by
      gcongr
    _ ≤ (2 / (8192 / alpha)) * (2 / alpha) := by
      have hbase : (0 : ℝ) < 8192 / alpha := by positivity
      have hdiv : 2 / (qQuant alpha : ℝ) ≤ 2 / (8192 / alpha) := by
        exact div_le_div_of_nonneg_left (by norm_num) hbase hceil
      exact mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = 1 / 2048 := by
      field_simp
      norm_num

lemma dyadic_tail_mul_sqrt_le
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    (2 * (1 / 2 : ℝ) ^ tailExponent alpha) *
        Real.sqrt (2 / alpha) ≤ 1 / 2048 := by
  have htail := inv_two_pow_tailExponent_le halpha
  have hsqrt := sqrt_two_div_le_two_div halpha halpha_one
  calc
    (2 * (1 / 2 : ℝ) ^ tailExponent alpha) *
        Real.sqrt (2 / alpha) ≤
      (2 * (alpha / 8192)) * (2 / alpha) := by
        gcongr
    _ = 1 / 2048 := by
      field_simp
      norm_num

lemma crootBeta_pos {alpha : ℝ} {k : ℕ} (halpha : 0 < alpha) :
    0 < crootBeta alpha k := by
  unfold crootBeta
  positivity

lemma log_two_div_crootBeta_eq
    {alpha : ℝ} {k : ℕ} (halpha : 0 < alpha) :
    Real.log (2 / crootBeta alpha k) =
      Real.log 4 + (k : ℝ) * Real.log (2 / alpha) := by
  have hhalf : (0 : ℝ) < alpha / 2 := by positivity
  have harg :
      2 / crootBeta alpha k = 4 / (alpha / 2) ^ k := by
    unfold crootBeta
    field_simp
    ring
  rw [harg, Real.log_div (by norm_num) (pow_ne_zero _ hhalf.ne'),
    Real.log_pow, Real.log_div (by norm_num) halpha.ne',
    Real.log_div halpha.ne' (by norm_num)]
  push_cast
  ring

lemma delta_card_le_changRankCost
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (T : Finset G) {alpha : ℝ} {k : ℕ}
    (halpha : 0 < alpha) (hT : T.Nonempty)
    (hbeta :
      crootBeta alpha k * (B.carrier.card : ℝ) ≤ (T.card : ℝ))
    (Delta : Finset (AddChar G Complex))
    (hDelta :
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension B T (1 / 2)) :
    Delta.card ≤ changRankCost alpha k := by
  apply card_le_natCeil_of_cast_card_le
  calc
    (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension B T (1 / 2) := hDelta
    _ ≤ 8 * (1 + Real.log (2 / crootBeta alpha k)) :=
      localChangDimension_half_le_of_mul_card_le B T
        (crootBeta_pos halpha) hT hbeta

lemma delta_card_le_dyadicRankCost
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (T : Finset G) {d : ℕ}
    (hT : T.Nonempty)
    (hbeta :
      crootBeta (dyadicSiftedAlpha d) (dyadicSampleKBound d) *
          (B.carrier.card : ℝ) ≤ (T.card : ℝ))
    (Delta : Finset (AddChar G Complex))
    (hDelta :
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension B T (1 / 2)) :
    Delta.card ≤ dyadicRankCost d := by
  apply (delta_card_le_changRankCost B T
    (dyadicSiftedAlpha_pos d) hT hbeta Delta hDelta).trans
  unfold dyadicRankCost dyadicSampleKBound
  exact le_max_right _ _

lemma dyadicRankCost_le_polynomial (d : ℕ) :
    dyadicRankCost d ≤ dyadicRankPolynomial d := by
  unfold dyadicRankCost dyadicRankPolynomial
  apply max_le
  · have hpos : 0 < 2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 := by
      positivity
    omega
  · unfold changRankCost
    apply Nat.ceil_le.mpr
    rw [log_two_div_crootBeta_eq (dyadicSiftedAlpha_pos d)]
    have hk := dyadicSampleKBound_le_polynomial d
    have hkR : (sampleKBound (dyadicSiftedAlpha d) : ℝ) ≤
        (2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3 : ℕ) := by
      exact_mod_cast hk
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
      norm_num
    have hlogfour : Real.log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have hmul := mul_le_mul_of_nonneg_left hlogtwo
        (show (0 : ℝ) ≤ 2 by norm_num)
      norm_num at hmul ⊢
      exact hmul
    have hlogalpha :
        Real.log (2 / dyadicSiftedAlpha d) ≤
          (dyadicAlphaExponent d + 1 : ℝ) := by
      unfold dyadicSiftedAlpha
      have harg :
          2 / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
            (2 : ℝ) ^ (dyadicAlphaExponent d + 1) := by
        field_simp
        rw [pow_succ]
        ring
      rw [harg, Real.log_pow]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hlogtwo
        (show (0 : ℝ) ≤ (dyadicAlphaExponent d + 1 : ℕ) by positivity)]
    have hE1 :
        (dyadicAlphaExponent d + 1 : ℝ) ≤
          dyadicAlphaExponent d + 13 := by norm_num
    have hbig :
        (1 : ℝ) ≤ (dyadicAlphaExponent d + 13) ^ 4 := by
      have hEzero : (0 : ℝ) ≤ dyadicAlphaExponent d := by positivity
      have : (1 : ℝ) ≤ dyadicAlphaExponent d + 13 := by nlinarith
      exact one_le_pow₀ this
    have hlognonneg :
        0 ≤ Real.log (2 / dyadicSiftedAlpha d) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (dyadicSiftedAlpha_pos d)).2
      nlinarith [dyadicSiftedAlpha_le_two d]
    have hkR' :
        (sampleKBound (dyadicSiftedAlpha d) : ℝ) ≤
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 := by
      norm_num at hkR ⊢
      exact hkR
    have hlogalpha' :
        Real.log (2 / dyadicSiftedAlpha d) ≤
          dyadicAlphaExponent d + 13 := hlogalpha.trans hE1
    have hmul :
        (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
            Real.log (2 / dyadicSiftedAlpha d) ≤
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 *
            (dyadicAlphaExponent d + 13) := by
      exact mul_le_mul hkR' hlogalpha' hlognonneg (by positivity)
    push_cast at ⊢
    calc
      8 * (1 + (Real.log 4 +
          (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
            Real.log (2 / dyadicSiftedAlpha d))) ≤
        8 * (1 + (2 +
          (2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3 : ℝ) *
            (dyadicAlphaExponent d + 13))) := by
              have hinner :
                  Real.log 4 +
                      (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
                        Real.log (2 / dyadicSiftedAlpha d) ≤
                    2 + (2 ^ 38 : ℝ) *
                      (dyadicAlphaExponent d + 13) ^ 3 *
                        (dyadicAlphaExponent d + 13) := by
                linarith
              nlinarith
      _ = 8 * (3 +
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 4) := by ring
      _ ≤ (2 ^ 42 : ℝ) * (dyadicAlphaExponent d + 13) ^ 4 := by
        norm_num at ⊢
        nlinarith
      _ = (4398046511104 : ℝ) *
          (dyadicAlphaExponent d + 13) ^ 4 := by norm_num

/-- The local-Chang rank cost is polynomial of degree eight in the dyadic
density index.  This is the form used by the final source-volume budget. -/
lemma dyadicRankCost_le_degree_eight (d : ℕ) :
    dyadicRankCost d ≤
      dyadicRankDegreeEightConstant * (d + 1) ^ 8 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hE13 :
      dyadicAlphaExponent d + 13 ≤ 1720335 * (d + 1) ^ 2 := by
    nlinarith
  calc
    dyadicRankCost d ≤
        2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 :=
      dyadicRankCost_le_polynomial d
    _ ≤ 2 ^ 42 * (1720335 * (d + 1) ^ 2) ^ 4 := by
      gcongr
    _ = dyadicRankDegreeEightConstant * (d + 1) ^ 8 := by
      unfold dyadicRankDegreeEightConstant
      ring

/-- The accumulated rank cap has degree nine after inserting the fixed
degree-eight local-Chang budget. -/
lemma dyadicRankCap_le_degree_nine (d : ℕ) :
    ConcreteNumerics.rankCap d (dyadicRankCost d) ≤
      (1024 * dyadicRankDegreeEightConstant) * (d + 1) ^ 9 := by
  unfold ConcreteNumerics.rankCap
  calc
    1024 * (d + 1) * dyadicRankCost d ≤
        1024 * (d + 1) *
          (dyadicRankDegreeEightConstant * (d + 1) ^ 8) := by
      gcongr
      exact dyadicRankCost_le_degree_eight d
    _ = (1024 * dyadicRankDegreeEightConstant) * (d + 1) ^ 9 := by
      ring

/-- A tiny reusable numerical estimate that keeps logarithmic losses
polynomial instead of replacing them by their (much larger) arguments. -/
lemma log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h :=
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

lemma log_natCast_le_natCast {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ n := by
  have h := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < n by exact_mod_cast hn)
  nlinarith

/-- The quantization logarithm is exactly linear in the dyadic exponent. -/
lemma log_dyadicQQuant_le_exponent (d : ℕ) :
    Real.log (dyadicQQuant d : ℝ) ≤
      (dyadicAlphaExponent d + 13 : ℝ) := by
  rw [dyadicQQuant_eq]
  push_cast
  rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, ← pow_add,
    Real.log_pow]
  push_cast
  have hnonneg : (0 : ℝ) ≤ 13 + dyadicAlphaExponent d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left log_two_le_one hnonneg]

/-- Degree-two version of the preceding quantization-log bound. -/
lemma log_dyadicQQuant_le_degree_two (d : ℕ) :
    Real.log (dyadicQQuant d : ℝ) ≤
      1720335 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hE13 :
      dyadicAlphaExponent d + 13 ≤ 1720335 * (d + 1) ^ 2 := by
    nlinarith
  calc
    Real.log (dyadicQQuant d : ℝ) ≤
        (dyadicAlphaExponent d + 13 : ℝ) :=
      log_dyadicQQuant_le_exponent d
    _ ≤ 1720335 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hE13

/-- The logarithm of the rank cost stays linear in the dyadic exponent,
even though the rank cost itself has degree four in that exponent. -/
lemma log_dyadicRankCost_le_exponent (d : ℕ) :
    Real.log (dyadicRankCost d : ℝ) ≤
      42 + 4 * (dyadicAlphaExponent d + 13 : ℝ) := by
  have hcost := dyadicRankCost_le_polynomial d
  have hcostR :
      (dyadicRankCost d : ℝ) ≤
        ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hcost
  have hcostPosR : (0 : ℝ) < dyadicRankCost d := by
    exact_mod_cast dyadicRankCost_pos d
  have hlog :
      Real.log (dyadicRankCost d : ℝ) ≤
        Real.log ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) :=
    Real.log_le_log hcostPosR hcostR
  have hpolylog :
      Real.log ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) =
        42 * Real.log 2 +
          4 * Real.log ((dyadicAlphaExponent d + 13 : ℕ) : ℝ) := by
    push_cast
    rw [show (4398046511104 : ℝ) = (2 : ℝ) ^ 42 by norm_num]
    rw [Real.log_mul (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity)),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hE13pos : 0 < dyadicAlphaExponent d + 13 := by positivity
  have hlogE13 :
      Real.log ((dyadicAlphaExponent d + 13 : ℕ) : ℝ) ≤
        (dyadicAlphaExponent d + 13 : ℕ) :=
    log_natCast_le_natCast hE13pos
  rw [hpolylog] at hlog
  have hfortytwo : 42 * Real.log (2 : ℝ) ≤ 42 := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 42 by norm_num)]
  have hfourE13 := mul_le_mul_of_nonneg_left hlogE13
    (show (0 : ℝ) ≤ 4 by norm_num)
  push_cast at hlog hfourE13
  nlinarith

/-- Degree-two form of the rank-cost logarithm. -/
lemma log_dyadicRankCost_le_degree_two (d : ℕ) :
    Real.log (dyadicRankCost d : ℝ) ≤
      6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hEbound :
      42 + 4 * (dyadicAlphaExponent d + 13) ≤
        6881382 * (d + 1) ^ 2 := by
    nlinarith
  calc
    Real.log (dyadicRankCost d : ℝ) ≤
        42 + 4 * (dyadicAlphaExponent d + 13 : ℝ) :=
      log_dyadicRankCost_le_exponent d
    _ ≤ 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hEbound

/-- The spectral factor `8R+1` has only a logarithmic cost in a positive
rank budget R. -/
lemma log_eight_mul_add_one_le_log
    {R : ℕ} (hR : 0 < R) :
    Real.log ((8 * R + 1 : ℕ) : ℝ) ≤
      9 + Real.log (R : ℝ) := by
  have hRone : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR.ne'
  have hnat : 8 * R + 1 ≤ 9 * R := by omega
  have hargPos : (0 : ℝ) < ((8 * R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 8 * R + 1 by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog :
      Real.log ((8 * R + 1 : ℕ) : ℝ) ≤
        Real.log ((9 * R : ℕ) : ℝ) :=
    Real.log_le_log hargPos (by exact_mod_cast hnat)
  have hprod :
      Real.log ((9 * R : ℕ) : ℝ) =
        Real.log 9 + Real.log (R : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hRpos.ne']
  rw [hprod] at hlog
  have h9 : Real.log (9 : ℝ) ≤ 9 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Logarithmic cost of the uniform quantization times spectral-cell base
used by the dyadic cell multiplier. -/
lemma log_dyadicSampleBase_le_degree_two (d : ℕ) :
    Real.log
        ((dyadicQQuant d * (8 * dyadicRankCost d + 1 : ℕ) : ℕ) : ℝ) ≤
      8601726 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hqPos : 0 < dyadicQQuant d := by
    unfold dyadicQQuant
    exact qQuant_pos (dyadicSiftedAlpha_pos d)
  have hRpos := dyadicRankCost_pos d
  have hqPosR : (0 : ℝ) < dyadicQQuant d := by exact_mod_cast hqPos
  have hcellPosR : (0 : ℝ) < 8 * dyadicRankCost d + 1 := by positivity
  have hlogQ := log_dyadicQQuant_le_degree_two d
  have hlogCell := log_eight_mul_add_one_le_log hRpos
  have hlogR := log_dyadicRankCost_le_degree_two d
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  push_cast
  rw [Real.log_mul hqPosR.ne' hcellPosR.ne']
  push_cast at hlogQ hlogR hsqOne hlogCell
  nlinarith

/-- The accumulated rank cap has only a degree-two logarithmic loss when
the dyadic local-Chang rank cost is substituted. -/
lemma log_dyadicRankCap_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hcostPos := dyadicRankCost_pos d
  have hcostPosR : (0 : ℝ) < dyadicRankCost d := by
    exact_mod_cast hcostPos
  have hdPos : 0 < d + 1 := by omega
  have hdPosR : (0 : ℝ) < d + 1 := by exact_mod_cast hdPos
  have hlogd : Real.log ((d + 1 : ℕ) : ℝ) ≤ (d + 1 : ℕ) :=
    log_natCast_le_natCast hdPos
  have hlogcost := log_dyadicRankCost_le_degree_two d
  have hsqR : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  unfold ConcreteNumerics.rankCap
  push_cast
  rw [Real.log_mul
      (mul_ne_zero (by norm_num) hdPosR.ne') hcostPosR.ne',
    Real.log_mul (by norm_num) hdPosR.ne']
  have hlog1024 : Real.log (1024 : ℝ) ≤ 10 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 10 by norm_num)]
  push_cast at hlogd hlogcost hsqR ⊢
  have hsqOne : (1 : ℝ) ≤ (↑d + 1) ^ 2 := by
    nlinarith
  nlinarith

lemma log_dyadicMOne_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.mOne d (dyadicRankCost d) : ℝ) ≤
      7700594 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hR := log_dyadicRankCap_le_degree_two d
  have hconst : Real.log (819200 : ℝ) ≤ 819200 :=
    log_natCast_le_natCast (by norm_num)
  have hpow : (d : ℝ) * Real.log 2 ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ d by positivity)]
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hdSq : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hd : (d : ℝ) ≤ d + 1 := by norm_num
    push_cast at hsqOne ⊢
    nlinarith
  have hRpos : 0 < ConcreteNumerics.rankCap d (dyadicRankCost d) :=
    ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hRposR : (0 : ℝ) <
      ConcreteNumerics.rankCap d (dyadicRankCost d) := by
    exact_mod_cast hRpos
  unfold ConcreteNumerics.mOne
  push_cast
  rw [Real.log_mul (mul_ne_zero (by norm_num) hRposR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hRposR.ne', Real.log_pow]
  push_cast at hR hpow hdSq ⊢
  nlinarith

lemma log_dyadicMTwo_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.mTwo d (dyadicRankCost d) : ℝ) ≤
      6958194 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hR := log_dyadicRankCap_le_degree_two d
  have hconst : Real.log (76800 : ℝ) ≤ 76800 :=
    log_natCast_le_natCast (by norm_num)
  have hpow : ((d + 1 : ℕ) : ℝ) * Real.log 2 ≤ d + 1 := by
    have hmul := mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by positivity)
    norm_num at hmul ⊢
    exact hmul
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hdSq : ((d + 1 : ℕ) : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hRpos : 0 < ConcreteNumerics.rankCap d (dyadicRankCost d) :=
    ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hRposR : (0 : ℝ) <
      ConcreteNumerics.rankCap d (dyadicRankCost d) := by
    exact_mod_cast hRpos
  unfold ConcreteNumerics.mTwo
  push_cast
  rw [Real.log_mul (mul_ne_zero (by norm_num) hRposR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hRposR.ne', Real.log_pow]
  push_cast at hR hpow hdSq ⊢
  nlinarith

/-- Logarithmic envelope for the exact natural expression used by
`ConcreteSupply.dyadicHierarchyDenominator`.  Keeping the statement at the
formula level avoids an import cycle while allowing `simpa` at the call site.
-/
lemma log_dyadicHierarchyFormula_le_of_rankCap
    (d rankCap : ℕ) (hrankCap : 0 < rankCap) {LR : ℝ}
    (hlogRankCap : Real.log (rankCap : ℝ) ≤ LR) :
    Real.log
        ((8388608 * max rankCap 1 *
          2 ^ dyadicAlphaExponent d : ℕ) : ℝ) ≤
      23 + LR + dyadicAlphaExponent d := by
  have hmax : max rankCap 1 = rankCap :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr hrankCap.ne')
  rw [hmax]
  have hrankCapR : (0 : ℝ) < rankCap := by exact_mod_cast hrankCap
  have hlogConst : Real.log (8388608 : ℝ) ≤ 23 := by
    rw [show (8388608 : ℝ) = 2 ^ 23 by norm_num, Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 23 by norm_num)]
  have hlogPow :
      (dyadicAlphaExponent d : ℝ) * Real.log 2 ≤
        dyadicAlphaExponent d := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ dyadicAlphaExponent d by positivity)]
  push_cast
  rw [Real.log_mul
      (mul_ne_zero (by norm_num) hrankCapR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hrankCapR.ne', Real.log_pow]
  nlinarith

lemma dyadic_quantized_phase_mul_sqrt_le (d : ℕ) :
    (2 / (dyadicQQuant d : ℝ)) *
        Real.sqrt (2 / dyadicSiftedAlpha d) ≤ 1 / 2048 := by
  unfold dyadicQQuant
  exact quantized_phase_mul_sqrt_le
    (dyadicSiftedAlpha_pos d) (dyadicSiftedAlpha_le_one d)

lemma dyadic_tail_error_mul_sqrt_le (d : ℕ) :
    (2 * (1 / 2 : ℝ) ^ dyadicTailExponent d) *
        Real.sqrt (2 / dyadicSiftedAlpha d) ≤ 1 / 2048 := by
  unfold dyadicTailExponent
  exact dyadic_tail_mul_sqrt_le
    (dyadicSiftedAlpha_pos d) (dyadicSiftedAlpha_le_one d)

lemma pow_le_eleventh {d e : ℕ} (he : e ≤ 11) :
    ((d + 1 : ℕ) : ℝ) ^ e ≤ ((d + 1 : ℕ) : ℝ) ^ 11 := by
  exact pow_le_pow_right₀ (by norm_num) he

/-- Two nonnegative polynomial losses of degree at most eleven can be
absorbed into one eleventh-power step budget. -/
lemma add_poly_losses_le_eleventh
    {d e f : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : e ≤ 11) (hf : f ≤ 11) :
    a * ((d + 1 : ℕ) : ℝ) ^ e +
        b * ((d + 1 : ℕ) : ℝ) ^ f ≤
      (a + b) * ((d + 1 : ℕ) : ℝ) ^ 11 := by
  calc
    a * ((d + 1 : ℕ) : ℝ) ^ e +
        b * ((d + 1 : ℕ) : ℝ) ^ f ≤
      a * ((d + 1 : ℕ) : ℝ) ^ 11 +
        b * ((d + 1 : ℕ) : ℝ) ^ 11 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_eleventh (d := d) he) ha)
            (mul_le_mul_of_nonneg_left (pow_le_eleventh (d := d) hf) hb)
    _ = (a + b) * ((d + 1 : ℕ) : ℝ) ^ 11 := by ring

/-- Logarithmic loss absorption in the exact exponential form used by child
cardinality bounds. -/
lemma exp_neg_eleventh_le_inv_of_log_loss
    {d : ℕ} {K loss : ℝ} (hloss : 0 < loss)
    (hlog : Real.log loss ≤ K * ((d + 1 : ℕ) : ℝ) ^ 11) :
    Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) ≤ loss⁻¹ := by
  have hneg :
      -(K * ((d + 1 : ℕ) : ℝ) ^ 11) ≤ -Real.log loss :=
    neg_le_neg hlog
  calc
    Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) ≤
        Real.exp (-Real.log loss) := Real.exp_le_exp.mpr hneg
    _ = loss⁻¹ := by rw [Real.exp_neg, Real.exp_log hloss]

/-! ## Source and multiplier losses -/

/-- The exact natural multiplier occurring in the commuted relative-T
localized package. -/
def cellMultiplier (rank delta n : ℕ) : ℕ :=
  n ^ delta * 4 ^ (rank + delta)

/-- Fixed multiplier envelope after replacing the actual dimension and
spectral cell count by their dyadic bounds. -/
def dyadicCellMultiplier (d : ℕ) : ℕ :=
  cellMultiplier
    (ConcreteNumerics.rankCap d (dyadicRankCost d))
    (dyadicRankCost d)
    (dyadicQQuant d * (8 * dyadicRankCost d + 1))

/-- Coefficient in the degree-ten logarithmic envelope for the preceding
cell multiplier. -/
def dyadicCellLogConstant : ℕ :=
  dyadicRankDegreeEightConstant * 8601726 +
    2 * (1024 * dyadicRankDegreeEightConstant +
      dyadicRankDegreeEightConstant)

/-- Formula-level versions of the finite losses defined in
`ConcreteSupply`; these avoid an import cycle and are discharged there by
`simpa` after unfolding the concrete definitions. -/
def reciprocalLossFormula (rank m : ℕ) : ℕ :=
  (3 * m) ^ rank * 4 ^ rank

def twoReciprocalLossFormula (rank mOne mTwo : ℕ) : ℕ :=
  reciprocalLossFormula rank mOne * reciprocalLossFormula rank mTwo

def smoothingHierarchyLossFormula (rank : ℕ) : ℕ :=
  reciprocalLossFormula rank (1600 * max rank 1) *
    reciprocalLossFormula rank (200 * max rank 1) *
      reciprocalLossFormula rank (200 * max rank 1)

def dyadicHierarchyFormula (d rankCap : ℕ) : ℕ :=
  8388608 * max rankCap 1 * 2 ^ dyadicAlphaExponent d

/-- Coarse monotonicity of the exact cell multiplier. -/
lemma cellMultiplier_mono
    {rank delta n R D N : ℕ}
    (hn : 0 < n) (hnN : n ≤ N)
    (hrank : rank ≤ R) (hdelta : delta ≤ D) :
    cellMultiplier rank delta n ≤ cellMultiplier R D N := by
  unfold cellMultiplier
  have hN : 0 < N := hn.trans_le hnN
  have hfirst : n ^ delta ≤ N ^ D := by
    calc
      n ^ delta ≤ N ^ delta := Nat.pow_le_pow_left hnN _
      _ ≤ N ^ D := Nat.pow_le_pow_right hN hdelta
  have hsecond : 4 ^ (rank + delta) ≤ 4 ^ (R + D) := by
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.add_le_add hrank hdelta
  exact Nat.mul_le_mul hfirst hsecond

/-- A dimension bounded by R has at most ceil(8R)+1 spectral cells.  The
constant eight only uses pi < 4 and keeps the proof arithmetic-only. -/
lemma spectralQuantization_le_of_le
    {D : ℝ} {R : ℕ} (hD0 : 0 ≤ D) (hDR : D ≤ R) :
    LocalizedAlmostPeriodicity.spectralQuantization D ≤
      ⌈8 * (R : ℝ)⌉₊ + 1 := by
  unfold LocalizedAlmostPeriodicity.spectralQuantization
  rw [max_eq_left hD0]
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by
    nlinarith [Real.pi_lt_four]
  calc
    2 * Real.pi * D ≤ 2 * Real.pi * R := by
      gcongr
    _ ≤ 8 * (R : ℝ) := by
      gcongr

lemma ceil_eight_mul_rank_add_one_eq (R : ℕ) :
    ⌈8 * (R : ℝ)⌉₊ + 1 = 8 * R + 1 := by
  rw [show 8 * (R : ℝ) = ((8 * R : ℕ) : ℝ) by
    push_cast
    ring]
  rw [Nat.ceil_natCast]

/-- Reciprocal denominator for the local-Chang regular scale followed by a
further reciprocal source scale.  The factor 200 pays for rho ≥ 1/2. -/
def sourceDenominator (rank cap m : ℕ) : ℕ :=
  200 * max rank 1 * (2 * cap + 1) * m

lemma sourceDenominator_pos {rank cap m : ℕ} (hm : 0 < m) :
    0 < sourceDenominator rank cap m := by
  unfold sourceDenominator
  positivity

/-- Exact additive logarithm of the nested local-Chang/source reciprocal
denominator. -/
lemma log_sourceDenominator {rank cap m : ℕ} (hm : 0 < m) :
    Real.log (sourceDenominator rank cap m : ℝ) =
      Real.log 200 + Real.log ((max rank 1 : ℕ) : ℝ) +
        Real.log ((2 * cap + 1 : ℕ) : ℝ) + Real.log (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold sourceDenominator
  push_cast
  rw [Real.log_mul (by positivity) hmR.ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity)]

/-- Monotone logarithmic envelope for the source denominator.  The constant
200 is intentionally left coarse; it is harmless in the final polynomial. -/
lemma log_sourceDenominator_le_of_bounds
    {rank cap m : ℕ} {LR LC LM : ℝ} (hm : 0 < m)
    (hRank : Real.log ((max rank 1 : ℕ) : ℝ) ≤ LR)
    (hCap : Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤ LC)
    (hM : Real.log (m : ℝ) ≤ LM) :
    Real.log (sourceDenominator rank cap m : ℝ) ≤
      200 + LR + LC + LM := by
  rw [log_sourceDenominator hm]
  have h200 : Real.log (200 : ℝ) ≤ 200 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Replacing a current rank by a positive uniform rank cap costs no extra
logarithmic factor. -/
lemma log_max_rank_le_log_rankCap
    {rank rankCap : ℕ} (hrankCap : 0 < rankCap) (hrank : rank ≤ rankCap) :
    Real.log ((max rank 1 : ℕ) : ℝ) ≤ Real.log (rankCap : ℝ) := by
  have hmax : max rank 1 ≤ rankCap :=
    max_le hrank (Nat.one_le_iff_ne_zero.mpr hrankCap.ne')
  have hmaxPos : (0 : ℝ) < max rank 1 := by positivity
  exact Real.log_le_log hmaxPos (by exact_mod_cast hmax)

/-- When the local-Chang cap is at most eight times a positive rank budget,
its logarithm is still just the logarithm of that budget plus a constant. -/
lemma log_two_mul_add_one_le_of_cap_le_eight_mul
    {cap R : ℕ} (hR : 0 < R) (hcap : cap ≤ 8 * R) :
    Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
      17 + Real.log (R : ℝ) := by
  have hRone : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR.ne'
  have hnat : 2 * cap + 1 ≤ 17 * R := by
    nlinarith
  have hargPos : (0 : ℝ) < ((2 * cap + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * cap + 1 by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog :
      Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
        Real.log ((17 * R : ℕ) : ℝ) :=
    Real.log_le_log hargPos (by exact_mod_cast hnat)
  have hprod :
      Real.log ((17 * R : ℕ) : ℝ) =
        Real.log 17 + Real.log (R : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hRpos.ne']
  rw [hprod] at hlog
  have h17 : Real.log (17 : ℝ) ≤ 17 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Fully concrete degree-two logarithmic budget for the nested source
denominator.  The rank and local-Chang cap hypotheses are exactly the two
facts exposed by the dyadic hierarchy adapter. -/
lemma log_sourceDenominator_dyadicFormula_le_degree_two
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log
        (sourceDenominator rank cap
          (8388608 *
            max (ConcreteNumerics.rankCap d (dyadicRankCost d)) 1 *
              2 ^ dyadicAlphaExponent d) : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let m := 8388608 * max R 1 * 2 ^ dyadicAlphaExponent d
  have hRpos : 0 < R := by
    unfold R
    exact ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hm : 0 < m := by
    unfold m
    positivity
  have hlogR : Real.log (R : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [R] using log_dyadicRankCap_le_degree_two d
  have hlogRank : Real.log ((max rank 1 : ℕ) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 :=
    (log_max_rank_le_log_rankCap hRpos (by simpa [R] using hrank)).trans hlogR
  have hlogCap : Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
      17 + 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
          17 + Real.log (dyadicRankCost d : ℝ) :=
        log_two_mul_add_one_le_of_cap_le_eight_mul
          (dyadicRankCost_pos d) hcap
      _ ≤ 17 + 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr
        exact log_dyadicRankCost_le_degree_two d
  have hlogM : Real.log (m : ℝ) ≤
      23 + 8601715 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hraw := log_dyadicHierarchyFormula_le_of_rankCap d R hRpos hlogR
    have hE := dyadicAlphaExponent_le d
    have hER : (dyadicAlphaExponent d : ℝ) ≤
        1720322 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hE
    unfold m
    nlinarith
  have hsource := log_sourceDenominator_le_of_bounds
    (rank := rank) (cap := cap) (m := m) hm hlogRank hlogCap hlogM
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  simpa [m, R] using (by nlinarith :
    Real.log (sourceDenominator rank cap m : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2)

/-- The source-volume power contributes degree eleven after multiplying its
degree-two logarithm by the degree-nine ambient rank cap. -/
lemma log_sourcePow_dyadicFormula_le_degree_eleven
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log
        (((3 * sourceDenominator rank cap
          (dyadicHierarchyFormula d
            (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank : ℕ) : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 22364733 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let m := dyadicHierarchyFormula d R
  let P := sourceDenominator rank cap m
  have hm : 0 < m := by
    unfold m dyadicHierarchyFormula
    positivity
  have hP : 0 < P := by
    unfold P
    exact sourceDenominator_pos hm
  have hlogP : Real.log (P : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [P, m, R, dyadicHierarchyFormula] using
      log_sourceDenominator_dyadicFormula_le_degree_two d rank cap hrank hcap
  have hlog3P : Real.log ((3 * P : ℕ) : ℝ) ≤
      3 + 22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have h3 : Real.log (3 : ℝ) ≤ 3 :=
      log_natCast_le_natCast (by norm_num)
    rw [show ((3 * P : ℕ) : ℝ) = (3 : ℝ) * (P : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hPR.ne']
    nlinarith
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hfactor : Real.log ((3 * P : ℕ) : ℝ) ≤
      22364733 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by simpa [R] using hrank)
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        simpa [R] using (show
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
            (1024 * dyadicRankDegreeEightConstant : ℕ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 by
          exact_mod_cast dyadicRankCap_le_degree_nine d)
  have hfactorNonneg : 0 ≤ Real.log ((3 * P : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * P by omega)
  have hmul := mul_le_mul hrankR hfactor hfactorNonneg (by positivity)
  push_cast
  rw [Real.log_pow]
  push_cast at hmul ⊢
  nlinarith

/-- The explicit source denominator is below the actual nested
local-Chang/source scale whenever the final source scale is 1/m. -/
lemma inv_sourceDenominator_le_localChang_source_scale
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (T : Finset G) (eta : ℝ) (m : ℕ)
    (hm : 0 < m) (rho : NNReal) (hrho : 1 / 2 ≤ rho) :
    ((sourceDenominator B.rank
        (RelativeChangSanders.localChangCap B T eta) m : NNReal)⁻¹) ≤
      rho * RelativeChangSanders.localChangBaseScale B T eta *
        (m : NNReal)⁻¹ := by
  unfold sourceDenominator RelativeChangSanders.localChangBaseScale
  have hrank : (0 : NNReal) < max B.rank 1 := by positivity
  have hcap : (0 : NNReal) <
      (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) := by
    positivity
  have hm' : (0 : NNReal) < m := by exact_mod_cast hm
  have hmul :
      (200 * (max B.rank 1 : NNReal) *
          (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) *
          (m : NNReal)) * (1 / 2) ≤
        (200 * (max B.rank 1 : NNReal) *
          (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) *
          (m : NNReal)) * rho := by
    exact mul_le_mul_of_nonneg_left hrho (by positivity)
  field_simp
  norm_num at hmul ⊢
  convert hmul using 1 <;> ring

/-- One reciprocal natural scale controls an arbitrary target scale above
it, with the clean three-P-to-rank loss from BohrScaleVolume. -/
lemma card_unit_le_three_mul_pow_rank_mul_card_dilate_of_inv_nat_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (P : ℕ) (hP : 0 < P) {rho : NNReal}
    (hrho : ((P : NNReal)⁻¹) ≤ rho) :
    B.carrier.card ≤
      (3 * P) ^ B.rank * (B.dilate rho).carrier.card := by
  have hbase :=
    BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div B 1 hP
  have hmono :
      (B.dilate ((P : NNReal)⁻¹)).carrier.card ≤
        (B.dilate rho).carrier.card :=
    Finset.card_le_card (BohrData.carrier_dilate_mono hrho)
  calc
    B.carrier.card = (B.dilate 1).carrier.card := by simp
    _ ≤ (3 * P) ^ B.rank *
        (B.dilate ((P : NNReal)⁻¹)).carrier.card := by
          simpa [div_eq_mul_inv] using hbase
    _ ≤ (3 * P) ^ B.rank * (B.dilate rho).carrier.card :=
      Nat.mul_le_mul_left _ hmono

/-- Real logarithm of the exact cell multiplier. -/
lemma log_cellMultiplier
    {rank delta n : ℕ} (hn : 0 < n) :
    Real.log (cellMultiplier rank delta n : ℝ) =
      (delta : ℝ) * Real.log (n : ℝ) +
        (rank + delta : ℝ) * Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellMultiplier
  push_cast
  rw [Real.log_mul (pow_ne_zero _ hnR.ne') (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma reciprocalLossFormula_pos {rank m : ℕ} (hm : 0 < m) :
    0 < reciprocalLossFormula rank m := by
  unfold reciprocalLossFormula
  positivity

lemma log_reciprocalLossFormula {rank m : ℕ} (hm : 0 < m) :
    Real.log (reciprocalLossFormula rank m : ℝ) =
      (rank : ℝ) *
        (Real.log ((3 * m : ℕ) : ℝ) + Real.log 4) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold reciprocalLossFormula
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (mul_ne_zero (by norm_num) hmR.ne'))
      (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma log_twoReciprocalLossFormula {rank mOne mTwo : ℕ}
    (hmOne : 0 < mOne) (hmTwo : 0 < mTwo) :
    Real.log (twoReciprocalLossFormula rank mOne mTwo : ℝ) =
      (rank : ℝ) *
        (Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4) +
      (rank : ℝ) *
        (Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4) := by
  unfold twoReciprocalLossFormula
  push_cast
  rw [Real.log_mul
      (by exact_mod_cast (reciprocalLossFormula_pos hmOne).ne')
      (by exact_mod_cast (reciprocalLossFormula_pos hmTwo).ne'),
    log_reciprocalLossFormula hmOne, log_reciprocalLossFormula hmTwo]
  push_cast
  ring

lemma log_smoothingHierarchyLossFormula (rank : ℕ) :
    Real.log (smoothingHierarchyLossFormula rank : ℝ) =
      (rank : ℝ) *
          (Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) +
        (rank : ℝ) *
          (Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) +
        (rank : ℝ) *
          (Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) := by
  have hmax : 0 < max rank 1 := by positivity
  have h1600 : 0 < 1600 * max rank 1 := by positivity
  have h200 : 0 < 200 * max rank 1 := by positivity
  have hAne :
      ((reciprocalLossFormula rank (1600 * max rank 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (reciprocalLossFormula_pos h1600).ne'
  have hBne :
      ((reciprocalLossFormula rank (200 * max rank 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (reciprocalLossFormula_pos h200).ne'
  unfold smoothingHierarchyLossFormula
  push_cast
  rw [Real.log_mul
      (mul_ne_zero hAne hBne) hBne,
    Real.log_mul hAne hBne,
    log_reciprocalLossFormula h1600,
    log_reciprocalLossFormula h200]
  push_cast
  ring

lemma log_three_mul_le_of_log_le
    {m : ℕ} {L : ℝ} (hm : 0 < m)
    (hlog : Real.log (m : ℝ) ≤ L) :
    Real.log ((3 * m : ℕ) : ℝ) ≤ 3 + L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : Real.log (3 : ℝ) ≤ 3 :=
    log_natCast_le_natCast (by norm_num)
  push_cast
  rw [Real.log_mul (by norm_num) hmR.ne']
  nlinarith

lemma log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left log_two_le_one
    (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at hmul ⊢
  exact hmul

/-- Logarithmic loss of the two reciprocal regular children at the concrete
first and second scales. -/
lemma log_twoReciprocalLossFormula_dyadic_le_degree_eleven
    (d rank : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d)) :
    Real.log
        (twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne d (dyadicRankCost d))
          (ConcreteNumerics.mTwo d (dyadicRankCost d)) : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 14658798 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let mOne := ConcreteNumerics.mOne d (dyadicRankCost d)
  let mTwo := ConcreteNumerics.mTwo d (dyadicRankCost d)
  have hmOne : 0 < mOne := by
    unfold mOne
    exact ConcreteNumerics.mOne_pos (dyadicRankCost_pos d)
  have hmTwo : 0 < mTwo := by
    unfold mTwo
    exact ConcreteNumerics.mTwo_pos (dyadicRankCost_pos d)
  have hlogMOne : Real.log (mOne : ℝ) ≤
      7700594 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [mOne] using log_dyadicMOne_le_degree_two d
  have hlogMTwo : Real.log (mTwo : ℝ) ≤
      6958194 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [mTwo] using log_dyadicMTwo_le_degree_two d
  have hlog3One := log_three_mul_le_of_log_le hmOne hlogMOne
  have hlog3Two := log_three_mul_le_of_log_le hmTwo hlogMTwo
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hfactorOne :
      Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4 ≤
        7700599 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hfactorTwo :
      Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4 ≤
        6958199 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) := by
        exact_mod_cast hrank
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        exact_mod_cast dyadicRankCap_le_degree_nine d
  have hfactorOneNonneg :
      0 ≤ Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * mOne : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * mOne by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hfactorTwoNonneg :
      0 ≤ Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * mTwo : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * mTwo by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  rw [log_twoReciprocalLossFormula hmOne hmTwo]
  have htermOne := mul_le_mul hrankR hfactorOne hfactorOneNonneg (by positivity)
  have htermTwo := mul_le_mul hrankR hfactorTwo hfactorTwoNonneg (by positivity)
  push_cast at htermOne htermTwo ⊢
  nlinarith

/-- Logarithmic loss of the three fixed smoothing-hierarchy children. -/
lemma log_smoothingHierarchyLossFormula_dyadic_le_degree_eleven
    (d rank : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d)) :
    Real.log (smoothingHierarchyLossFormula rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 20646194 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  have hRpos : 0 < R := by
    unfold R
    exact ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hlogR : Real.log (R : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [R] using log_dyadicRankCap_le_degree_two d
  have hlogMax : Real.log ((max rank 1 : ℕ) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 :=
    (log_max_rank_le_log_rankCap hRpos (by simpa [R] using hrank)).trans hlogR
  have hmaxPos : 0 < max rank 1 := by positivity
  have hmaxPosR : (0 : ℝ) < max rank 1 := by exact_mod_cast hmaxPos
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hlogEta :
      Real.log ((1600 * max rank 1 : ℕ) : ℝ) ≤
        1600 + 6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show ((1600 * max rank 1 : ℕ) : ℝ) =
        (1600 : ℝ) * ((max rank 1 : ℕ) : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hmaxPosR.ne']
    have h1600 : Real.log (1600 : ℝ) ≤ 1600 :=
      log_natCast_le_natCast (by norm_num)
    nlinarith
  have hlogSmall :
      Real.log ((200 * max rank 1 : ℕ) : ℝ) ≤
        200 + 6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show ((200 * max rank 1 : ℕ) : ℝ) =
        (200 : ℝ) * ((max rank 1 : ℕ) : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hmaxPosR.ne']
    have h200 : Real.log (200 : ℝ) ≤ 200 :=
      log_natCast_le_natCast (by norm_num)
    nlinarith
  have hEtaPos : 0 < 1600 * max rank 1 := by positivity
  have hSmallPos : 0 < 200 * max rank 1 := by positivity
  have hlog3Eta := log_three_mul_le_of_log_le hEtaPos hlogEta
  have hlog3Small := log_three_mul_le_of_log_le hSmallPos hlogSmall
  have hfactorEta :
      Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) + Real.log 4 ≤
        6882998 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hfactorSmall :
      Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) + Real.log 4 ≤
        6881598 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by simpa [R] using hrank)
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        simpa [R] using (show
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
            (1024 * dyadicRankDegreeEightConstant : ℕ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 by
          exact_mod_cast dyadicRankCap_le_degree_nine d)
  have hfactorEtaNonneg :
      0 ≤ Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * (1600 * max rank 1) : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * (1600 * max rank 1) by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hfactorSmallNonneg :
      0 ≤ Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * (200 * max rank 1) : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * (200 * max rank 1) by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  rw [log_smoothingHierarchyLossFormula]
  have htermEta := mul_le_mul hrankR hfactorEta hfactorEtaNonneg (by positivity)
  have htermSmall := mul_le_mul hrankR hfactorSmall hfactorSmallNonneg (by positivity)
  push_cast at htermEta htermSmall ⊢
  nlinarith

/-- Formula-level product of every finite loss used in the final raw
high-norm branch.  ConcreteSupply unfolds its names to this expression. -/
def dyadicTotalLossFormula (d rank cap : ℕ) : ℕ :=
  twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne d (dyadicRankCost d))
      (ConcreteNumerics.mTwo d (dyadicRankCost d)) *
    smoothingHierarchyLossFormula rank *
      (3 * sourceDenominator rank cap
        (dyadicHierarchyFormula d
          (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank *
        dyadicCellMultiplier d

def dyadicTotalLogConstant : ℕ :=
  1024 * dyadicRankDegreeEightConstant * 57669725 +
    dyadicCellLogConstant

/-- The fixed dyadic cell multiplier has a degree-ten logarithmic loss.  This
is the main quantitative input for a uniform `cardMultiplier` in the final
raw supply. -/
lemma log_dyadicCellMultiplier_le_degree_ten (d : ℕ) :
    Real.log (dyadicCellMultiplier d : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 10 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let delta := dyadicRankCost d
  let n := dyadicQQuant d * (8 * dyadicRankCost d + 1)
  have hqPos : 0 < dyadicQQuant d := by
    unfold dyadicQQuant
    exact qQuant_pos (dyadicSiftedAlpha_pos d)
  have hdeltaPos : 0 < delta := by
    simpa [delta] using dyadicRankCost_pos d
  have hn : 0 < n := by
    unfold n
    positivity
  have hlogn : Real.log (n : ℝ) ≤
      8601726 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [n] using log_dyadicSampleBase_le_degree_two d
  have hlognNonneg : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by exact Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hdelta : (delta : ℝ) ≤
      (dyadicRankDegreeEightConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 8 := by
    unfold delta
    exact_mod_cast dyadicRankCost_le_degree_eight d
  have hR : (R : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    unfold R
    exact_mod_cast dyadicRankCap_le_degree_nine d
  have hx : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ d + 1 by omega)
  have hpow8 : ((d + 1 : ℕ) : ℝ) ^ 8 ≤
      ((d + 1 : ℕ) : ℝ) ^ 10 :=
    pow_le_pow_right₀ hx (by omega)
  have hpow9 : ((d + 1 : ℕ) : ℝ) ^ 9 ≤
      ((d + 1 : ℕ) : ℝ) ^ 10 :=
    pow_le_pow_right₀ hx (by omega)
  have hfirst :
      (delta : ℝ) * Real.log (n : ℝ) ≤
        ((dyadicRankDegreeEightConstant : ℝ) * 8601726) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (delta : ℝ) * Real.log (n : ℝ) ≤
          ((dyadicRankDegreeEightConstant : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 8) *
            (8601726 * ((d + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul hdelta hlogn hlognNonneg (by positivity)
      _ = ((dyadicRankDegreeEightConstant : ℝ) * 8601726) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by ring
  have hsum10 : (R + delta : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant +
        dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (R : ℝ) + delta ≤
          ((1024 * dyadicRankDegreeEightConstant : ℕ) : ℝ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 +
            dyadicRankDegreeEightConstant *
              ((d + 1 : ℕ) : ℝ) ^ 8 := add_le_add hR hdelta
      _ ≤ ((1024 * dyadicRankDegreeEightConstant : ℕ) : ℝ) *
              ((d + 1 : ℕ) : ℝ) ^ 10 +
            dyadicRankDegreeEightConstant *
              ((d + 1 : ℕ) : ℝ) ^ 10 := by
        gcongr
      _ = ((1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant : ℕ) : ℝ) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
        push_cast
        ring
  have hlogfour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num at hmul ⊢
    exact hmul
  have hlogfourNonneg : 0 ≤ Real.log (4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hsecond :
      (R + delta : ℝ) * Real.log 4 ≤
        (2 : ℝ) *
          (1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (R + delta : ℝ) * Real.log 4 ≤
          ((1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant : ℕ) : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 10 * 2 :=
        mul_le_mul hsum10 hlogfour hlogfourNonneg (by positivity)
      _ = (2 : ℝ) *
          (1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
        push_cast
        ring
  unfold dyadicCellMultiplier
  change Real.log (cellMultiplier R delta n : ℝ) ≤ _
  rw [log_cellMultiplier hn]
  unfold dyadicCellLogConstant
  push_cast at hfirst hsecond ⊢
  nlinarith

/-- One fixed degree-eleven logarithmic envelope for all global, hierarchy,
source, and localized-cell cardinality losses. -/
lemma log_dyadicTotalLossFormula_le_degree_eleven
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log (dyadicTotalLossFormula d rank cap : ℝ) ≤
      (dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let two := twoReciprocalLossFormula rank
    (ConcreteNumerics.mOne d (dyadicRankCost d))
    (ConcreteNumerics.mTwo d (dyadicRankCost d))
  let smooth := smoothingHierarchyLossFormula rank
  let source :=
    (3 * sourceDenominator rank cap
      (dyadicHierarchyFormula d
        (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank
  let cell := dyadicCellMultiplier d
  have htwo : Real.log (two : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 14658798 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [two] using
      log_twoReciprocalLossFormula_dyadic_le_degree_eleven d rank hrank
  have hsmooth : Real.log (smooth : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 20646194 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [smooth] using
      log_smoothingHierarchyLossFormula_dyadic_le_degree_eleven d rank hrank
  have hsource : Real.log (source : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 22364733 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [source] using
      log_sourcePow_dyadicFormula_le_degree_eleven d rank cap hrank hcap
  have hcell : Real.log (cell : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 10 := by
    simpa [cell] using log_dyadicCellMultiplier_le_degree_ten d
  have hx : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ d + 1 by omega)
  have hpow10 : ((d + 1 : ℕ) : ℝ) ^ 10 ≤
      ((d + 1 : ℕ) : ℝ) ^ 11 :=
    pow_le_pow_right₀ hx (by omega)
  have hcell11 : Real.log (cell : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 :=
    hcell.trans (mul_le_mul_of_nonneg_left hpow10 (by positivity))
  have htwoPos : (0 : ℝ) < two := by
    have hmOne := ConcreteNumerics.mOne_pos (d := d)
      (rankCost := dyadicRankCost d) (dyadicRankCost_pos d)
    have hmTwo := ConcreteNumerics.mTwo_pos (d := d)
      (rankCost := dyadicRankCost d) (dyadicRankCost_pos d)
    unfold two twoReciprocalLossFormula
    exact_mod_cast Nat.mul_pos
      (reciprocalLossFormula_pos hmOne) (reciprocalLossFormula_pos hmTwo)
  have hsmoothPos : (0 : ℝ) < smooth := by
    unfold smooth smoothingHierarchyLossFormula reciprocalLossFormula
    positivity
  have hsourcePos : (0 : ℝ) < source := by
    unfold source sourceDenominator dyadicHierarchyFormula
    positivity
  have hcellPos : (0 : ℝ) < cell := by
    have hq : 0 < dyadicQQuant d := by
      unfold dyadicQQuant
      exact qQuant_pos (dyadicSiftedAlpha_pos d)
    unfold cell dyadicCellMultiplier cellMultiplier
    positivity
  change Real.log ((two * smooth * source * cell : ℕ) : ℝ) ≤ _
  push_cast
  rw [Real.log_mul
      (mul_ne_zero
        (mul_ne_zero htwoPos.ne' hsmoothPos.ne') hsourcePos.ne')
      hcellPos.ne',
    Real.log_mul (mul_ne_zero htwoPos.ne' hsmoothPos.ne') hsourcePos.ne',
    Real.log_mul htwoPos.ne' hsmoothPos.ne']
  unfold dyadicTotalLogConstant
  push_cast at htwo hsmooth hsource hcell11 ⊢
  nlinarith

/-- Compose a source-volume loss with the cell multiplier into the single
finite loss consumed by child_card_of_loss. -/
lemma card_le_source_cellMultiplier_mul_child
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {B : BohrData G} {source child : Finset G}
    {P rank delta n : ℕ}
    (hB :
      B.carrier.card ≤ (3 * P) ^ B.rank * source.card)
    (hsource :
      source.card ≤ cellMultiplier rank delta n * child.card) :
    B.carrier.card ≤
      ((3 * P) ^ B.rank * cellMultiplier rank delta n) * child.card := by
  calc
    B.carrier.card ≤ (3 * P) ^ B.rank * source.card := hB
    _ ≤ (3 * P) ^ B.rank *
        (cellMultiplier rank delta n * child.card) :=
      Nat.mul_le_mul_left _ hsource
    _ = ((3 * P) ^ B.rank * cellMultiplier rank delta n) *
        child.card := by ring

/-- Additive logarithmic form of the source-volume times cell-multiplier
loss. -/
lemma log_source_cellMultiplier
    {P rank delta n : ℕ} (hP : 0 < P) (hn : 0 < n) :
    Real.log (((3 * P) ^ rank * cellMultiplier rank delta n : ℕ) : ℝ) =
      (rank : ℝ) * Real.log ((3 * P : ℕ) : ℝ) +
        ((delta : ℝ) * Real.log (n : ℝ) +
          (rank + delta : ℝ) * Real.log 4) := by
  have hleft : (0 : ℝ) < (3 * (P : ℝ)) ^ rank := by positivity
  have hmult : (0 : ℝ) < (cellMultiplier rank delta n : ℕ) := by
    unfold cellMultiplier
    positivity
  have hmult' : (0 : ℝ) < (cellMultiplier rank delta n : ℝ) := hmult
  push_cast
  rw [Real.log_mul hleft.ne' hmult'.ne', Real.log_pow,
    log_cellMultiplier hn]

/-- Monotone envelope for the exact source/cell logarithm.  ConcreteSupply
only has to provide polynomial bounds for R, D, log(3P), and log n. -/
lemma log_source_cellMultiplier_le_of_bounds
    {P rank delta n R D : ℕ} {LP LN : ℝ}
    (hP : 0 < P) (hn : 0 < n)
    (hrank : rank ≤ R) (hdelta : delta ≤ D)
    (hPlog : Real.log ((3 * P : ℕ) : ℝ) ≤ LP)
    (hnlog : Real.log (n : ℝ) ≤ LN) :
    Real.log (((3 * P) ^ rank * cellMultiplier rank delta n : ℕ) : ℝ) ≤
      (R : ℝ) * LP +
        ((D : ℝ) * LN + (R + D : ℝ) * Real.log 4) := by
  rw [log_source_cellMultiplier hP hn]
  have hlogP : 0 ≤ Real.log ((3 * P : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * P by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hrankR : (rank : ℝ) ≤ R := by exact_mod_cast hrank
  have hdeltaD : (delta : ℝ) ≤ D := by exact_mod_cast hdelta
  have hadd : (rank + delta : ℝ) ≤ R + D := by
    exact_mod_cast Nat.add_le_add hrank hdelta
  gcongr

end

end Erdos140.RawSupplyNumerics

#print axioms Erdos140.RawSupplyNumerics.quantized_phase_mul_sqrt_le
#print axioms Erdos140.RawSupplyNumerics.dyadic_tail_mul_sqrt_le
#print axioms Erdos140.RawSupplyNumerics.delta_card_le_changRankCost
