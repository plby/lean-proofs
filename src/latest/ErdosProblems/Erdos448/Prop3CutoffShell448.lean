import ErdosProblems.Erdos448.Prop3WeightedT448
import ErdosProblems.Erdos448.FirstShiftedSmall448
import ErdosProblems.Erdos448.LogConvolution448
import ErdosProblems.Erdos448.ConvolutionExtra448

open scoped BigOperators
open Finset

namespace Prop3CutoffShell448

open Prop3WeightedT448

/-! The dyadic-shell step between the two shifted mean-value estimates. -/

/-- A uniform constant for the first shifted estimate, including its
two-point endpoint. -/
noncomputable def firstShiftedEnvelopeConstant : ℝ :=
  Prop3ShiftedMean448.shiftedReciprocalMeanConstant +
    Real.sqrt (Real.log 4)

lemma firstShiftedEnvelopeConstant_nonneg :
    0 ≤ firstShiftedEnvelopeConstant := by
  unfold firstShiftedEnvelopeConstant
  exact add_nonneg
    Prop3ShiftedMean448.shiftedReciprocalMeanConstant_pos.le
    (Real.sqrt_nonneg _)

lemma log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

lemma log_four_pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)

lemma ceilDiv_ge_two_of_lt {z t : ℕ} (ht : 0 < t) (htz : t < z) :
    2 ≤ z ⌈/⌉ t := by
  by_contra h
  have hle : z ⌈/⌉ t ≤ 1 := by omega
  have hzle : z ≤ t := by
    calc
      z ≤ t * (z ⌈/⌉ t) := (ceilDiv_le_iff_le_mul ht).1 le_rfl
      _ ≤ t * 1 := Nat.mul_le_mul_left t hle
      _ = t := by simp
  omega

lemma one_div_sqrt_eq_rpow_neg_half {y : ℝ} (hy : 0 < y) :
    1 / Real.sqrt y = y ^ (-(1 : ℝ) / 2) := by
  rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le]
  congr 1
  ring

/-- The all-cutoff shifted bound is dominated by one uniform logarithmic
envelope.  The equality of nested ceiling divisions is the reason for using
`z = ceil (x/q)` in the shell argument. -/
theorem weightedFirstShiftedBoundAll_le_envelope
    {x q t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (htz : t < x ⌈/⌉ q) :
    FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t) ≤
      firstShiftedEnvelopeConstant * ((x ⌈/⌉ q) ⌈/⌉ t : ℕ) *
        Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t) /
          Real.sqrt (Real.log
            (2 * (((x ⌈/⌉ q) ⌈/⌉ t : ℕ) : ℝ))) := by
  let z := x ⌈/⌉ q
  let u := z ⌈/⌉ t
  have hu2 : 2 ≤ u := by
    dsimp [u, z]
    exact ceilDiv_ge_two_of_lt ht htz
  have huPos : 0 < (u : ℝ) := by positivity
  have hlog : 0 < Real.log (2 * (u : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 * u by omega)
  have hsqrt : 0 < Real.sqrt (Real.log (2 * (u : ℝ))) :=
    Real.sqrt_pos.2 hlog
  have hw : 0 ≤
      Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t) :=
    Prop3ShiftedMean448.sharpShiftedReciprocalWeight_nonneg _
  have hceil : x ⌈/⌉ (q * t) = u := by
    dsimp [u, z]
    exact (FirstShiftedSmall448.ceilDiv_mul x q t hq ht).symm
  by_cases hlarge : 3 ≤ u
  · rw [FirstShiftedSmall448.weightedFirstShiftedBoundAll, if_pos (hceil ▸ hlarge)]
    rw [hceil]
    apply div_le_div_of_nonneg_right _ hsqrt.le
    apply mul_le_mul_of_nonneg_right _ hw
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg u)
    unfold firstShiftedEnvelopeConstant
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  · have hu : u = 2 := by omega
    have hnested : (x ⌈/⌉ q) ⌈/⌉ t = u := by rfl
    rw [FirstShiftedSmall448.weightedFirstShiftedBoundAll,
      if_neg (by simpa [hceil] using hlarge)]
    rw [hnested, hu]
    ·
      norm_num only [Nat.cast_ofNat]
      have hsqrt4 : 0 < Real.sqrt (Real.log (4 : ℝ)) :=
        Real.sqrt_pos.2 log_four_pos
      rw [div_eq_mul_inv]
      have hconst : Real.sqrt (Real.log (4 : ℝ)) ≤
          firstShiftedEnvelopeConstant := by
        unfold firstShiftedEnvelopeConstant
        linarith [Prop3ShiftedMean448.shiftedReciprocalMeanConstant_pos]
      have hunit : (1 : ℝ) ≤
          firstShiftedEnvelopeConstant * 2 *
            (Real.sqrt (Real.log (4 : ℝ)))⁻¹ := by
        have hinv : 0 ≤ (Real.sqrt (Real.log (4 : ℝ)))⁻¹ := by positivity
        calc
          (1 : ℝ) = Real.sqrt (Real.log (4 : ℝ)) *
              (Real.sqrt (Real.log (4 : ℝ)))⁻¹ := by
                field_simp [hsqrt4.ne']
          _ ≤ firstShiftedEnvelopeConstant *
              (Real.sqrt (Real.log (4 : ℝ)))⁻¹ :=
                mul_le_mul_of_nonneg_right hconst hinv
          _ ≤ firstShiftedEnvelopeConstant * 2 *
              (Real.sqrt (Real.log (4 : ℝ)))⁻¹ := by
                have hc := firstShiftedEnvelopeConstant_nonneg
                nlinarith [mul_nonneg hc hinv]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hunit)]

/-- Number of dyadic `t`-shells below a nontrivial residual cutoff. -/
def shellHeight (z : ℕ) : ℕ := Nat.log 2 (z - 1) + 1

/-- The shell `2^j ≤ t < 2^(j+1)`, intersected with `0 < t < z`. -/
def dyadicTShell (z j : ℕ) : Finset ℕ :=
  (Finset.Ico 1 z).filter (fun t ↦ Nat.log 2 t = j)

lemma mem_dyadicTShell {z j t : ℕ} :
    t ∈ dyadicTShell z j ↔
      1 ≤ t ∧ t < z ∧ Nat.log 2 t = j := by
  simp [dyadicTShell, and_assoc]

lemma log_lt_shellHeight {z t : ℕ} (ht : t ∈ Finset.Ico 1 z) :
    Nat.log 2 t < shellHeight z := by
  have ht' := Finset.mem_Ico.mp ht
  have htle : t ≤ z - 1 := by omega
  unfold shellHeight
  exact Nat.lt_succ_of_le (Nat.log_mono_right htle)

lemma sum_dyadicTShell (z : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (shellHeight z), ∑ t ∈ dyadicTShell z j, f t) =
      ∑ t ∈ Finset.Ico 1 z, f t := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun t ht ↦ Finset.mem_range.mpr (log_lt_shellHeight ht)) f

lemma dyadicTShell_subset_prefix {z j : ℕ} :
    dyadicTShell z j ⊆ Finset.Ico 1 (2 ^ (j + 1)) := by
  intro t ht
  rw [mem_dyadicTShell] at ht
  refine Finset.mem_Ico.mpr ⟨ht.1, ?_⟩
  simpa [ht.2.2] using Nat.lt_pow_succ_log_self Nat.one_lt_two t

lemma pow_shellHeight_lt_two_mul {z : ℕ} (hz : 2 ≤ z) :
    2 ^ shellHeight z < 2 * z := by
  have hz1 : z - 1 ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 (z - 1) ≤ z - 1 :=
    Nat.pow_log_le_self 2 hz1
  unfold shellHeight
  rw [pow_succ]
  omega

lemma le_pow_shellHeight {z : ℕ} (hz : 2 ≤ z) :
    z ≤ 2 ^ shellHeight z := by
  have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two (z - 1)
  unfold shellHeight
  omega

lemma shell_ceilDiv_upper {z j t : ℕ} (hz : 2 ≤ z)
    (ht : t ∈ dyadicTShell z j) :
    z ⌈/⌉ t ≤ 2 ^ (shellHeight z - j) := by
  rw [mem_dyadicTShell] at ht
  have hj : j < shellHeight z := by
    rw [← ht.2.2]
    exact log_lt_shellHeight (Finset.mem_Ico.mpr ⟨ht.1, ht.2.1⟩)
  have htPow : 2 ^ j ≤ t := by
    simpa [ht.2.2] using Nat.pow_log_le_self 2 (by omega : t ≠ 0)
  rw [ceilDiv_le_iff_le_mul (by omega : 0 < t)]
  calc
    z ≤ 2 ^ shellHeight z := le_pow_shellHeight hz
    _ = 2 ^ j * 2 ^ (shellHeight z - j) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ t * 2 ^ (shellHeight z - j) :=
      Nat.mul_le_mul_right _ htPow

lemma shell_log_lower {z j t : ℕ} (hz : 2 ≤ z)
    (ht : t ∈ dyadicTShell z j) (hj : j + 1 < shellHeight z) :
    ((shellHeight z - (j + 1) : ℕ) : ℝ) * Real.log 2 ≤
      Real.log (2 * ((z ⌈/⌉ t : ℕ) : ℝ)) := by
  rw [mem_dyadicTShell] at ht
  let J := shellHeight z
  let b := J - (j + 1)
  let u := z ⌈/⌉ t
  have hb : 1 ≤ b := by dsimp [b, J]; omega
  have htPos : 0 < t := by omega
  have huPos : 0 < u := by
    dsimp [u]
    exact (ceilDiv_ge_two_of_lt htPos ht.2.1).trans' (by omega)
  have hzLower : 2 ^ (J - 1) < z := by
    have hz1 : z - 1 ≠ 0 := by omega
    have hpow : 2 ^ Nat.log 2 (z - 1) ≤ z - 1 :=
      Nat.pow_log_le_self 2 hz1
    dsimp [J, shellHeight]
    simpa using (show 2 ^ Nat.log 2 (z - 1) < z by omega)
  have htUpper : t < 2 ^ (j + 1) := by
    simpa [ht.2.2] using Nat.lt_pow_succ_log_self Nat.one_lt_two t
  have hzu : z ≤ t * u := by
    exact (ceilDiv_le_iff_le_mul htPos).1 le_rfl
  have hpowLt : 2 ^ (J - 1) < 2 ^ (j + 1) * u := by
    calc
      2 ^ (J - 1) < z := hzLower
      _ ≤ t * u := hzu
      _ < 2 ^ (j + 1) * u := Nat.mul_lt_mul_of_pos_right htUpper huPos
  have hJ : j + 1 ≤ J := by omega
  have hpowRewrite : 2 ^ (J - 1) = 2 ^ j * 2 ^ b := by
    rw [← pow_add]
    congr 1
    dsimp [b]
    omega
  have hrightRewrite : 2 ^ (j + 1) * u = 2 ^ j * (2 * u) := by
    rw [pow_succ]
    ring
  rw [hpowRewrite, hrightRewrite] at hpowLt
  have htwoU : 2 ^ b ≤ 2 * u := by
    have hpowPos : 0 < 2 ^ j := pow_pos (by norm_num) _
    exact (Nat.mul_lt_mul_left hpowPos).mp hpowLt |>.le
  have hcast : (((2 ^ b : ℕ) : ℝ)) ≤ 2 * (u : ℝ) := by
    exact_mod_cast htwoU
  have hpowPos : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) b)
  have hlog := Real.log_le_log hpowPos hcast
  rw [show Real.log (((2 ^ b : ℕ) : ℝ)) = (b : ℝ) * Real.log 2 by
    norm_num [Real.log_pow]] at hlog
  simpa [J, b, u] using hlog

lemma shell_envelope_factor_le {z j t : ℕ} (hz : 2 ≤ z)
    (ht : t ∈ dyadicTShell z j) (hj : j + 1 < shellHeight z) :
    ((z ⌈/⌉ t : ℕ) : ℝ) /
        Real.sqrt (Real.log (2 * ((z ⌈/⌉ t : ℕ) : ℝ))) ≤
      ((2 ^ (shellHeight z - (j + 1) + 1) : ℕ) : ℝ) *
        (Real.log 2) ^ (-(1 : ℝ) / 2) *
        ((shellHeight z - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
  let b := shellHeight z - (j + 1)
  let u := z ⌈/⌉ t
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hu2 : 2 ≤ u := by
    dsimp [u]
    rw [mem_dyadicTShell] at ht
    exact ceilDiv_ge_two_of_lt (by omega) ht.2.1
  have hlog2 : 0 < Real.log (2 : ℝ) := log_two_pos
  have hbR : 0 < (b : ℝ) := by positivity
  have hlogU : 0 < Real.log (2 * (u : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 * u by omega)
  have hlower : (b : ℝ) * Real.log 2 ≤ Real.log (2 * (u : ℝ)) := by
    simpa [b, u] using shell_log_lower hz ht hj
  have huUpper : u ≤ 2 ^ (b + 1) := by
    have h := shell_ceilDiv_upper hz ht
    have he : shellHeight z - j = b + 1 := by dsimp [b]; omega
    simpa [u, he] using h
  change (u : ℝ) / Real.sqrt (Real.log (2 * (u : ℝ))) ≤ _
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hlogU.le]
  have hpowLog :
      (Real.log (2 * (u : ℝ))) ^ (-(1 : ℝ) / 2) ≤
        ((b : ℝ) * Real.log 2) ^ (-(1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hbR hlog2) hlower (by norm_num)
  have hmulPow : ((b : ℝ) * Real.log 2) ^ (-(1 : ℝ) / 2) =
      (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (b : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow hbR.le hlog2.le]
    ring
  rw [hmulPow] at hpowLog
  have huCast : (u : ℝ) ≤ ((2 ^ (b + 1) : ℕ) : ℝ) := by
    exact_mod_cast huUpper
  have hexp : (-(1 : ℝ) / 2) = (-(1 / 2 : ℝ)) := by ring
  rw [hexp] at hpowLog ⊢
  calc
    (u : ℝ) * (Real.log (2 * (u : ℝ))) ^ (-(1 / 2 : ℝ)) ≤
        ((2 ^ (b + 1) : ℕ) : ℝ) *
          (Real.log (2 * (u : ℝ))) ^ (-(1 / 2 : ℝ)) := by
      gcongr
    _ ≤ ((2 ^ (b + 1) : ℕ) : ℝ) *
          ((Real.log 2) ^ (-(1 / 2 : ℝ)) *
            (b : ℝ) ^ (-(1 / 2 : ℝ))) := by
      gcongr
    _ = _ := by ring

lemma sharp_weightedTKernel_eq {q k t : ℕ} (ht : t ≠ 0) :
    weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t =
      omegaWeight k t *
        Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t) := by
  rw [weightedTKernel, roughIndicator_two_of_ne_zero ht]
  simp [Nat.mul_comm]

lemma sharpHybridCorrectionWeight_nonneg (k q : ℕ) :
    0 ≤ hybridCorrectionWeight sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) q := by
  exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
    (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
    (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
    (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q

lemma weightedFirstShiftedBoundAll_nonneg (x q : ℕ) :
    0 ≤ FirstShiftedSmall448.weightedFirstShiftedBoundAll x q := by
  unfold FirstShiftedSmall448.weightedFirstShiftedBoundAll
  split_ifs
  · exact div_nonneg
      (mul_nonneg
        (mul_nonneg Prop3ShiftedMean448.shiftedReciprocalMeanConstant_pos.le
          (Nat.cast_nonneg _))
        (Prop3ShiftedMean448.sharpShiftedReciprocalWeight_nonneg q))
      (Real.sqrt_nonneg _)
  · exact Prop3ShiftedMean448.sharpShiftedReciprocalWeight_nonneg q

/-- One interior dyadic shell, before inserting the arbitrary-cutoff HR
estimate.  This is the exact cancellation of the first shifted cutoff
against the length of the second shifted sum. -/
theorem dyadicTShell_firstShifted_le_weightedTSum
    {x q k z j : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hj : j + 1 < shellHeight z) :
    (∑ t ∈ dyadicTShell z j,
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      firstShiftedEnvelopeConstant *
        (((2 ^ (shellHeight z - (j + 1) + 1) : ℕ) : ℝ) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) *
          ((shellHeight z - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) *
        weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ (j + 1)) := by
  let E : ℝ := (((2 ^ (shellHeight z - (j + 1) + 1) : ℕ) : ℝ) *
    (Real.log 2) ^ (-(1 : ℝ) / 2) *
    ((shellHeight z - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc : 0 ≤ firstShiftedEnvelopeConstant :=
    firstShiftedEnvelopeConstant_nonneg
  calc
    (∑ t ∈ dyadicTShell z j,
        omegaWeight k t *
          FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      ∑ t ∈ dyadicTShell z j,
        firstShiftedEnvelopeConstant * E *
          weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t := by
      apply Finset.sum_le_sum
      intro t ht
      have htData := (mem_dyadicTShell.mp ht)
      have htPos : 0 < t := by omega
      have hfirst := weightedFirstShiftedBoundAll_le_envelope hq htPos (by
        rw [← hzEq]
        exact htData.2.1)
      have hfac := shell_envelope_factor_le hz ht hj
      have homega := omegaWeight_nonneg k t
      have hw := Prop3ShiftedMean448.sharpShiftedReciprocalWeight_nonneg (q * t)
      calc
        omegaWeight k t *
            FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t) ≤
          omegaWeight k t *
            (firstShiftedEnvelopeConstant * (((x ⌈/⌉ q) ⌈/⌉ t : ℕ) : ℝ) *
              Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t) /
                Real.sqrt (Real.log
                  (2 * ((((x ⌈/⌉ q) ⌈/⌉ t : ℕ) : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_left hfirst homega
        _ = firstShiftedEnvelopeConstant *
            (((z ⌈/⌉ t : ℕ) : ℝ) /
              Real.sqrt (Real.log (2 * ((z ⌈/⌉ t : ℕ) : ℝ)))) *
            (omegaWeight k t *
              Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t)) := by
                rw [hzEq]
                ring
        _ ≤ firstShiftedEnvelopeConstant * E *
            (omegaWeight k t *
              Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t)) := by
                have hweight : 0 ≤ omegaWeight k t *
                    Prop3ShiftedMean448.sharpShiftedReciprocalWeight (q * t) :=
                  mul_nonneg homega hw
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hfac hc) hweight
        _ = firstShiftedEnvelopeConstant * E *
            weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t := by
              rw [sharp_weightedTKernel_eq htPos.ne']
    _ = firstShiftedEnvelopeConstant * E *
        (∑ t ∈ dyadicTShell z j,
          weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t) := by
      rw [Finset.mul_sum]
    _ ≤ firstShiftedEnvelopeConstant * E *
        weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ (j + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hE)
      unfold weightedTSum
      apply Finset.sum_le_sum_of_subset_of_nonneg dyadicTShell_subset_prefix
      intro t ht hnot
      exact weightedTKernel_nonneg sharpShiftedReciprocalWeightAF
        sharpShiftedReciprocalWeightAF_nonneg q k 2 t
    _ = _ := by rfl

lemma sharpWeightedTSum_two_pow_middle_le
    {q k a : ℕ} (hq : q ≠ 0) (ha : 1 ≤ a) (hak : a < k) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) ≤
      sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ)) *
        (a : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hk : 1 ≤ k := by omega
  have hnot : ¬ 2 ^ k ≤ 2 ^ a := by
    simpa [Nat.pow_le_pow_iff_right Nat.one_lt_two] using (not_le.mpr hak)
  have htwo : 2 ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
    simpa using this
  have h := sharpWeightedTSum_half_le hq k hk (2 ^ a)
  rw [if_neg hnot, if_pos htwo] at h
  have haR : 0 < (a : ℝ) := by positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := log_two_pos
  have hlog : Real.log (((2 ^ a : ℕ) : ℝ)) =
      (a : ℝ) * Real.log 2 := by
    norm_num [Real.log_pow]
  rw [hlog, Real.mul_rpow haR.le hlog2.le] at h
  calc
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) ≤
      sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        ((a : ℝ) ^ (-(3 : ℝ) / 4) *
          (Real.log 2) ^ (-(3 : ℝ) / 4)) := h
    _ = _ := by
      have hlogs : (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log 2) ^ (-(3 : ℝ) / 4) =
          (Real.log 2) ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hlog2]
        congr 1
        ring
      rw [← hlogs]
      ring

lemma sharpWeightedTSum_two_pow_long_le
    {q k a : ℕ} (hq : q ≠ 0) (hk : 1 ≤ k) (hka : k ≤ a) :
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) ≤
      sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (a : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpow : 2 ^ k ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hka
  have h := sharpWeightedTSum_half_le hq k hk (2 ^ a)
  rw [if_pos hpow] at h
  have ha : 1 ≤ a := hk.trans hka
  have haR : 0 < (a : ℝ) := by positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := log_two_pos
  have hlog : Real.log (((2 ^ a : ℕ) : ℝ)) =
      (a : ℝ) * Real.log 2 := by
    norm_num [Real.log_pow]
  rw [hlog, Real.mul_rpow haR.le hlog2.le] at h
  calc
    weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) ≤
      sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(1 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        ((a : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.log 2) ^ (-(1 : ℝ) / 2)) := h
    _ = _ := by
      have hlogs : (Real.log 2) ^ (-(1 : ℝ) / 4) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) =
          (Real.log 2) ^ (-(3 : ℝ) / 4) := by
        rw [← Real.rpow_add hlog2]
        congr 1
        ring
      rw [← hlogs]
      ring

lemma shell_power_product_le_four_mul {z j : ℕ} (hz : 2 ≤ z)
    (hj : j + 1 ≤ shellHeight z) :
    (((2 ^ (shellHeight z - (j + 1) + 1) : ℕ) : ℝ)) *
        (((2 ^ (j + 1) : ℕ) : ℝ)) ≤ 4 * (z : ℝ) := by
  have hpow := pow_shellHeight_lt_two_mul hz
  have hnat :
      2 ^ (shellHeight z - (j + 1) + 1) * 2 ^ (j + 1) ≤ 4 * z := by
    rw [← pow_add]
    have he : shellHeight z - (j + 1) + 1 + (j + 1) =
        shellHeight z + 1 := by omega
    rw [he, pow_succ]
    omega
  exact_mod_cast hnat

theorem dyadicTShell_firstShifted_middle_le
    {x q k z j : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hj : j + 1 < shellHeight z) (hjk : j + 1 < k) :
    (∑ t ∈ dyadicTShell z j,
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      4 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
        (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(3 : ℝ) / 2) *
        ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
        ((shellHeight z - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
  let a := j + 1
  let b := shellHeight z - a
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [a, b]; omega
  have hC : 0 ≤ firstShiftedEnvelopeConstant :=
    firstShiftedEnvelopeConstant_nonneg
  have hE : 0 ≤ (((2 ^ (b + 1) : ℕ) : ℝ) *
      (Real.log 2) ^ (-(1 : ℝ) / 2) *
      (b : ℝ) ^ (-(1 : ℝ) / 2)) := by positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  have hbase := dyadicTShell_firstShifted_le_weightedTSum
    (k := k) hq hzEq hz hj
  have hHR := sharpWeightedTSum_two_pow_middle_le hq.ne' ha (by simpa [a] using hjk)
  have hprefix : 0 ≤ firstShiftedEnvelopeConstant *
      (((2 ^ (b + 1) : ℕ) : ℝ) *
        (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (b : ℝ) ^ (-(1 : ℝ) / 2)) := mul_nonneg hC hE
  have hpowers : (((2 ^ (b + 1) : ℕ) : ℝ)) *
      (((2 ^ a : ℕ) : ℝ)) ≤ 4 * (z : ℝ) := by
    simpa [a, b] using shell_power_product_le_four_mul hz (by omega)
  calc
    (∑ t ∈ dyadicTShell z j,
        omegaWeight k t *
          FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      firstShiftedEnvelopeConstant *
        (((2 ^ (b + 1) : ℕ) : ℝ) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (b : ℝ) ^ (-(1 : ℝ) / 2)) *
        weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) := by
          simpa [a, b] using hbase
    _ ≤ firstShiftedEnvelopeConstant *
        (((2 ^ (b + 1) : ℕ) : ℝ) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (b : ℝ) ^ (-(1 : ℝ) / 2)) *
        (sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) * W *
          (Real.log 2) ^ (-(1 : ℝ)) *
          (a : ℝ) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hHR hprefix
    _ ≤ 4 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
        (z : ℝ) * W *
        (Real.log 2) ^ (-(3 : ℝ) / 2) *
        (a : ℝ) ^ (-(3 : ℝ) / 4) *
        (b : ℝ) ^ (-(1 : ℝ) / 2) := by
      have hrest : 0 ≤ firstShiftedEnvelopeConstant *
          sharpWeightedThreeRegimeConstant * W *
          (Real.log 2) ^ (-(3 : ℝ) / 2) *
          (a : ℝ) ^ (-(3 : ℝ) / 4) *
          (b : ℝ) ^ (-(1 : ℝ) / 2) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg hC sharpWeightedThreeRegimeConstant_nonneg) hW)
                (Real.rpow_nonneg log_two_pos.le _))
              (Real.rpow_nonneg (Nat.cast_nonneg a) _))
          (Real.rpow_nonneg (Nat.cast_nonneg b) _)
      have hp := mul_le_mul_of_nonneg_right hpowers hrest
      have hlogs : (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (Real.log 2) ^ (-(1 : ℝ)) =
          (Real.log 2) ^ (-(3 : ℝ) / 2) := by
        rw [← Real.rpow_add log_two_pos]
        congr 1
        ring
      calc
        firstShiftedEnvelopeConstant *
              (((2 ^ (b + 1) : ℕ) : ℝ) *
                (Real.log 2) ^ (-(1 : ℝ) / 2) *
                (b : ℝ) ^ (-(1 : ℝ) / 2)) *
            (sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(1 : ℝ)) *
              (a : ℝ) ^ (-(3 : ℝ) / 4)) =
          (((2 ^ (b + 1) : ℕ) : ℝ) * (((2 ^ a : ℕ) : ℝ))) *
            (firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant * W *
              (Real.log 2) ^ (-(3 : ℝ) / 2) *
              (a : ℝ) ^ (-(3 : ℝ) / 4) *
              (b : ℝ) ^ (-(1 : ℝ) / 2)) := by
                rw [← hlogs]
                ring
        _ ≤ 4 * (z : ℝ) *
            (firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant * W *
              (Real.log 2) ^ (-(3 : ℝ) / 2) *
              (a : ℝ) ^ (-(3 : ℝ) / 4) *
              (b : ℝ) ^ (-(1 : ℝ) / 2)) := hp
        _ = _ := by ring
    _ = _ := by simp [a, b, W]

theorem dyadicTShell_firstShifted_long_le
    {x q k z j : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hk : 1 ≤ k) (hj : j + 1 < shellHeight z)
    (hkj : k ≤ j + 1) :
    (∑ t ∈ dyadicTShell z j,
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      4 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
        (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(5 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
        ((shellHeight z - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
  let a := j + 1
  let b := shellHeight z - a
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  have hb : 1 ≤ b := by dsimp [a, b]; omega
  have hC : 0 ≤ firstShiftedEnvelopeConstant :=
    firstShiftedEnvelopeConstant_nonneg
  have hE : 0 ≤ (((2 ^ (b + 1) : ℕ) : ℝ) *
      (Real.log 2) ^ (-(1 : ℝ) / 2) *
      (b : ℝ) ^ (-(1 : ℝ) / 2)) := by positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  have hbase := dyadicTShell_firstShifted_le_weightedTSum
    (k := k) hq hzEq hz hj
  have hHR := sharpWeightedTSum_two_pow_long_le hq.ne' hk (by simpa [a] using hkj)
  have hprefix : 0 ≤ firstShiftedEnvelopeConstant *
      (((2 ^ (b + 1) : ℕ) : ℝ) *
        (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (b : ℝ) ^ (-(1 : ℝ) / 2)) := mul_nonneg hC hE
  have hpowers : (((2 ^ (b + 1) : ℕ) : ℝ)) *
      (((2 ^ a : ℕ) : ℝ)) ≤ 4 * (z : ℝ) := by
    simpa [a, b] using shell_power_product_le_four_mul hz (by omega)
  calc
    (∑ t ∈ dyadicTShell z j,
        omegaWeight k t *
          FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      firstShiftedEnvelopeConstant *
        (((2 ^ (b + 1) : ℕ) : ℝ) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (b : ℝ) ^ (-(1 : ℝ) / 2)) *
        weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ a) := by
          simpa [a, b] using hbase
    _ ≤ firstShiftedEnvelopeConstant *
        (((2 ^ (b + 1) : ℕ) : ℝ) *
          (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (b : ℝ) ^ (-(1 : ℝ) / 2)) *
        (sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) * W *
          (Real.log 2) ^ (-(3 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (a : ℝ) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hHR hprefix
    _ ≤ 4 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
        (z : ℝ) * W *
        (Real.log 2) ^ (-(5 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (a : ℝ) ^ (-(1 : ℝ) / 2) *
        (b : ℝ) ^ (-(1 : ℝ) / 2) := by
      have hrest : 0 ≤ firstShiftedEnvelopeConstant *
          sharpWeightedThreeRegimeConstant * W *
          (Real.log 2) ^ (-(5 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) *
          (a : ℝ) ^ (-(1 : ℝ) / 2) *
          (b : ℝ) ^ (-(1 : ℝ) / 2) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg hC sharpWeightedThreeRegimeConstant_nonneg) hW)
                  (Real.rpow_nonneg log_two_pos.le _))
                (Real.rpow_nonneg (Nat.cast_nonneg k) _))
              (Real.rpow_nonneg (Nat.cast_nonneg a) _))
          (Real.rpow_nonneg (Nat.cast_nonneg b) _)
      have hp := mul_le_mul_of_nonneg_right hpowers hrest
      have hlogs : (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (Real.log 2) ^ (-(3 : ℝ) / 4) =
          (Real.log 2) ^ (-(5 : ℝ) / 4) := by
        rw [← Real.rpow_add log_two_pos]
        congr 1
        ring
      calc
        firstShiftedEnvelopeConstant *
              (((2 ^ (b + 1) : ℕ) : ℝ) *
                (Real.log 2) ^ (-(1 : ℝ) / 2) *
                (b : ℝ) ^ (-(1 : ℝ) / 2)) *
            (sharpWeightedThreeRegimeConstant * (((2 ^ a : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(3 : ℝ) / 4) *
              (k : ℝ) ^ (-(1 : ℝ) / 4) *
              (a : ℝ) ^ (-(1 : ℝ) / 2)) =
          (((2 ^ (b + 1) : ℕ) : ℝ) * (((2 ^ a : ℕ) : ℝ))) *
            (firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant * W *
              (Real.log 2) ^ (-(5 : ℝ) / 4) *
              (k : ℝ) ^ (-(1 : ℝ) / 4) *
              (a : ℝ) ^ (-(1 : ℝ) / 2) *
              (b : ℝ) ^ (-(1 : ℝ) / 2)) := by
                rw [← hlogs]
                ring
        _ ≤ 4 * (z : ℝ) *
            (firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant * W *
              (Real.log 2) ^ (-(5 : ℝ) / 4) *
              (k : ℝ) ^ (-(1 : ℝ) / 4) *
              (a : ℝ) ^ (-(1 : ℝ) / 2) *
              (b : ℝ) ^ (-(1 : ℝ) / 2)) := hp
        _ = _ := by ring
    _ = _ := by simp [a, b, W]

/-- The final shell has residual ceiling exactly two, so it is already a
subsum of the second shifted kernel, with no logarithmic envelope loss. -/
theorem dyadicTShell_last_le_weightedTSum
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q) (hz : 2 ≤ z) :
    (∑ t ∈ dyadicTShell z (shellHeight z - 1),
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      weightedTSum sharpShiftedReciprocalWeightAF q k 2
        (2 ^ shellHeight z) := by
  have hJ : 1 ≤ shellHeight z := by unfold shellHeight; omega
  calc
    (∑ t ∈ dyadicTShell z (shellHeight z - 1),
        omegaWeight k t *
          FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) =
      ∑ t ∈ dyadicTShell z (shellHeight z - 1),
        weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t := by
      apply Finset.sum_congr rfl
      intro t ht
      have htData := mem_dyadicTShell.mp ht
      have htPos : 0 < t := by omega
      have hu2 : 2 ≤ z ⌈/⌉ t := ceilDiv_ge_two_of_lt htPos htData.2.1
      have huUpper := shell_ceilDiv_upper hz ht
      have hu : z ⌈/⌉ t = 2 := by
        have he : shellHeight z - (shellHeight z - 1) = 1 := by omega
        rw [he] at huUpper
        norm_num at huUpper
        omega
      have hceil : x ⌈/⌉ (q * t) = 2 := by
        rw [← FirstShiftedSmall448.ceilDiv_mul x q t hq htPos, ← hzEq, hu]
      rw [FirstShiftedSmall448.weightedFirstShiftedBoundAll, if_neg (by
        rw [hceil]
        omega)]
      rw [sharp_weightedTKernel_eq htPos.ne']
    _ ≤ ∑ t ∈ Finset.Ico 1 (2 ^ shellHeight z),
        weightedTKernel sharpShiftedReciprocalWeightAF q k 2 t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg dyadicTShell_subset_prefix
      intro t ht hnot
      exact weightedTKernel_nonneg sharpShiftedReciprocalWeightAF
        sharpShiftedReciprocalWeightAF_nonneg q k 2 t
    _ = weightedTSum sharpShiftedReciprocalWeightAF q k 2
        (2 ^ shellHeight z) := by rfl

/-- The exact cutoff convolution after the first shifted mean. -/
noncomputable def cutoffFirstShiftedSum (x q k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico 1 (x ⌈/⌉ q),
    omegaWeight k t *
      FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)

lemma cutoffFirstShiftedSum_eq_shells (x q k : ℕ) :
    cutoffFirstShiftedSum x q k =
      ∑ j ∈ Finset.range (shellHeight (x ⌈/⌉ q)),
        ∑ t ∈ dyadicTShell (x ⌈/⌉ q) j,
          omegaWeight k t *
            FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t) := by
  unfold cutoffFirstShiftedSum
  exact (sum_dyadicTShell (x ⌈/⌉ q) _).symm

lemma sum_range_pred_add_last {J : ℕ} (hJ : 1 ≤ J) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range J, f j) =
      (∑ j ∈ Finset.range (J - 1), f j) + f (J - 1) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Finset.sum_range_succ]
  simp

lemma sum_range_pred_succ_eq_Ioo (J : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (J - 1), f (j + 1)) =
      ∑ a ∈ Finset.Ioo 0 J, f a := by
  by_cases hJ : J = 0
  · subst J
    simp
  have hset : Finset.Ioo 0 J = Finset.Ico 1 J := by
    ext a
    simp
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

/-- Sum of all shells except the last two-point endpoint. -/
noncomputable def interiorCutoffShellSum (x q k : ℕ) : ℝ :=
  let z := x ⌈/⌉ q
  ∑ j ∈ Finset.range (shellHeight z - 1),
    ∑ t ∈ dyadicTShell z j,
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)

theorem interiorCutoffShellSum_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hk : 1 ≤ k) (hJ : 2 ≤ shellHeight z) :
    interiorCutoffShellSum x q k ≤
      48 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(3 : ℝ) / 2) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        32 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(5 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  let J := shellHeight z
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  let A : ℝ := 4 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
    (Real.log 2) ^ (-(3 : ℝ) / 2)
  let B : ℝ := 4 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
    (Real.log 2) ^ (-(5 : ℝ) / 4) *
    (k : ℝ) ^ (-(1 : ℝ) / 4)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  have hA : 0 ≤ A := by
    dsimp only [A]
    have h₄E : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant :=
      mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg
    have h₄ES : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant :=
      mul_nonneg h₄E sharpWeightedThreeRegimeConstant_nonneg
    have h₄ESz : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant * (z : ℝ) :=
      mul_nonneg h₄ES (Nat.cast_nonneg z)
    have h₄ESzW : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant * (z : ℝ) * W :=
      mul_nonneg h₄ESz hW
    exact mul_nonneg h₄ESzW (Real.rpow_nonneg log_two_pos.le _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    have h₄E : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant :=
      mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg
    have h₄ES : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant :=
      mul_nonneg h₄E sharpWeightedThreeRegimeConstant_nonneg
    have h₄ESz : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant * (z : ℝ) :=
      mul_nonneg h₄ES (Nat.cast_nonneg z)
    have h₄ESzW : 0 ≤ (4 : ℝ) * firstShiftedEnvelopeConstant *
        sharpWeightedThreeRegimeConstant * (z : ℝ) * W :=
      mul_nonneg h₄ESz hW
    have hlogpow : 0 ≤ (Real.log 2) ^ (-(5 : ℝ) / 4) :=
      Real.rpow_nonneg log_two_pos.le _
    exact mul_nonneg (mul_nonneg h₄ESzW hlogpow)
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hshell : ∀ j ∈ Finset.range (J - 1),
      (∑ t ∈ dyadicTShell z j,
        omegaWeight k t *
          FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
        A * ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) +
          B * ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
    intro j hj
    have hjlt : j + 1 < J := by
      have := Finset.mem_range.mp hj
      omega
    by_cases hjk : j + 1 < k
    · have hm := dyadicTShell_firstShifted_middle_le
        hq hzEq hz hjlt hjk
      have hlongNonneg : 0 ≤ B * ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
          ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
      calc
        _ ≤ A * ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
              simpa [A, J, W] using hm
        _ ≤ _ := le_add_of_nonneg_right hlongNonneg
    · have hkj : k ≤ j + 1 := by omega
      have hl := dyadicTShell_firstShifted_long_le
        hq hzEq hz hk hjlt hkj
      have hmidNonneg : 0 ≤ A * ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
          ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
      calc
        _ ≤ B * ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
              simpa [B, J, W] using hl
        _ ≤ _ := le_add_of_nonneg_left hmidNonneg
  have hmidConv :
      (∑ j ∈ Finset.range (J - 1),
        ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
          ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) ≤
        12 * (J : ℝ) ^ (-(1 : ℝ) / 4) := by
    rw [sum_range_pred_succ_eq_Ioo J (fun a ↦
      (a : ℝ) ^ (-(3 : ℝ) / 4) *
        ((J - a : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))]
    convert ConvolutionExtra448.convolution_three_quarters_half_le_twelve J hJ using 1 <;>
      ring
  have hlongConv :
      (∑ j ∈ Finset.range (J - 1),
        ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
          ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) ≤ 8 := by
    rw [sum_range_pred_succ_eq_Ioo J (fun a ↦
      (a : ℝ) ^ (-(1 : ℝ) / 2) *
        ((J - a : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))]
    convert ConvolutionExtra448.convolution_half_half_le_eight J hJ using 1 <;>
      ring
  calc
    interiorCutoffShellSum x q k =
      ∑ j ∈ Finset.range (J - 1),
        ∑ t ∈ dyadicTShell z j,
          omegaWeight k t *
            FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t) := by
              simp [interiorCutoffShellSum, J, hzEq]
    _ ≤ ∑ j ∈ Finset.range (J - 1),
        (A * ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) +
          B * ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) :=
      Finset.sum_le_sum hshell
    _ = A * (∑ j ∈ Finset.range (J - 1),
          ((j + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) +
        B * (∑ j ∈ Finset.range (J - 1),
          ((j + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) *
            ((J - (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;>
        apply Finset.sum_congr rfl <;>
        intro i hi <;> ring
    _ ≤ A * (12 * (J : ℝ) ^ (-(1 : ℝ) / 4)) + B * 8 :=
      add_le_add (mul_le_mul_of_nonneg_left hmidConv hA)
        (mul_le_mul_of_nonneg_left hlongConv hB)
    _ = _ := by simp [A, B, J, W]; ring

lemma one_le_shellHeight {z : ℕ} : 1 ≤ shellHeight z := by
  unfold shellHeight
  omega

lemma shellHeight_ge_scale_of_pow_le {z k : ℕ} (hk : 1 ≤ k)
    (hpow : 2 ^ k ≤ z) : k ≤ shellHeight z := by
  have hz : 2 ≤ z := (by
    have htwo : 2 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      simpa using this
    exact htwo.trans hpow)
  have hp : 2 ^ k ≤ 2 ^ shellHeight z := hpow.trans (le_pow_shellHeight hz)
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hp

lemma shellHeight_le_scale_of_lt_pow {z k : ℕ} (hz : 2 ≤ z)
    (hpow : z < 2 ^ k) : shellHeight z ≤ k := by
  have hlower : 2 ^ (shellHeight z - 1) < z := by
    have hz1 : z - 1 ≠ 0 := by omega
    have h := Nat.pow_log_le_self 2 hz1
    simpa [shellHeight] using (show 2 ^ Nat.log 2 (z - 1) < z by omega)
  have hp : 2 ^ (shellHeight z - 1) < 2 ^ k := hlower.trans hpow
  have he : shellHeight z - 1 < k :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hp
  have hJ := one_le_shellHeight (z := z)
  omega

lemma nat_rpow_neg_quarter_antitone {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b : ℝ) ^ (-(1 : ℝ) / 4) ≤ (a : ℝ) ^ (-(1 : ℝ) / 4) := by
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast (show 0 < a by omega))
    (by exact_mod_cast hab) (by norm_num)

lemma nat_rpow_neg_half_le_one {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 := by
  have h := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast ha : (1 : ℝ) ≤ a)
    (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  simpa using h

lemma nat_rpow_neg_three_quarters_le_neg_quarter {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ^ (-(3 : ℝ) / 4) ≤ (a : ℝ) ^ (-(1 : ℝ) / 4) := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast ha) (by norm_num)

theorem lastCutoffShell_long_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hk : 1 ≤ k) (hlong : 2 ^ k ≤ z) :
    (∑ t ∈ dyadicTShell z (shellHeight z - 1),
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      2 * sharpWeightedThreeRegimeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hz : 2 ≤ z := by
    have htwo : 2 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      simpa using this
    exact htwo.trans hlong
  let J := shellHeight z
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  have hkJ : k ≤ J := by
    dsimp [J]
    exact shellHeight_ge_scale_of_pow_le hk hlong
  have hlast := dyadicTShell_last_le_weightedTSum (k := k) hq hzEq hz
  have hHR := sharpWeightedTSum_two_pow_long_le hq.ne' hk hkJ
  have hpow : (((2 ^ J : ℕ) : ℝ)) ≤ 2 * (z : ℝ) := by
    exact_mod_cast (pow_shellHeight_lt_two_mul hz).le
  have hJhalf := nat_rpow_neg_half_le_one (one_le_shellHeight (z := z))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact sharpHybridCorrectionWeight_nonneg k q
  have hnonneg : 0 ≤ sharpWeightedThreeRegimeConstant * W *
      (Real.log 2) ^ (-(3 : ℝ) / 4) *
      (k : ℝ) ^ (-(1 : ℝ) / 4) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg hW)
        (Real.rpow_nonneg log_two_pos.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  calc
    _ ≤ weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ J) := by
      simpa [J] using hlast
    _ ≤ sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) *
        (J : ℝ) ^ (-(1 : ℝ) / 2) := hHR
    _ ≤ sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
      let R : ℝ := sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4)
      have hR : 0 ≤ R := by
        dsimp [R]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg
                (Nat.cast_nonneg (2 ^ J))) hW)
              (Real.rpow_nonneg log_two_pos.le _))
          (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      calc
        _ = R * (J : ℝ) ^ (-(1 : ℝ) / 2) := by rfl
        _ ≤ R * 1 := mul_le_mul_of_nonneg_left hJhalf hR
        _ = _ := by simp [R]
    _ ≤ 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
      let R : ℝ := sharpWeightedThreeRegimeConstant * W *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4)
      have hR : 0 ≤ R := by
        dsimp [R]
        exact hnonneg
      calc
        _ = (((2 ^ J : ℕ) : ℝ)) * R := by ring
        _ ≤ (2 * (z : ℝ)) * R := mul_le_mul_of_nonneg_right hpow hR
        _ = _ := by simp [R]; ring
    _ = _ := by simp [W]

theorem lastCutoffShell_middle_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hk : 1 ≤ k) (hmiddle : z < 2 ^ k) :
    (∑ t ∈ dyadicTShell z (shellHeight z - 1),
      omegaWeight k t *
        FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t)) ≤
      2 * sharpWeightedThreeRegimeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        ((Real.log 2) ^ (-(1 : ℝ)) +
          (Real.log 2) ^ (-(3 : ℝ) / 4)) *
        (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) := by
  let J := shellHeight z
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  have hJ : 1 ≤ J := one_le_shellHeight
  have hJk : J ≤ k := by
    dsimp [J]
    exact shellHeight_le_scale_of_lt_pow hz hmiddle
  have hlast := dyadicTShell_last_le_weightedTSum (k := k) hq hzEq hz
  have hpow : (((2 ^ J : ℕ) : ℝ)) ≤ 2 * (z : ℝ) := by
    exact_mod_cast (pow_shellHeight_lt_two_mul hz).le
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  calc
    _ ≤ weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ J) := by
      simpa [J] using hlast
    _ ≤ 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
        ((Real.log 2) ^ (-(1 : ℝ)) +
          (Real.log 2) ^ (-(3 : ℝ) / 4)) *
        (J : ℝ) ^ (-(1 : ℝ) / 4) := by
      rcases hJk.eq_or_lt with hEq | hLt
      · subst k
        have hHR := sharpWeightedTSum_two_pow_long_le hq.ne' hJ le_rfl
        have h34 := nat_rpow_neg_three_quarters_le_neg_quarter hJ
        have hfac : 0 ≤ sharpWeightedThreeRegimeConstant * W :=
          mul_nonneg sharpWeightedThreeRegimeConstant_nonneg hW
        calc
          weightedTSum sharpShiftedReciprocalWeightAF q J 2 (2 ^ J) ≤
            sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(3 : ℝ) / 4) *
              (J : ℝ) ^ (-(1 : ℝ) / 4) *
              (J : ℝ) ^ (-(1 : ℝ) / 2) := hHR
          _ = sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(3 : ℝ) / 4) *
              (J : ℝ) ^ (-(3 : ℝ) / 4) := by
                have hJJ : (J : ℝ) ^ (-(1 : ℝ) / 4) *
                    (J : ℝ) ^ (-(1 : ℝ) / 2) =
                    (J : ℝ) ^ (-(3 : ℝ) / 4) := by
                  rw [← Real.rpow_add (by positivity : (0 : ℝ) < J)]
                  congr 1
                  ring
                calc
                  _ = (sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
                      (Real.log 2) ^ (-(3 : ℝ) / 4)) *
                        ((J : ℝ) ^ (-(1 : ℝ) / 4) *
                          (J : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
                  _ = (sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
                      (Real.log 2) ^ (-(3 : ℝ) / 4)) *
                        (J : ℝ) ^ (-(3 : ℝ) / 4) := by rw [hJJ]
                  _ = _ := by ring
          _ ≤ sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(3 : ℝ) / 4) *
              (J : ℝ) ^ (-(1 : ℝ) / 4) := by
                have hcoef : 0 ≤ sharpWeightedThreeRegimeConstant *
                    (((2 ^ J : ℕ) : ℝ)) * W *
                    (Real.log 2) ^ (-(3 : ℝ) / 4) := by
                  exact mul_nonneg
                    (mul_nonneg
                      (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg
                        (Nat.cast_nonneg (2 ^ J))) hW)
                    (Real.rpow_nonneg log_two_pos.le _)
                exact mul_le_mul_of_nonneg_left h34 hcoef
          _ ≤ 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
              (Real.log 2) ^ (-(3 : ℝ) / 4) *
              (J : ℝ) ^ (-(1 : ℝ) / 4) := by
                let R : ℝ := sharpWeightedThreeRegimeConstant * W *
                  (Real.log 2) ^ (-(3 : ℝ) / 4) *
                  (J : ℝ) ^ (-(1 : ℝ) / 4)
                have hR : 0 ≤ R := by
                  dsimp [R]
                  exact mul_nonneg
                    (mul_nonneg
                      (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg hW)
                      (Real.rpow_nonneg log_two_pos.le _))
                    (Real.rpow_nonneg (Nat.cast_nonneg J) _)
                calc
                  _ = (((2 ^ J : ℕ) : ℝ)) * R := by ring
                  _ ≤ (2 * (z : ℝ)) * R :=
                    mul_le_mul_of_nonneg_right hpow hR
                  _ = _ := by simp [R]; ring
          _ ≤ _ := by
            have hlogNonneg : 0 ≤ (Real.log 2) ^ (-(1 : ℝ)) := by positivity
            let R : ℝ := 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
              (J : ℝ) ^ (-(1 : ℝ) / 4)
            have hR : 0 ≤ R := by
              dsimp [R]
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg
                    (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
                    (Nat.cast_nonneg z)) hW)
                (Real.rpow_nonneg (Nat.cast_nonneg J) _)
            have hadd : (Real.log 2) ^ (-(3 : ℝ) / 4) ≤
                (Real.log 2) ^ (-(1 : ℝ)) +
                  (Real.log 2) ^ (-(3 : ℝ) / 4) :=
              le_add_of_nonneg_left hlogNonneg
            calc
              _ = R * (Real.log 2) ^ (-(3 : ℝ) / 4) := by ring
              _ ≤ R * ((Real.log 2) ^ (-(1 : ℝ)) +
                  (Real.log 2) ^ (-(3 : ℝ) / 4)) :=
                mul_le_mul_of_nonneg_left hadd hR
              _ = _ := by ring
      · have hHR := sharpWeightedTSum_two_pow_middle_le hq.ne' hJ hLt
        have h34 := nat_rpow_neg_three_quarters_le_neg_quarter hJ
        calc
          weightedTSum sharpShiftedReciprocalWeightAF q k 2 (2 ^ J) ≤
            sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(1 : ℝ)) *
              (J : ℝ) ^ (-(3 : ℝ) / 4) := hHR
          _ ≤ sharpWeightedThreeRegimeConstant * (((2 ^ J : ℕ) : ℝ)) * W *
              (Real.log 2) ^ (-(1 : ℝ)) *
              (J : ℝ) ^ (-(1 : ℝ) / 4) := by
                have hcoef : 0 ≤ sharpWeightedThreeRegimeConstant *
                    (((2 ^ J : ℕ) : ℝ)) * W *
                    (Real.log 2) ^ (-(1 : ℝ)) := by
                  exact mul_nonneg
                    (mul_nonneg
                      (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg
                        (Nat.cast_nonneg (2 ^ J))) hW)
                    (Real.rpow_nonneg log_two_pos.le _)
                exact mul_le_mul_of_nonneg_left h34 hcoef
          _ ≤ 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
              (Real.log 2) ^ (-(1 : ℝ)) *
              (J : ℝ) ^ (-(1 : ℝ) / 4) := by
                let R : ℝ := sharpWeightedThreeRegimeConstant * W *
                  (Real.log 2) ^ (-(1 : ℝ)) *
                  (J : ℝ) ^ (-(1 : ℝ) / 4)
                have hR : 0 ≤ R := by
                  dsimp [R]
                  exact mul_nonneg
                    (mul_nonneg
                      (mul_nonneg sharpWeightedThreeRegimeConstant_nonneg hW)
                      (Real.rpow_nonneg log_two_pos.le _))
                    (Real.rpow_nonneg (Nat.cast_nonneg J) _)
                calc
                  _ = (((2 ^ J : ℕ) : ℝ)) * R := by ring
                  _ ≤ (2 * (z : ℝ)) * R :=
                    mul_le_mul_of_nonneg_right hpow hR
                  _ = _ := by simp [R]; ring
          _ ≤ _ := by
            have hlogNonneg : 0 ≤ (Real.log 2) ^ (-(3 : ℝ) / 4) := by positivity
            let R : ℝ := 2 * sharpWeightedThreeRegimeConstant * (z : ℝ) * W *
              (J : ℝ) ^ (-(1 : ℝ) / 4)
            have hR : 0 ≤ R := by
              dsimp [R]
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg
                    (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
                    (Nat.cast_nonneg z)) hW)
                (Real.rpow_nonneg (Nat.cast_nonneg J) _)
            have hadd : (Real.log 2) ^ (-(1 : ℝ)) ≤
                (Real.log 2) ^ (-(1 : ℝ)) +
                  (Real.log 2) ^ (-(3 : ℝ) / 4) :=
              le_add_of_nonneg_right hlogNonneg
            calc
              _ = R * (Real.log 2) ^ (-(1 : ℝ)) := by ring
              _ ≤ R * ((Real.log 2) ^ (-(1 : ℝ)) +
                  (Real.log 2) ^ (-(3 : ℝ) / 4)) :=
                mul_le_mul_of_nonneg_left hadd hR
              _ = _ := by ring
    _ = _ := by simp [J, W]

lemma cutoffFirstShiftedSum_eq_interior_add_last
    {x q k z : ℕ} (hzEq : z = x ⌈/⌉ q) :
    cutoffFirstShiftedSum x q k =
      interiorCutoffShellSum x q k +
        ∑ t ∈ dyadicTShell z (shellHeight z - 1),
          omegaWeight k t *
            FirstShiftedSmall448.weightedFirstShiftedBoundAll x (q * t) := by
  subst z
  rw [cutoffFirstShiftedSum_eq_shells]
  rw [sum_range_pred_add_last (one_le_shellHeight (z := x ⌈/⌉ q))]
  rfl

lemma interiorCutoffShellSum_nonneg (x q k : ℕ) :
    0 ≤ interiorCutoffShellSum x q k := by
  unfold interiorCutoffShellSum
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (omegaWeight_nonneg k t)
    (weightedFirstShiftedBoundAll_nonneg x (q * t))

lemma interiorAnalyticBound_nonneg (z k q : ℕ) :
    0 ≤
      48 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(3 : ℝ) / 2) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        32 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(5 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hW := sharpHybridCorrectionWeight_nonneg k q
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
              sharpWeightedThreeRegimeConstant_nonneg)
            (Nat.cast_nonneg z)) hW)
        (Real.rpow_nonneg log_two_pos.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg (shellHeight z)) _)
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
              sharpWeightedThreeRegimeConstant_nonneg)
            (Nat.cast_nonneg z)) hW)
        (Real.rpow_nonneg log_two_pos.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)

theorem cutoffFirstShiftedSum_long_raw_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hk : 1 ≤ k) (hlong : 2 ^ k ≤ z) :
    cutoffFirstShiftedSum x q k ≤
      (48 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(3 : ℝ) / 2) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        32 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(5 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4)) +
      2 * sharpWeightedThreeRegimeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (Real.log 2) ^ (-(3 : ℝ) / 4) *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hz : 2 ≤ z := by
    have htwo : 2 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      simpa using this
    exact htwo.trans hlong
  rw [cutoffFirstShiftedSum_eq_interior_add_last hzEq]
  apply add_le_add
  · by_cases hJ : 2 ≤ shellHeight z
    · exact interiorCutoffShellSum_le hq hzEq hz hk hJ
    · have he : shellHeight z = 1 := by
        have := one_le_shellHeight (z := z)
        omega
      have hzero : interiorCutoffShellSum x q k = 0 := by
        have he' : shellHeight (x ⌈/⌉ q) = 1 := by simpa [← hzEq]
        simp [interiorCutoffShellSum, he']
      rw [hzero]
      exact interiorAnalyticBound_nonneg z k q
  · exact lastCutoffShell_long_le hq hzEq hk hlong

theorem cutoffFirstShiftedSum_middle_raw_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hk : 1 ≤ k) (hmiddle : z < 2 ^ k) :
    cutoffFirstShiftedSum x q k ≤
      (48 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(3 : ℝ) / 2) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        32 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
          (z : ℝ) *
          hybridCorrectionWeight sharpShiftedReciprocalWeightAF
            (omegaWeightAF k) q *
          (Real.log 2) ^ (-(5 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 4)) +
      2 * sharpWeightedThreeRegimeConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        ((Real.log 2) ^ (-(1 : ℝ)) +
          (Real.log 2) ^ (-(3 : ℝ) / 4)) *
        (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) := by
  rw [cutoffFirstShiftedSum_eq_interior_add_last hzEq]
  apply add_le_add
  · by_cases hJ : 2 ≤ shellHeight z
    · exact interiorCutoffShellSum_le hq hzEq hz hk hJ
    · have he : shellHeight z = 1 := by
        have := one_le_shellHeight (z := z)
        omega
      have hzero : interiorCutoffShellSum x q k = 0 := by
        have he' : shellHeight (x ⌈/⌉ q) = 1 := by simpa [← hzEq]
        simp [interiorCutoffShellSum, he']
      rw [hzero]
      exact interiorAnalyticBound_nonneg z k q
  · exact lastCutoffShell_middle_le hq hzEq hz hk hmiddle

/-- Uniform constant for both nonempty residual regimes. -/
noncomputable def cutoffShellConstant : ℝ :=
  1 +
    48 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
      (Real.log 2) ^ (-(3 : ℝ) / 2) +
    32 * firstShiftedEnvelopeConstant * sharpWeightedThreeRegimeConstant *
      (Real.log 2) ^ (-(5 : ℝ) / 4) +
    2 * sharpWeightedThreeRegimeConstant *
      ((Real.log 2) ^ (-(1 : ℝ)) +
        (Real.log 2) ^ (-(3 : ℝ) / 4))

lemma cutoffShellConstant_nonneg : 0 ≤ cutoffShellConstant := by
  unfold cutoffShellConstant
  have hc₁ : 0 ≤ 48 * firstShiftedEnvelopeConstant *
      sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(3 : ℝ) / 2) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₂ : 0 ≤ 32 * firstShiftedEnvelopeConstant *
      sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(5 : ℝ) / 4) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₃ : 0 ≤ 2 * sharpWeightedThreeRegimeConstant *
      ((Real.log 2) ^ (-(1 : ℝ)) +
        (Real.log 2) ^ (-(3 : ℝ) / 4)) :=
    mul_nonneg (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
      (add_nonneg (Real.rpow_nonneg log_two_pos.le _)
        (Real.rpow_nonneg log_two_pos.le _))
  linarith

/-- Aggregate long-regime cutoff convolution in the form consumed by the
close-pair mean. -/
theorem cutoffFirstShiftedSum_long_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hk : 1 ≤ k) (hlong : 2 ^ k ≤ z) :
    cutoffFirstShiftedSum x q k ≤
      cutoffShellConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  let c₁ := 48 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(3 : ℝ) / 2)
  let c₂ := 32 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(5 : ℝ) / 4)
  let c₃ := 2 * sharpWeightedThreeRegimeConstant *
    (Real.log 2) ^ (-(3 : ℝ) / 4)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  have hc₁ : 0 ≤ c₁ := by
    dsimp only [c₁]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₂ : 0 ≤ c₂ := by
    dsimp only [c₂]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₃ : 0 ≤ c₃ := by
    dsimp only [c₃]
    exact mul_nonneg (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hbase : 0 ≤ (z : ℝ) * W := mul_nonneg (Nat.cast_nonneg z) hW
  have hkpow : 0 ≤ (k : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
  have hkJ := shellHeight_ge_scale_of_pow_le hk hlong
  have hJpow := nat_rpow_neg_quarter_antitone hk hkJ
  have hraw := cutoffFirstShiftedSum_long_raw_le hq hzEq hk hlong
  have hc : c₁ + c₂ + c₃ ≤ cutoffShellConstant := by
    dsimp [c₁, c₂, c₃, cutoffShellConstant]
    have hextra : 0 ≤ 1 + 2 * sharpWeightedThreeRegimeConstant *
        (Real.log 2) ^ (-(1 : ℝ)) := by
      exact add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
          (Real.rpow_nonneg log_two_pos.le _))
    linarith
  calc
    cutoffFirstShiftedSum x q k ≤
      (c₁ * ((z : ℝ) * W) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        c₂ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4)) +
      c₃ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4) := by
        convert hraw using 1 <;> dsimp [c₁, c₂, c₃, W] <;> ring
    _ ≤ (c₁ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4) +
        c₂ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4)) +
      c₃ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4) := by
        gcongr
    _ = (c₁ + c₂ + c₃) *
        ((z : ℝ) * W * (k : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
    _ ≤ cutoffShellConstant *
        ((z : ℝ) * W * (k : ℝ) ^ (-(1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hbase hkpow)
    _ = _ := by simp [W]; ring

/-- Aggregate middle-regime cutoff convolution.  Its remaining scale is the
quarter power of the number of residual dyadic shells. -/
theorem cutoffFirstShiftedSum_middle_le
    {x q k z : ℕ} (hq : 0 < q) (hzEq : z = x ⌈/⌉ q)
    (hz : 2 ≤ z) (hk : 1 ≤ k) (hmiddle : z < 2 ^ k) :
    cutoffFirstShiftedSum x q k ≤
      cutoffShellConstant * (z : ℝ) *
        hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k) q *
        (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) := by
  let W := hybridCorrectionWeight sharpShiftedReciprocalWeightAF
    (omegaWeightAF k) q
  let c₁ := 48 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(3 : ℝ) / 2)
  let c₂ := 32 * firstShiftedEnvelopeConstant *
    sharpWeightedThreeRegimeConstant * (Real.log 2) ^ (-(5 : ℝ) / 4)
  let c₃ := 2 * sharpWeightedThreeRegimeConstant *
    ((Real.log 2) ^ (-(1 : ℝ)) +
      (Real.log 2) ^ (-(3 : ℝ) / 4))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact hybridCorrectionWeight_nonneg sharpShiftedReciprocalWeightAF
      (omegaWeightAF k) sharpShiftedReciprocalWeightAF_one
      (omegaWeightAF_one k) sharpShiftedReciprocalWeightAF_nonneg
      (omegaWeightAF_nonneg k) sharpShiftedReciprocalWeightAF_logType
      (fun {p} hp n ↦ omegaWeightAF_le_one k (p ^ n)) q
  have hc₁ : 0 ≤ c₁ := by
    dsimp only [c₁]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₂ : 0 ≤ c₂ := by
    dsimp only [c₂]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) firstShiftedEnvelopeConstant_nonneg)
        sharpWeightedThreeRegimeConstant_nonneg)
      (Real.rpow_nonneg log_two_pos.le _)
  have hc₃ : 0 ≤ c₃ := by
    dsimp only [c₃]
    exact mul_nonneg (mul_nonneg (by norm_num) sharpWeightedThreeRegimeConstant_nonneg)
      (add_nonneg (Real.rpow_nonneg log_two_pos.le _)
        (Real.rpow_nonneg log_two_pos.le _))
  have hbase : 0 ≤ (z : ℝ) * W := mul_nonneg (Nat.cast_nonneg z) hW
  have hJpow : 0 ≤ (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hJk := shellHeight_le_scale_of_lt_pow hz hmiddle
  have hkToJ := nat_rpow_neg_quarter_antitone
    (one_le_shellHeight (z := z)) hJk
  have hraw := cutoffFirstShiftedSum_middle_raw_le hq hzEq hz hk hmiddle
  have hc : c₁ + c₂ + c₃ ≤ cutoffShellConstant := by
    dsimp [c₁, c₂, c₃, cutoffShellConstant]
    linarith
  calc
    cutoffFirstShiftedSum x q k ≤
      (c₁ * ((z : ℝ) * W) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        c₂ * ((z : ℝ) * W) * (k : ℝ) ^ (-(1 : ℝ) / 4)) +
      c₃ * ((z : ℝ) * W) *
        (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) := by
        convert hraw using 1 <;> dsimp [c₁, c₂, c₃, W] <;> ring
    _ ≤ (c₁ * ((z : ℝ) * W) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) +
        c₂ * ((z : ℝ) * W) *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4)) +
      c₃ * ((z : ℝ) * W) *
        (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4) := by
          gcongr
    _ = (c₁ + c₂ + c₃) *
        ((z : ℝ) * W *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
    _ ≤ cutoffShellConstant *
        ((z : ℝ) * W *
          (shellHeight z : ℝ) ^ (-(1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hbase hJpow)
    _ = _ := by simp [W]; ring

end Prop3CutoffShell448

#print axioms Prop3CutoffShell448.weightedFirstShiftedBoundAll_le_envelope
#print axioms Prop3CutoffShell448.interiorCutoffShellSum_le
#print axioms Prop3CutoffShell448.cutoffFirstShiftedSum_long_le
#print axioms Prop3CutoffShell448.cutoffFirstShiftedSum_middle_le
