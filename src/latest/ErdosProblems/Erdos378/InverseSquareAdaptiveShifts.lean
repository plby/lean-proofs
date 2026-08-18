/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareCorrelation
import ErdosProblems.Erdos378.AdaptiveShifts

/-!
# Capped adaptive shifts for inverse-square phases

For `e(-Q/t²)` the terminal derivative has one extra inverse power of the
ambient scale.  We therefore maximize the derivative cutoff under the
natural `M^35` constraint and separately cap it by `M / C`.  When the cap is
inactive, maximality controls the terminal term; when it is active, a lower
bound on `Q / M²` controls it directly.
-/

open scoped BigOperators

namespace Erdos378
namespace InverseSquareAdaptiveShifts

open HigherDerivative
open InverseSquareHigherDerivative
open InverseSquareCorrelation
open AdaptiveShifts

noncomputable section

def inverseSquareShiftPredicate (Q : ℝ) (M q : ℕ) : Prop :=
  2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 *
      logarithmicSafety M ^ 32 ≤ (M : ℝ) ^ 35

noncomputable def inverseSquareShift (Q : ℝ) (M : ℕ) : ℕ :=
  @Nat.findGreatest (inverseSquareShiftPredicate Q M)
    (Classical.decPred (inverseSquareShiftPredicate Q M)) M

def cappedInverseSquareShift (Q : ℝ) (M C : ℕ) : ℕ :=
  min (inverseSquareShift Q M) (M / C)

lemma inverseSquareShift_le (Q : ℝ) (M : ℕ) :
    inverseSquareShift Q M ≤ M := by
  classical
  unfold inverseSquareShift
  exact Nat.findGreatest_le M

lemma inverseSquareShift_spec {Q : ℝ} (hQ : 0 ≤ Q) (M : ℕ) :
    inverseSquareShiftPredicate Q M (inverseSquareShift Q M) := by
  classical
  unfold inverseSquareShift
  apply Nat.findGreatest_spec (m := 0) (n := M) (by omega)
  unfold inverseSquareShiftPredicate
  norm_num

lemma inverseSquareShiftPredicate_mono {Q : ℝ} (hQ : 0 ≤ Q) {M q r : ℕ}
    (hqr : q ≤ r) (hr : inverseSquareShiftPredicate Q M r) :
    inverseSquareShiftPredicate Q M q := by
  unfold inverseSquareShiftPredicate at hr ⊢
  have hpow : (q : ℝ) ^ 32 ≤ (r : ℝ) ^ 32 := by gcongr
  calc
    2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 ≤
      2 * Q * ((34).factorial : ℝ) * (r : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 := by gcongr
    _ ≤ (M : ℝ) ^ 35 := hr

lemma cappedInverseSquareShift_le_shift (Q : ℝ) (M C : ℕ) :
    cappedInverseSquareShift Q M C ≤ inverseSquareShift Q M :=
  Nat.min_le_left _ _

lemma cappedInverseSquareShift_le_div (Q : ℝ) (M C : ℕ) :
    cappedInverseSquareShift Q M C ≤ M / C :=
  Nat.min_le_right _ _

lemma cappedInverseSquareShift_spec {Q : ℝ} (hQ : 0 ≤ Q) (M C : ℕ) :
    inverseSquareShiftPredicate Q M (cappedInverseSquareShift Q M C) := by
  exact inverseSquareShiftPredicate_mono hQ
    (cappedInverseSquareShift_le_shift Q M C)
    (inverseSquareShift_spec hQ M)

def inverseSquareFrequencyConstant : ℝ := 4 * 8 ^ 16

lemma inverseSquareFrequencyConstant_pos : 0 < inverseSquareFrequencyConstant := by
  unfold inverseSquareFrequencyConstant
  positivity

def inverseSquareCorrelationSizeCondition (M : ℕ) : Prop :=
  2 * inverseSquareFrequencyConstant *
      ((34).factorial : ℝ) * logarithmicSafety M ^ 32 ≤ (M : ℝ) ^ 2

lemma baseShift_inverseSquarePredicate_of_frequency_upper
    {Q : ℝ} (hQ : 0 ≤ Q) {M : ℕ} (hM : 1 ≤ M)
    (hQupper : Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31)
    (hsize : inverseSquareCorrelationSizeCondition M) :
    inverseSquareShiftPredicate Q M (baseShift M) := by
  have hbaseNat := baseShift_pow_thirtytwo_le_sq (Nat.zero_lt_of_lt hM)
  have hbase : (baseShift M : ℝ) ^ 32 ≤ (M : ℝ) ^ 2 := by
    exact_mod_cast hbaseNat
  have hC : 0 ≤ inverseSquareFrequencyConstant :=
    inverseSquareFrequencyConstant_pos.le
  have hsize' : 2 * inverseSquareFrequencyConstant *
      ((34).factorial : ℝ) * logarithmicSafety M ^ 32 ≤ (M : ℝ) ^ 2 := by
    simpa only [inverseSquareCorrelationSizeCondition] using hsize
  unfold inverseSquareShiftPredicate
  calc
    2 * Q * ((34).factorial : ℝ) * (baseShift M : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 ≤
      2 * (inverseSquareFrequencyConstant * (M : ℝ) ^ 31) *
        ((34).factorial : ℝ) * (M : ℝ) ^ 2 *
          logarithmicSafety M ^ 32 := by gcongr
    _ = (2 * inverseSquareFrequencyConstant *
          ((34).factorial : ℝ) * logarithmicSafety M ^ 32) *
            (M : ℝ) ^ 33 := by ring
    _ ≤ (M : ℝ) ^ 2 * (M : ℝ) ^ 33 := by gcongr
    _ = (M : ℝ) ^ 35 := by ring

lemma baseShift_le_inverseSquareShift {Q : ℝ} {M : ℕ}
    (hbase : inverseSquareShiftPredicate Q M (baseShift M)) :
    baseShift M ≤ inverseSquareShift Q M := by
  classical
  unfold inverseSquareShift
  exact Nat.le_findGreatest (baseShift_le M) hbase

lemma baseShift_le_cappedInverseSquareShift {Q : ℝ} {M C : ℕ}
    (hbase : inverseSquareShiftPredicate Q M (baseShift M))
    (hcap : baseShift M ≤ M / C) :
    baseShift M ≤ cappedInverseSquareShift Q M C := by
  unfold cappedInverseSquareShift
  exact le_min (baseShift_le_inverseSquareShift hbase) hcap

lemma inverseSquareShift_derivative_small
    {Q : ℝ} (hQ : 0 < Q) {M q : ℕ} (hM : 1 ≤ M)
    (hq : inverseSquareShiftPredicate Q M q) :
    Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 /
        (M : ℝ) ^ 35 ≤ 1 / 2 := by
  have hSone : (1 : ℝ) ≤ logarithmicSafety M ^ 32 := by
    exact one_le_pow₀ (one_lt_logarithmicSafety hM).le
  have hcore : 2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 ≤
      (M : ℝ) ^ 35 := by
    calc
      2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 =
          (2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32) * 1 := by ring
      _ ≤ (2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32) *
          logarithmicSafety M ^ 32 := by gcongr
      _ ≤ (M : ℝ) ^ 35 := by
        simpa only [inverseSquareShiftPredicate] using hq
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  rw [div_le_iff₀ (pow_pos hMpos 35)]
  calc
    Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 =
        (2 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32) / 2 := by ring
    _ ≤ (M : ℝ) ^ 35 / 2 := by gcongr
    _ = 1 / 2 * (M : ℝ) ^ 35 := by ring

lemma inverseSquareShift_succ_not_predicate
    {Q : ℝ} {M q : ℕ} (hqeq : q = inverseSquareShift Q M)
    (hqM : q < M) :
    ¬ inverseSquareShiftPredicate Q M (q + 1) := by
  classical
  intro hpred
  have hsuccM : q + 1 ≤ M := by omega
  have hle : q + 1 ≤
      @Nat.findGreatest (inverseSquareShiftPredicate Q M)
        (Classical.decPred (inverseSquareShiftPredicate Q M)) M :=
    Nat.le_findGreatest hsuccM hpred
  change q + 1 ≤ inverseSquareShift Q M at hle
  rw [← hqeq] at hle
  omega

lemma inverseSquareShift_reverse_product
    {Q : ℝ} (hQ : 0 ≤ Q) {M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q)
    (hqeq : q = inverseSquareShift Q M) (hqM : q < M) :
    (M : ℝ) ^ 35 <
      2 ^ 33 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 := by
  have hfail := inverseSquareShift_succ_not_predicate hqeq hqM
  have hraw : (M : ℝ) ^ 35 <
      2 * Q * ((34).factorial : ℝ) * ((q + 1 : ℕ) : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 := lt_of_not_ge hfail
  have hsucc : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    push_cast
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have hpow : ((q + 1 : ℕ) : ℝ) ^ 32 ≤ (2 * (q : ℝ)) ^ 32 := by
    gcongr
  have hout := hraw.trans_le <| mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have heq :
      2 * Q * ((34).factorial : ℝ) * (2 * (q : ℝ)) ^ 32 *
          logarithmicSafety M ^ 32 =
        2 ^ 33 * Q * ((34).factorial : ℝ) * (q : ℝ) ^ 32 *
          logarithmicSafety M ^ 32 := by ring
  exact hout.trans_eq heq

lemma reciprocalShiftFactor_capped_le
    {Q : ℝ} {M C : ℕ} (hM : 1 ≤ M)
    (hq : 1 ≤ cappedInverseSquareShift Q M C) :
    reciprocalShiftFactor
        (derivativeCutoffs (cappedInverseSquareShift Q M C)) ≤
      logarithmicSafety M ^ 32 /
        (cappedInverseSquareShift Q M C : ℝ) ^ 32 := by
  let q := cappedInverseSquareShift Q M C
  let H : ℝ := ∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))
  have hqM : q ≤ M :=
    (cappedInverseSquareShift_le_shift Q M C).trans
      (inverseSquareShift_le Q M)
  have hH : H ≤ logarithmicSafety M :=
    harmonic_cutoff_le_logarithmicSafety hq hqM hM
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  rw [reciprocalShiftFactor_derivativeCutoffs]
  change ((1 / (q : ℝ)) * H) ^ 32 ≤ _
  calc
    ((1 / (q : ℝ)) * H) ^ 32 ≤
        ((1 / (q : ℝ)) * logarithmicSafety M) ^ 32 := by gcongr
    _ = logarithmicSafety M ^ 32 / (q : ℝ) ^ 32 := by
      field_simp [ne_of_gt hqreal]

def inverseSquareTerminalConstant : ℝ := 3 * 2 ^ 64

lemma inverseSquareTerminalConstant_pos : 0 < inverseSquareTerminalConstant := by
  unfold inverseSquareTerminalConstant
  positivity

/-- Terminal bound when the adaptive maximum occurs before the external
cap. -/
lemma inactive_cap_terminal_le
    {Q : ℝ} (hQ : 0 < Q) {M C A N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N)
    (hq : 1 ≤ cappedInverseSquareShift Q M C)
    (hinactive : cappedInverseSquareShift Q M C = inverseSquareShift Q M)
    (hcaplt : cappedInverseSquareShift Q M C < M)
    (hAN : A + N ≤ 2 * M) :
    (3 * ((A + N : ℕ) : ℝ) ^ 35 /
        (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
        reciprocalShiftFactor
          (derivativeCutoffs (cappedInverseSquareShift Q M C)) ≤
      inverseSquareTerminalConstant * logarithmicSafety M ^ 64 / (N : ℝ) := by
  let q := cappedInverseSquareShift Q M C
  let S := logarithmicSafety M
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hSpos : 0 < S := by dsimp only [S]; exact logarithmicSafety_pos hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactor := reciprocalShiftFactor_capped_le (Q := Q) (C := C) hM hq
  have hreverse := inverseSquareShift_reverse_product hQ.le hM hq
    hinactive hcaplt
  have hfrac : S ^ 32 / (q : ℝ) ^ 32 <
      2 ^ 33 * Q * ((34).factorial : ℝ) * S ^ 64 /
        (M : ℝ) ^ 35 := by
    rw [div_lt_div_iff₀ (pow_pos hqpos 32) (pow_pos hMpos 35)]
    have hout : S ^ 32 * (M : ℝ) ^ 35 <
        S ^ 32 * (2 ^ 33 * Q * ((34).factorial : ℝ) *
          (q : ℝ) ^ 32 * S ^ 32) :=
      mul_lt_mul_of_pos_left hreverse (pow_pos hSpos 32)
    exact hout.trans_eq (by ring)
  have hfactorStrict : reciprocalShiftFactor (derivativeCutoffs q) <
      2 ^ 33 * Q * ((34).factorial : ℝ) * S ^ 64 /
        (M : ℝ) ^ 35 := hfactor.trans_lt hfrac
  have hANR : (((A + N : ℕ) : ℝ)) ≤ 2 * (M : ℝ) := by exact_mod_cast hAN
  have hANpow : (((A + N : ℕ) : ℝ)) ^ 35 ≤ (2 * (M : ℝ)) ^ 35 := by
    gcongr
  apply le_of_lt
  calc
    (3 * ((A + N : ℕ) : ℝ) ^ 35 /
        (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
          reciprocalShiftFactor (derivativeCutoffs q) ≤
      (3 * (2 * (M : ℝ)) ^ 35 /
        (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
          reciprocalShiftFactor (derivativeCutoffs q) := by
        apply mul_le_mul_of_nonneg_right _ (reciprocalShiftFactor_nonneg _)
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
    _ < (3 * (2 * (M : ℝ)) ^ 35 /
        (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
      (2 ^ 33 * Q * ((34).factorial : ℝ) * S ^ 64 /
        (M : ℝ) ^ 35) := by
      exact mul_lt_mul_of_pos_left hfactorStrict (by positivity)
    _ = inverseSquareTerminalConstant * S ^ 64 / (N : ℝ) := by
      unfold inverseSquareTerminalConstant
      field_simp [ne_of_gt hMpos, ne_of_gt hNpos, ne_of_gt hQ]
      ring
    _ = _ := by rfl

/-- A terminal majorant which uses maximality before the cap and the direct
derivative estimate when the cap is active. -/
def cappedTerminalMajorant (Q : ℝ) (M C : ℕ) : ℝ :=
  let q := cappedInverseSquareShift Q M C
  if inverseSquareShift Q M ≤ M / C then
    inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
      (32 * (q : ℝ))
  else
    (3 * (2 * (M : ℝ)) ^ 35 /
      (16 * (32 * (q : ℝ)) * Q * ((34).factorial : ℝ))) *
        (logarithmicSafety M ^ 32 / (q : ℝ) ^ 32)

def cappedInverseSquareMomentEnvelope (Q : ℝ) (M C : ℕ) : ℝ :=
  let q := cappedInverseSquareShift Q M C
  vdcMomentConstant 32 *
    (32 / (q : ℝ) + 1 / (256 * (q : ℝ)) +
      cappedTerminalMajorant Q M C)

def cappedInverseSquareCorrelationEnvelope (Q : ℝ) (M C : ℕ) : ℝ :=
  34 * ((M / C : ℕ) : ℝ) + 34 +
    8 * (M : ℝ) *
      (cappedInverseSquareMomentEnvelope Q M C) ^
        ((2 ^ 32 : ℕ) : ℝ)⁻¹

lemma cappedTerminalMajorant_nonneg
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ} :
    0 ≤ cappedTerminalMajorant Q M C := by
  have hS : 0 ≤ logarithmicSafety M := by
    unfold logarithmicSafety
    exact Even.pow_nonneg (by norm_num [even_iff_two_dvd] : Even 100) _
  unfold cappedTerminalMajorant
  split_ifs
  · exact div_nonneg
      (mul_nonneg inverseSquareTerminalConstant_pos.le
        (pow_nonneg hS 64)) (by positivity)
  · exact mul_nonneg
      (div_nonneg (by positivity) (by positivity))
      (div_nonneg (pow_nonneg hS 32)
        (by positivity))

lemma cappedInverseSquareMomentEnvelope_nonneg
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ}
    (hq : 1 ≤ cappedInverseSquareShift Q M C) :
    0 ≤ cappedInverseSquareMomentEnvelope Q M C := by
  unfold cappedInverseSquareMomentEnvelope
  have hqR : (0 : ℝ) < cappedInverseSquareShift Q M C := by
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hT := cappedTerminalMajorant_nonneg (M := M) (C := C) hQ
  apply mul_nonneg (vdcMomentConstant_pos 32).le
  exact add_nonneg
    (add_nonneg (div_nonneg (by norm_num) hqR.le)
      (div_nonneg (by norm_num) (by positivity))) hT

lemma cappedInverseSquareCorrelationEnvelope_nonneg
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ}
    (hq : 1 ≤ cappedInverseSquareShift Q M C) :
    0 ≤ cappedInverseSquareCorrelationEnvelope Q M C := by
  unfold cappedInverseSquareCorrelationEnvelope
  have hE := cappedInverseSquareMomentEnvelope_nonneg hQ hq
  positivity

lemma cappedInverseSquare_tail_le_correlationEnvelope
    (Q : ℝ) (M C : ℕ) :
    8 * (M : ℝ) *
          cappedInverseSquareMomentEnvelope Q M C ^
            ((2 ^ 32 : ℕ) : ℝ)⁻¹ ≤
      cappedInverseSquareCorrelationEnvelope Q M C := by
  unfold cappedInverseSquareCorrelationEnvelope
  exact le_add_of_nonneg_left (by positivity)

lemma cappedInverseSquare_base_le_correlationEnvelope
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ}
    (hq : 1 ≤ cappedInverseSquareShift Q M C) :
    34 * ((M / C : ℕ) : ℝ) + 34 ≤
      cappedInverseSquareCorrelationEnvelope Q M C := by
  unfold cappedInverseSquareCorrelationEnvelope
  have hE := cappedInverseSquareMomentEnvelope_nonneg hQ hq
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) (Real.rpow_nonneg hE _))

lemma terminal_term_le_cappedTerminalMajorant
    {Q : ℝ} (hQ : 0 < Q) {M C A N : ℕ}
    (hC : 2 ≤ C) (hM : 1 ≤ M) (hN : 0 < N)
    (hq : 1 ≤ cappedInverseSquareShift Q M C)
    (hfit : 32 * cappedInverseSquareShift Q M C ≤ N)
    (hAN : A + N ≤ 2 * M) :
    (3 * ((A + N : ℕ) : ℝ) ^ 35 /
        (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
        reciprocalShiftFactor
          (derivativeCutoffs (cappedInverseSquareShift Q M C)) ≤
      cappedTerminalMajorant Q M C := by
  let q := cappedInverseSquareShift Q M C
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hfactor := reciprocalShiftFactor_capped_le
    (Q := Q) (C := C) hM hq
  by_cases hinactive : inverseSquareShift Q M ≤ M / C
  · have hqeq : q = inverseSquareShift Q M := by
      dsimp only [q, cappedInverseSquareShift]
      exact min_eq_left hinactive
    have hcaplt : q < M := by
      have hdivlt : M / C < M := Nat.div_lt_self
        (Nat.zero_lt_of_lt hM) (by omega)
      exact (show q ≤ M / C from cappedInverseSquareShift_le_div Q M C).trans_lt
        hdivlt
    have hbase := inactive_cap_terminal_le hQ hM hN hq hqeq hcaplt hAN
    unfold cappedTerminalMajorant
    rw [if_pos hinactive]
    exact hbase.trans <| by
      apply div_le_div_of_nonneg_left
        (mul_nonneg inverseSquareTerminalConstant_pos.le
          (pow_nonneg (logarithmicSafety_pos hM).le 64))
        (by positivity)
      exact_mod_cast hfit
  · have hANR : (((A + N : ℕ) : ℝ)) ≤ 2 * (M : ℝ) := by exact_mod_cast hAN
    have hfitR : 32 * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hfit
    have hcoef :
        3 * ((A + N : ℕ) : ℝ) ^ 35 /
            (16 * (N : ℝ) * Q * ((34).factorial : ℝ)) ≤
          3 * (2 * (M : ℝ)) ^ 35 /
            (16 * (32 * (q : ℝ)) * Q * ((34).factorial : ℝ)) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · gcongr
    unfold cappedTerminalMajorant
    rw [if_neg hinactive]
    exact calc
      _ ≤ (3 * ((A + N : ℕ) : ℝ) ^ 35 /
          (16 * (N : ℝ) * Q * ((34).factorial : ℝ))) *
            (logarithmicSafety M ^ 32 / (q : ℝ) ^ 32) := by
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ (3 * (2 * (M : ℝ)) ^ 35 /
          (16 * (32 * (q : ℝ)) * Q * ((34).factorial : ℝ))) *
            (logarithmicSafety M ^ 32 / (q : ℝ) ^ 32) := by gcongr

/-- Uniform inverse-square estimate on a subinterval of a dyadic block,
with the external cap left as a parameter. -/
theorem norm_inverseSquareProductIntervalSum_le_capped
    {Q : ℝ} (hQ : 0 < Q) {M C a b : ℕ}
    (hC : 2 ≤ C) (hM : 1 ≤ M)
    (hbase : inverseSquareShiftPredicate Q M (baseShift M))
    (hbaseCap : baseShift M ≤ M / C)
    (hab : a < b) (hMa : M ≤ a) (hbM : b ≤ 2 * M) :
    ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤
      cappedInverseSquareCorrelationEnvelope Q M C := by
  let q := cappedInverseSquareShift Q M C
  let N := b - a
  have hN : 0 < N := by dsimp only [N]; omega
  have hNle : N ≤ M := by dsimp only [N]; omega
  have hq : 1 ≤ q := by
    exact (baseShift_pos (Nat.zero_lt_of_lt hM)).trans_le
      (baseShift_le_cappedInverseSquareShift hbase hbaseCap)
  have hqdiv : q ≤ M / C := cappedInverseSquareShift_le_div Q M C
  by_cases hlong : 32 * q + 2 ≤ N
  · let Ls := derivativeCutoffs q
    have hcut : ∀ L ∈ Ls, 1 ≤ L := by
      intro L hL
      simp only [Ls, derivativeCutoffs, List.mem_replicate] at hL
      exact hL.2 ▸ hq
    have hfit : Ls.sum + 2 ≤ N := by
      simpa only [Ls, derivativeCutoffs_sum] using hlong
    have hpred := cappedInverseSquareShift_spec hQ.le M C
    have hsmallM := inverseSquareShift_derivative_small hQ hM hpred
    have hMaR : (M : ℝ) ≤ a := by exact_mod_cast hMa
    have hMpow : (M : ℝ) ^ 35 ≤ (a : ℝ) ^ 35 := by gcongr
    have hsmall : Q * ((Ls.length + 2).factorial : ℝ) *
        (Ls.prod : ℝ) / (a : ℝ) ^ (Ls.length + 3) ≤ 1 / 2 := by
      simp only [Ls, derivativeCutoffs_length, derivativeCutoffs_prod]
      calc
        Q * ((34).factorial : ℝ) * (q ^ 32 : ℕ) /
            (a : ℝ) ^ 35 ≤
          Q * ((34).factorial : ℝ) * (q ^ 32 : ℕ) /
            (M : ℝ) ^ 35 := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity) hMpow
        _ ≤ 1 / 2 := by
          simpa only [Nat.cast_pow, q] using hsmallM
    have hroot :=
      norm_inverseSquareProductIntervalSum_le_highDerivative
        Q hQ (a := a) (b := b) (by omega) hab Ls hcut
          (by simpa only [N] using hfit) hsmall
    have hAN : a + N ≤ 2 * M := by dsimp only [N]; omega
    have hterm := terminal_term_le_cappedTerminalMajorant
      hQ hC hM hN hq (by omega) hAN
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hErr : 32 / (q : ℝ) = 32 / (q : ℝ) := rfl
    have hOne : 1 / (8 * (N : ℝ)) ≤ 1 / (256 * (q : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (256 : ℝ) * q ≤ 8 * N := by exact_mod_cast (by omega : 256 * q ≤ 8 * N)
      exact this
    have hR : inverseSquareMomentMajorant Q a N Ls ≤
        cappedInverseSquareMomentEnvelope Q M C := by
      unfold inverseSquareMomentMajorant cappedInverseSquareMomentEnvelope
      simp only [Ls, derivativeCutoffs_length, differencingError_derivativeCutoffs]
      apply mul_le_mul_of_nonneg_left _ (vdcMomentConstant_pos 32).le
      exact add_le_add (add_le_add hErr.le hOne) (by
        simpa only [Ls, q] using hterm)
    have hR0 := inverseSquareMomentMajorant_nonneg hQ a hN Ls
    have hE0 := cappedInverseSquareMomentEnvelope_nonneg hQ hq
    have hrpow :
        inverseSquareMomentMajorant Q a N Ls ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ ≤
          cappedInverseSquareMomentEnvelope Q M C ^
            ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
      exact Real.rpow_le_rpow hR0 hR (by positivity)
    unfold inverseSquareHighDerivativeBound at hroot
    unfold cappedInverseSquareCorrelationEnvelope
    calc
      ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤
          8 * (N : ℝ) *
            inverseSquareMomentMajorant Q a N Ls ^
              ((2 ^ Ls.length : ℕ) : ℝ)⁻¹ := hroot
      _ ≤ 8 * (M : ℝ) *
            inverseSquareMomentMajorant Q a N Ls ^
              ((2 ^ Ls.length : ℕ) : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hNle) (by norm_num)
        · exact Real.rpow_nonneg hR0 _
      _ ≤ 8 * (M : ℝ) *
            cappedInverseSquareMomentEnvelope Q M C ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
        simp only [Ls, derivativeCutoffs_length]
        exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ 34 * ((M / C : ℕ) : ℝ) + 34 +
          8 * (M : ℝ) *
            cappedInverseSquareMomentEnvelope Q M C ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
        exact cappedInverseSquare_tail_le_correlationEnvelope Q M C
  · have hshort : N ≤ 32 * (M / C) + 1 := by omega
    have htriv := norm_inverseSquareProductIntervalSum_le_length Q a b
    unfold cappedInverseSquareCorrelationEnvelope
    calc
      ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤ (N : ℕ) := by
        simpa only [N] using htriv
      _ ≤ 32 * ((M / C : ℕ) : ℝ) + 1 := by exact_mod_cast hshort
      _ ≤ 34 * ((M / C : ℕ) : ℝ) + 34 := by
        exact_mod_cast (by omega : 32 * (M / C) + 1 ≤ 34 * (M / C) + 34)
      _ ≤ 34 * ((M / C : ℕ) : ℝ) + 34 +
          8 * (M : ℝ) *
            cappedInverseSquareMomentEnvelope Q M C ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
        exact cappedInverseSquare_base_le_correlationEnvelope hQ hq

end

end InverseSquareAdaptiveShifts
end Erdos378
