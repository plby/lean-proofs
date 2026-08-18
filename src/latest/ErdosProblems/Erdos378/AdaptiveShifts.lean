/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.HighFrequencyCorrelation

/-!
# Adaptive shifts for high reciprocal frequencies

The thirty-second derivative is enough for the range used in the central-row
argument.  The shift is selected maximally under the derivative constraint,
with a logarithmic safety factor.  The maximality inequality is later used in
the opposite direction to control the averaged terminal correlation.
-/

open scoped BigOperators

namespace Erdos378
namespace AdaptiveShifts

open HigherDerivative
open HighFrequencyCorrelation

noncomputable section

def logarithmicSafety (M : ℕ) : ℝ := (Real.log (M : ℝ) + 2) ^ 100

def baseShift (M : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt M)))

def adaptiveShiftPredicate (Q : ℝ) (M q : ℕ) : Prop :=
  2 * Q * ((33).factorial : ℝ) * (q : ℝ) ^ 32 *
      (logarithmicSafety M) ^ 32 ≤ (M : ℝ) ^ 34

noncomputable def adaptiveShift (Q : ℝ) (M : ℕ) : ℕ :=
  @Nat.findGreatest (adaptiveShiftPredicate Q M)
    (Classical.decPred (adaptiveShiftPredicate Q M)) M

def derivativeCutoffs (q : ℕ) : List ℕ := List.replicate 32 q

@[simp] lemma derivativeCutoffs_length (q : ℕ) :
    (derivativeCutoffs q).length = 32 := by
  simp [derivativeCutoffs]

@[simp] lemma derivativeCutoffs_sum (q : ℕ) :
    (derivativeCutoffs q).sum = 32 * q := by
  unfold derivativeCutoffs
  rw [List.sum_replicate]
  rfl

@[simp] lemma derivativeCutoffs_prod (q : ℕ) :
    (derivativeCutoffs q).prod = q ^ 32 := by
  unfold derivativeCutoffs
  exact List.prod_replicate 32 q

lemma differencingError_replicate (n q : ℕ) :
    differencingError (List.replicate n q) = (n : ℝ) / q := by
  induction n with
  | zero => simp [differencingError]
  | succ n ih =>
      simp only [List.replicate_succ, differencingError, ih, Nat.cast_add,
        Nat.cast_one]
      push_cast
      ring

@[simp] lemma differencingError_derivativeCutoffs (q : ℕ) :
    differencingError (derivativeCutoffs q) = 32 / (q : ℝ) := by
  simpa [derivativeCutoffs] using differencingError_replicate 32 q

lemma reciprocalShiftFactor_replicate (n q : ℕ) :
    reciprocalShiftFactor (List.replicate n q) =
      ((1 / (q : ℝ)) *
        ∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))) ^ n := by
  induction n with
  | zero => simp [reciprocalShiftFactor]
  | succ n ih =>
      simp only [List.replicate_succ, reciprocalShiftFactor, ih, pow_succ']

@[simp] lemma reciprocalShiftFactor_derivativeCutoffs (q : ℕ) :
    reciprocalShiftFactor (derivativeCutoffs q) =
      ((1 / (q : ℝ)) *
        ∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))) ^ 32 := by
  simpa [derivativeCutoffs] using reciprocalShiftFactor_replicate 32 q

lemma logarithmicSafety_pos {M : ℕ} (hM : 1 ≤ M) :
    0 < logarithmicSafety M := by
  unfold logarithmicSafety
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  positivity

lemma one_lt_logarithmicSafety {M : ℕ} (hM : 1 ≤ M) :
    1 < logarithmicSafety M := by
  unfold logarithmicSafety
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hbase : (1 : ℝ) < Real.log (M : ℝ) + 2 := by linarith
  calc
    1 = (1 : ℝ) ^ 100 := by norm_num
    _ < (Real.log (M : ℝ) + 2) ^ 100 :=
      pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)

lemma baseShift_pos {M : ℕ} (hM : 0 < M) : 0 < baseShift M := by
  unfold baseShift
  simpa only [Nat.sqrt_pos] using hM

lemma baseShift_le (M : ℕ) : baseShift M ≤ M := by
  by_cases hM : M = 0
  · subst M
    simp [baseShift]
  · have hpos : 0 < M := Nat.pos_of_ne_zero hM
    have h₁ : Nat.sqrt M ≤ M := Nat.sqrt_le_self M
    have h₂ : Nat.sqrt (Nat.sqrt M) ≤ Nat.sqrt M :=
      Nat.sqrt_le_self _
    have h₃ : Nat.sqrt (Nat.sqrt (Nat.sqrt M)) ≤
        Nat.sqrt (Nat.sqrt M) := Nat.sqrt_le_self _
    have h₄ : baseShift M ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt M)) := by
      exact Nat.sqrt_le_self _
    exact h₄.trans (h₃.trans (h₂.trans h₁))

/-- Four successive integer square roots have sixteenth power at most the
original integer. -/
lemma baseShift_pow_sixteen_le (M : ℕ) :
    (baseShift M) ^ 16 ≤ M := by
  let a := Nat.sqrt M
  let b := Nat.sqrt a
  let c := Nat.sqrt b
  let q := Nat.sqrt c
  have hqa : q ^ 2 ≤ c := by
    simpa only [pow_two] using Nat.sqrt_le c
  have hcb : c ^ 2 ≤ b := by
    simpa only [pow_two] using Nat.sqrt_le b
  have hba : b ^ 2 ≤ a := by
    simpa only [pow_two] using Nat.sqrt_le a
  have haM : a ^ 2 ≤ M := by
    simpa only [pow_two] using Nat.sqrt_le M
  have hqfour : q ^ 4 ≤ b := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ ≤ c ^ 2 := pow_le_pow_left₀ (by omega) hqa 2
      _ ≤ b := hcb
  have hqeight : q ^ 8 ≤ a := by
    calc
      q ^ 8 = (q ^ 4) ^ 2 := by ring
      _ ≤ b ^ 2 := pow_le_pow_left₀ (by omega) hqfour 2
      _ ≤ a := hba
  have hqsixteen : q ^ 16 ≤ M := by
    calc
      q ^ 16 = (q ^ 8) ^ 2 := by ring
      _ ≤ a ^ 2 := pow_le_pow_left₀ (by omega) hqeight 2
      _ ≤ M := haM
  simpa only [baseShift, q, c, b, a] using hqsixteen

lemma baseShift_pow_thirtytwo_le_sq {M : ℕ} (hM : 0 < M) :
    (baseShift M) ^ 32 ≤ M ^ 2 := by
  have hq16 := baseShift_pow_sixteen_le M
  calc
    (baseShift M) ^ 32 =
        (baseShift M) ^ 16 * (baseShift M) ^ 16 := by ring
    _ ≤ M * M := Nat.mul_le_mul hq16 hq16
    _ = M ^ 2 := by ring

lemma adaptiveShift_le (Q : ℝ) (M : ℕ) : adaptiveShift Q M ≤ M :=
  by
    classical
    unfold adaptiveShift
    exact Nat.findGreatest_le M

lemma adaptiveShift_spec {Q : ℝ} (hQ : 0 ≤ Q) (M : ℕ) :
    adaptiveShiftPredicate Q M (adaptiveShift Q M) := by
  classical
  unfold adaptiveShift
  apply Nat.findGreatest_spec (m := 0) (n := M) (by omega)
  unfold adaptiveShiftPredicate
  norm_num

lemma baseShift_le_adaptiveShift {Q : ℝ} {M : ℕ}
    (hbase : adaptiveShiftPredicate Q M (baseShift M)) :
    baseShift M ≤ adaptiveShift Q M := by
  classical
  unfold adaptiveShift
  exact Nat.le_findGreatest (baseShift_le M) hbase

/-- The source harmonic sum at a cutoff is bounded by the logarithmic safety
factor at the ambient scale. -/
lemma harmonic_cutoff_le_logarithmicSafety {q M : ℕ}
    (hq : 1 ≤ q) (hqM : q ≤ M) (hM : 1 ≤ M) :
    (∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))) ≤
      logarithmicSafety M := by
  have hsum : (∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))) =
      (harmonic (q - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  have hh := harmonic_le_one_add_log (q - 1)
  have hhR : (harmonic (q - 1) : ℝ) ≤ 1 + Real.log (q - 1) := by
    exact_mod_cast hh
  by_cases hqone : q = 1
  · subst q
    simpa using (logarithmicSafety_pos hM).le
  · have hqsub : 0 < q - 1 := by omega
    have hsubM : (q - 1 : ℝ) ≤ M := by exact_mod_cast (by omega : q - 1 ≤ M)
    have hlogmono : Real.log (q - 1) ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast hqsub) hsubM
    unfold logarithmicSafety
    have hbase : (1 : ℝ) ≤ Real.log (M : ℝ) + 2 := by
      have hlogM : 0 ≤ Real.log (M : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hM)
      linarith
    have hpow : Real.log (M : ℝ) + 2 ≤
        (Real.log (M : ℝ) + 2) ^ 100 := by
      exact le_self_pow₀ hbase (by norm_num)
    linarith

/-- The derivative constraint forces the adaptive shift, multiplied by its
logarithmic safety factor, to be no larger than the ambient scale. -/
lemma adaptiveShift_mul_safety_le
    {Q : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q) :
    (adaptiveShift Q M : ℝ) * logarithmicSafety M ≤ M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hQ : 0 ≤ Q := by nlinarith [sq_pos_of_pos hMpos]
  have hspec := adaptiveShift_spec hQ M
  let q := adaptiveShift Q M
  let S := logarithmicSafety M
  have hfact : (8 : ℝ) ≤ ((33).factorial : ℝ) := by norm_num
  have hQ' : (M : ℝ) ^ 2 / 16 ≤ Q := by linarith
  have hcoef : (M : ℝ) ^ 2 ≤ 2 * Q * ((33).factorial : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hfact hQ
    nlinarith
  have hmain : (M : ℝ) ^ 2 * (q : ℝ) ^ 32 * S ^ 32 ≤
      (M : ℝ) ^ 34 := by
    calc
      (M : ℝ) ^ 2 * (q : ℝ) ^ 32 * S ^ 32 ≤
          (2 * Q * ((33).factorial : ℝ)) * (q : ℝ) ^ 32 * S ^ 32 := by
        gcongr
      _ ≤ (M : ℝ) ^ 34 := by
        simpa only [q, S, adaptiveShiftPredicate] using hspec
  have hpow : ((q : ℝ) * S) ^ 32 ≤ (M : ℝ) ^ 32 := by
    rw [show ((q : ℝ) * S) ^ 32 = (q : ℝ) ^ 32 * S ^ 32 by ring]
    apply le_of_mul_le_mul_left (a := (M : ℝ) ^ 2)
    · calc
      (M : ℝ) ^ 2 * ((q : ℝ) ^ 32 * S ^ 32) =
          (M : ℝ) ^ 2 * (q : ℝ) ^ 32 * S ^ 32 := by ring
      _ ≤ (M : ℝ) ^ 34 := hmain
      _ = (M : ℝ) ^ 2 * (M : ℝ) ^ 32 := by ring
    · exact sq_pos_of_pos hMpos
  have hleft0 : 0 ≤ (q : ℝ) * S := by
    exact mul_nonneg (by positivity) (by
      dsimp only [S]
      exact (logarithmicSafety_pos hM).le)
  have hright0 : (0 : ℝ) ≤ M := by positivity
  exact (pow_le_pow_iff_left₀ hleft0 hright0
    (by norm_num : (32 : ℕ) ≠ 0)).mp hpow

lemma adaptiveShift_lt_ambient
    {Q : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q) :
    adaptiveShift Q M < M := by
  have hle := adaptiveShift_le Q M
  have hmul := adaptiveShift_mul_safety_le hM hQlower
  have hS := one_lt_logarithmicSafety hM
  by_contra hnot
  have heq : adaptiveShift Q M = M := by omega
  rw [heq] at hmul
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  nlinarith

lemma adaptiveShift_succ_not_predicate
    {Q : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q) :
    ¬ adaptiveShiftPredicate Q M (adaptiveShift Q M + 1) := by
  classical
  intro hpred
  have hsuccM : adaptiveShift Q M + 1 ≤ M := by
    have := adaptiveShift_lt_ambient hM hQlower
    omega
  have hle : adaptiveShift Q M + 1 ≤
      @Nat.findGreatest (adaptiveShiftPredicate Q M)
        (Classical.decPred (adaptiveShiftPredicate Q M)) M :=
    Nat.le_findGreatest hsuccM hpred
  change adaptiveShift Q M + 1 ≤ adaptiveShift Q M at hle
  omega

/-- Maximality gives the reverse product inequality. -/
lemma adaptiveShift_reverse_product
    {Q : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hq : 1 ≤ adaptiveShift Q M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q) :
    (M : ℝ) ^ 34 <
      2 ^ 33 * Q * ((33).factorial : ℝ) *
        (adaptiveShift Q M : ℝ) ^ 32 *
          (logarithmicSafety M) ^ 32 := by
  have hfail := adaptiveShift_succ_not_predicate hM hQlower
  have hraw : (M : ℝ) ^ 34 <
      2 * Q * ((33).factorial : ℝ) *
        ((adaptiveShift Q M + 1 : ℕ) : ℝ) ^ 32 *
          (logarithmicSafety M) ^ 32 := by
    exact lt_of_not_ge hfail
  have hsucc : ((adaptiveShift Q M + 1 : ℕ) : ℝ) ≤
      2 * (adaptiveShift Q M : ℝ) := by
    push_cast
    exact_mod_cast (by omega : adaptiveShift Q M + 1 ≤ 2 * adaptiveShift Q M)
  have hQ : 0 ≤ Q := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
    nlinarith [sq_pos_of_pos hMpos]
  have hS : 0 ≤ logarithmicSafety M := (logarithmicSafety_pos hM).le
  have hcoef0 : 0 ≤ 2 * Q * ((33).factorial : ℝ) := by positivity
  have hpowmono :
      ((adaptiveShift Q M + 1 : ℕ) : ℝ) ^ 32 ≤
        (2 * (adaptiveShift Q M : ℝ)) ^ 32 :=
    pow_le_pow_left₀ (by positivity) hsucc 32
  have hout : (M : ℝ) ^ 34 <
      2 * Q * ((33).factorial : ℝ) *
        (2 * (adaptiveShift Q M : ℝ)) ^ 32 *
          (logarithmicSafety M) ^ 32 :=
    hraw.trans_le <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpowmono hcoef0) (by positivity)
  convert hout using 1 <;> ring

lemma reciprocalShiftFactor_adaptive_le
    {Q : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hq : 1 ≤ adaptiveShift Q M) :
    reciprocalShiftFactor
        (derivativeCutoffs (adaptiveShift Q M)) ≤
      (logarithmicSafety M) ^ 32 /
        (adaptiveShift Q M : ℝ) ^ 32 := by
  let q := adaptiveShift Q M
  let H : ℝ := ∑ r ∈ Finset.Icc 1 (q - 1), (1 / (r : ℝ))
  have hqM : q ≤ M := adaptiveShift_le Q M
  have hH : H ≤ logarithmicSafety M :=
    harmonic_cutoff_le_logarithmicSafety hq hqM hM
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  rw [reciprocalShiftFactor_derivativeCutoffs]
  change ((1 / (q : ℝ)) * H) ^ 32 ≤ _
  calc
    ((1 / (q : ℝ)) * H) ^ 32 ≤
        ((1 / (q : ℝ)) * logarithmicSafety M) ^ 32 := by
      gcongr
    _ = (logarithmicSafety M) ^ 32 / (q : ℝ) ^ 32 := by
      field_simp [ne_of_gt hqreal]

/-- The logarithmic safety factor makes the actual thirty-second-derivative
condition an immediate consequence of the defining stronger condition. -/
lemma adaptiveShift_derivative_small
    {Q : ℝ} (hQ : 0 < Q) {M : ℕ} (hM : 1 ≤ M) :
    Q * ((33).factorial : ℝ) * (adaptiveShift Q M : ℝ) ^ 32 /
        (M : ℝ) ^ 34 ≤ 1 / 2 := by
  have hspec := adaptiveShift_spec hQ.le M
  have hSone : (1 : ℝ) ≤ (logarithmicSafety M) ^ 32 := by
    have := (one_lt_logarithmicSafety hM).le
    exact one_le_pow₀ this
  have hcore : 2 * Q * ((33).factorial : ℝ) *
      (adaptiveShift Q M : ℝ) ^ 32 ≤ (M : ℝ) ^ 34 := by
    calc
      2 * Q * ((33).factorial : ℝ) *
          (adaptiveShift Q M : ℝ) ^ 32 =
        (2 * Q * ((33).factorial : ℝ) *
          (adaptiveShift Q M : ℝ) ^ 32) * 1 := by ring
      _ ≤ (2 * Q * ((33).factorial : ℝ) *
          (adaptiveShift Q M : ℝ) ^ 32) *
            (logarithmicSafety M) ^ 32 := by
        gcongr
      _ ≤ (M : ℝ) ^ 34 := by
        simpa only [adaptiveShiftPredicate] using hspec
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  rw [div_le_iff₀ (pow_pos hMpos 34)]
  calc
    Q * ((33).factorial : ℝ) * (adaptiveShift Q M : ℝ) ^ 32 =
        (2 * Q * ((33).factorial : ℝ) *
          (adaptiveShift Q M : ℝ) ^ 32) / 2 := by ring
    _ ≤ (M : ℝ) ^ 34 / 2 := by gcongr
    _ = 1 / 2 * (M : ℝ) ^ 34 := by ring

/-- Absolute constant left after cancelling the maximal-shift inequality in
the terminal contribution. -/
def terminalSafetyConstant : ℝ := 3 * 2 ^ 63

lemma terminalSafetyConstant_pos : 0 < terminalSafetyConstant := by
  unfold terminalSafetyConstant
  positivity

/-- The terminal term in the moment majorant loses only a fixed power of the
logarithmic safety factor. -/
lemma adaptive_terminal_term_le
    {Q : ℝ} (hQ : 0 < Q) {M A N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N)
    (hq : 1 ≤ adaptiveShift Q M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q)
    (hAN : A + N ≤ 2 * M) :
    (3 * ((A + N : ℕ) : ℝ) ^ 34 /
        (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
        reciprocalShiftFactor
          (derivativeCutoffs (adaptiveShift Q M)) ≤
      terminalSafetyConstant * (logarithmicSafety M) ^ 64 / (N : ℝ) := by
  let q := adaptiveShift Q M
  let S := logarithmicSafety M
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hSpos : 0 < S := by
    dsimp only [S]
    exact logarithmicSafety_pos hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactor := reciprocalShiftFactor_adaptive_le
    (Q := Q) hM hq
  have hreverse := adaptiveShift_reverse_product hM hq hQlower
  have hfrac : S ^ 32 / (q : ℝ) ^ 32 <
      2 ^ 33 * Q * ((33).factorial : ℝ) * S ^ 64 /
        (M : ℝ) ^ 34 := by
    rw [div_lt_div_iff₀ (pow_pos hqpos 32) (pow_pos hMpos 34)]
    have hout : S ^ 32 * (M : ℝ) ^ 34 <
        S ^ 32 *
          (2 ^ 33 * Q * ((33).factorial : ℝ) *
            (q : ℝ) ^ 32 * S ^ 32) :=
      mul_lt_mul_of_pos_left hreverse (pow_pos hSpos 32)
    exact hout.trans_eq (by ring)
  have hfactorStrict :
      reciprocalShiftFactor (derivativeCutoffs q) <
        2 ^ 33 * Q * ((33).factorial : ℝ) * S ^ 64 /
          (M : ℝ) ^ 34 := hfactor.trans_lt hfrac
  have hANR : (((A + N : ℕ) : ℝ)) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hAN
  have hANpow : (((A + N : ℕ) : ℝ)) ^ 34 ≤
      (2 * (M : ℝ)) ^ 34 :=
    pow_le_pow_left₀ (by positivity) hANR 34
  have hdenpos : 0 < 16 * (N : ℝ) * Q * ((33).factorial : ℝ) := by
    positivity
  have hfactor0 : 0 ≤ reciprocalShiftFactor (derivativeCutoffs q) :=
    reciprocalShiftFactor_nonneg _
  apply le_of_lt
  calc
    (3 * ((A + N : ℕ) : ℝ) ^ 34 /
          (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
          reciprocalShiftFactor (derivativeCutoffs q) ≤
        (3 * (2 * (M : ℝ)) ^ 34 /
          (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
          reciprocalShiftFactor (derivativeCutoffs q) := by
      apply mul_le_mul_of_nonneg_right _ hfactor0
      apply div_le_div_of_nonneg_right _ hdenpos.le
      gcongr
    _ < (3 * (2 * (M : ℝ)) ^ 34 /
          (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
        (2 ^ 33 * Q * ((33).factorial : ℝ) * S ^ 64 /
          (M : ℝ) ^ 34) := by
      exact mul_lt_mul_of_pos_left hfactorStrict (by positivity)
    _ = terminalSafetyConstant * S ^ 64 / (N : ℝ) := by
      unfold terminalSafetyConstant
      field_simp [ne_of_gt hMpos, ne_of_gt hNpos, ne_of_gt hQ]
      ring
    _ = terminalSafetyConstant * (logarithmicSafety M) ^ 64 /
        (N : ℝ) := by rfl

/-- A uniform normalized moment envelope. -/
def adaptiveMomentEnvelope (M : ℕ) : ℝ :=
  vdcMomentConstant 32 *
    (32 / (baseShift M : ℝ) + 1 / (256 * (baseShift M : ℝ)) +
      terminalSafetyConstant * (logarithmicSafety M) ^ 64 /
        (32 * (baseShift M : ℝ)))

lemma adaptiveMomentEnvelope_nonneg {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ adaptiveMomentEnvelope M := by
  unfold adaptiveMomentEnvelope
  have hq := baseShift_pos (Nat.zero_lt_of_lt hM)
  have hC := (vdcMomentConstant_pos 32).le
  have hT := terminalSafetyConstant_pos.le
  apply mul_nonneg hC
  apply add_nonneg
  · apply add_nonneg
    · exact div_nonneg (by norm_num) (by positivity)
    · exact div_nonneg (by norm_num) (by positivity)
  · exact div_nonneg
      (mul_nonneg hT (pow_nonneg (logarithmicSafety_pos hM).le 64))
      (mul_nonneg (by norm_num) (by positivity))

/-- Uniform correlation envelope, with one term for short supports and one
for supports to which the thirty-second-derivative estimate applies. -/
def adaptiveCorrelationEnvelope (M : ℕ) : ℝ :=
  34 * (M : ℝ) / logarithmicSafety M +
    8 * (M : ℝ) *
      (adaptiveMomentEnvelope M) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹

lemma adaptiveCorrelationEnvelope_nonneg {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ adaptiveCorrelationEnvelope M := by
  unfold adaptiveCorrelationEnvelope
  have hS := (logarithmicSafety_pos hM).le
  have hE := adaptiveMomentEnvelope_nonneg hM
  exact add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (by positivity)) hS)
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (Real.rpow_nonneg hE _))

lemma norm_reciprocalProductIntervalSum_le_length
    (Q : ℝ) (a b : ℕ) :
    ‖PrimeReciprocal.reciprocalProductIntervalSum Q 1 a b‖ ≤
      (b - a : ℕ) := by
  unfold PrimeReciprocal.reciprocalProductIntervalSum
  calc
    ‖∑ r ∈ Finset.Ioc a b,
        PrimeReciprocal.reciprocalWeight Q (1 * r)‖ ≤
      ∑ r ∈ Finset.Ioc a b,
        ‖PrimeReciprocal.reciprocalWeight Q (1 * r)‖ := norm_sum_le _ _
    _ = ∑ _r ∈ Finset.Ioc a b, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp
    _ = (b - a : ℕ) := by simp

/-- Uniform high-frequency estimate on any subinterval of a dyadic block. -/
theorem norm_reciprocalProductIntervalSum_le_adaptive
    {Q : ℝ} (hQ : 0 < Q) {M a b : ℕ}
    (hM : 1 ≤ M)
    (hQlower : (M : ℝ) ^ 2 ≤ 16 * Q)
    (hbase : adaptiveShiftPredicate Q M (baseShift M))
    (hab : a < b) (hMa : M ≤ a) (hbM : b ≤ 2 * M) :
    ‖PrimeReciprocal.reciprocalProductIntervalSum Q 1 a b‖ ≤
      adaptiveCorrelationEnvelope M := by
  let q := adaptiveShift Q M
  let q₀ := baseShift M
  let N := b - a
  let S := logarithmicSafety M
  have hN : 0 < N := by dsimp only [N]; omega
  have hNle : N ≤ M := by dsimp only [N]; omega
  have hq₀ : 1 ≤ q₀ := by
    dsimp only [q₀]
    exact baseShift_pos (Nat.zero_lt_of_lt hM)
  have hq₀q : q₀ ≤ q := by
    dsimp only [q₀, q]
    exact baseShift_le_adaptiveShift hbase
  have hq : 1 ≤ q := hq₀.trans hq₀q
  have hqM : q ≤ M := by
    dsimp only [q]
    exact adaptiveShift_le Q M
  have hSpos : 0 < S := by
    dsimp only [S]
    exact logarithmicSafety_pos hM
  have hqS : (q : ℝ) * S ≤ M := by
    dsimp only [q, S]
    exact adaptiveShift_mul_safety_le hM hQlower
  by_cases hlong : 32 * q + 2 ≤ N
  · let Ls := derivativeCutoffs q
    have hcut : ∀ L ∈ Ls, 1 ≤ L := by
      intro L hL
      simp only [Ls, derivativeCutoffs, List.mem_replicate] at hL
      exact hL.2 ▸ hq
    have hfit : Ls.sum + 2 ≤ N := by
      simpa only [Ls, derivativeCutoffs_sum] using hlong
    have hsmallM := adaptiveShift_derivative_small hQ hM
    have hMaR : (M : ℝ) ≤ a := by exact_mod_cast hMa
    have hMpow : (M : ℝ) ^ 34 ≤ (a : ℝ) ^ 34 :=
      pow_le_pow_left₀ (by positivity) hMaR 34
    have hsmall : Q * (((Ls.length + 1).factorial : ℕ) : ℝ) *
        (Ls.prod : ℝ) / (a : ℝ) ^ (Ls.length + 2) ≤ 1 / 2 := by
      simp only [Ls, derivativeCutoffs_length, derivativeCutoffs_prod]
      calc
        Q * ((33).factorial : ℝ) * (q ^ 32 : ℕ) /
              (a : ℝ) ^ 34 ≤
            Q * ((33).factorial : ℝ) * (q ^ 32 : ℕ) /
              (M : ℝ) ^ 34 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hMpow
        _ ≤ 1 / 2 := by
          simpa only [Nat.cast_pow, q] using hsmallM
    have hroot :=
      HighFrequencyCorrelation.norm_reciprocalProductIntervalSum_le_highDerivative
        Q hQ (a := a) (b := b) (by omega) hab Ls hcut
          (by simpa only [N] using hfit) hsmall
    have hAN : a + N ≤ 2 * M := by
      dsimp only [N]
      omega
    have hterm := adaptive_terminal_term_le hQ hM hN hq hQlower hAN
    have hq₀pos : (0 : ℝ) < q₀ := by exact_mod_cast (Nat.zero_lt_of_lt hq₀)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hqcast : (q₀ : ℝ) ≤ q := by exact_mod_cast hq₀q
    have hErr : 32 / (q : ℝ) ≤ 32 / (q₀ : ℝ) := by
      exact div_le_div_of_nonneg_left (by norm_num) hq₀pos hqcast
    have hbaseN : 32 * q₀ ≤ N := by omega
    have hbaseNR : (256 : ℝ) * q₀ ≤ 8 * N := by
      exact_mod_cast (show 256 * q₀ ≤ 8 * N by omega)
    have hOne : 1 / (8 * (N : ℝ)) ≤ 1 / (256 * (q₀ : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact hbaseNR
    have hTerminal :
        terminalSafetyConstant * S ^ 64 / (N : ℝ) ≤
          terminalSafetyConstant * S ^ 64 / (32 * (q₀ : ℝ)) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg terminalSafetyConstant_pos.le (pow_nonneg hSpos.le 64))
        (by positivity)
      exact_mod_cast hbaseN
    have hR :
        reciprocalMomentMajorant Q a N Ls ≤ adaptiveMomentEnvelope M := by
      unfold reciprocalMomentMajorant adaptiveMomentEnvelope
      simp only [Ls, derivativeCutoffs_length, differencingError_derivativeCutoffs]
      apply mul_le_mul_of_nonneg_left _ (vdcMomentConstant_pos 32).le
      have hterm' :
          (3 * ((a + N : ℕ) : ℝ) ^ 34 /
            (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
              reciprocalShiftFactor Ls ≤
            terminalSafetyConstant * S ^ 64 / (N : ℝ) := by
        simpa only [Ls, q, S] using hterm
      calc
        32 / (q : ℝ) + 1 / (8 * (N : ℝ)) +
            (3 * ((a + N : ℕ) : ℝ) ^ 34 /
              (16 * (N : ℝ) * Q * ((33).factorial : ℝ))) *
                reciprocalShiftFactor Ls ≤
          32 / (q₀ : ℝ) + 1 / (256 * (q₀ : ℝ)) +
            terminalSafetyConstant * S ^ 64 / (32 * (q₀ : ℝ)) := by
          exact add_le_add (add_le_add hErr hOne) (hterm'.trans hTerminal)
        _ = 32 / (baseShift M : ℝ) +
              1 / (256 * (baseShift M : ℝ)) +
              terminalSafetyConstant * (logarithmicSafety M) ^ 64 /
                (32 * (baseShift M : ℝ)) := by rfl
    have hR0 := HighFrequencyCorrelation.reciprocalMomentMajorant_nonneg
      hQ a hN Ls
    have hE0 := adaptiveMomentEnvelope_nonneg hM
    have hrpow :
        (reciprocalMomentMajorant Q a N Ls) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ ≤
          (adaptiveMomentEnvelope M) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ :=
      Real.rpow_le_rpow hR0 hR (by positivity)
    unfold HighFrequencyCorrelation.reciprocalHighDerivativeBound at hroot
    rw [show Ls.length = 32 by simp [Ls]] at hroot
    calc
      ‖PrimeReciprocal.reciprocalProductIntervalSum Q 1 a b‖ ≤
          8 * (N : ℝ) *
            (reciprocalMomentMajorant Q a N Ls) ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
        simpa only [N] using hroot
      _ ≤ 8 * (M : ℝ) *
            (adaptiveMomentEnvelope M) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
        have hNMul : 8 * (N : ℝ) ≤ 8 * (M : ℝ) := by
          gcongr
        exact mul_le_mul hNMul hrpow
          (Real.rpow_nonneg hR0 _) (by positivity)
      _ ≤ adaptiveCorrelationEnvelope M := by
        unfold adaptiveCorrelationEnvelope
        exact le_add_of_nonneg_left
          (div_nonneg (by positivity) (logarithmicSafety_pos hM).le)
  · have hNq : N ≤ 33 * q := by omega
    have hNR : (N : ℝ) ≤ 34 * (M : ℝ) / S := by
      rw [le_div_iff₀ hSpos]
      have hNqR : (N : ℝ) ≤ 33 * q := by exact_mod_cast hNq
      calc
        (N : ℝ) * S ≤ (33 * (q : ℝ)) * S := by gcongr
        _ = 33 * ((q : ℝ) * S) := by ring
        _ ≤ 33 * (M : ℝ) := by gcongr
        _ ≤ 34 * (M : ℝ) := by
          have hM0 : (0 : ℝ) ≤ M := by positivity
          nlinarith
    calc
      ‖PrimeReciprocal.reciprocalProductIntervalSum Q 1 a b‖ ≤
          (N : ℝ) := by
        simpa only [N] using norm_reciprocalProductIntervalSum_le_length Q a b
      _ ≤ 34 * (M : ℝ) / S := hNR
      _ ≤ adaptiveCorrelationEnvelope M := by
        unfold adaptiveCorrelationEnvelope
        exact le_add_of_nonneg_right <|
          mul_nonneg (by positivity) <|
            Real.rpow_nonneg (adaptiveMomentEnvelope_nonneg hM) _

end

end AdaptiveShifts
end Erdos378
