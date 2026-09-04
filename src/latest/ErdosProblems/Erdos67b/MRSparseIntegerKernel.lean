import ErdosProblems.Erdos67b.MRSparseIntegerBlock
import ErdosProblems.Erdos67b.MRSparseDuality
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

/-!
# Integer logarithmic kernels for sparse energy

The critical prefix is decomposed into dyadic blocks, each with the
proved square-root estimate. The complementary long tail is treated
by the finite first-derivative test.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

open Erdos1149 LogSecondDerivativeReal LogPhaseHigherDerivative

noncomputable section

def mrIntegerLogPhase (a : ℝ) (n : ℕ) : ℂ :=
  HigherDerivative.phase (a * Real.log n)

/-- Sum over the positive integers through `N`. -/
def mrIntegerLogSum (a : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 (N + 1), mrIntegerLogPhase a n

theorem mrIntegerLogPhase_add (a : ℝ) (U n : ℕ) :
    mrIntegerLogPhase a (U + n) = realBlockPhase a U n := by
  simp only [mrIntegerLogPhase, realBlockPhase, shiftedLogPhase, Nat.cast_add]

theorem mrIntegerLogSum_Ico_eq_realBlock (a : ℝ) (U P : ℕ) :
    (∑ n ∈ Finset.Ico U (U + P), mrIntegerLogPhase a n) =
      ∑ n ∈ Finset.range P, realBlockPhase a U n := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [Nat.add_comm] using mrIntegerLogPhase_add a U n

theorem mrIntegerLogSum_le_dyadic_count
    {a : ℝ} (ha : 1 ≤ a) (k : ℕ) {N : ℕ} (hNk : N < 2 ^ k) (hNa : (N : ℝ) ≤ 8 * a) :
    ‖mrIntegerLogSum a N‖ ≤ (k : ℝ) * (400 * Real.sqrt a * (1 + Real.log (8 * a))) := by
  let B : ℝ := 400 * Real.sqrt a * (1 + Real.log (8 * a))
  have hB : 0 ≤ B := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 8 * a by linarith)
    dsimp only [B]
    positivity
  change _ ≤ (k : ℝ) * B
  induction k generalizing N with
  | zero =>
      have hN : N = 0 := by norm_num only [pow_zero] at hNk; omega
      subst N
      simp only [mrIntegerLogSum, Finset.Ico_self, Finset.sum_empty, norm_zero, Nat.cast_zero, zero_mul]
      exact le_rfl
  | succ k ih =>
      by_cases hsmall : N < 2 ^ k
      · have hh := ih hsmall hNa
        have hmul : (k : ℝ) * B ≤ (k + 1 : ℕ) * B := by
          push_cast
          nlinarith
        exact hh.trans hmul
      have hUN : 2 ^ k ≤ N := Nat.le_of_not_gt hsmall
      have hUpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
      have hUreal : (0 : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast hUpos
      have hUa : ((2 ^ k : ℕ) : ℝ) ≤ 8 * a := (by exact_mod_cast hUN : ((2 ^ k : ℕ) : ℝ) ≤ N).trans hNa
      have hprev : 2 ^ k - 1 < 2 ^ k := by omega
      have hprevA : ((2 ^ k - 1 : ℕ) : ℝ) ≤ 8 * a :=
        (by exact_mod_cast Nat.sub_le (2 ^ k) 1 : ((2 ^ k - 1 : ℕ) : ℝ) ≤ (2 ^ k : ℕ)).trans hUa
      have hfirst := ih hprev hprevA
      let P : ℕ := N + 1 - 2 ^ k
      have hP : P ≤ 2 ^ k := by
        dsimp only [P]
        rw [pow_succ, Nat.mul_two] at hNk
        omega
      have hsum : mrIntegerLogSum a N = mrIntegerLogSum a (2 ^ k - 1) +
          ∑ n ∈ range P, realBlockPhase a (2 ^ k : ℕ) n := by
        have hend : 2 ^ k + P = N + 1 := by dsimp only [P]; omega
        have hprevEnd : 2 ^ k - 1 + 1 = 2 ^ k := by omega
        rw [← mrIntegerLogSum_Ico_eq_realBlock, hend]
        unfold mrIntegerLogSum
        rw [hprevEnd]
        exact (Finset.sum_Ico_consecutive (mrIntegerLogPhase a) (by omega) (by omega)).symm
      have hblock : ‖∑ n ∈ range P, realBlockPhase a (2 ^ k : ℕ) n‖ ≤ B :=
        mrRealLogBlock_le_sqrt ha hUreal hUa (by exact_mod_cast hP)
      rw [hsum]
      calc
        _ ≤ ‖mrIntegerLogSum a (2 ^ k - 1)‖ + ‖∑ n ∈ range P, realBlockPhase a (2 ^ k : ℕ) n‖ := norm_add_le _ _
        _ ≤ (k : ℝ) * B + B := add_le_add hfirst hblock
        _ = _ := by push_cast; ring

/-- The dyadic count costs at most two logarithmic scale factors. -/
theorem mrNat_log_count_le {a : ℝ} (_ha : 1 ≤ a) {N : ℕ} (hN : 0 < N)
    (hNa : (N : ℝ) ≤ 8 * a) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (8 * a)) := by
  have hpow := Nat.pow_log_le_self 2 hN.ne'
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 N := by positivity
  have hpowle : (2 : ℝ) ^ Nat.log 2 N ≤ 8 * a :=
    (by exact_mod_cast hpow : (2 : ℝ) ^ Nat.log 2 N ≤ N).trans hNa
  have hlog := Real.log_le_log hpowpos hpowle
  rw [Real.log_pow] at hlog
  have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hj : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem mrIntegerLogSum_critical_le
    {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hNa : (N : ℝ) ≤ 8 * a) :
    ‖mrIntegerLogSum a N‖ ≤ 800 * Real.sqrt a * (1 + Real.log (8 * a)) ^ 2 := by
  have hlog : 0 ≤ Real.log (8 * a) := Real.log_nonneg (by linarith)
  by_cases hN : N = 0
  · subst N
    simp only [mrIntegerLogSum, Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  have hcount := mrNat_log_count_le ha (Nat.pos_of_ne_zero hN) hNa
  have hdyadic := mrIntegerLogSum_le_dyadic_count ha (Nat.log 2 N + 1)
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N) hNa
  calc
    _ ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * (400 * Real.sqrt a * (1 + Real.log (8 * a))) := hdyadic
    _ ≤ (2 * (1 + Real.log (8 * a))) * (400 * Real.sqrt a * (1 + Real.log (8 * a))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

/-- First-derivative control on an arbitrarily long tail starting beyond
the critical range. No dyadic restriction on the tail length is needed. -/
theorem mrRealLogBlock_firstDerivative_le
    {a U : ℝ} (ha : 0 < a) (hUa : 8 * a ≤ U) (P : ℕ) :
    ‖∑ n ∈ range P, realBlockPhase a U n‖ ≤ (U + P + 1) / a := by
  let lam : ℝ := a / (U + P + 1)
  let tower : ℕ → ℝ → ℝ := signedShiftedLogDerivative a U 0
  have hU : 0 < U := by linarith
  have hden : 0 < U + (P : ℝ) + 1 := by positivity
  have hlam : 0 < lam := div_pos ha hden
  have hupper : a / U ≤ (1 : ℝ) / 8 := (div_le_iff₀ hU).mpr (by linarith)
  have hlamupper : lam ≤ (1 : ℝ) / 8 := by
    apply le_trans _ hupper
    exact div_le_div_of_nonneg_left ha.le hU (by linarith [show (0 : ℝ) ≤ P by positivity])
  have hfirst (y : ℝ) : tower 1 y = a / (U + y) := by
    dsimp only [tower]
    rw [show 1 = 0 + 1 by rfl, signedShiftedLogDerivative_terminal]
    norm_num [div_eq_mul_inv]
  have hsecond (y : ℝ) : tower 2 y = -(a / (U + y) ^ 2) := by
    dsimp only [tower]
    rw [show 2 = 0 + 2 by rfl, signedShiftedLogDerivative_next]
    norm_num [zpow_neg, div_eq_mul_inv]
  have hcond : HigherDerivative.TerminalIncrementCondition
      (fun n ↦ shiftedLogPhase a U n) P lam := by
    have hh := HigherDerivative.terminalIncrementCondition_of_derivBounds_and_next_nonpos_on_Icc
      tower (shiftedLogPhase a U) [] P 0 ((P : ℝ) + 1)
      lam (a / U) (-(a / U ^ 2)) 0 lam
    apply hh
    · dsimp only [tower]
      simpa only [pow_zero, one_mul] using signedShiftedLogDerivative_zero a U 0
    · simp [MixedDifference.realHistory]
    · simp [MixedDifference.realHistory]
    · intro j hj y hy
      exact hasDerivAt_signedShiftedLogDerivative a U 0 j (by linarith [hy.1])
    · intro y hy
      simp only [MixedDifference.realHistory, List.map_nil, MixedDifference.historySteps_nil,
        List.length_nil, zero_add, hfirst]
      have hUy : 0 < U + y := by linarith [hy.1]
      constructor
      · exact div_le_div_of_nonneg_left ha.le hUy (by linarith [hy.2])
      · exact div_le_div_of_nonneg_left ha.le hU (by linarith [hy.1])
    · intro y hy
      simp only [MixedDifference.realHistory, List.map_nil, MixedDifference.historySteps_nil,
        List.length_nil, zero_add, hsecond]
      have hUy : 0 < U + y := by linarith [hy.1]
      constructor
      · apply neg_le_neg
        apply div_le_div_of_nonneg_left ha.le (sq_pos_of_pos hU)
        nlinarith [hy.1]
      · exact neg_nonpos.mpr (by positivity)
    · exact le_rfl
    · simp [MixedDifference.realHistory]
    · simp only [MixedDifference.realHistory, List.map_nil, MixedDifference.historySteps_nil,
        List.prod_nil, mul_one]
      linarith
  have hmain := HigherDerivative.norm_phaseSum_le_inv_of_terminalIncrementCondition
    (fun n ↦ shiftedLogPhase a U n) P lam hlam (by linarith) hcond
  calc
    _ ≤ 1 / lam := hmain
    _ = _ := by dsimp only [lam]; field_simp

/-- The full normalized integer kernel, with every dyadic and tail
parameter discharged. -/
theorem mrIntegerLogSum_le
    {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    ‖mrIntegerLogSum a N‖ ≤ 3 * (N : ℝ) / a +
      800 * Real.sqrt a * (1 + Real.log (8 * a)) ^ 2 := by
  have ha0 : 0 < a := by linarith
  let M : ℕ := ⌊8 * a⌋₊
  have hMle : (M : ℝ) ≤ 8 * a := Nat.floor_le (by positivity)
  by_cases hNM : N ≤ M
  · have hNa : (N : ℝ) ≤ 8 * a := (by exact_mod_cast hNM : (N : ℝ) ≤ M).trans hMle
    have hh := mrIntegerLogSum_critical_le ha hNa
    have hnonneg : 0 ≤ 3 * (N : ℝ) / a := by positivity
    linarith
  have hMN : M < N := Nat.lt_of_not_ge hNM
  have hN : 0 < N := by omega
  have hMupper : 8 * a < (M : ℝ) + 1 := Nat.lt_floor_add_one (8 * a)
  have hfirst := mrIntegerLogSum_critical_le ha hMle
  have htail := mrRealLogBlock_firstDerivative_le ha0
    (show 8 * a ≤ ((M + 1 : ℕ) : ℝ) by push_cast; exact hMupper.le) (N - M)
  have hsplit : mrIntegerLogSum a N = mrIntegerLogSum a M +
      ∑ n ∈ range (N - M), realBlockPhase a (M + 1 : ℕ) n := by
    rw [← mrIntegerLogSum_Ico_eq_realBlock]
    have hend : M + 1 + (N - M) = N + 1 := by omega
    rw [hend]
    unfold mrIntegerLogSum
    exact (Finset.sum_Ico_consecutive (mrIntegerLogPhase a) (by omega) (by omega)).symm
  have hlength : ((M + 1 : ℕ) : ℝ) + (N - M : ℕ) + 1 = (N : ℝ) + 2 := by
    have hh : M + 1 + (N - M) + 1 = N + 2 := by omega
    exact_mod_cast hh
  rw [hlength] at htail
  have htail' : ‖∑ n ∈ range (N - M), realBlockPhase a (M + 1 : ℕ) n‖ ≤ 3 * (N : ℝ) / a := by
    apply htail.trans
    apply div_le_div_of_nonneg_right _ ha0.le
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [hsplit]
  calc
    _ ≤ ‖mrIntegerLogSum a M‖ + ‖∑ n ∈ range (N - M), realBlockPhase a (M + 1 : ℕ) n‖ := norm_add_le _ _
    _ ≤ (800 * Real.sqrt a * (1 + Real.log (8 * a)) ^ 2) + 3 * (N : ℝ) / a := add_le_add hfirst htail'
    _ = _ := by ring

theorem mrIntegerLogSum_eq_logarithmic (a : ℝ) (N : ℕ) :
    mrIntegerLogSum a N = logarithmicDirichletPolynomial (Finset.Icc 1 N)
      (fun _ ↦ 1) (2 * Real.pi * a) := by
  have hsets : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  unfold mrIntegerLogSum logarithmicDirichletPolynomial
  rw [hsets]
  apply Finset.sum_congr rfl
  intro n hn
  rw [one_mul]
  unfold mrIntegerLogPhase HigherDerivative.phase logarithmicPhase
  rw [Real.fourierChar_apply]
  congr 1
  congr 1
  ring_nf

theorem mrLogarithmicIntegerKernel_norm_neg (N : ℕ) (t : ℝ) :
    ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) (-t)‖ =
      ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) t‖ := by
  have heq : logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) (-t) =
      conj (logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) t) := by
    unfold logarithmicDirichletPolynomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [one_mul]
    change realExponentialPhase ((-t) * Real.log n) = conj (realExponentialPhase (t * Real.log n))
    rw [conj_realExponentialPhase, neg_mul]
  rw [heq, Complex.norm_conj]

theorem mrLogarithmicIntegerKernel_norm_abs (N : ℕ) (t : ℝ) :
    ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) |t|‖ =
      ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) t‖ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, mrLogarithmicIntegerKernel_norm_neg]

theorem mrLogarithmicIntegerKernel_norm_le_card (N : ℕ) (t : ℝ) :
    ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) t‖ ≤ N := by
  unfold logarithmicDirichletPolynomial
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖(1 : ℂ) * logarithmicPhase n t‖ := norm_sum_le _ _
    _ = _ := by simp only [one_mul, norm_logarithmicPhase, Finset.sum_const, nsmul_eq_mul,
      mul_one, Nat.card_Icc, Nat.add_sub_cancel]

/-- Full integer kernel estimate in the exact phase convention used by
the finite Gram matrix, for either sign of the frequency. -/
theorem mrLogarithmicIntegerKernel_le (N : ℕ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) t‖ ≤
      6 * Real.pi * N / |t| + 800 * Real.sqrt |t| * (1 + Real.log (8 * |t|)) ^ 2 := by
  have ht0 : 0 < |t| := by linarith
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hlogt : 0 ≤ Real.log (8 * |t|) := Real.log_nonneg (by linarith)
  rw [← mrLogarithmicIntegerKernel_norm_abs N t]
  by_cases hsmall : |t| ≤ 2 * Real.pi
  · have hh := mrLogarithmicIntegerKernel_norm_le_card N |t|
    have hmain : (N : ℝ) ≤ 6 * Real.pi * N / |t| := by
      apply (le_div_iff₀ ht0).mpr
      nlinarith [show (0 : ℝ) ≤ N by positivity]
    have herr : 0 ≤ 800 * Real.sqrt |t| * (1 + Real.log (8 * |t|)) ^ 2 := by positivity
    linarith
  let a : ℝ := |t| / (2 * Real.pi)
  have ha : 1 ≤ a := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr (by linarith)
  have ha0 : 0 < a := by linarith
  have hat : a ≤ |t| := by
    dsimp only [a]
    exact div_le_self ht0.le hpi
  have hphase : 2 * Real.pi * a = |t| := by dsimp only [a]; field_simp
  have hmain := mrIntegerLogSum_le ha N
  rw [mrIntegerLogSum_eq_logarithmic, hphase] at hmain
  have hrecip : 3 * (N : ℝ) / a = 6 * Real.pi * N / |t| := by dsimp only [a]; field_simp; ring
  have hlog : 1 + Real.log (8 * a) ≤ 1 + Real.log (8 * |t|) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 8 * a) (by linarith : 8 * a ≤ 8 * |t|)
    linarith
  have hloga : 0 ≤ 1 + Real.log (8 * a) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 8 * a by linarith)
    linarith
  have herr : 800 * Real.sqrt a * (1 + Real.log (8 * a)) ^ 2 ≤
      800 * Real.sqrt |t| * (1 + Real.log (8 * |t|)) ^ 2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hat) (by norm_num))
      (pow_le_pow_left₀ hloga hlog 2) (by positivity) (by positivity)
  rw [hrecip] at hmain
  exact hmain.trans (add_le_add le_rfl herr)

end

end Erdos67b
