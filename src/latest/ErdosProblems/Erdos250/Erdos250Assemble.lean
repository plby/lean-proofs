import ErdosProblems.Erdos250.Erdos250RatFrac
import ErdosProblems.Erdos250.Erdos250ZPF
import ErdosProblems.Erdos250.Erdos250QApery
import ErdosProblems.Erdos250.Erdos250Arithmetic
import ErdosProblems.Erdos250.Erdos250VNormalization
import ErdosProblems.Erdos250.Erdos250RawLogDeriv
import ErdosProblems.Erdos250.Erdos250ShiftedSums
import ErdosProblems.Erdos250.Erdos250ScaledDecay
import ErdosProblems.Erdos250.Erdos250Core
import ErdosProblems.Erdos250.Erdos250OldScaledLinearForm

open Filter
open scoped BigOperators Topology

namespace Erdos250

lemma ratCast_R (n : ℕ) (T : ℚ) :
    ((DoublePartialFraction.OldRational.R n T : ℚ) : ℝ) = QApery.R n (T : ℝ) := by
  simpa [DoublePartialFraction.OldRational.Rreal, QApery.R] using
    DoublePartialFraction.OldRational.cast_R n T

lemma q_real_eq_cast : ZPF.q = ((1 / 2 : ℚ) : ℝ) := by
  norm_num [ZPF.q]

lemma q_QApery_eq : QApery.q = ZPF.q := by
  norm_num [QApery.q, ZPF.q]

lemma qpow_rat_not_root (l j : ℕ) :
    (1 / 2 : ℚ) ^ l ≠ DoublePartialFraction.OldRational.root j := by
  have hleft : (1 / 2 : ℚ) ^ l ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hright : (1 : ℚ) < DoublePartialFraction.OldRational.root j := by
    rw [DoublePartialFraction.OldRational.root]
    exact one_lt_pow₀ (by norm_num) (by omega)
  exact ne_of_lt (hleft.trans_lt hright)

lemma partial_fraction_real (n l : ℕ) :
    QApery.R n (ZPF.q ^ l) =
      ∑ j ∈ Finset.range (n + 1),
        (((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) /
            (1 - ZPF.q ^ (j + 1 + l)) +
          ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ) /
            (1 - ZPF.q ^ (j + 1 + l)) ^ 2) := by
  have hpf := DoublePartialFraction.OldRational.partial_fraction_real n ((1 / 2 : ℚ) ^ l)
    (fun j _hj ↦ qpow_rat_not_root l j)
  rw [show DoublePartialFraction.OldRational.Rreal n
      (((1 / 2 : ℚ) ^ l : ℚ) : ℝ) = QApery.R n (ZPF.q ^ l) by
        congr 2
        push_cast
        norm_num [ZPF.q]] at hpf
  apply hpf.trans
  apply Finset.sum_congr rfl
  intro j hj
  have hratio : ZPF.q ^ l / (2 : ℝ) ^ (j + 1) =
      ZPF.q ^ (j + 1 + l) := by
    rw [show ZPF.q ^ l = 1 / (2 : ℝ) ^ l by simp [ZPF.q]]
    rw [show ZPF.q ^ (j + 1 + l) = 1 / (2 : ℝ) ^ (j + 1 + l) by
      simp [ZPF.q]]
    rw [div_div, ← pow_add]
    congr 2
    omega
  have hcastq : (((1 / 2 : ℚ) ^ l : ℚ) : ℝ) = ZPF.q ^ l := by
    push_cast
    norm_num [ZPF.q]
  rw [hcastq, hratio]

lemma partial_fraction_term (n l : ℕ) :
    ZPF.q ^ l * QApery.R n (ZPF.q ^ l) =
      ∑ j ∈ Finset.range (n + 1),
        ((((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) *
            (ZPF.q ^ l / (1 - ZPF.q ^ (j + 1 + l)))) +
          (((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ) *
            (ZPF.q ^ l / (1 - ZPF.q ^ (j + 1 + l)) ^ 2))) := by
  rw [partial_fraction_real]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma q_zpow_neg_eq_root_cast (j : ℕ) :
    ZPF.q ^ (-(j + 1 : ℤ)) =
      ((DoublePartialFraction.OldRational.root j : ℚ) : ℝ) := by
  rw [show -(j + 1 : ℤ) = -((j + 1 : ℕ) : ℤ) by omega]
  rw [zpow_neg, zpow_natCast]
  simp [ZPF.q, DoublePartialFraction.OldRational.root]

lemma simple_pole_cancel_real (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      ZPF.q ^ (-(j + 1 : ℤ)) *
        ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) = 0 := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (DoublePartialFraction.OldRational.sum_root_mul_uCoeff_eq_zero n)
  push_cast at h
  simpa only [q_zpow_neg_eq_root_cast] using h

noncomputable def coeffC (n : ℕ) : ℝ :=
  ZPF.coeffC (n + 1)
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))

noncomputable def coeffA (n : ℕ) : ℝ :=
  ZPF.coeffA (n + 1)
    (fun j ↦ ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ))
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))

lemma S_eq_linear_form (n : ℕ) :
    QApery.S n = coeffC n * ZPF.lambert2 - coeffA n := by
  rw [QApery.S]
  change (∑' l : ℕ, ZPF.q ^ l * QApery.R n (ZPF.q ^ l)) = _
  exact ZPF.partialFractions_tsum (n + 1) (QApery.R n)
    (fun j ↦ ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ))
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))
    (partial_fraction_term n) (simple_pole_cancel_real n)

noncomputable def lambda (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (Erdos250Arithmetic.denProd n : ℚ) /
    (2 : ℚ) ^ (n ^ 2 + 2 * n + 1)

noncomputable def coeffCQ (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    DoublePartialFraction.OldRational.root j *
      DoublePartialFraction.OldRational.vCoeff n j

noncomputable def coeffAQ (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    DoublePartialFraction.OldRational.root j *
      (DoublePartialFraction.OldRational.uCoeff n j *
          Erdos250Arithmetic.hOne j +
        DoublePartialFraction.OldRational.vCoeff n j *
          Erdos250Arithmetic.hTwo j)

lemma cast_hOne_eq_eta (k : ℕ) :
    ((Erdos250Arithmetic.hOne k : ℚ) : ℝ) = ZPF.eta k := by
  induction k with
  | zero => simp [Erdos250Arithmetic.hOne, ZPF.eta]
  | succ k ih =>
      have hrec : Erdos250Arithmetic.hOne (k + 1) =
          Erdos250Arithmetic.hOne k +
            (1 : ℚ) / (Erdos250Arithmetic.oddFactor (k + 1) : ℕ) := by
        rw [Erdos250Arithmetic.hOne, Finset.sum_Icc_succ_top (by omega)]
        rfl
      have hrecEta : ZPF.eta (k + 1) = ZPF.eta k +
          ZPF.q ^ (k + 1) / (1 - ZPF.q ^ (k + 1)) := by
        rw [ZPF.eta, Finset.sum_range_succ]
        rfl
      rw [hrec, hrecEta, Rat.cast_add, ih]
      congr 1
      push_cast
      rw [show ZPF.q ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) by simp [ZPF.q]]
      simp only [Erdos250Arithmetic.oddFactor]
      have hnat : 1 ≤ (2 : ℕ) ^ (k + 1) := one_le_pow₀ (by omega)
      rw [Nat.cast_sub hnat]
      push_cast
      have hp : (1 : ℝ) < (2 : ℝ) ^ (k + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      field_simp [ne_of_gt hp]

lemma cast_hTwo_eq_theta (k : ℕ) :
    ((Erdos250Arithmetic.hTwo k : ℚ) : ℝ) = ZPF.theta k := by
  induction k with
  | zero => simp [Erdos250Arithmetic.hTwo, ZPF.theta]
  | succ k ih =>
      have hrec : Erdos250Arithmetic.hTwo (k + 1) =
          Erdos250Arithmetic.hTwo k +
            ((2 ^ (k + 1) : ℕ) : ℚ) /
              ((Erdos250Arithmetic.oddFactor (k + 1) : ℕ) ^ 2 : ℕ) := by
        rw [Erdos250Arithmetic.hTwo, Finset.sum_Icc_succ_top (by omega)]
        rfl
      have hrecTheta : ZPF.theta (k + 1) = ZPF.theta k +
          ZPF.q ^ (k + 1) / (1 - ZPF.q ^ (k + 1)) ^ 2 := by
        rw [ZPF.theta, Finset.sum_range_succ]
        rfl
      rw [hrec, hrecTheta, Rat.cast_add, ih]
      congr 1
      push_cast
      rw [show ZPF.q ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) by simp [ZPF.q]]
      simp only [Erdos250Arithmetic.oddFactor]
      have hnat : 1 ≤ (2 : ℕ) ^ (k + 1) := one_le_pow₀ (by omega)
      rw [Nat.cast_sub hnat]
      push_cast
      have hp : (1 : ℝ) < (2 : ℝ) ^ (k + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      field_simp [ne_of_gt hp]

lemma coeffC_eq_cast (n : ℕ) : coeffC n = ((coeffCQ n : ℚ) : ℝ) := by
  simp only [coeffC, ZPF.coeffC, coeffCQ]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [q_zpow_neg_eq_root_cast]

lemma coeffA_eq_cast (n : ℕ) : coeffA n = ((coeffAQ n : ℚ) : ℝ) := by
  simp only [coeffA, ZPF.coeffA, coeffAQ]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [q_zpow_neg_eq_root_cast, cast_hOne_eq_eta, cast_hTwo_eq_theta]

lemma cast_oddFactor_eq_oddFactorQ {d : ℕ} (_hd : 1 ≤ d) :
    ((Erdos250Arithmetic.oddFactor d : ℕ) : ℚ) =
      DoublePartialFraction.OldRational.oddFactorQ d := by
  rw [Erdos250Arithmetic.oddFactor,
    DoublePartialFraction.OldRational.oddFactorQ, Nat.cast_sub]
  · norm_num
  · exact one_le_pow₀ (by omega)

lemma rawLogDeriv_eq_logDerivCoeff {n k : ℕ} (hk : k ≤ n) :
    DoublePartialFraction.OldRational.rawLogDeriv n k =
      Erdos250Arithmetic.logDerivCoeff n k := by
  rw [DoublePartialFraction.OldRational.rawLogDeriv_eq_targetLogDeriv n k hk]
  rw [DoublePartialFraction.OldRational.targetLogDeriv,
    Erdos250Arithmetic.logDerivCoeff]
  have hhigh :
      (∑ d ∈ Finset.Icc (k + 1) (n + k),
        (2 : ℚ) ^ d / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc (k + 1) (n + k),
        ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (by
      have := (Finset.mem_Icc.mp hd).1
      omega)]
    norm_num
  have hmid :
      (∑ d ∈ Finset.Icc 1 k,
        (2 : ℚ) ^ d / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc 1 k,
        ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (Finset.mem_Icc.mp hd).1]
    norm_num
  have hlow :
      (∑ d ∈ Finset.Icc 1 (n - k),
        (1 : ℚ) / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc 1 (n - k),
        (1 : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (Finset.mem_Icc.mp hd).1]
  rw [hhigh, hmid, hlow]

lemma lambda_mul_coeffCQ (n : ℕ) :
    lambda n * coeffCQ n = Erdos250Arithmetic.bStar n := by
  rw [coeffCQ, Finset.mul_sum, Erdos250Arithmetic.bStar_eq_sum_cCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simpa only [lambda, VNormalization.lambda, mul_assoc] using
    (VNormalization.lambda_root_mul_vCoeff_eq_cCoeff hkn)

lemma lambda_mul_coeffAQ (n : ℕ) :
    lambda n * coeffAQ n = Erdos250Arithmetic.aStarRegrouped n := by
  rw [coeffAQ, Finset.mul_sum, Erdos250Arithmetic.aStarRegrouped]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [DoublePartialFraction.OldRational.uCoeff_eq_neg_vCoeff_mul_rawLogDeriv
    (Finset.mem_range.mp hk)]
  rw [DoublePartialFraction.OldRational.rawLogDeriv_eq_arithmetic_logDerivCoeff n k hkn]
  rw [show lambda n *
      (DoublePartialFraction.OldRational.root k *
        (-DoublePartialFraction.OldRational.vCoeff n k *
            Erdos250Arithmetic.logDerivCoeff n k * Erdos250Arithmetic.hOne k +
          DoublePartialFraction.OldRational.vCoeff n k * Erdos250Arithmetic.hTwo k)) =
      (lambda n * DoublePartialFraction.OldRational.root k *
          DoublePartialFraction.OldRational.vCoeff n k) *
        (Erdos250Arithmetic.hTwo k -
          Erdos250Arithmetic.logDerivCoeff n k * Erdos250Arithmetic.hOne k) by ring]
  rw [show lambda n * DoublePartialFraction.OldRational.root k *
      DoublePartialFraction.OldRational.vCoeff n k =
      Erdos250Arithmetic.cCoeff n k by
    simpa only [lambda, VNormalization.lambda] using
      (VNormalization.lambda_root_mul_vCoeff_eq_cCoeff hkn)]

lemma lambda_mul_S_eq_integer_form (n : ℕ) :
    ((lambda n : ℚ) : ℝ) * QApery.S n =
      ((Erdos250Arithmetic.bStar n : ℚ) : ℝ) * ZPF.lambert2 -
        ((Erdos250Arithmetic.aStarRegrouped n : ℚ) : ℝ) := by
  rw [S_eq_linear_form, coeffC_eq_cast, coeffA_eq_cast]
  have hb := congrArg (fun x : ℚ ↦ (x : ℝ)) (lambda_mul_coeffCQ n)
  have ha := congrArg (fun x : ℚ ↦ (x : ℝ)) (lambda_mul_coeffAQ n)
  push_cast at hb ha
  calc
    ((lambda n : ℚ) : ℝ) *
        (((coeffCQ n : ℚ) : ℝ) * ZPF.lambert2 - ((coeffAQ n : ℚ) : ℝ)) =
      (((lambda n : ℚ) : ℝ) * ((coeffCQ n : ℚ) : ℝ)) * ZPF.lambert2 -
        (((lambda n : ℚ) : ℝ) * ((coeffAQ n : ℚ) : ℝ)) := by ring
    _ = _ := by rw [hb, ha]

lemma lambert2_eq_zetaQ2 : ZPF.lambert2 = ShiftedSums.zetaQ2 := by
  change ShiftedSums.zetaQ2sq = ShiftedSums.zetaQ2
  exact ShiftedSums.zetaQ2sq_eq_zetaQ2

def intScale (n : ℕ) : ℕ :=
  2 ^ (n ^ 2 / 4) * Erdos250Arithmetic.denProd n ^ 2

noncomputable def bInt (n : ℕ) : ℤ :=
  Classical.choose (Erdos250Arithmetic.E_mul_bStar_eq_intCast n)

noncomputable def aInt (n : ℕ) : ℤ :=
  Classical.choose (Erdos250Arithmetic.E_mul_aStarRegrouped_eq_intCast n)

lemma bInt_spec (n : ℕ) :
    ((intScale n : ℕ) : ℚ) * Erdos250Arithmetic.bStar n = (bInt n : ℚ) := by
  exact Classical.choose_spec (Erdos250Arithmetic.E_mul_bStar_eq_intCast n)

lemma aInt_spec (n : ℕ) :
    ((intScale n : ℕ) : ℚ) * Erdos250Arithmetic.aStarRegrouped n = (aInt n : ℚ) := by
  exact Classical.choose_spec
    (Erdos250Arithmetic.E_mul_aStarRegrouped_eq_intCast n)

lemma integer_form_eq_scaled_S (n : ℕ) :
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) =
      (intScale n : ℝ) * ((lambda n : ℚ) : ℝ) * QApery.S n := by
  have hb := congrArg (fun x : ℚ ↦ (x : ℝ)) (bInt_spec n)
  have ha := congrArg (fun x : ℚ ↦ (x : ℝ)) (aInt_spec n)
  push_cast at hb ha
  have hlin := lambda_mul_S_eq_integer_form n
  calc
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) =
        (intScale n : ℝ) *
          (((Erdos250Arithmetic.bStar n : ℚ) : ℝ) * ZPF.lambert2 -
            ((Erdos250Arithmetic.aStarRegrouped n : ℚ) : ℝ)) := by
      push_cast
      rw [mul_sub, ← mul_assoc, hb, ← ha]
      ring
    _ = (intScale n : ℝ) *
        (((lambda n : ℚ) : ℝ) * QApery.S n) := by rw [hlin]
    _ = _ := by ring

lemma lambda_ne_zero (n : ℕ) : lambda n ≠ 0 := by
  rw [lambda]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast (ZV.denProd_pos n).ne'
  · positivity

lemma integer_form_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) ≠ 0 := by
  rw [integer_form_eq_scaled_S]
  apply mul_ne_zero
  · apply mul_ne_zero
    · have hscale : 0 < intScale n := by
        exact mul_pos (pow_pos (by omega) _) (pow_pos (ZV.denProd_pos n) _)
      exact_mod_cast hscale.ne'
    · exact_mod_cast lambda_ne_zero n
  · exact ne_of_gt (QApery.S_pos hn)

lemma scaled_S_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (intScale n : ℝ) * |((lambda n : ℚ) : ℝ)| * QApery.S n)
      atTop (𝓝 0) := by
  simpa only [intScale, OldScaledLinearForm.E, lambda, VNormalization.lambda] using
    OldScaledLinearForm.scaled_linear_form_tendsto_zero

lemma integer_form_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply scaled_S_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change (intScale n : ℝ) * |((lambda n : ℚ) : ℝ)| * QApery.S n =
    |(bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ)|
  rw [integer_form_eq_scaled_S]
  symm
  calc
    |(intScale n : ℝ) * ((lambda n : ℚ) : ℝ) * QApery.S n| =
        |(intScale n : ℝ)| * |((lambda n : ℚ) : ℝ)| * |QApery.S n| := by
      rw [abs_mul, abs_mul]
    _ = _ := by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (QApery.S_pos hn)]

theorem irrational_lambert2 : Irrational ZPF.lambert2 := by
  apply Erdos250Scratch.irrational_of_integer_linear_forms_tendsto_zero
    ZPF.lambert2 bInt (fun n ↦ -aInt n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact integer_form_ne_zero hn
  · exact integer_form_tendsto_zero

theorem irrational_zetaQ2 : Irrational ShiftedSums.zetaQ2 := by
  rw [← lambert2_eq_zetaQ2]
  exact irrational_lambert2

end Erdos250
