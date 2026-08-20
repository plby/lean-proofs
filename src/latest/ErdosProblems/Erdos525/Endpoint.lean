import ErdosProblems.Erdos525.BadArc

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace
open Classical Filter Finset Set MeasureTheory
open Erdos525

namespace Erdos525

lemma endpoint_sign_sum_abs_ge_one (n : ℕ) (e : Erdos525.SignVector (2 * n)) :
    1 ≤ |∑ j : Fin (2 * n + 1), Erdos525.sign (e j)| := by
  let k : ℕ := (Finset.univ.filter fun j : Fin (2 * n + 1) ↦ e j).card
  have hsum : (∑ j : Fin (2 * n + 1), Erdos525.sign (e j)) =
      2 * (k : ℝ) - (2 * n + 1 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin (2 * n + 1) ↦ e j)
      (f := fun j ↦ Erdos525.sign (e j))]
    have ht : (∑ j with e j, Erdos525.sign (e j)) =
        ((Finset.univ.filter fun j : Fin (2 * n + 1) ↦ e j).card : ℝ) := by
      calc
        (∑ j with e j, Erdos525.sign (e j)) =
            ∑ _j ∈ Finset.univ.filter (fun j : Fin (2 * n + 1) ↦ e j),
              (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp [Erdos525.sign, hj]
        _ = _ := by simp
    have hf : (∑ j with ¬e j, Erdos525.sign (e j)) =
        -((Finset.univ.filter fun j : Fin (2 * n + 1) ↦ ¬e j).card : ℝ) := by
      calc
        (∑ j with ¬e j, Erdos525.sign (e j)) =
            ∑ _j ∈ Finset.univ.filter (fun j : Fin (2 * n + 1) ↦ ¬e j),
              (-1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp [Erdos525.sign, Bool.eq_false_of_not_eq_true hj]
        _ = _ := by simp
    rw [ht, hf]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * n + 1))))
      (p := fun j : Fin (2 * n + 1) ↦ e j)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    dsimp [k]
    have hcR :
        ((Finset.univ.filter fun j : Fin (2 * n + 1) ↦ e j).card : ℝ) +
          ((Finset.univ.filter fun j : Fin (2 * n + 1) ↦ ¬e j).card : ℝ) =
            (2 * n + 1 : ℕ) := by exact_mod_cast hc
    push_cast at hcR ⊢
    linarith
  rw [hsum]
  have hzne : (2 * (k : ℤ) - (2 * n + 1 : ℕ)) ≠ 0 := by omega
  have hzabs := Int.one_le_abs hzne
  exact_mod_cast hzabs

lemma norm_rescaledCenteredEval_zero_lower
    (n : ℕ) (e : Erdos525.SignVector (2 * n)) :
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
      ‖Erdos525.rescaledCenteredEval n e 0‖ := by
  have hs := endpoint_sign_sum_abs_ge_one n e
  unfold Erdos525.rescaledCenteredEval Erdos525.centeredEval
  simp only [zero_div, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hroot : 0 ≤ Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_nonneg _
  rw [abs_of_nonneg hroot]
  have hsum :
      ‖∑ j : Fin (2 * n + 1), (Erdos525.sign (e j) : ℂ)‖ =
        |∑ j : Fin (2 * n + 1), Erdos525.sign (e j)| := by
    rw [show (∑ j : Fin (2 * n + 1), (Erdos525.sign (e j) : ℂ)) =
        ((∑ j : Fin (2 * n + 1), Erdos525.sign (e j) : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hsum]
  simpa using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hroot)

def endpointTwistedSigns (n : ℕ) (e : Erdos525.SignVector (2 * n)) :
    Erdos525.SignVector (2 * n) := fun j ↦
  if Even (Erdos525.centeredIndex n j) then e j else !e j

lemma exp_centeredFrequency_at_pi
    (n : ℕ) (hn : 0 < n) (j : Fin (2 * n + 1)) :
    Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
        (((Real.pi * n) / n : ℝ) : ℂ) * Complex.I) =
      ((((Erdos525.centeredIndex n j).negOnePow : ℤ) : ℝ) : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hratio : Real.pi * (n : ℝ) / n = Real.pi := by
    field_simp [hnR]
  rw [hratio]
  apply Complex.ext
  · rw [Erdos525.exp_centeredFrequency_re]
    have harg : Erdos525.centeredFrequency n j * Real.pi =
        (Erdos525.centeredIndex n j : ℝ) * Real.pi := by
      rw [Erdos525.centeredIndex_cast]
    rw [harg, Real.cos_int_mul_pi]
    change (-1 : ℝ) ^ (Erdos525.centeredIndex n j) =
      (((Erdos525.centeredIndex n j).negOnePow : ℤ) : ℝ)
    exact ((Erdos525.centeredIndex n j).cast_negOnePow ℝ).symm
  · rw [Erdos525.exp_centeredFrequency_im]
    have harg : Erdos525.centeredFrequency n j * Real.pi =
        (Erdos525.centeredIndex n j : ℝ) * Real.pi := by
      rw [Erdos525.centeredIndex_cast]
    rw [harg, Real.sin_int_mul_pi]
    exact (Complex.ofReal_im
      (((Erdos525.centeredIndex n j).negOnePow : ℤ) : ℝ)).symm

lemma endpointTwistedSigns_term
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n))
    (j : Fin (2 * n + 1)) :
    (Erdos525.sign (e j) : ℂ) *
        Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
          (((Real.pi * n) / n : ℝ) : ℂ) * Complex.I) =
      Erdos525.sign (endpointTwistedSigns n e j) := by
  rw [exp_centeredFrequency_at_pi n hn j]
  by_cases hEven : Even (Erdos525.centeredIndex n j)
  · rw [Int.negOnePow_even _ hEven]
    simp [endpointTwistedSigns, hEven]
  · have hOdd : Odd (Erdos525.centeredIndex n j) :=
      (Int.even_or_odd (Erdos525.centeredIndex n j)).resolve_left hEven
    rw [Int.negOnePow_odd _ hOdd]
    simp [endpointTwistedSigns, hEven, Erdos525.sign_not]

lemma norm_rescaledCenteredEval_pi_lower
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n)) :
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
      ‖Erdos525.rescaledCenteredEval n e (Real.pi * n)‖ := by
  have hs := endpoint_sign_sum_abs_ge_one n (endpointTwistedSigns n e)
  unfold Erdos525.rescaledCenteredEval Erdos525.centeredEval
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hroot : 0 ≤ Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_nonneg _
  rw [abs_of_nonneg hroot]
  have hterms :
      (∑ j : Fin (2 * n + 1),
          (Erdos525.sign (e j) : ℂ) *
            Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
              ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)) =
        ((∑ j : Fin (2 * n + 1),
          Erdos525.sign (endpointTwistedSigns n e j) : ℝ) : ℂ) := by
    rw [show ((∑ j : Fin (2 * n + 1),
        Erdos525.sign (endpointTwistedSigns n e j) : ℝ) : ℂ) =
          ∑ j : Fin (2 * n + 1),
            (Erdos525.sign (endpointTwistedSigns n e j) : ℂ) by
      push_cast
      rfl]
    apply Finset.sum_congr rfl
    intro j _hj
    exact endpointTwistedSigns_term n hn e j
  rw [hterms, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hroot)

lemma rescaledCenteredEval_zero_im
    (n : ℕ) (e : Erdos525.SignVector (2 * n)) :
    (Erdos525.rescaledCenteredEval n e 0).im = 0 := by
  unfold Erdos525.rescaledCenteredEval Erdos525.centeredEval
  simp

lemma rescaledCenteredVelocity_zero_re
    (n : ℕ) (e : Erdos525.SignVector (2 * n)) :
    (Erdos525.rescaledCenteredVelocity n e 0).re = 0 := by
  unfold Erdos525.rescaledCenteredVelocity
  simp

lemma rescaledCenteredEval_pi_im
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n)) :
    (Erdos525.rescaledCenteredEval n e (Real.pi * n)).im = 0 := by
  unfold Erdos525.rescaledCenteredEval Erdos525.centeredEval
  rw [Finset.mul_sum]
  simp_rw [endpointTwistedSigns_term n hn e]
  push_cast
  simp

lemma rescaledCenteredVelocity_pi_re
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n)) :
    (Erdos525.rescaledCenteredVelocity n e (Real.pi * n)).re = 0 := by
  unfold Erdos525.rescaledCenteredVelocity
  have hterm : ∀ j : Fin (2 * n + 1),
      ((Erdos525.sign (e j) : ℂ) *
        (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
            ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)).re = 0 := by
    intro j
    rw [show
        (Erdos525.sign (e j) : ℂ) *
            (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
              Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
                ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I) =
          (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
            ((Erdos525.sign (e j) : ℂ) *
              Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
                ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)) by ring,
      endpointTwistedSigns_term n hn e j]
    simp
  rw [Complex.mul_re]
  have hsumRe :
      (∑ j : Fin (2 * n + 1),
        (Erdos525.sign (e j) : ℂ) *
          (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
            Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
              ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)).re = 0 := by
    calc
      (∑ j : Fin (2 * n + 1),
        (Erdos525.sign (e j) : ℂ) *
          (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
            Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
              ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)).re =
        ∑ j : Fin (2 * n + 1),
          ((Erdos525.sign (e j) : ℂ) *
            (((Erdos525.centeredFrequency n j / n : ℝ) : ℂ) * Complex.I) *
              Complex.exp ((Erdos525.centeredFrequency n j : ℂ) *
                ((((Real.pi * n) / n : ℝ)) : ℂ) * Complex.I)).re := by
          rw [Complex.re_sum]
      _ = ∑ _j : Fin (2 * n + 1), (0 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hterm j
      _ = 0 := by simp
  rw [hsumRe]
  simp

lemma endpoint_linear_norm_ge_zero
    (n : ℕ) (e : Erdos525.SignVector (2 * n)) (t : ℝ) :
    ‖Erdos525.rescaledCenteredEval n e 0‖ ≤
      ‖Erdos525.rescaledCenteredEval n e 0 +
        (t : ℂ) * Erdos525.rescaledCenteredVelocity n e 0‖ := by
  have hz := rescaledCenteredEval_zero_im n e
  have hv := rescaledCenteredVelocity_zero_re n e
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im, zero_add]
  rw [hz, hv]
  nlinarith [sq_nonneg (t * (Erdos525.rescaledCenteredVelocity n e 0).im)]

lemma endpoint_linear_norm_ge_pi
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n)) (t : ℝ) :
    ‖Erdos525.rescaledCenteredEval n e (Real.pi * n)‖ ≤
      ‖Erdos525.rescaledCenteredEval n e (Real.pi * n) +
        (t : ℂ) * Erdos525.rescaledCenteredVelocity n e (Real.pi * n)‖ := by
  have hz := rescaledCenteredEval_pi_im n hn e
  have hv := rescaledCenteredVelocity_pi_re n hn e
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im, zero_add]
  rw [hz, hv]
  nlinarith [sq_nonneg (t *
    (Erdos525.rescaledCenteredVelocity n e (Real.pi * n)).im)]

lemma endpoint_zero_lower_via_taylor
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n))
    (hgood : ¬Erdos525.HasHighMeshAcceleration n e)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
      ‖Erdos525.rescaledCenteredEval n e t‖ +
        Erdos525.globalAccelerationBound n * t ^ 2 := by
  let L : ℂ := Erdos525.rescaledCenteredEval n e 0 +
    (t : ℂ) * Erdos525.rescaledCenteredVelocity n e 0
  have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith, hp⟩
  have htIcc : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith [ht.1], ht.2⟩
  have hTaylor := Erdos525.norm_rescaledCenteredEval_sub_linear_le_of_not_high
    n hn e hgood 0 t hzeroIcc htIcc
  have hlin : ‖Erdos525.rescaledCenteredEval n e 0‖ ≤ ‖L‖ := by
    exact endpoint_linear_norm_ge_zero n e t
  have htri : ‖L‖ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
      ‖Erdos525.rescaledCenteredEval n e t - L‖ := by
    have hid : L = Erdos525.rescaledCenteredEval n e t -
        (Erdos525.rescaledCenteredEval n e t - L) := by abel
    calc
      ‖L‖ = ‖Erdos525.rescaledCenteredEval n e t -
          (Erdos525.rescaledCenteredEval n e t - L)‖ := congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  calc
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
        ‖Erdos525.rescaledCenteredEval n e 0‖ :=
      norm_rescaledCenteredEval_zero_lower n e
    _ ≤ ‖L‖ := hlin
    _ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
        ‖Erdos525.rescaledCenteredEval n e t - L‖ := htri
    _ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
        Erdos525.globalAccelerationBound n * t ^ 2 := by
      dsimp [L]
      simpa using add_le_add_left hTaylor
        ‖Erdos525.rescaledCenteredEval n e t‖

lemma endpoint_pi_lower_via_taylor
    (n : ℕ) (hn : 0 < n) (e : Erdos525.SignVector (2 * n))
    (hgood : ¬Erdos525.HasHighMeshAcceleration n e)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
      ‖Erdos525.rescaledCenteredEval n e t‖ +
        Erdos525.globalAccelerationBound n * (Real.pi * n - t) ^ 2 := by
  let x : ℝ := Real.pi * n
  let L : ℂ := Erdos525.rescaledCenteredEval n e x +
    ((t - x : ℝ) : ℂ) * Erdos525.rescaledCenteredVelocity n e x
  have hxIcc : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    dsimp [x]
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith, le_rfl⟩
  have htIcc : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith [ht.1], ht.2⟩
  have hTaylor := Erdos525.norm_rescaledCenteredEval_sub_linear_le_of_not_high
    n hn e hgood x t hxIcc htIcc
  have hlin : ‖Erdos525.rescaledCenteredEval n e x‖ ≤ ‖L‖ := by
    dsimp [L, x]
    exact endpoint_linear_norm_ge_pi n hn e (t - Real.pi * n)
  have htri : ‖L‖ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
      ‖Erdos525.rescaledCenteredEval n e t - L‖ := by
    have hid : L = Erdos525.rescaledCenteredEval n e t -
        (Erdos525.rescaledCenteredEval n e t - L) := by abel
    calc
      ‖L‖ = ‖Erdos525.rescaledCenteredEval n e t -
          (Erdos525.rescaledCenteredEval n e t - L)‖ := congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  calc
    (Real.sqrt (2 * n + 1 : ℝ))⁻¹ ≤
        ‖Erdos525.rescaledCenteredEval n e x‖ := by
      dsimp [x]
      exact norm_rescaledCenteredEval_pi_lower n hn e
    _ ≤ ‖L‖ := hlin
    _ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
        ‖Erdos525.rescaledCenteredEval n e t - L‖ := htri
    _ ≤ ‖Erdos525.rescaledCenteredEval n e t‖ +
        Erdos525.globalAccelerationBound n * (Real.pi * n - t) ^ 2 := by
      have hsquare : (t - x) ^ 2 = (Real.pi * n - t) ^ 2 := by
        dsimp [x]
        ring
      rw [← hsquare]
      dsimp [L]
      simpa using add_le_add_left hTaylor
        ‖Erdos525.rescaledCenteredEval n e t‖

noncomputable def endpointExclusionRadius (n : ℕ) : ℝ :=
  Erdos525.rigidityPower n (-3 / 8)

lemma acceleration_endpoint_scaled_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Erdos525.accelerationCutoff n * endpointExclusionRadius n ^ 2 *
        Real.sqrt (2 * n + 1 : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hinside : Tendsto (fun n : ℕ ↦ Real.sqrt (2 + ((n : ℝ))⁻¹))
      atTop (𝓝 (Real.sqrt 2)) := by
    have hbase : Tendsto (fun n : ℕ ↦ (2 : ℝ) + ((n : ℝ))⁻¹)
        atTop (𝓝 2) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).add hinv
    exact hbase.sqrt
  have hpower := Erdos525.tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 1 / 8 by norm_num)
  have hprod := hinside.mul hpower
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (2 * n + 1 : ℝ) =
      Real.sqrt (2 + ((n : ℝ))⁻¹) * Real.sqrt n := by
    have hfactor : (2 * n + 1 : ℝ) = (2 + ((n : ℝ))⁻¹) * n := by
      field_simp [hnR.ne']
    rw [hfactor, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 + ((n : ℝ))⁻¹)]
  have hsqrtPower : Real.sqrt (n : ℝ) =
      Erdos525.rigidityPower n (1 / 2) := by
    unfold Erdos525.rigidityPower
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt, hsqrtPower]
  unfold Erdos525.accelerationCutoff endpointExclusionRadius
  rw [Erdos525.rigidityPower_nat_pow hn]
  rw [show (-3 / 8 : ℝ) * (2 : ℕ) = -3 / 4 by norm_num]
  have hp : Erdos525.rigidityPower n (1 / 8) *
        Erdos525.rigidityPower n (-3 / 4) *
          Erdos525.rigidityPower n (1 / 2) =
      Erdos525.rigidityPower n (-1 / 8) := by
    rw [← Erdos525.rigidityPower_add hn,
      ← Erdos525.rigidityPower_add hn]
    norm_num
  rw [show -(1 / 8 : ℝ) = -1 / 8 by ring, ← hp]
  ring

lemma mesh_endpoint_scaled_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      (2 * Real.sqrt (2 * n + 1 : ℝ) * Erdos525.localMeshHalfWidth n) *
        endpointExclusionRadius n ^ 2 * Real.sqrt (2 * n + 1 : ℝ))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ 2 + ((n : ℝ))⁻¹)
      atTop (𝓝 2) := by simpa using tendsto_const_nhds.add hinv
  have hhalf := Erdos525.scaled_localMeshHalfWidth_tendsto_pi
  have hradius := Erdos525.tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 3 / 4 by norm_num)
  have hprod := ((hratio.mul hhalf).mul hradius).const_mul 2
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtSq : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = 2 * n + 1 :=
    Real.sq_sqrt (by positivity)
  unfold endpointExclusionRadius
  rw [Erdos525.rigidityPower_nat_pow hn]
  rw [show (-3 / 8 : ℝ) * (2 : ℕ) = -3 / 4 by norm_num]
  have heq :
      (2 * Real.sqrt (2 * n + 1 : ℝ) * Erdos525.localMeshHalfWidth n) *
          Erdos525.rigidityPower n (-3 / 4) *
            Real.sqrt (2 * n + 1 : ℝ) =
        2 * (2 + ((n : ℝ))⁻¹) *
          ((n : ℝ) * Erdos525.localMeshHalfWidth n) *
            Erdos525.rigidityPower n (-3 / 4) := by
    calc
      _ = 2 * (Real.sqrt (2 * n + 1 : ℝ) ^ 2) *
          Erdos525.localMeshHalfWidth n *
            Erdos525.rigidityPower n (-3 / 4) := by ring
      _ = 2 * (2 * n + 1 : ℝ) * Erdos525.localMeshHalfWidth n *
            Erdos525.rigidityPower n (-3 / 4) := by rw [hsqrtSq]
      _ = _ := by
        field_simp [hnR.ne']
  rw [heq]
  ring

lemma globalAcceleration_endpoint_scaled_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Erdos525.globalAccelerationBound n * endpointExclusionRadius n ^ 2 *
        Real.sqrt (2 * n + 1 : ℝ)) atTop (𝓝 0) := by
  have hsum := acceleration_endpoint_scaled_tendsto_zero.add
    mesh_endpoint_scaled_tendsto_zero
  have hsum' : Tendsto (fun n : ℕ ↦
      Erdos525.accelerationCutoff n * endpointExclusionRadius n ^ 2 *
          Real.sqrt (2 * n + 1 : ℝ) +
        (2 * Real.sqrt (2 * n + 1 : ℝ) * Erdos525.localMeshHalfWidth n) *
          endpointExclusionRadius n ^ 2 * Real.sqrt (2 * n + 1 : ℝ))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum'.congr'
  exact Eventually.of_forall fun n ↦ by
    unfold Erdos525.globalAccelerationBound
    ring

lemma endpoint_small_value_scaled_tendsto_zero (u : ℝ) :
    Tendsto (fun n : ℕ ↦
      (u / n + Erdos525.globalAccelerationBound n *
        endpointExclusionRadius n ^ 2) * Real.sqrt (2 * n + 1 : ℝ))
      atTop (𝓝 0) := by
  have hfirst := Erdos525.sqrt_centeredCount_div_tendsto_zero.const_mul u
  have hsecond := globalAcceleration_endpoint_scaled_tendsto_zero
  have hsum := hfirst.add hsecond
  have hsum' : Tendsto (fun n : ℕ ↦
      u * (Real.sqrt (2 * n + 1 : ℝ) / n) +
        Erdos525.globalAccelerationBound n * endpointExclusionRadius n ^ 2 *
          Real.sqrt (2 * n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

lemma eventually_endpoint_small_value_error_lt (u : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      u / n + Erdos525.globalAccelerationBound n *
          endpointExclusionRadius n ^ 2 <
        (Real.sqrt (2 * n + 1 : ℝ))⁻¹ := by
  have hscaled := (endpoint_small_value_scaled_tendsto_zero u).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Nat.eventually_pos, hscaled] with n hn hscaledN
  have hsqrt : 0 < Real.sqrt (2 * n + 1 : ℝ) := by positivity
  rw [inv_eq_one_div, lt_div_iff₀ hsqrt]
  simpa [mul_comm] using hscaledN

lemma eventually_small_value_away_from_endpoints (u : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ e : Erdos525.SignVector (2 * n),
      ¬Erdos525.HasHighMeshAcceleration n e →
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
        ‖Erdos525.rescaledCenteredEval n e t‖ ≤ u / n →
        endpointExclusionRadius n < t ∧
          endpointExclusionRadius n < Real.pi * n - t := by
  filter_upwards [Nat.eventually_pos,
      eventually_endpoint_small_value_error_lt u] with n hn herr
  intro e hgood t ht hsmall
  have hC : 0 ≤ Erdos525.globalAccelerationBound n := by
    unfold Erdos525.globalAccelerationBound Erdos525.accelerationCutoff
    exact add_nonneg (Erdos525.rigidityPower_nonneg n _)
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold Erdos525.localMeshHalfWidth; positivity))
  have hr : 0 ≤ endpointExclusionRadius n := by
    unfold endpointExclusionRadius
    exact Erdos525.rigidityPower_nonneg n _
  constructor
  · by_contra hnot
    have htr : t ≤ endpointExclusionRadius n := le_of_not_gt hnot
    have ht0 : 0 ≤ t := ht.1
    have htSq : t ^ 2 ≤ endpointExclusionRadius n ^ 2 :=
      (sq_le_sq₀ ht0 hr).2 htr
    have hlower := endpoint_zero_lower_via_taylor n hn e hgood t ht
    have hupper : ‖Erdos525.rescaledCenteredEval n e t‖ +
          Erdos525.globalAccelerationBound n * t ^ 2 ≤
        u / n + Erdos525.globalAccelerationBound n *
          endpointExclusionRadius n ^ 2 :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left htSq hC)
    exact (not_lt_of_ge (hlower.trans hupper)) herr
  · by_contra hnot
    have htr : Real.pi * n - t ≤ endpointExclusionRadius n :=
      le_of_not_gt hnot
    have ht0 : 0 ≤ Real.pi * n - t := sub_nonneg.mpr ht.2
    have htSq : (Real.pi * n - t) ^ 2 ≤ endpointExclusionRadius n ^ 2 :=
      (sq_le_sq₀ ht0 hr).2 htr
    have hlower := endpoint_pi_lower_via_taylor n hn e hgood t ht
    have hupper : ‖Erdos525.rescaledCenteredEval n e t‖ +
          Erdos525.globalAccelerationBound n * (Real.pi * n - t) ^ 2 ≤
        u / n + Erdos525.globalAccelerationBound n *
          endpointExclusionRadius n ^ 2 :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left htSq hC)
    exact (not_lt_of_ge (hlower.trans hupper)) herr

end Erdos525
