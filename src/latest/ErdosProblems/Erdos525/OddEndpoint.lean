import ErdosProblems.Erdos525.OddBadProbability

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

def boolFunEquivFinset (d : ℕ) : (Fin d → Bool) ≃ Finset (Fin d) where
  toFun e := Finset.univ.filter fun j ↦ e j
  invFun s j := decide (j ∈ s)
  left_inv e := by
    funext j
    cases h : e j <;> simp [h]
  right_inv s := by
    ext j
    simp

noncomputable def trueCount {d : ℕ} (e : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun j ↦ e j).card

lemma card_bool_vectors_trueCount_eq (d k : ℕ) :
    ((Finset.univ.filter fun e : Fin d → Bool ↦ trueCount e = k).card) =
      Nat.choose d k := by
  have hsub : Fintype.card {e : Fin d → Bool // trueCount e = k} =
      Fintype.card {s : Finset (Fin d) // s.card = k} := by
    exact Fintype.card_congr ((boolFunEquivFinset d).subtypeEquiv fun e ↦ Iff.rfl)
  calc
    (Finset.univ.filter fun e : Fin d → Bool ↦ trueCount e = k).card =
        Fintype.card {e : Fin d → Bool // trueCount e = k} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card {s : Finset (Fin d) // s.card = k} := hsub
    _ = (Finset.univ.filter fun s : Finset (Fin d) ↦ s.card = k).card := by
      rw [Fintype.card_subtype]
    _ = (Finset.univ.powersetCard k).card := by
      congr 1
      ext s
      simp
    _ = Nat.choose d k := by simp

lemma sign_sum_eq_two_trueCount_sub (d : ℕ) (e : Fin d → Bool) :
    (∑ j : Fin d, sign (e j)) = 2 * (trueCount e : ℝ) - d := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun j : Fin d ↦ e j) (f := fun j ↦ sign (e j))]
  have ht : (∑ j with e j, sign (e j)) = (trueCount e : ℝ) := by
    unfold trueCount
    calc
      (∑ j with e j, sign (e j)) =
          ∑ _j ∈ Finset.univ.filter (fun j : Fin d ↦ e j), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [sign, hj]
      _ = _ := by simp
  have hf : (∑ j with ¬e j, sign (e j)) =
      -(((Finset.univ.filter fun j : Fin d ↦ ¬e j).card : ℕ) : ℝ) := by
    calc
      (∑ j with ¬e j, sign (e j)) =
          ∑ _j ∈ Finset.univ.filter (fun j : Fin d ↦ ¬e j), (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [sign, Bool.eq_false_of_not_eq_true hj]
      _ = _ := by simp
  rw [ht, hf]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin d))) (p := fun j : Fin d ↦ e j)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hcR : (trueCount e : ℝ) +
      ((Finset.univ.filter fun j : Fin d ↦ ¬e j).card : ℝ) = d := by
    unfold trueCount
    exact_mod_cast hc
  linarith

lemma sign_sum_eq_zero_iff_trueCount
    (n : ℕ) (e : SignVector (2 * n + 1)) :
    (∑ j : Fin (2 * n + 2), sign (e j)) = 0 ↔ trueCount e = n + 1 := by
  rw [sign_sum_eq_two_trueCount_sub]
  constructor
  · intro h
    have hR : (trueCount e : ℝ) = n + 1 := by
      push_cast at h
      linarith
    exact_mod_cast hR
  · intro h
    rw [h]
    push_cast
    ring

lemma choose_two_mul_le_four_pow_div_sqrt (m : ℕ) :
    (Nat.choose (2 * m) m : ℝ) ≤
      (4 : ℝ) ^ m / Real.sqrt (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hidentity : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) =
          (2 * (2 * m + 1) / (m + 1)) *
            (Nat.choose (2 * m) m : ℝ) := by
        rw [Nat.cast_choose, Nat.cast_choose] <;> try linarith
        norm_num [two_mul, Nat.factorial]
        rw [div_mul_div_comm, div_eq_div_iff] <;> first | positivity | ring_nf
        try rw [show 1 + m * 2 = m * 2 + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      rw [hidentity, pow_succ']
      refine le_trans (mul_le_mul_of_nonneg_left ih (by positivity)) ?_
      field_simp
      norm_num
      nlinarith [sq_nonneg (Real.sqrt (m + 1) - Real.sqrt (m + 1 + 1)),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ m + 1 by positivity),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ m + 1 + 1 by positivity),
        Real.sqrt_nonneg (m + 1 : ℝ), Real.sqrt_nonneg (m + 1 + 1 : ℝ)]

lemma uniformProbability_sign_sum_zero_eq (n : ℕ) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        (∑ j : Fin (2 * n + 2), sign (e j)) = 0) =
      (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) / 4 ^ (n + 1) := by
  unfold uniformProbability
  rw [show (Finset.univ.filter fun e : SignVector (2 * n + 1) ↦
      (∑ j : Fin (2 * n + 2), sign (e j)) = 0) =
      Finset.univ.filter fun e : Fin (2 * n + 2) → Bool ↦
        trueCount e = n + 1 by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sign_sum_eq_zero_iff_trueCount n e]
  rw [card_bool_vectors_trueCount_eq]
  simp only [card_signVector]
  push_cast
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
    show (2 : ℝ) ^ (2 * (n + 1)) = 4 ^ (n + 1) by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]

lemma uniformProbability_sign_sum_zero_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability
      (fun e : SignVector (2 * n + 1) ↦
        (∑ j : Fin (2 * n + 2), sign (e j)) = 0)) atTop (𝓝 0) := by
  have hupper : ∀ n : ℕ,
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
          (∑ j : Fin (2 * n + 2), sign (e j)) = 0) ≤
        1 / Real.sqrt (n + 2 : ℝ) := by
    intro n
    rw [uniformProbability_sign_sum_zero_eq]
    have hchoose := choose_two_mul_le_four_pow_div_sqrt (n + 1)
    have hpow : (0 : ℝ) < 4 ^ (n + 1) := by positivity
    apply (div_le_iff₀ hpow).2
    norm_num only [Nat.cast_add, Nat.cast_one] at hchoose
    have hsqrtEq : Real.sqrt ((n : ℝ) + 1 + 1) =
        Real.sqrt ((n : ℝ) + 2) := by
      congr 1
      ring
    rw [hsqrtEq] at hchoose
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hchoose
  have hsqrtDiv : Tendsto (fun n : ℕ ↦ Real.sqrt n / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [Real.sqrt_div_self] using tendsto_inv_atTop_nhds_zero_nat.sqrt
  have honeDiv : Tendsto (fun n : ℕ ↦ 1 / Real.sqrt n) atTop (𝓝 0) := by
    apply hsqrtDiv.congr'
    filter_upwards [Nat.eventually_pos] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp [(Real.sqrt_pos.2 hnR).ne', hnR.ne']
    rw [Real.sq_sqrt hnR.le]
  have hbound : Tendsto (fun n : ℕ ↦ 1 / Real.sqrt (n + 2 : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ honeDiv
    filter_upwards [Nat.eventually_pos] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hnR)
      (Real.sqrt_le_sqrt (by linarith : (n : ℝ) ≤ (n : ℝ) + 2))
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
    (Eventually.of_forall hupper) hbound

def parityTwist (d : ℕ) (e : Fin d → Bool) : Fin d → Bool := fun j ↦
  if Even (j : ℕ) then e j else !e j

def parityTwistEquiv (d : ℕ) : (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun := parityTwist d
  invFun := parityTwist d
  left_inv e := by
    funext j
    by_cases hj : Even (j : ℕ) <;> simp [parityTwist, hj]
  right_inv e := by
    funext j
    by_cases hj : Even (j : ℕ) <;> simp [parityTwist, hj]

lemma sign_parityTwist (d : ℕ) (e : Fin d → Bool) (j : Fin d) :
    sign (parityTwist d e j) = (-1 : ℝ) ^ (j : ℕ) * sign (e j) := by
  by_cases hj : Even (j : ℕ)
  · rw [Even.neg_one_pow hj]
    simp [parityTwist, hj]
  · have hjOdd : Odd (j : ℕ) := (Nat.even_or_odd (j : ℕ)).resolve_left hj
    rw [Odd.neg_one_pow hjOdd]
    simp [parityTwist, hj, sign_not]

noncomputable def endpointPiSignSum (n : ℕ)
    (e : SignVector (2 * n + 1)) : ℝ :=
  ∑ j : Fin (2 * n + 2), sign (parityTwist (2 * n + 2) e j)

lemma uniformProbability_endpointPiSignSum_zero_eq (n : ℕ) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        endpointPiSignSum n e = 0) =
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        (∑ j : Fin (2 * n + 2), sign (e j)) = 0) := by
  have hcard :
      (Finset.univ.filter fun e : SignVector (2 * n + 1) ↦
          endpointPiSignSum n e = 0).card =
        (Finset.univ.filter fun e : SignVector (2 * n + 1) ↦
          (∑ j : Fin (2 * n + 2), sign (e j)) = 0).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr ((parityTwistEquiv (2 * n + 2)).subtypeEquiv
      (fun e ↦ by rfl))
  unfold uniformProbability
  rw [hcard]

lemma uniformProbability_endpointPiSignSum_zero_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability
      (fun e : SignVector (2 * n + 1) ↦ endpointPiSignSum n e = 0))
      atTop (𝓝 0) := by
  apply uniformProbability_sign_sum_zero_tendsto_zero.congr'
  exact Eventually.of_forall fun n ↦
    (uniformProbability_endpointPiSignSum_zero_eq n).symm

lemma littlewoodEval_one (n : ℕ) (e : SignVector (2 * n + 1)) :
    littlewoodEval e 1 =
      ((∑ j : Fin (2 * n + 2), sign (e j) : ℝ) : ℂ) := by
  unfold littlewoodEval
  simp only [one_pow, mul_one]
  push_cast
  rfl

lemma littlewoodEval_neg_one (n : ℕ) (e : SignVector (2 * n + 1)) :
    littlewoodEval e (-1) = (endpointPiSignSum n e : ℂ) := by
  unfold littlewoodEval endpointPiSignSum
  rw [show ((∑ j : Fin (2 * n + 2),
      sign (parityTwist (2 * n + 2) e j) : ℝ) : ℂ) =
      ∑ j : Fin (2 * n + 2),
        (sign (parityTwist (2 * n + 2) e j) : ℂ) by push_cast; rfl]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sign_parityTwist]
  push_cast
  ring

lemma sign_sum_abs_ge_one_of_ne
    {d : ℕ} (e : Fin d → Bool)
    (hne : (∑ j : Fin d, sign (e j)) ≠ 0) :
    1 ≤ |∑ j : Fin d, sign (e j)| := by
  let z : ℤ := 2 * (trueCount e : ℤ) - d
  have hcast : ((z : ℤ) : ℝ) = ∑ j : Fin d, sign (e j) := by
    dsimp [z]
    rw [sign_sum_eq_two_trueCount_sub]
    push_cast
    rfl
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    rw [← hcast, hz]
    simp
  have := Int.one_le_abs hz
  rw [← hcast]
  exact_mod_cast this

lemma endpointPiSignSum_abs_ge_one_of_ne
    (n : ℕ) (e : SignVector (2 * n + 1))
    (hne : endpointPiSignSum n e ≠ 0) :
    1 ≤ |endpointPiSignSum n e| := by
  exact sign_sum_abs_ge_one_of_ne (parityTwist (2 * n + 2) e) hne

lemma norm_eval_zero_lower_of_signSum_ne
    (n : ℕ) (e : SignVector (2 * n + 1))
    (hne : (∑ j : Fin (2 * n + 2), sign (e j)) ≠ 0) :
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤ ‖eval n e 0‖ := by
  rw [norm_eval, zero_div, norm_oddCenteredEval]
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, littlewoodEval_one]
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa [one_div] using div_le_div_of_nonneg_right
    (sign_sum_abs_ge_one_of_ne e hne) (Real.sqrt_nonneg (2 * n + 2 : ℝ))

lemma norm_eval_pi_lower_of_signSum_ne
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hne : endpointPiSignSum n e ≠ 0) :
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤
      ‖eval n e (Real.pi * n)‖ := by
  rw [norm_eval]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show Real.pi * (n : ℝ) / n = Real.pi by field_simp [hn0],
    norm_oddCenteredEval, Complex.exp_pi_mul_I, littlewoodEval_neg_one,
    Complex.norm_real, Real.norm_eq_abs]
  simpa [one_div] using div_le_div_of_nonneg_right
    (endpointPiSignSum_abs_ge_one_of_ne n e hne)
    (Real.sqrt_nonneg (2 * n + 2 : ℝ))

def HasEndpointZero (n : ℕ) (e : SignVector (2 * n + 1)) : Prop :=
  (∑ j : Fin (2 * n + 2), sign (e j)) = 0 ∨ endpointPiSignSum n e = 0

lemma uniformProbability_hasEndpointZero_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasEndpointZero n))
      atTop (𝓝 0) := by
  have hsum := uniformProbability_sign_sum_zero_tendsto_zero.add
    uniformProbability_endpointPiSignSum_zero_tendsto_zero
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · exact Eventually.of_forall fun n ↦ uniformProbability_or_le_add _ _
  · simpa [HasEndpointZero] using hsum

lemma eval_zero_im (n : ℕ) (e : SignVector (2 * n + 1)) :
    (eval n e 0).im = 0 := by
  unfold eval
  rw [Complex.add_im, Complex.mul_im]
  simp [rescaledCenteredEval_zero_im]

lemma velocity_zero_re (n : ℕ) (e : SignVector (2 * n + 1)) :
    (velocity n e 0).re = 0 := by
  unfold velocity
  rw [Complex.add_re, Complex.mul_re]
  simp [rescaledCenteredVelocity_zero_re]

lemma extra_exp_pi_im (n : ℕ) (hn : 0 < n) :
    (Complex.exp (((((n + 1 : ℕ) : ℝ) : ℂ) *
      (((Real.pi * (n : ℝ) : ℝ) : ℂ) / (n : ℂ))) * Complex.I)).im = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0C : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have harg : (((((n + 1 : ℕ) : ℝ) : ℂ) *
      (((Real.pi * (n : ℝ) : ℝ) : ℂ) / (n : ℂ))) * Complex.I) =
      (((((n + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp [hn0C]
  rw [harg, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    zero_mul, add_zero, mul_one]
  rw [Real.sin_nat_mul_pi]
  simp

lemma eval_pi_im (n : ℕ) (hn : 0 < n)
    (e : SignVector (2 * n + 1)) :
    (eval n e (Real.pi * n)).im = 0 := by
  unfold eval
  rw [Complex.add_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [rescaledCenteredEval_pi_im n hn]
  have him := extra_exp_pi_im n hn
  change prefixScale n * 0 + 0 *
      (rescaledCenteredEval n (initialSegment n e) (Real.pi * n)).re +
      (((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((((n + 1 : ℕ) : ℝ) : ℂ) *
          (((Real.pi * (n : ℝ) : ℝ) : ℂ) / (n : ℂ))) * Complex.I)).im = 0
  rw [Complex.mul_im, him]
  simp

lemma velocity_pi_re (n : ℕ) (hn : 0 < n)
    (e : SignVector (2 * n + 1)) :
    (velocity n e (Real.pi * n)).re = 0 := by
  let c : ℂ := (sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ)
  let q : ℂ := (((n + 1 : ℕ) : ℝ) : ℂ) / (n : ℂ)
  let z : ℂ := Complex.exp (((((n + 1 : ℕ) : ℝ) : ℂ) *
    (((Real.pi * (n : ℝ) : ℝ) : ℂ) / (n : ℂ))) * Complex.I)
  have hz : z.im = 0 := by
    dsimp [z]
    exact extra_exp_pi_im n hn
  have hqI : (q * Complex.I).re = 0 := by simp [q, Complex.mul_re]
  have hcqI : (c * (q * Complex.I)).re = 0 := by
    rw [Complex.mul_re, hqI]
    simp [c, q, Complex.mul_im]
  have hextra : (c * (q * Complex.I) * z).re = 0 := by
    rw [Complex.mul_re, hcqI, hz]
    ring
  unfold velocity
  change (((prefixScale n : ℝ) : ℂ) *
      rescaledCenteredVelocity n (initialSegment n e) (Real.pi * n) +
        c * (q * Complex.I) * z).re = 0
  rw [Complex.add_re, Complex.mul_re,
    rescaledCenteredVelocity_pi_re n hn, hextra]
  simp

lemma endpoint_linear_norm_ge_zero
    (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖eval n e 0‖ ≤ ‖eval n e 0 + (t : ℂ) * velocity n e 0‖ := by
  have hz := eval_zero_im n e
  have hv := velocity_zero_re n e
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im, zero_add]
  rw [hz, hv]
  nlinarith [sq_nonneg (t * (velocity n e 0).im)]

lemma endpoint_linear_norm_ge_pi
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖eval n e (Real.pi * n)‖ ≤
      ‖eval n e (Real.pi * n) + (t : ℂ) * velocity n e (Real.pi * n)‖ := by
  have hz := eval_pi_im n hn e
  have hv := velocity_pi_re n hn e
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im, zero_add]
  rw [hz, hv]
  nlinarith [sq_nonneg (t * (velocity n e (Real.pi * n)).im)]

lemma endpoint_zero_lower_via_taylor
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration 0 n e)
    (hne : (∑ j : Fin (2 * n + 2), sign (e j)) ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤
      ‖eval n e t‖ + fineGlobalAccelerationBound 0 n * t ^ 2 := by
  let L : ℂ := eval n e 0 + (t : ℂ) * velocity n e 0
  have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith, hp⟩
  have htIcc : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith [ht.1], ht.2⟩
  have hTaylor := norm_eval_sub_linear_le_of_not_highPrefixFine
    0 n hn e hgood 0 t hzeroIcc htIcc
  have hlin : ‖eval n e 0‖ ≤ ‖L‖ := endpoint_linear_norm_ge_zero n e t
  have htri : ‖L‖ ≤ ‖eval n e t‖ + ‖eval n e t - L‖ := by
    have hid : L = eval n e t - (eval n e t - L) := by abel
    calc
      ‖L‖ = ‖eval n e t - (eval n e t - L)‖ := congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  calc
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤ ‖eval n e 0‖ :=
      norm_eval_zero_lower_of_signSum_ne n e hne
    _ ≤ ‖L‖ := hlin
    _ ≤ ‖eval n e t‖ + ‖eval n e t - L‖ := htri
    _ ≤ ‖eval n e t‖ + fineGlobalAccelerationBound 0 n * t ^ 2 := by
      dsimp [L]
      simpa using add_le_add_left hTaylor ‖eval n e t‖

lemma endpoint_pi_lower_via_taylor
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration 0 n e)
    (hne : endpointPiSignSum n e ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n)) :
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤
      ‖eval n e t‖ + fineGlobalAccelerationBound 0 n *
        (Real.pi * n - t) ^ 2 := by
  let x : ℝ := Real.pi * n
  let L : ℂ := eval n e x + ((t - x : ℝ) : ℂ) * velocity n e x
  have hxIcc : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    dsimp [x]
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith, le_rfl⟩
  have htIcc : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hp : 0 ≤ Real.pi * (n : ℝ) :=
      mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)
    exact ⟨by linarith [ht.1], ht.2⟩
  have hTaylor := norm_eval_sub_linear_le_of_not_highPrefixFine
    0 n hn e hgood x t hxIcc htIcc
  have hlin : ‖eval n e x‖ ≤ ‖L‖ := by
    dsimp [L, x]
    exact endpoint_linear_norm_ge_pi n hn e (t - Real.pi * n)
  have htri : ‖L‖ ≤ ‖eval n e t‖ + ‖eval n e t - L‖ := by
    have hid : L = eval n e t - (eval n e t - L) := by abel
    calc
      ‖L‖ = ‖eval n e t - (eval n e t - L)‖ := congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  calc
    (Real.sqrt (2 * n + 2 : ℝ))⁻¹ ≤ ‖eval n e x‖ := by
      dsimp [x]
      exact norm_eval_pi_lower_of_signSum_ne n hn e hne
    _ ≤ ‖L‖ := hlin
    _ ≤ ‖eval n e t‖ + ‖eval n e t - L‖ := htri
    _ ≤ ‖eval n e t‖ + fineGlobalAccelerationBound 0 n *
        (Real.pi * n - t) ^ 2 := by
      have hsquare : (t - x) ^ 2 = (Real.pi * n - t) ^ 2 := by
        dsimp [x]
        ring
      rw [← hsquare]
      dsimp [L]
      simpa using add_le_add_left hTaylor ‖eval n e t‖

lemma eventually_fineGlobalAccelerationBound_le_two_global :
    ∀ᶠ n : ℕ in atTop,
      fineGlobalAccelerationBound 0 n ≤ 2 * Erdos525.globalAccelerationBound n := by
  have hexp : Erdos525.fineAccelerationExponent 0 ≤ 1 / 8 := by
    have hweak := Erdos525.weakSeparationExponent_le_ten_thousandth 0
    unfold Erdos525.fineAccelerationExponent
    linarith
  have hextra := extraAccelerationBound_tendsto_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Nat.eventually_pos, hextra] with n hn hextraN
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcut : Erdos525.fineAccelerationCutoff 0 n ≤
      Erdos525.accelerationCutoff n := by
    unfold Erdos525.fineAccelerationCutoff Erdos525.accelerationCutoff
      Erdos525.rigidityPower
    exact Real.rpow_le_rpow_of_exponent_le hnOne hexp
  have hcommon : Erdos525.fineGlobalAccelerationBound 0 n ≤
      Erdos525.globalAccelerationBound n := by
    unfold Erdos525.fineGlobalAccelerationBound Erdos525.globalAccelerationBound
    gcongr
  have hglobalOne : (1 : ℝ) ≤ Erdos525.globalAccelerationBound n := by
    unfold Erdos525.globalAccelerationBound Erdos525.accelerationCutoff
      Erdos525.rigidityPower
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow hnOne (by norm_num)
    exact hpow.trans (le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold localMeshHalfWidth; positivity)))
  unfold fineGlobalAccelerationBound
  nlinarith

lemma common_globalAcceleration_endpoint_scaled_oddCount_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Erdos525.globalAccelerationBound n * endpointExclusionRadius n ^ 2 *
        Real.sqrt (2 * n + 2 : ℝ)) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ ↦ (prefixScale n)⁻¹) atTop (𝓝 1) := by
    simpa using prefixScale_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := Erdos525.globalAcceleration_endpoint_scaled_tendsto_zero.mul hratio
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hroot1 : Real.sqrt (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have hroot2 : Real.sqrt (2 * n + 2 : ℝ) ≠ 0 := by positivity
  unfold prefixScale
  field_simp

lemma fineGlobalAcceleration_endpoint_scaled_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 *
        Real.sqrt (2 * n + 2 : ℝ)) atTop (𝓝 0) := by
  have hupper := common_globalAcceleration_endpoint_scaled_oddCount_tendsto_zero.const_mul 2
  simp only [mul_zero] at hupper
  refine squeeze_zero' ?_ ?_ hupper
  · exact Eventually.of_forall fun n ↦
      mul_nonneg
        (mul_nonneg (fineGlobalAccelerationBound_nonneg 0 n) (sq_nonneg _))
        (Real.sqrt_nonneg _)
  · filter_upwards [eventually_fineGlobalAccelerationBound_le_two_global] with n hn
    have hr : 0 ≤ endpointExclusionRadius n ^ 2 := sq_nonneg _
    have hs : 0 ≤ Real.sqrt (2 * n + 2 : ℝ) := Real.sqrt_nonneg _
    calc
      fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 *
          Real.sqrt (2 * n + 2 : ℝ) ≤
        (2 * Erdos525.globalAccelerationBound n) *
          endpointExclusionRadius n ^ 2 * Real.sqrt (2 * n + 2 : ℝ) := by
            gcongr
      _ = 2 * (Erdos525.globalAccelerationBound n *
          endpointExclusionRadius n ^ 2 * Real.sqrt (2 * n + 2 : ℝ)) := by ring

lemma sqrt_oddCount_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.sqrt (2 * n + 2 : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ ↦ (prefixScale n)⁻¹) atTop (𝓝 1) := by
    simpa using prefixScale_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := Erdos525.sqrt_centeredCount_div_tendsto_zero.mul hratio
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot1 : Real.sqrt (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have hroot2 : Real.sqrt (2 * n + 2 : ℝ) ≠ 0 := by positivity
  unfold prefixScale
  field_simp

lemma endpoint_small_value_scaled_tendsto_zero (u : ℝ) :
    Tendsto (fun n : ℕ ↦
      (u / n + fineGlobalAccelerationBound 0 n *
        endpointExclusionRadius n ^ 2) * Real.sqrt (2 * n + 2 : ℝ))
      atTop (𝓝 0) := by
  have hfirst := sqrt_oddCount_div_tendsto_zero.const_mul u
  have hsecond := fineGlobalAcceleration_endpoint_scaled_tendsto_zero
  have hsum := hfirst.add hsecond
  have hsum' : Tendsto (fun n : ℕ ↦
      u * (Real.sqrt (2 * n + 2 : ℝ) / n) +
        fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 *
          Real.sqrt (2 * n + 2 : ℝ)) atTop (𝓝 0) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

lemma eventually_endpoint_small_value_error_lt (u : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      u / n + fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 <
        (Real.sqrt (2 * n + 2 : ℝ))⁻¹ := by
  have hscaled := (endpoint_small_value_scaled_tendsto_zero u).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Nat.eventually_pos, hscaled] with n hn hscaledN
  have hsqrt : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
  rw [inv_eq_one_div, lt_div_iff₀ hsqrt]
  simpa [mul_comm] using hscaledN

lemma eventually_small_value_away_from_endpoints (u : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      ¬HasHighPrefixFineMeshAcceleration 0 n e →
      ¬HasEndpointZero n e →
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
        ‖eval n e t‖ ≤ u / n →
        endpointExclusionRadius n < t ∧
          endpointExclusionRadius n < Real.pi * n - t := by
  filter_upwards [Nat.eventually_pos,
      eventually_endpoint_small_value_error_lt u] with n hn herr
  intro e hgood hendpoint t ht hsmall
  have hnonzero := not_or.mp hendpoint
  have hC : 0 ≤ fineGlobalAccelerationBound 0 n :=
    fineGlobalAccelerationBound_nonneg 0 n
  have hr : 0 ≤ endpointExclusionRadius n := by
    unfold endpointExclusionRadius
    exact rigidityPower_nonneg n _
  constructor
  · by_contra hnot
    have htr : t ≤ endpointExclusionRadius n := le_of_not_gt hnot
    have ht0 : 0 ≤ t := ht.1
    have htSq : t ^ 2 ≤ endpointExclusionRadius n ^ 2 :=
      (sq_le_sq₀ ht0 hr).2 htr
    have hlower := endpoint_zero_lower_via_taylor n hn e hgood hnonzero.1 t ht
    have hupper : ‖eval n e t‖ + fineGlobalAccelerationBound 0 n * t ^ 2 ≤
        u / n + fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left htSq hC)
    exact (not_lt_of_ge (hlower.trans hupper)) herr
  · by_contra hnot
    have htr : Real.pi * n - t ≤ endpointExclusionRadius n := le_of_not_gt hnot
    have ht0 : 0 ≤ Real.pi * n - t := sub_nonneg.mpr ht.2
    have htSq : (Real.pi * n - t) ^ 2 ≤ endpointExclusionRadius n ^ 2 :=
      (sq_le_sq₀ ht0 hr).2 htr
    have hlower := endpoint_pi_lower_via_taylor n hn e hgood hnonzero.2 t ht
    have hupper : ‖eval n e t‖ + fineGlobalAccelerationBound 0 n *
          (Real.pi * n - t) ^ 2 ≤
        u / n + fineGlobalAccelerationBound 0 n * endpointExclusionRadius n ^ 2 :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left htSq hC)
    exact (not_lt_of_ge (hlower.trans hupper)) herr

end Odd

end Erdos525
