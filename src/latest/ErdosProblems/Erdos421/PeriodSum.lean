import ErdosProblems.Erdos421.FirstDerivativeSum
import ErdosProblems.Erdos421.PhasePeriod

/-! # A first-derivative sum test away from integral multiples of a period -/

namespace Erdos421

theorem periodic_increment_sum_bound (f : ℕ → ℝ) (N : ℕ) {δ : ℝ}
    (hanti : AntitoneOn (phaseIncrement f) (Set.Icc 0 N)) (hδ : 0 < δ)
    (hlo : δ ≤ phaseIncrement f N) (hhi : phaseIncrement f 0 ≤ 2 * Real.pi - δ) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤ 12 / δ := by
  let d := phaseIncrement f
  let w : ℕ → ℂ := fun n ↦ oscillatoryPhase 1 (f n)
  let a : ℕ → ℂ := fun n ↦ phaseReciprocal (d n)
  have hanti' {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : d j ≤ d i :=
    hanti ⟨Nat.zero_le i, hij.trans hj⟩ ⟨Nat.zero_le j, hj⟩ hij
  have hdlo : ∀ n, n ≤ N → δ ≤ d n := fun n hn ↦ hlo.trans (hanti' hn le_rfl)
  have hdhi : ∀ n, n ≤ N → d n ≤ 2 * Real.pi - δ :=
    fun n hn ↦ (hanti' (Nat.zero_le n) hn).trans hhi
  have hnormw : ∀ n, ‖w n‖ = 1 := fun n ↦ norm_oscillatoryPhase 1 (f n)
  have hterm : ∀ n ∈ Finset.range N, w n = (w (n + 1) - w n) * a n := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_range.mp hn).le
    have hnhi := hdhi n hnN
    have hne := phase_sub_one_ne_zero_period (hδ.trans_le (hdlo n hnN)) (by linarith)
    change w n = (w (n + 1) - w n) * (oscillatoryPhase 1 (d n) - 1)⁻¹
    have hstep : w (n + 1) = w n * oscillatoryPhase 1 (d n) := phase_increment_step f n
    rw [hstep, ← mul_sub_one, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hid : (∑ n ∈ Finset.range N, w n) = w N * a N - w 0 * a 0 -
      ∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n) := by
    rw [Finset.sum_congr rfl hterm]
    exact sum_difference_mul w a N
  have hvar : ∀ n ∈ Finset.range N, ‖a (n + 1) - a n‖ ≤
      phaseVariationWeight (d (n + 1)) - phaseVariationWeight (d n) := by
    intro n hn
    have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
    have hnhi := hdhi n (by omega)
    have h := phaseReciprocal_variation_period (hδ.trans_le (hdlo (n + 1) hnN))
      (hanti' (Nat.le_succ n) hnN) (by linarith)
    simpa only [a, norm_sub_rev] using h
  have hsum : ‖∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n)‖ ≤
      phaseVariationWeight (d N) - phaseVariationWeight (d 0) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖w (n + 1) * (a (n + 1) - a n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖a (n + 1) - a n‖ := by
        simp only [norm_mul, hnormw, one_mul]
      _ ≤ ∑ n ∈ Finset.range N,
          (phaseVariationWeight (d (n + 1)) - phaseVariationWeight (d n)) := Finset.sum_le_sum hvar
      _ = _ := Finset.sum_range_sub (fun n ↦ phaseVariationWeight (d n)) N
  have hvarbound : phaseVariationWeight (d N) - phaseVariationWeight (d 0) ≤ 8 / δ := by
    have hloinv : 4 / d N ≤ 4 / δ := div_le_div_of_nonneg_left (by norm_num) hδ hlo
    have h0hi := hdhi 0 (Nat.zero_le N)
    have hNhi := hdhi N le_rfl
    have hhiinv : 4 / (2 * Real.pi - d 0) ≤ 4 / δ :=
      div_le_div_of_nonneg_left (by norm_num) hδ (by linarith)
    have hNpos : 0 ≤ 4 / (2 * Real.pi - d N) := by
      apply div_nonneg (by norm_num)
      linarith
    have h0pos : 0 ≤ 4 / d 0 := div_nonneg (by norm_num) (hδ.trans_le (hdlo 0 (Nat.zero_le N))).le
    unfold phaseVariationWeight
    simp only [div_eq_mul_inv] at hloinv hhiinv hNpos h0pos ⊢
    linarith
  have haN : ‖a N‖ ≤ 2 / δ := phaseReciprocal_norm_le_period hδ hlo (hdhi N le_rfl)
  have ha0 : ‖a 0‖ ≤ 2 / δ :=
    phaseReciprocal_norm_le_period hδ (hdlo 0 (Nat.zero_le N)) hhi
  have hendpoint : ‖w N * a N - w 0 * a 0‖ ≤ 4 / δ := by
    have h := norm_sub_le (w N * a N) (w 0 * a 0)
    simp only [norm_mul, hnormw, one_mul] at h
    simp only [div_eq_mul_inv] at haN ha0 ⊢
    linarith
  have htotal := (norm_sub_le (w N * a N - w 0 * a 0)
    (∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n))).trans
      (add_le_add hendpoint (hsum.trans hvarbound))
  change ‖∑ n ∈ Finset.range N, w n‖ ≤ 12 / δ
  rw [hid]
  simp only [div_eq_mul_inv] at htotal ⊢
  linarith

theorem oscillatoryPhase_sub_two_pi_int (x : ℝ) (j : ℤ) :
    oscillatoryPhase 1 (x - 2 * Real.pi * j) = oscillatoryPhase 1 x := by
  have heq : Complex.I * (x - 2 * Real.pi * j : ℝ) =
      Complex.I * (x : ℂ) + (-j : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [oscillatoryPhase, Complex.ofReal_one, mul_one]
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem phaseIncrement_sub_linear (f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    phaseIncrement (fun n ↦ f n - c * n) n = phaseIncrement f n - c := by
  simp only [phaseIncrement, Nat.cast_add, Nat.cast_one]
  ring

theorem integer_band_increment_sum_bound (f : ℕ → ℝ) (N : ℕ) (j : ℤ) {δ : ℝ}
    (hanti : AntitoneOn (phaseIncrement f) (Set.Icc 0 N)) (hδ : 0 < δ)
    (hlo : 2 * Real.pi * j + δ ≤ phaseIncrement f N)
    (hhi : phaseIncrement f 0 ≤ 2 * Real.pi * (j + 1) - δ) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤ 12 / δ := by
  let g : ℕ → ℝ := fun n ↦ f n - (2 * Real.pi * j) * n
  have hg : ∀ n, phaseIncrement g n = phaseIncrement f n - 2 * Real.pi * j :=
    phaseIncrement_sub_linear f _
  have hga : AntitoneOn (phaseIncrement g) (Set.Icc 0 N) := by
    intro i hi k hk hik
    rw [hg, hg]
    exact sub_le_sub_right (hanti hi hk hik) _
  have hgl : δ ≤ phaseIncrement g N := by rw [hg]; linarith
  have hgh : phaseIncrement g 0 ≤ 2 * Real.pi - δ := by rw [hg]; nlinarith
  have h := periodic_increment_sum_bound g N hga hδ hgl hgh
  have heq : ∀ n, oscillatoryPhase 1 (g n) = oscillatoryPhase 1 (f n) := by
    intro n
    have hjn := oscillatoryPhase_sub_two_pi_int (f n) (j * (n : ℤ))
    simpa only [Int.cast_mul, Int.cast_natCast, mul_assoc, g] using hjn
  simpa only [heq] using h

end Erdos421
