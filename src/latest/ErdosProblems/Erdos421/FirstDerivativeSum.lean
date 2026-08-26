import ErdosProblems.Erdos421.PhaseReciprocalPi

/-! # A first-derivative exponential-sum bound for small monotone increments -/

namespace Erdos421

theorem sum_difference_mul (w a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (w (n + 1) - w n) * a n) =
      w N * a N - w 0 * a 0 - ∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

def phaseIncrement (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

theorem phase_increment_step (f : ℕ → ℝ) (n : ℕ) :
    oscillatoryPhase 1 (f (n + 1)) =
      oscillatoryPhase 1 (f n) * oscillatoryPhase 1 (phaseIncrement f n) := by
  unfold oscillatoryPhase phaseIncrement
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A quantitative first-derivative test with all constants explicit.
Only the actual successive phase increments, in radians, enter the hypotheses. -/
theorem monotone_increment_sum_bound_pi (f : ℕ → ℝ) (N : ℕ)
    (hanti : AntitoneOn (phaseIncrement f) (Set.Icc 0 N)) (hpos : 0 < phaseIncrement f N)
    (hpi : phaseIncrement f 0 ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤ 8 / phaseIncrement f N := by
  let d := phaseIncrement f
  let w : ℕ → ℂ := fun n ↦ oscillatoryPhase 1 (f n)
  let a : ℕ → ℂ := fun n ↦ phaseReciprocal (d n)
  have hanti' {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : d j ≤ d i :=
    hanti ⟨Nat.zero_le i, hij.trans hj⟩ ⟨Nat.zero_le j, hj⟩ hij
  have hdpos : ∀ n, n ≤ N → 0 < d n := fun n hn ↦ hpos.trans_le (hanti' hn le_rfl)
  have hdpi : ∀ n, n ≤ N → d n ≤ Real.pi :=
    fun n hn ↦ (hanti' (Nat.zero_le n) hn).trans hpi
  have hnormw : ∀ n, ‖w n‖ = 1 := fun n ↦ norm_oscillatoryPhase 1 (f n)
  have hterm : ∀ n ∈ Finset.range N, w n = (w (n + 1) - w n) * a n := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_range.mp hn).le
    have hne := phase_sub_one_ne_zero_pi (hdpos n hnN) (hdpi n hnN)
    change w n = (w (n + 1) - w n) * (oscillatoryPhase 1 (d n) - 1)⁻¹
    have hstep : w (n + 1) = w n * oscillatoryPhase 1 (d n) := phase_increment_step f n
    rw [hstep, ← mul_sub_one, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hid : (∑ n ∈ Finset.range N, w n) = w N * a N - w 0 * a 0 -
      ∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n) := by
    rw [Finset.sum_congr rfl hterm]
    exact sum_difference_mul w a N
  have hvar : ∀ n ∈ Finset.range N, ‖a (n + 1) - a n‖ ≤ 4 / d (n + 1) - 4 / d n := by
    intro n hn
    have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
    have h := phaseReciprocal_variation_pi (hdpos (n + 1) hnN)
      (hanti' (Nat.le_succ n) hnN) (hdpi n (by omega))
    simpa only [a, norm_sub_rev] using h
  have hsum : ‖∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n)‖ ≤
      4 / d N - 4 / d 0 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖w (n + 1) * (a (n + 1) - a n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖a (n + 1) - a n‖ := by simp only [norm_mul, hnormw, one_mul]
      _ ≤ ∑ n ∈ Finset.range N, (4 / d (n + 1) - 4 / d n) := Finset.sum_le_sum hvar
      _ = _ := Finset.sum_range_sub (fun n ↦ 4 / d n) N
  have haN : ‖a N‖ ≤ 2 / d N := phaseReciprocal_norm_le_pi hpos (hdpi N le_rfl)
  have ha0 : ‖a 0‖ ≤ 2 / d 0 := phaseReciprocal_norm_le_pi (hdpos 0 (Nat.zero_le N)) hpi
  have hendpoint : ‖w N * a N - w 0 * a 0‖ ≤ 2 / d N + 2 / d 0 := by
    have h := norm_sub_le (w N * a N) (w 0 * a 0)
    simp only [norm_mul, hnormw, one_mul] at h
    exact h.trans (add_le_add haN ha0)
  have h0 : 0 ≤ 1 / d 0 := (one_div_pos.mpr (hdpos 0 (Nat.zero_le N))).le
  have hN : 0 ≤ 1 / d N := by positivity
  have htotal := (norm_sub_le (w N * a N - w 0 * a 0)
    (∑ n ∈ Finset.range N, w (n + 1) * (a (n + 1) - a n))).trans
      (add_le_add hendpoint hsum)
  change ‖∑ n ∈ Finset.range N, w n‖ ≤ 8 / d N
  rw [hid]
  simp only [div_eq_mul_inv] at htotal h0 hN ⊢
  linarith

theorem monotone_increment_sum_bound (f : ℕ → ℝ) (N : ℕ)
    (hanti : Antitone (phaseIncrement f)) (hpos : 0 < phaseIncrement f N)
    (hone : phaseIncrement f 0 ≤ 1) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤ 8 / phaseIncrement f N := by
  apply monotone_increment_sum_bound_pi f N (fun _ _ _ _ hij ↦ hanti hij) hpos
  exact hone.trans (by linarith [Real.one_le_pi_div_two])

end Erdos421
