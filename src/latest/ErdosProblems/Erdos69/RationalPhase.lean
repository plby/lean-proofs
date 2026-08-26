import ErdosProblems.Erdos69.CorrectionAverages
import ErdosProblems.Erdos69.FourierTransfer
import ErdosProblems.Erdos69.TailCancellation

/-! # The Fourier consequence of rationality of the original series -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

@[simp] theorem complexMean_const (μ : FiniteLaw Ω) (c : ℂ) :
    μ.complexMean (fun _ ↦ c) = c := by
  rw [complexMean, ← Finset.sum_mul, ← Complex.ofReal_sum, μ.total]
  simp

theorem norm_phase_mean_sub_one_le (μ : FiniteLaw Ω) (U C : Ω → ℝ)
    (h : ∀ x, ∃ z : ℤ, U x + C x = z) :
    ‖μ.complexMean (fun x ↦ fourierPhase (U x)) - 1‖ ≤
      2 * Real.pi * μ.mean (fun x ↦ |C x|) := by
  have hid (x : Ω) : fourierPhase (U x + C x) = 1 := by
    obtain ⟨z, hz⟩ := h x
    rw [hz, fourierPhase_intCast]
  have hbound := norm_mean_fourierPhase_sub_le μ U (fun x ↦ U x + C x)
  simpa only [hid, complexMean_const, sub_add_cancel_left, abs_neg] using hbound

theorem abs_signed_correction_le {ι : Type*} [Fintype ι] (q : ℝ) (s : ι → ℤ)
    (hs : ∀ i, |(s i : ℝ)| = 1) (a b : ι → ℕ) :
    |q * ∑ i, (s i : ℝ) * compositeCorrection (a i) (b i)| ≤
      |q| * ∑ i, compositeCorrection (a i) (b i) := by
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  calc
    _ ≤ ∑ i, |(s i : ℝ) * compositeCorrection (a i) (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_mul, hs, abs_of_nonneg (compositeCorrection_nonneg _ _)]

theorem rational_signed_tail_phase_le {ι : Type*} [Fintype ι]
    {q : ℕ} {z : ℤ} (h : (q : ℝ) * binaryOmegaSum = z)
    (μ : FiniteLaw Ω) (a : ι → ℕ) (ha : ∀ i, a i ≠ 0)
    (s : ι → ℤ) (hs : ∀ i, |(s i : ℝ)| = 1) (b : Ω → ι → ℕ) :
    ‖μ.complexMean (fun x ↦ fourierPhase
      ((q : ℝ) * ∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (b x i))) - 1‖ ≤
        2 * Real.pi * q * ∑ i, μ.mean (fun x ↦ compositeCorrection (a i) (b x i)) := by
  have hphase := norm_phase_mean_sub_one_le μ
    (fun x ↦ (q : ℝ) * ∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (b x i))
    (fun x ↦ (q : ℝ) * ∑ i, (s i : ℝ) * compositeCorrection (a i) (b x i))
    (fun x ↦ corrected_signed_tail_integer h a (b x) ha s)
  have habs := μ.mean_mono (fun x ↦ abs_signed_correction_le (q : ℝ) s hs a (b x))
  simp only [Nat.abs_cast, mean_const_mul, mean_sum] at habs
  exact hphase.trans (by
    have hmul := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2 * Real.pi)
    simpa only [mul_assoc] using hmul)

end Erdos69.Elementary.FiniteLaw
