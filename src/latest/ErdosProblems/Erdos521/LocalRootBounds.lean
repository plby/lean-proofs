/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Local root-count probability bounds from Jensen and maximal moments.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.JensenDisk
import ErdosProblems.Erdos521.CircularMaximal
import ErdosProblems.Erdos521.RootStatistics

namespace Erdos521

open MeasureTheory Filter Metric
open scoped BigOperators

/-- Distinct real roots within distance `r` of `c`. -/
noncomputable def localRootCount (ε : ℕ → ℝ) (n : ℕ) (c r : ℝ) : ℕ := by
  classical
  exact ((realRoots ε n).filter fun x ↦ |x - c| ≤ r).card

theorem localRootCount_aemeasurable (n : ℕ) (c r : ℝ) :
    AEMeasurable (fun ε ↦ localRootCount ε n c r) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro a b hab
  rw [localRootCount, localRootCount, realRoots_congr_prefix a b n hab]

theorem complex_polynomial_eval (ε : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ((polynomial ε n).map Complex.ofRealHom).eval z = complexPowerSum ε n z := by
  simp [polynomial, complexPowerSum, Polynomial.map_sum, Polynomial.eval_finsetSum]

theorem localRootCount_pow_le (n m : ℕ) (hm : m ≤ n) (c : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (ε : ℕ → ℝ) (hε : |ε 0| = 1)
    (hcenter : δ ≤ |powerSum ε (m + 1) c|) :
    δ ^ 2 * (4 : ℝ) ^ localRootCount ε m c r ≤
      2 * circularMaximum n (c : ℂ) (4 * r) ε := by
  classical
  let T := (realRoots ε m).filter fun x ↦ |x - c| ≤ r
  let S := T.image (fun x : ℝ ↦ (x : ℂ))
  have hcard : S.card = localRootCount ε m c r :=
    Finset.card_image_of_injective T Complex.ofReal_injective
  have hε₀ : ε 0 ≠ 0 := by
    intro hz
    simp [hz] at hε
  have hS : ∀ z ∈ S, z ∈ closedBall (c : ℂ) r ∧
      ((polynomial ε m).map Complex.ofRealHom).eval z = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxroot, hxdist⟩ := Finset.mem_filter.mp hx
    constructor
    · simpa only [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hxdist
    · rw [complex_polynomial_eval, complexPowerSum_ofReal,
        (mem_realRoots ε m hε₀ x).mp hxroot]
      simp
  have h := polynomial_zeros_pow_le ((polynomial ε m).map Complex.ofRealHom) (c : ℂ)
    hδ (by simpa only [complex_polynomial_eval, complexPowerSum_ofReal,
      Complex.norm_real, Real.norm_eq_abs] using hcenter) hr
    (circularMaximum_one_le n (c : ℂ) (4 * r) ε hε)
    (by simpa only [complex_polynomial_eval] using
      circleAverage_powerSum_sq_le n m hm (c : ℂ) (4 * r) ε) S hS
  rwa [hcard] at h

theorem measureReal_le_integral_div_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hnonneg : 0 ≤ᵐ[μ] f) {t : ℝ} (ht : 0 < t) {E : Set Ω}
    (hE : ∀ᵐ ω ∂μ, ω ∈ E → t ≤ f ω) :
    μ.real E ≤ (∫ ω, f ω ∂μ) / t := by
  have hmono : μ E ≤ μ {ω | t ≤ f ω} := measure_mono_ae hE
  have hreal : μ.real E ≤ μ.real {ω | t ≤ f ω} :=
    ENNReal.toReal_mono (measure_ne_top μ _) hmono
  apply hreal.trans
  apply (le_div_iff₀ ht).mpr
  have h := mul_meas_ge_le_integral_of_nonneg hnonneg hf t
  simpa only [mul_comm] using h

/-- The count can be large only when the boundary maximum is large or the
polynomial at the center is small. This estimate handles the first event. -/
theorem localRootCount_large_center_probability (n k : ℕ) (c : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) :
    sequenceLaw.real {ε | ∃ m ≤ n, δ ≤ |powerSum ε (m + 1) c| ∧
      k ≤ localRootCount ε m c r} ≤
      2 * (geometricVariance (‖(c : ℂ)‖ + |4 * r|) (n + 1) *
        (1 + Real.log (n + 1))) / (δ ^ 2 * (4 : ℝ) ^ k) := by
  have ht : 0 < δ ^ 2 * (4 : ℝ) ^ k / 2 := by positivity
  have h := measureReal_le_integral_div_of_ae sequenceLaw
    (E := {ε | ∃ m ≤ n, δ ≤ |powerSum ε (m + 1) c| ∧ k ≤ localRootCount ε m c r})
    (circularMaximum_integrable n (c : ℂ) (4 * r))
    (Eventually.of_forall (circularMaximum_nonneg n (c : ℂ) (4 * r))) ht ?_
  · apply h.trans
    have hmean := integral_circleAverage_maximum_le n (c : ℂ) (4 * r)
    change (∫ ε, circularMaximum n (c : ℂ) (4 * r) ε ∂sequenceLaw) ≤ _ at hmean
    have hdiv := div_le_div_of_nonneg_right hmean ht.le
    convert hdiv using 1
    ring
  · filter_upwards [ae_sequence_signs] with ε hε hEvent
    obtain ⟨m, hm, hcenter, hk⟩ := hEvent
    have hsign : |ε 0| = 1 := by rcases hε 0 with h | h <;> simp [h]
    have hJ := localRootCount_pow_le n m hm c hr hδ ε hsign hcenter
    have hp : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ localRootCount ε m c r :=
      pow_le_pow_right₀ (by norm_num) hk
    have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg δ)
    linarith

end Erdos521
