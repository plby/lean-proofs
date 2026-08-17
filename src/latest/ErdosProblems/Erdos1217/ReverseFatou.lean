import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# A uniform-second-moment reverse Fatou lemma

This file isolates the measure-theoretic compactness argument used in the
proof of Erdős problem 1217.  Ordinary Fatou gives the inequality in the
opposite direction.  A uniform second-moment bound supplies uniform
integrability, and truncation then gives the reverse inequality for `limsup`.
-/

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace Erdos1217

private lemma nnreal_le_min_add_sq_div (x c : NNReal) (hc : 0 < c) :
    x ≤ min x c + x ^ 2 / c := by
  by_cases hxc : x ≤ c
  · rw [min_eq_left hxc]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right (le_of_not_ge hxc)]
    have htail : x ≤ x ^ 2 / c := by
      rw [le_div_iff₀ hc]
      simpa [pow_two] using mul_le_mul_right (le_of_not_ge hxc) x
    exact htail.trans (le_add_of_nonneg_left (by positivity))

private lemma ennreal_le_min_add_sq_div {x c : ℝ≥0∞} (hx : x ≠ ∞)
    (hc : c ≠ 0) (hctop : c ≠ ∞) : x ≤ min x c + x ^ 2 / c := by
  lift x to NNReal using hx
  lift c to NNReal using hctop
  have hc' : 0 < c := pos_iff_ne_zero.mpr (by simpa using hc)
  rw [← ENNReal.coe_min, ← ENNReal.coe_pow, ← ENNReal.coe_div hc'.ne']
  exact_mod_cast nnreal_le_min_add_sq_div x c hc'

/-- The quantitative truncation estimate behind the reverse-Fatou argument.
The hypotheses say that all values are finite and the second moments are
bounded by the same finite number `M`. -/
lemma lintegral_le_truncated_add_secondMoment_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    (hfinite : ∀ n ω, X n ω ≠ ∞) {M c : ℝ≥0∞}
    (hsecond : ∀ n, ∫⁻ ω, (X n ω) ^ 2 ∂μ ≤ M)
    (hc : c ≠ 0) (hctop : c ≠ ∞) (n : ℕ) :
    (∫⁻ ω, X n ω ∂μ) ≤ (∫⁻ ω, min (X n ω) c ∂μ) + M / c := by
  calc
    (∫⁻ ω, X n ω ∂μ) ≤
        ∫⁻ ω, min (X n ω) c + (X n ω) ^ 2 / c ∂μ :=
      lintegral_mono fun ω => ennreal_le_min_add_sq_div (hfinite n ω) hc hctop
    _ = (∫⁻ ω, min (X n ω) c ∂μ) + (∫⁻ ω, (X n ω) ^ 2 ∂μ) / c := by
      rw [lintegral_add_left ((hX n).min measurable_const)]
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ ((hX n).pow_const 2)]
    _ ≤ (∫⁻ ω, min (X n ω) c ∂μ) + M / c := by
      gcongr
      exact hsecond n

/-- Reverse Fatou for nonnegative random variables with uniformly bounded
second moments.  The probability-space assumption is only used to make every
constant truncation integrable. -/
theorem limsup_lintegral_le_lintegral_limsup_of_uniform_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    (hfinite : ∀ n ω, X n ω ≠ ∞) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hsecond : ∀ n, ∫⁻ ω, (X n ω) ^ 2 ∂μ ≤ M) :
    limsup (fun n => ∫⁻ ω, X n ω ∂μ) atTop ≤
      ∫⁻ ω, limsup (fun n => X n ω) atTop ∂μ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε htarget
  let c : ℝ≥0∞ := M / (ε : ℝ≥0∞) + 1
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have hctop : c ≠ ∞ := by
    dsimp [c]
    finiteness
  have htail : M / c ≤ (ε : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff hc0 hctop]
    dsimp [c]
    calc
      M ≤ M + (ε : ℝ≥0∞) := le_add_of_nonneg_right (by positivity)
      _ = (ε : ℝ≥0∞) * (M / (ε : ℝ≥0∞) + 1) := by
        rw [mul_add, mul_one, ENNReal.mul_div_cancel hε0 ENNReal.coe_ne_top]
  have hseq : ∀ n,
      (∫⁻ ω, X n ω ∂μ) ≤ (∫⁻ ω, min (X n ω) c ∂μ) + M / c :=
    fun n => lintegral_le_truncated_add_secondMoment_div X hX hfinite hsecond hc0 hctop n
  calc
    limsup (fun n => ∫⁻ ω, X n ω ∂μ) atTop ≤
        limsup (fun n => (∫⁻ ω, min (X n ω) c ∂μ) + M / c) atTop :=
      limsup_le_limsup (Eventually.of_forall hseq)
    _ = limsup (fun n => ∫⁻ ω, min (X n ω) c ∂μ) atTop + M / c := by
      exact limsup_add_const atTop (fun n => ∫⁻ ω, min (X n ω) c ∂μ) (M / c)
        (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ (∫⁻ ω, limsup (fun n => min (X n ω) c) atTop ∂μ) + M / c := by
      gcongr
      refine limsup_lintegral_le (fun _ : Ω => c) (fun n => (hX n).min measurable_const)
        (fun n => ae_of_all μ fun ω => min_le_right _ _) ?_
      simp [hctop]
    _ ≤ (∫⁻ ω, limsup (fun n => X n ω) atTop ∂μ) + M / c := by
      gcongr
      exact limsup_le_limsup (Eventually.of_forall fun n => min_le_left (X n ω) c)
    _ ≤ (∫⁻ ω, limsup (fun n => X n ω) atTop ∂μ) + ε :=
      add_le_add (le_refl _) htail

/-- If the integral of a nonnegative function is at least `δ`, some point has
value at least `δ`.  The conclusion can avoid any prescribed null set. -/
lemma exists_ge_of_le_lintegral_away_null
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} {δ : ℝ≥0∞} {N : Set Ω}
    (hδtop : δ ≠ ∞) (hδ : δ ≤ ∫⁻ ω, f ω ∂μ) (hN : μ N = 0) :
    ∃ ω ∉ N, δ ≤ f ω := by
  by_cases hint : (∫⁻ ω, f ω ∂μ) = ∞
  · by_contra! h
    have hae : ∀ᵐ ω ∂μ, f ω ≤ δ := by
      filter_upwards [compl_mem_ae_iff.2 hN] with ω hω
      exact (h ω hω).le
    have hle : (∫⁻ ω, f ω ∂μ) ≤ δ := by
      calc
        (∫⁻ ω, f ω ∂μ) ≤ ∫⁻ _ : Ω, δ ∂μ := lintegral_mono_ae hae
        _ = δ := by simp
    exact hδtop (top_unique (hint ▸ hle))
  · obtain ⟨ω, hωN, hω⟩ := exists_notMem_null_lintegral_le hint hN
    exact ⟨ω, hωN, hδ.trans hω⟩

/-- Extraction from the reverse-Fatou conclusion. -/
theorem exists_limsup_ge_of_uniform_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    (hfinite : ∀ n ω, X n ω ≠ ∞) {M δ : ℝ≥0∞} (hM : M ≠ ∞)
    (hsecond : ∀ n, ∫⁻ ω, (X n ω) ^ 2 ∂μ ≤ M)
    (hmean : δ ≤ limsup (fun n => ∫⁻ ω, X n ω ∂μ) atTop)
    (hδtop : δ ≠ ∞) {N : Set Ω} (hN : μ N = 0) :
    ∃ ω ∉ N, δ ≤ limsup (fun n => X n ω) atTop := by
  apply exists_ge_of_le_lintegral_away_null hδtop
    (hmean.trans (limsup_lintegral_le_lintegral_limsup_of_uniform_secondMoment
      X hX hfinite hM hsecond)) hN

end Erdos1217
