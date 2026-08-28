import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianDisk
import Wikipedia.SmoothSixDPoincare.SupportedIsotopyExtension
import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph

/-!
# A supported native isotopy with an exact linear-time chart formula

A smooth bounded time parameter equals the identity on the entire unit
interval. Small cutoff-weighted translations are genuine diffeomorphisms
for every real time, and extend through the actual native partial chart.
The full unit-interval formula and uniform compact support are retained.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def linearTimeCutoff : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def linearTimeParameter (t : ℝ) : ℝ := linearTimeCutoff t * t

theorem linearTimeParameter_smooth : ContDiff ℝ ∞ linearTimeParameter :=
  linearTimeCutoff.contDiff.mul contDiff_id

theorem linearTimeParameter_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    linearTimeParameter t = t := by
  have hβ : linearTimeCutoff t = 1 := linearTimeCutoff.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    change t ≤ 2
    linarith [ht.2])
  rw [linearTimeParameter, hβ, one_mul]

theorem linearTimeParameter_norm_le (t : ℝ) : ‖linearTimeParameter t‖ ≤ 3 := by
  by_cases hβ : linearTimeCutoff t = 0
  · simp only [linearTimeParameter, hβ, zero_mul, norm_zero]
    norm_num
  have ht : t ∈ Function.support (linearTimeCutoff : ℝ → ℝ) := hβ
  rw [linearTimeCutoff.support_eq, mem_ball, Real.dist_eq, sub_zero] at ht
  change |t| < 3 at ht
  rw [Real.norm_eq_abs, linearTimeParameter, abs_mul,
    abs_of_nonneg linearTimeCutoff.nonneg]
  exact (mul_le_of_le_one_left (abs_nonneg t) linearTimeCutoff.le_one).trans ht.le

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_small_linear_time_bump_isotopy
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hsource : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∃ (A : ℝ × M → M) (K : Set M),
        IsCompact K ∧ K ⊆ Φ.target ∧ ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = A (t, y)) ∧
        (∀ t y, y ∉ K → A (t, y) = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Φ.source,
          x + (t * β x) • a ∈ Φ.source) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Φ.source,
          A (t, Φ x) = Φ (x + (t * β x) • a) := by
  obtain ⟨δ, hδ, hsmall⟩ := SmallPerturbation.exists_radius_bumpTranslation hβ hc
  refine ⟨δ / 4, by positivity, ?_⟩
  intro a ha
  let B : ℝ × E → E := fun z => z.2 + β z.2 • (linearTimeParameter z.1 • a)
  have htime : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ linearTimeParameter :=
    linearTimeParameter_smooth.contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B :=
    contMDiff_snd.add ((hβ.contMDiff.comp contMDiff_snd).smul
      ((htime.comp contMDiff_fst).smul contMDiff_const))
  have hB0 : ∀ x, B (0, x) = x := by
    intro x
    simp only [B, linearTimeParameter_eq (left_mem_Icc.mpr zero_le_one),
      zero_smul, smul_zero, add_zero]
  have hdiff : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x, d x = B (t, x) := by
    intro t
    have hnorm : ‖linearTimeParameter t • a‖ < δ := by
      rw [norm_smul]
      have hh := mul_le_mul_of_nonneg_right (linearTimeParameter_norm_le t) (norm_nonneg a)
      nlinarith
    obtain ⟨d, hd, -⟩ := hsmall (linearTimeParameter t • a) hnorm
    exact ⟨d, hd⟩
  have hfix : ∀ t x, x ∉ tsupport β → B (t, x) = x := by
    intro t x hx
    have hz : β x = 0 := by
      by_contra hne
      exact hx (subset_tsupport β hne)
    simp only [B, hz, zero_smul, add_zero]
  obtain ⟨A, K, hK, hKΦ, hA, hA0, hAd, hAf, hBs, hformula⟩ :=
    exists_supported_isotopy_extension Φ hB hB0 hdiff hc.isCompact hsource hfix
  have hmodel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      B (t, x) = x + (t * β x) • a := by
    dsimp only [B]
    rw [linearTimeParameter_eq ht, smul_smul, mul_comm (β x) t]
  refine ⟨A, K, hK, hKΦ, hA, hA0, hAd, hAf, ?_, ?_⟩
  · intro t ht x hx
    rw [← hmodel t ht x]
    exact hBs t hx
  · intro t ht x hx
    rw [hformula t x hx, hmodel t ht x]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
