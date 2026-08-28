import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneDomains
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneCutoff
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbar

/-!
# Actual smooth representatives away from both deleted axes

Two inner bump functions remove both axes while preserving all germs a
fixed distance from them. An annular compact cutoff localizes the first
Cauchy–Green correction inside the region where those germs agree.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open PeriodTorusLineBundleClassification

theorem exists_smooth_representative_away_axes {f : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (a : ℝ) (ha : 0 < a) :
    ∃ v : ℂ × ℂ → ℂ, ContDiff ℝ ∞ v ∧
      ∀ q, a ≤ ‖q.1‖ → a ≤ ‖q.2‖ → v =ᶠ[𝓝 q] f := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := a / 4
      rOut := a / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let v : ℂ × ℂ → ℂ := fun q => (1 - (b q.1 : ℂ)) * (1 - (b q.2 : ℂ)) * f q
  have hb₁ : ContDiff ℝ ∞ (fun q : ℂ × ℂ => (b q.1 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).comp contDiff_fst
  have hb₂ : ContDiff ℝ ∞ (fun q : ℂ × ℂ => (b q.2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).comp contDiff_snd
  have hv : ContDiff ℝ ∞ v := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq₁ : q.1 = 0
    · have hnear : {p : ℂ × ℂ | p.1 ∈ ball (0 : ℂ) b.rIn} ∈ 𝓝 q :=
        (isOpen_ball.preimage continuous_fst).mem_nhds (by
          change q.1 ∈ ball (0 : ℂ) b.rIn
          rw [hq₁]
          exact mem_ball_self b.rIn_pos)
      have he : v =ᶠ[𝓝 q] (fun _ => 0) := by
        filter_upwards [hnear] with p hp
        simp only [v, b.one_of_mem_closedBall (ball_subset_closedBall hp),
          Complex.ofReal_one, sub_self, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · by_cases hq₂ : q.2 = 0
      · have hnear : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) b.rIn} ∈ 𝓝 q :=
          (isOpen_ball.preimage continuous_snd).mem_nhds (by
            change q.2 ∈ ball (0 : ℂ) b.rIn
            rw [hq₂]
            exact mem_ball_self b.rIn_pos)
        have he : v =ᶠ[𝓝 q] (fun _ => 0) := by
          filter_upwards [hnear] with p hp
          simp only [v, b.one_of_mem_closedBall (ball_subset_closedBall hp),
            Complex.ofReal_one, sub_self, mul_zero, zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq he
      · exact ((contDiffAt_const.sub hb₁.contDiffAt).mul
          (contDiffAt_const.sub hb₂.contDiffAt)).mul
          ((hf q ⟨hq₁, hq₂⟩).contDiffAt (isOpen_domain.mem_nhds ⟨hq₁, hq₂⟩))
  refine ⟨v, hv, ?_⟩
  intro q hq₁ hq₂
  have hout (z : ℂ) (hz : a ≤ ‖z‖) : z ∉ tsupport b := by
    intro hmem
    rw [b.tsupport_eq] at hmem
    have hbound : ‖z‖ ≤ a / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hmem
    linarith
  have hnear₁ : {p : ℂ × ℂ | p.1 ∉ tsupport b} ∈ 𝓝 q :=
    ((isClosed_tsupport b).isOpen_compl.preimage continuous_fst).mem_nhds (hout q.1 hq₁)
  have hnear₂ : {p : ℂ × ℂ | p.2 ∉ tsupport b} ∈ 𝓝 q :=
    ((isClosed_tsupport b).isOpen_compl.preimage continuous_snd).mem_nhds (hout q.2 hq₂)
  filter_upwards [hnear₁, hnear₂] with p hp₁ hp₂
  simp only [v, image_eq_zero_of_notMem_tsupport hp₁, image_eq_zero_of_notMem_tsupport hp₂,
    Complex.ofReal_zero, sub_zero, one_mul]

theorem exists_annular_cutoff (R : ℝ) (hR : 0 < R) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z ∈ closedAnnulus R, χ z = 1) ∧
      ∀ z, χ z ≠ 0 → R⁻¹ / 2 < ‖z‖ := by
  obtain ⟨χ₀, hχ₀, hcχ₀, hχ₀one⟩ := exists_complex_cutoff R hR
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := R⁻¹ / 2
      rOut := R⁻¹
      rIn_pos := by positivity
      rIn_lt_rOut := by have hi := inv_pos.mpr hR; linarith }
  let χ : ℂ → ℂ := fun z => χ₀ z * (1 - (b z : ℂ))
  have hb : ContDiff ℝ ∞ (fun z : ℂ => (b z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨χ, hχ₀.mul (contDiff_const.sub hb), hcχ₀.mul_right, ?_, ?_⟩
  · intro z hz
    have hlo : R⁻¹ ≤ ‖z‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
    have hbz : b z = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hlo)
    simp only [χ, hχ₀one z hz.1, hbz, Complex.ofReal_zero, sub_zero, mul_one]
  · intro z hz
    by_contra hle
    have hm : z ∈ closedBall (0 : ℂ) b.rIn :=
      mem_closedBall_zero_iff.mpr (not_lt.mp hle)
    apply hz
    simp only [χ, b.one_of_mem_closedBall hm, Complex.ofReal_one, sub_self, mul_zero]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
