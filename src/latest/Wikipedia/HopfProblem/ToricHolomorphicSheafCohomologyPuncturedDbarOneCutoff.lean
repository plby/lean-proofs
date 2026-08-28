import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneDomains
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneCutoff

/-!
# Actual smooth extension away from the deleted coordinate

An inner cutoff removes the singular coordinate and preserves the germ at
every point a fixed positive distance from it. No closedness is imposed
on the resulting global smooth representative.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

theorem exists_smooth_representative_away_zero {f : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (a : ℝ) (ha : 0 < a) :
    ∃ v : ℂ × ℂ → ℂ, ContDiff ℝ ∞ v ∧
      ∀ q, a ≤ ‖q.2‖ → v =ᶠ[𝓝 q] f := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := a / 4
      rOut := a / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let v : ℂ × ℂ → ℂ := fun q => (1 - (b q.2 : ℂ)) * f q
  have hb : ContDiff ℝ ∞ (fun q : ℂ × ℂ => (b q.2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).comp contDiff_snd
  have hv : ContDiff ℝ ∞ v := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2 ≠ 0
    · exact (contDiffAt_const.sub hb.contDiffAt).mul
        ((hf q hq).contDiffAt (isOpen_domain.mem_nhds hq))
    · have hq0 : q.2 = 0 := not_ne_iff.mp hq
      have hnear : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) b.rIn} ∈ 𝓝 q :=
        (isOpen_ball.preimage continuous_snd).mem_nhds (by
          change q.2 ∈ ball (0 : ℂ) b.rIn
          rw [hq0]
          exact mem_ball_self b.rIn_pos)
      have he : v =ᶠ[𝓝 q] (fun _ => 0) := by
        filter_upwards [hnear] with p hp
        simp only [v, b.one_of_mem_closedBall (ball_subset_closedBall hp),
          Complex.ofReal_one, sub_self, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨v, hv, ?_⟩
  intro q hq
  have hout : q.2 ∉ tsupport b := by
    intro hmem
    rw [b.tsupport_eq] at hmem
    have hbound : ‖q.2‖ ≤ a / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hmem
    linarith
  have hnear : {p : ℂ × ℂ | p.2 ∉ tsupport b} ∈ 𝓝 q :=
    ((isClosed_tsupport b).isOpen_compl.preimage continuous_snd).mem_nhds hout
  filter_upwards [hnear] with p hp
  simp only [v, image_eq_zero_of_notMem_tsupport hp, Complex.ofReal_zero,
    sub_zero, one_mul]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
