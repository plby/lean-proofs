import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Derivative estimates for locally uniform holomorphic limits

The Schwarz estimate controls differences of Fréchet derivatives on a smaller ball.
Consequently, a uniformly Cauchy family of holomorphic maps has uniformly Cauchy
derivatives there.  Both domain and target can be arbitrary complex normed spaces.
-/

noncomputable section

open Set Metric Filter
open scoped Topology Uniformity

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bound on a holomorphic difference on a ball controls its derivative on the
concentric ball of half the radius. -/
theorem norm_fderiv_sub_le_of_ball_bound {f g : E → F} {c y : E} {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c (2 * r)))
    (hg : DifferentiableOn ℂ g (ball c (2 * r)))
    (hfg : ∀ z ∈ ball c (2 * r), ‖f z - g z‖ ≤ C) (hy : y ∈ ball c r) :
    ‖fderiv ℂ f y - fderiv ℂ g y‖ ≤ 2 * C / r := by
  have hball : ball y r ⊆ ball c (2 * r) := by
    intro z hz
    exact (dist_triangle z y c).trans_lt (by
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      linarith)
  have hy' : y ∈ ball c (2 * r) := hball (mem_ball_self hr)
  have hmaps : MapsTo (fun z => f z - g z) (ball y r)
      (closedBall (f y - g y) (2 * C)) := by
    intro z hz
    rw [mem_closedBall]
    exact (dist_le_norm_add_norm _ _).trans (by
      have hz' := hfg z (hball hz)
      have hy'' := hfg y hy'
      linarith)
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball
    ((hf.sub hg).mono hball) hmaps hr
  rwa [fderiv_sub (hf.differentiableAt (isOpen_ball.mem_nhds hy'))
    (hg.differentiableAt (isOpen_ball.mem_nhds hy'))] at h

/-- Uniformly Cauchy holomorphic maps have uniformly Cauchy Fréchet derivatives on
a smaller ball.  Holomorphicity is only required eventually in the indexing filter. -/
theorem uniformCauchySeqOn_fderiv_ball {seq : ι → E → F} {φ : Filter ι} {c : E} {r : ℝ}
    (hr : 0 < r) (hf : UniformCauchySeqOn seq φ (ball c (2 * r)))
    (hseq : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) (ball c (2 * r))) :
    UniformCauchySeqOn (fun n => fderiv ℂ (seq n)) φ (ball c r) := by
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  have hδ : 0 < ε * r / 4 := by positivity
  have hpair : ∀ᶠ p : ι × ι in φ ×ˢ φ,
      DifferentiableOn ℂ (seq p.1) (ball c (2 * r)) ∧
        DifferentiableOn ℂ (seq p.2) (ball c (2 * r)) := hseq.prod_mk hseq
  filter_upwards [hf _ (Metric.dist_mem_uniformity hδ), hpair] with p hp hpd y hy
  apply hεV
  rw [dist_eq_norm]
  have hbound : ∀ z ∈ ball c (2 * r), ‖seq p.1 z - seq p.2 z‖ ≤ ε * r / 4 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm] using hp z hz)
  have h := norm_fderiv_sub_le_of_ball_bound hr hpd.1 hpd.2 hbound hy
  have heq : 2 * (ε * r / 4) / r = ε / 2 := by field_simp; ring
  exact h.trans_lt (by rw [heq]; linarith)

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
