import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyLimitEstimates
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyLimitFilter
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Multivariable Weierstrass theorem

Locally uniform limits of holomorphic maps on open subsets of a finite-dimensional
complex normed space are holomorphic. Their Fréchet derivatives also converge
locally uniformly. The derivative convergence is proved from Schwarz's estimate
and completeness, rather than assumed.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : Filter ι} [φ.NeBot] {seq : ι → E → F} {f : E → F}

/-- Uniform convergence on a ball gives holomorphicity of the limit and uniform
convergence of derivatives on the concentric ball of half the radius. -/
theorem differentiableOn_and_tendstoUniformlyOn_fderiv_ball {c : E} {r : ℝ}
    (hr : 0 < r) (hf : TendstoUniformlyOn seq f φ (ball c (2 * r)))
    (hseq : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) (ball c (2 * r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (seq n)) (fderiv ℂ f) φ (ball c r) := by
  have hsub : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  have hC := uniformCauchySeqOn_fderiv_ball hr hf.uniformCauchySeqOn hseq
  obtain ⟨g', hg'⟩ := exists_tendstoUniformlyOn_of_uniformCauchySeqOn hC
  have hseq' : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) (ball c r) :=
    hseq.mono fun _ hn => hn.mono hsub
  have hd : ∀ y ∈ ball c r, HasFDerivAt f (g' y) y := by
    intro y hy
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn_eventually_differentiableOn
      isOpen_ball hg'.tendstoLocallyUniformlyOn hseq'
      (fun z hz => hf.tendsto_at (hsub hz)) hy
  refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact hg'.congr_right fun y hy => (hd y hy).fderiv.symm

variable [FiniteDimensional ℂ E] {U : Set E}

/-- Every point has a ball on which the limit is holomorphic and its Fréchet
derivative is the uniform limit of the derivatives of the family. -/
theorem exists_ball_differentiableOn_and_tendstoUniformlyOn_fderiv
    (hf : TendstoLocallyUniformlyOn seq f φ U)
    (hseq : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) U)
    (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ r > 0, ball x r ⊆ U ∧ DifferentiableOn ℂ f (ball x r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (seq n)) (fderiv ℂ f) φ (ball x r) := by
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hconv : TendstoUniformlyOn seq f φ (closedBall x R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x R)).mp (hf.mono hRU)
  have hrad : 2 * (R / 2) = R := by ring
  have houter : ball x (2 * (R / 2)) ⊆ closedBall x R := by
    rw [hrad]
    exact ball_subset_closedBall
  have hseq' : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) (ball x (2 * (R / 2))) :=
    hseq.mono fun _ hn => hn.mono (houter.trans hRU)
  have h := differentiableOn_and_tendstoUniformlyOn_fderiv_ball (half_pos hR)
    (hconv.mono houter) hseq'
  refine ⟨R / 2, half_pos hR, ?_, h⟩
  exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hRU

/-- The multivariable Weierstrass theorem: locally uniform limits of holomorphic
maps into a complete complex normed space are holomorphic. -/
theorem tendstoLocallyUniformlyOn_differentiableOn
    (hf : TendstoLocallyUniformlyOn seq f φ U)
    (hseq : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) U)
    (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  intro x hx
  obtain ⟨r, hr, _, hd, _⟩ :=
    exists_ball_differentiableOn_and_tendstoUniformlyOn_fderiv hf hseq hU hx
  exact (hd.differentiableAt (ball_mem_nhds x hr)).differentiableWithinAt

/-- Fréchet derivatives of a locally uniformly convergent holomorphic family
converge locally uniformly to the Fréchet derivative of its limit. -/
theorem tendstoLocallyUniformlyOn_fderiv
    (hf : TendstoLocallyUniformlyOn seq f φ U)
    (hseq : ∀ᶠ n in φ, DifferentiableOn ℂ (seq n) U)
    (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (fun n => fderiv ℂ (seq n)) (fderiv ℂ f) φ U := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨r, hr, _, _, hconv⟩ :=
    exists_ball_differentiableOn_and_tendstoUniformlyOn_fderiv hf hseq hU hx
  exact ⟨ball x r, nhdsWithin_le_nhds (ball_mem_nhds x hr), hconv⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
