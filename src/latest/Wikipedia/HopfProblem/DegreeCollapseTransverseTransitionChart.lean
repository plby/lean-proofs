import Wikipedia.HopfProblem.DegreeCollapseVerticalTransitionPhase
import Wikipedia.HopfProblem.DegreeCollapseAxisDerivativeBlock
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# The transverse transition is an actual local diffeomorphism

The full native transition is invertible, and its vertical derivative is
identity. Its actual transverse derivative is therefore invertible. The
inverse function theorem constructs the transverse partial diffeomorphism,
while retaining the exact smooth scalar phase and product formula.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Extract a genuine transverse partial diffeomorphism and a smooth phase
from the actual vertical transition, with an exact formula on a product domain. -/
theorem exists_transverse_transition_chart
    (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0))
    {t₀ : ℝ} (hp : (t₀, (0 : Z)) ∈ R.source) (hfix : R (t₀, 0) = (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧ (0 : Z) ∈ P.source ∧ P 0 = 0 ∧ v 0 = 0 ∧
      ContDiffOn ℝ ∞ v P.source ∧
      Ioo (t₀ - ε) (t₀ + ε) ×ˢ P.source ⊆ R.source ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ z ∈ P.source,
        R (t, z) = (t + v z, P z) := by
  obtain ⟨ε, Q, v, hε, hQ, hv, hQ0, hv0, hsub, hformula⟩ :=
    exists_vertical_transition_phase R hvertical hp hfix
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hQeq : Q =ᶠ[𝓝 (0 : Z)] (fun z => (R (t₀, z)).2) := by
    filter_upwards [ball_mem_nhds (0 : Z) hε] with z hz
    exact (congrArg Prod.snd (hformula t₀ ht₀ z hz)).symm
  have hRdiff := (R.contMDiffOn_toFun.contDiffOn.contDiffAt
    (R.open_source.mem_nhds hp)).differentiableAt (by simp)
  have hι : HasFDerivAt (fun z : Z => (t₀, z)) (ContinuousLinearMap.inr ℝ ℝ Z) 0 := by
    exact (hasFDerivAt_const t₀ (0 : Z)).prodMk (hasFDerivAt_id (0 : Z))
  have hslice : HasFDerivAt (fun z : Z => (R (t₀, z)).2)
      (AxisCoordinates.transverseBlock (fderiv ℝ R (t₀, 0))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := R (t₀, 0))).comp 0 (hRdiff.hasFDerivAt.comp 0 hι)
  have hfull : (fderiv ℝ R (t₀, 0)).IsInvertible := by
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) ∞ R (t₀, 0) :=
      ⟨R, hp, fun _ _ => rfl⟩
    refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
    have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
    rw [mfderiv_eq_fderiv] at he
    exact he
  have hQinv : (fderiv ℝ Q 0).IsInvertible := by
    rw [hQeq.fderiv_eq, hslice.fderiv]
    exact AxisCoordinates.isInvertible_transverseBlock _ (hvertical (t₀, 0) hp) hfull
  obtain ⟨P, hP0, hPsub, hPmap⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    isOpen_ball (mem_ball_self hε) hQ hQinv
  refine ⟨ε, P, v, hε, hP0, ?_, hv0, hv.mono hPsub, ?_, ?_⟩
  · rw [hPmap]
    exact hQ0
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hsub ⟨ht, hPsub hz⟩
  · intro t ht z hz
    rw [hPmap]
    exact hformula t ht z (hPsub hz)

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
