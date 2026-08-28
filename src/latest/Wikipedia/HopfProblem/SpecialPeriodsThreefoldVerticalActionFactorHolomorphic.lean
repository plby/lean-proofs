import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFactorBasic

/-!
# Holomorphic factorization of an integral-period additive flow

The local inverses of the actual normalized exponential descend joint
holomorphy from the additive parameter to the existing complex manifold
`ℂˣ`.  Every descended parameter acts by a genuine biholomorphism of the
original manifold, with inverse given by the inverse parameter.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor

open Exponential

namespace AdditiveFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℂ E H} (F : AdditiveFlow M)

/-- Joint holomorphy descends through the actual exponential local
biholomorphism, with both the original manifold and units atlases. -/
theorem act_holomorphic
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) :
    ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂˣ => F.act p.2 p.1) := by
  intro p
  obtain ⟨s, hs⟩ := normalizedExponential_surjective p.2
  let e := normalizedExponential_isLocalDiffeomorph s
  have hlog : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.localInverse p.2 := by
    simpa only [hs] using e.localInverse_contMDiffAt
  have hpair : ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω
      (fun q : M × ℂˣ => (q.1, e.localInverse q.2)) p :=
    contMDiffAt_fst.prodMk (hlog.comp p contMDiffAt_snd)
  have hcomp : ContMDiffAt (I.prod 𝓘(ℂ)) I ω
      (fun q : M × ℂˣ => F (e.localInverse q.2) q.1) p :=
    hF.contMDiffAt.comp p hpair
  apply hcomp.congr_of_eventuallyEq
  have he := e.localInverse_eventuallyEq_right
  rw [hs] at he
  filter_upwards [(continuous_snd.tendsto p).eventually he] with q hq
  change normalizedExponential (e.localInverse q.2) = q.2 at hq
  exact (congrArg (fun u => F.act u q.1) hq).symm.trans
    (F.act_normalizedExponential (e.localInverse q.2) q.1)

/-- Each fixed nonzero complex parameter acts holomorphically. -/
theorem act_holomorphic_const
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) (u : ℂˣ) :
    ContMDiff I I ω (F.act u) :=
  (F.act_holomorphic hF).comp (contMDiff_id.prodMk contMDiff_const)

/-- The selected multiplicative action is jointly holomorphic. -/
theorem action_holomorphic
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) :
    letI := F.action
    ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂˣ => p.2 • p.1) :=
  F.act_holomorphic hF

/-- Joint holomorphy gives joint continuity for the selected action. -/
theorem continuousSMul
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) :
    letI := F.action
    ContinuousSMul ℂˣ M := by
  let := F.action
  refine ⟨?_⟩
  change Continuous (fun p : ℂˣ × M => F.act p.1 p.2)
  exact (F.act_holomorphic hF).continuous.comp continuous_swap

variable (I)

/-- Every descended parameter acts by a biholomorphism of the original
manifold; the inverse is literally the inverse-parameter action. -/
def biholomorph
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1)) (u : ℂˣ) :
    Diffeomorph I I M M ω where
  toEquiv := F.equiv u
  contMDiff_toFun := F.act_holomorphic_const hF u
  contMDiff_invFun := F.act_holomorphic_const hF u⁻¹

@[simp] theorem biholomorph_apply
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1))
    (u : ℂˣ) (x : M) : F.biholomorph I hF u x = F.act u x := rfl

@[simp] theorem biholomorph_symm_apply
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1))
    (u : ℂˣ) (x : M) : (F.biholomorph I hF u).symm x = F.act u⁻¹ x := rfl

end AdditiveFlow

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor
