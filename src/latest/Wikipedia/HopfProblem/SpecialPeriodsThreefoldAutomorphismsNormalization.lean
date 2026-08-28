import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassification

/-!
# Removing the actual vertical translation near the identity

A genuine local inverse of the original regular period-vector covering
supplies a scalar coordinate whose derivative on the native generator
is exactly one. Subtracting that scalar by the already constructed global
flow normalizes any sufficiently small automorphism. This is an operation
on the full automorphism group, not a restriction of its definition.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

open HolomorphicForms.RegularCover
open VerticalAction

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space coverChartedSpace cover_isManifold

/-- One point of the actual regular vector cover, on its zero section. -/
def normalizationCoverPoint : Cover :=
  (Classical.choice (inferInstance : Nonempty TriangleRegularPoint), 0)

/-- The corresponding original threefold point. -/
def normalizationPoint : Threefold.Space := globalCover normalizationCoverPoint

/-- A genuine local inverse of the unchanged regular covering map. -/
def normalizationInverse : PartialDiffeomorph IF IF Threefold.Space Cover ω :=
  (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse

theorem normalizationInverse_mem_source : normalizationPoint ∈ normalizationInverse.source :=
  (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_mem_source

theorem normalizationInverse_mem_target :
    normalizationCoverPoint ∈ normalizationInverse.target :=
  (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_mem_target

@[simp] theorem normalizationInverse_point :
    normalizationInverse normalizationPoint = normalizationCoverPoint :=
  (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_left_inv
    normalizationInverse_mem_target

theorem normalizationInverse_holomorphicAt :
    ContMDiffAt IF IF ω normalizationInverse normalizationPoint :=
  (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_contMDiffAt

/-- The actual second fibre coordinate in that local inverse. -/
def detector (y : Threefold.Space) : ℂ := (normalizationInverse y).2 1

@[simp] theorem detector_point : detector normalizationPoint = 0 := by
  rw [detector, normalizationInverse_point]
  rfl

theorem detector_holomorphicAt : ContMDiffAt IF I₁ ω detector normalizationPoint := by
  have hp : ContMDiff IF I₁ ω (fun x : Cover => x.2 1) := by
    rw [modelWithCornersSelf_prod]
    exact (ContinuousLinearMap.proj 1 : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp contMDiff_snd
  exact hp.contMDiffAt.comp normalizationPoint normalizationInverse_holomorphicAt

theorem detector_flow_eventually :
    ∀ᶠ s : ℂ in 𝓝 0, detector (flow s normalizationPoint) = s := by
  have hc : Continuous (fun s : ℂ => Period.vectorFlow s normalizationCoverPoint) :=
    vectorJointFlow_holomorphic.continuous.comp (continuous_const.prodMk continuous_id)
  have ht : Tendsto (fun s : ℂ => Period.vectorFlow s normalizationCoverPoint)
      (𝓝 0) (𝓝 normalizationCoverPoint) := by
    simpa only [Period.vectorFlow, Period.vector_zero, add_zero] using hc.tendsto 0
  have hi := ht.eventually
    (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_eventuallyEq_left
  filter_upwards [hi] with s hs
  change (normalizationInverse (flow s (globalCover normalizationCoverPoint))).2 1 = s
  rw [flow_globalCover]
  rw [show normalizationInverse (globalCover (Period.vectorFlow s normalizationCoverPoint)) =
    Period.vectorFlow s normalizationCoverPoint from hs]
  simp [Period.vectorFlow, Period.vector, normalizationCoverPoint]

/-- The detector reads the exact original `e₂` normalization of the
native generator; no nonzero scalar is silently rescaled. -/
theorem detector_mfderiv_generator :
    mfderiv IF I₁ detector normalizationPoint (generator normalizationPoint) = (1 : ℂ) := by
  have hc : ContMDiff I₁ IF ω (fun s : ℂ => flow s normalizationPoint) :=
    jointFlow_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)
  have hchain := mfderiv_comp (I := I₁) (I' := IF) (I'' := I₁) 0
    (show MDifferentiableAt IF I₁ detector (flow 0 normalizationPoint) by
      simpa only [flow_zero] using detector_holomorphicAt.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  have he : (fun s : ℂ => detector (flow s normalizationPoint)) =ᶠ[𝓝 0] id :=
    detector_flow_eventually
  have hid := congrArg (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ))
    (he.mfderiv_eq (I := I₁) (I' := I₁))
  have hd : (mfderiv I₁ I₁ (fun s : ℂ => detector (flow s normalizationPoint)) 0)
      (1 : ℂ) = (1 : ℂ) := by
    exact hid.trans (by rw [mfderiv_id]; rfl)
  have hchain' := congrArg (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) hchain
  change (mfderiv I₁ I₁ (fun s : ℂ => detector (flow s normalizationPoint)) 0) (1 : ℂ) =
    (mfderiv IF I₁ detector (flow 0 normalizationPoint))
      ((mfderiv I₁ IF (fun s : ℂ => flow s normalizationPoint) 0) (1 : ℂ)) at hchain'
  rw [flow_zero] at hchain'
  rw [generator_apply]
  exact hchain'.symm.trans hd

/-- The additive time maps as elements of the full native group. -/
def additiveAutomorphism (s : ℂ) : Aut :=
  verticalHom (Exponential.normalizedExponential s)

@[simp] theorem additiveAutomorphism_apply (s : ℂ) (y : Threefold.Space) :
    additiveAutomorphism s y = flow s y := actionBiholomorph_exponential s y

@[simp] theorem additiveAutomorphism_zero : additiveAutomorphism 0 = 1 := by
  simp only [additiveAutomorphism, Exponential.normalizedExponential_zero, map_one]

theorem additiveAutomorphism_continuous : Continuous additiveAutomorphism :=
  verticalHom_continuous.comp Exponential.normalizedExponential_continuous

/-- The scalar vertical translation to remove from a native automorphism. -/
def gauge (f : Aut) : ℂ := detector (f normalizationPoint)

@[simp] theorem gauge_one : gauge 1 = 0 := detector_point

theorem evaluation_normalizationPoint_continuous :
    Continuous (fun f : Aut => f normalizationPoint) :=
  (show Continuous (fun f : C(Threefold.Space, Threefold.Space) => f normalizationPoint) from
    continuous_eval_const normalizationPoint).comp
    (HolomorphicAutomorphism.continuous_toContinuousMap IF Threefold.Space)

theorem gauge_continuousAt_one : ContinuousAt gauge 1 :=
  detector_holomorphicAt.continuousAt.comp_of_eq
    (evaluation_normalizationPoint_continuous.continuousAt (x := 1)) rfl

/-- Normalize an arbitrary full automorphism by an actual global time map. -/
def normalize (f : Aut) : Aut := additiveAutomorphism (-gauge f) * f

@[simp] theorem normalize_one : normalize 1 = 1 := by
  simp only [normalize, gauge_one, neg_zero, additiveAutomorphism_zero, mul_one]

theorem normalize_continuousAt_one : ContinuousAt normalize 1 :=
  ((additiveAutomorphism_continuous.continuousAt.comp gauge_continuousAt_one.neg).mul
    continuousAt_id)

theorem normalize_not_mem_range {f : Aut} (hf : f ∉ verticalHom.range) :
    normalize f ∉ verticalHom.range := by
  intro hn
  apply hf
  have ha : additiveAutomorphism (-gauge f) ∈ verticalHom.range :=
    ⟨Exponential.normalizedExponential (-gauge f), rfl⟩
  simpa only [normalize, inv_mul_cancel_left] using verticalHom.range.mul_mem
    (verticalHom.range.inv_mem ha) hn

/-- The normalized automorphism has zero actual detector at the chosen
point whenever the original automorphism is sufficiently close to one. -/
theorem normalize_detector_eventually :
    ∀ᶠ f : Aut in 𝓝 1, detector (normalize f normalizationPoint) = 0 := by
  have hl : ContinuousAt (fun f : Aut => normalizationInverse (f normalizationPoint)) 1 :=
    normalizationInverse_holomorphicAt.continuousAt.comp_of_eq
      (evaluation_normalizationPoint_continuous.continuousAt (x := 1)) rfl
  have hp : ContinuousAt (fun f : Aut =>
      Period.vectorFlow (-gauge f) (normalizationInverse (f normalizationPoint))) 1 :=
    vectorJointFlow_holomorphic.continuous.continuousAt.comp
      (f := fun f : Aut => (normalizationInverse (f normalizationPoint), -gauge f))
      (hl.prodMk gauge_continuousAt_one.neg)
  have ht : Tendsto (fun f : Aut =>
      Period.vectorFlow (-gauge f) (normalizationInverse (f normalizationPoint)))
      (𝓝 1) (𝓝 normalizationCoverPoint) := by
    simpa only [HolomorphicAutomorphism.one_apply, normalizationInverse_point, gauge_one,
      neg_zero, Period.vectorFlow, Period.vector_zero, add_zero] using hp.tendsto
  have hsrc : ∀ᶠ f : Aut in 𝓝 1, f normalizationPoint ∈ normalizationInverse.source :=
    evaluation_normalizationPoint_continuous.continuousAt
      (normalizationInverse.open_source.mem_nhds normalizationInverse_mem_source)
  have htgt := ht.eventually
    (normalizationInverse.open_target.mem_nhds normalizationInverse_mem_target)
  filter_upwards [hsrc, htgt] with f hfs hft
  have hright : globalCover (normalizationInverse (f normalizationPoint)) = f normalizationPoint :=
    (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_right_inv hfs
  have hleft : normalizationInverse
      (globalCover (Period.vectorFlow (-gauge f) (normalizationInverse (f normalizationPoint)))) =
      Period.vectorFlow (-gauge f) (normalizationInverse (f normalizationPoint)) :=
    (globalCover_isLocalDiffeomorph normalizationCoverPoint).localInverse_left_inv hft
  rw [normalize, HolomorphicAutomorphism.mul_apply, additiveAutomorphism_apply]
  change (normalizationInverse (flow (-gauge f) (f normalizationPoint))).2 1 = 0
  rw [← hright, flow_globalCover, hleft]
  change (normalizationInverse (f normalizationPoint)).2 1 +
    -(normalizationInverse (f normalizationPoint)).2 1 = 0
  exact add_neg_cancel _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
