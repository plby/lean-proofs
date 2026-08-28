import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFactorHolomorphic

/-!
# The faithful holomorphic multiplicative action factored from an additive flow

The construction uses the actual integer quotient and normalized exponential.
The original manifold atlas and the inherited atlas on `ℂˣ` remain fixed.
The hypotheses below concern only the given additive flow; its descended
action, holomorphy, inverse maps, and faithfulness are proved consequences.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor

open Exponential

namespace AdditiveFlow

variable {M : Type*} (F : AdditiveFlow M)

/-- The exact exponential formula uniquely determines the factored map. -/
theorem act_unique (a : ℂˣ → M → M)
    (ha : ∀ (s : ℂ) (x : M), a (normalizedExponential s) x = F s x) :
    a = F.act := by
  funext u x
  obtain ⟨s, rfl⟩ := normalizedExponential_surjective u
  rw [ha, F.act_normalizedExponential]

/-- For an exact-kernel flow, only the identity multiplicative parameter
fixes every point of the original space. -/
theorem act_eq_id_iff
    (hkernel : ∀ s : ℂ, (∀ x : M, F s x = x) ↔ ∃ n : ℤ, s = (n : ℂ))
    (u : ℂˣ) : (∀ x : M, F.act u x = x) ↔ u = 1 := by
  let := F.action
  constructor
  · exact _root_.faithfulSMul_iff.mp (F.faithfulSMul hkernel) u
  · rintro rfl
    exact F.act_one

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℂ E H}

/-- The exact lift formula also holds for the constructed biholomorphisms. -/
theorem biholomorph_normalizedExponential
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1))
    (s : ℂ) (x : M) : F.biholomorph I hF (normalizedExponential s) x = F s x :=
  F.act_normalizedExponential s x

/-- An actual additive holomorphic flow with exact integer kernel gives a
faithful jointly holomorphic action of the existing complex multiplicative
group on the original manifold, with the prescribed exponential lift. -/
theorem exists_faithful_holomorphic_action
    (hF : ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂ => F p.2 p.1))
    (hkernel : ∀ s : ℂ, (∀ x : M, F s x = x) ↔ ∃ n : ℤ, s = (n : ℂ)) :
    ∃ A : MulAction ℂˣ M,
      letI := A
      FaithfulSMul ℂˣ M ∧ ContinuousSMul ℂˣ M ∧
        ContMDiff (I.prod 𝓘(ℂ)) I ω (fun p : M × ℂˣ => p.2 • p.1) ∧
        ∀ (s : ℂ) (x : M), normalizedExponential s • x = F s x := by
  refine ⟨F.action, F.faithfulSMul hkernel, F.continuousSMul hF,
    F.action_holomorphic hF, ?_⟩
  intro s x
  exact F.action_normalizedExponential s x

end AdditiveFlow

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Factor
