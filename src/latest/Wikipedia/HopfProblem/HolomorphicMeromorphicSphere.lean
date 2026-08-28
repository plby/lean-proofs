import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRational
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluation
import Wikipedia.HopfProblem.HolomorphicMeromorphicTranscendence

/-!
# Intrinsic rationality and algebraic dimension of the Riemann sphere

The genuine native meromorphic field is complex-algebra equivalent to
the rational-function field. Its original affine coordinate is a
transcendence basis, so its actual algebraic transcendence degree is one.
These results have no rationality or presentation hypothesis.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative

/-- The actual affine coordinate is transcendental in the full native field. -/
theorem coordinate_transcendental : Transcendental ℂ coordinate :=
  Transcendence.transcendental_of_algEquiv_ratFunc_eq_X meromorphicFieldEquiv
    meromorphicFieldEquiv_coordinate

/-- The original coordinate, not an auxiliary assumed generator, is a
singleton transcendence basis of the native meromorphic function field. -/
theorem coordinate_isTranscendenceBasis :
    IsTranscendenceBasis ℂ (fun _ : Unit => coordinate) := by
  simpa only [meromorphicFieldEquiv, AlgEquiv.symm_symm, rationalEquiv_X] using
    Transcendence.isTranscendenceBasis_of_algEquiv_ratFunc meromorphicFieldEquiv

/-- The actual cardinal-valued transcendence degree of the original field. -/
theorem meromorphic_trdeg_eq_one :
    Algebra.trdeg ℂ (Function 𝓘(ℂ) RiemannSphere) = 1 :=
  Transcendence.trdeg_eq_one_of_algEquiv_ratFunc meromorphicFieldEquiv

/-- The finite natural-number-valued algebraic dimension is one. -/
theorem meromorphic_trdeg_toNat_eq_one :
    Cardinal.toNat (Algebra.trdeg ℂ (Function 𝓘(ℂ) RiemannSphere)) = 1 :=
  Transcendence.trdeg_toNat_eq_one_of_algEquiv_ratFunc meromorphicFieldEquiv

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative
