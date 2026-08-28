import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicConstantFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicRationalEmbedding

/-!
# The genuine meromorphic field of the constructed threefold

Every native meromorphic function admits honest restrictions outside a
proved countable set of fibres. The genuine meromorphic field of every
remaining nonexceptional period torus consists of constants. Lemma 9.6
therefore applies to every function, and the original sphere projection
induces an algebra equivalence of the full native meromorphic fields.

Combining this proved surjectivity with native sphere rationality gives
`M(X) ≃ ℂ(t)` and algebraic dimension one. The element corresponding to
`t` is the actual meromorphic base coordinate of the original projection.
Neither field is defined by the asserted rational representation.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Every genuine global meromorphic function descends uniquely, with
the uncountable-fibre hypothesis now discharged for the actual threefold. -/
theorem existsUnique_sphere_meromorphic_descent_unconditional
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    ∃! s : HolomorphicMeromorphic.Function I₁ RiemannSphere, sphereMeromorphicPullback s = g :=
  existsUnique_sphere_meromorphic_descent g (MeromorphicFibres.constantRegularFibres_uncountable g)

/-- Surjectivity of the original meromorphic pullback, for the full
sheaf of locally represented native fraction germs. -/
theorem sphereMeromorphicPullback_surjective : Function.Surjective sphereMeromorphicPullback :=
  fun g => (existsUnique_sphere_meromorphic_descent_unconditional g).exists

namespace MeromorphicRational

theorem spherePullbackAlgHom_surjective : Function.Surjective spherePullbackAlgHom :=
  sphereMeromorphicPullback_surjective

/-- The original sphere pullback is an equivalence of genuine fields. -/
def spherePullbackAlgEquiv :
    HolomorphicMeromorphic.Function I₁ RiemannSphere ≃ₐ[ℂ]
      HolomorphicMeromorphic.Function IF Threefold.Space :=
  AlgEquiv.ofBijective spherePullbackAlgHom
    ⟨spherePullbackAlgHom_injective, spherePullbackAlgHom_surjective⟩

@[simp] theorem spherePullbackAlgEquiv_apply
    (s : HolomorphicMeromorphic.Function I₁ RiemannSphere) :
    spherePullbackAlgEquiv s = sphereMeromorphicPullback s := rfl

/-- The previously constructed actual rational embedding exhausts the
entire meromorphic field, as a theorem rather than a definition. -/
theorem rationalFunctionEmbedding_surjective : Function.Surjective rationalFunctionEmbedding :=
  spherePullbackAlgHom_surjective.comp HolomorphicMeromorphic.SphereNative.rationalEquiv.surjective

/-- Rational functions identify with all native meromorphic functions. -/
def rationalFunctionEquiv :
    RatFunc ℂ ≃ₐ[ℂ] HolomorphicMeromorphic.Function IF Threefold.Space :=
  AlgEquiv.ofBijective rationalFunctionEmbedding
    ⟨rationalFunctionEmbedding_injective, rationalFunctionEmbedding_surjective⟩

@[simp] theorem rationalFunctionEquiv_apply (r : RatFunc ℂ) :
    rationalFunctionEquiv r = rationalFunctionEmbedding r := rfl

@[simp] theorem rationalFunctionEquiv_X : rationalFunctionEquiv RatFunc.X = baseCoordinate :=
  rationalFunctionEmbedding_X

/-- The original full meromorphic field is complex-algebra equivalent
to the usual rational-function field. -/
def meromorphicFieldEquiv :
    HolomorphicMeromorphic.Function IF Threefold.Space ≃ₐ[ℂ] RatFunc ℂ :=
  rationalFunctionEquiv.symm

@[simp] theorem meromorphicFieldEquiv_baseCoordinate :
    meromorphicFieldEquiv baseCoordinate = RatFunc.X := by
  rw [← rationalFunctionEquiv_X]
  exact rationalFunctionEquiv.symm_apply_apply RatFunc.X

/-- Polynomial evaluation agrees with the original sphere pullback. -/
theorem spherePullback_polynomial (P : Polynomial ℂ) :
    spherePullbackAlgHom (HolomorphicMeromorphic.SphereNative.polynomialMap P) =
      Polynomial.aeval baseCoordinate P :=
  (Polynomial.aeval_algHom_apply spherePullbackAlgHom
    HolomorphicMeromorphic.SphereNative.coordinate P).symm

/-- Every native meromorphic function is an actual rational expression
in the original projection coordinate, with a nonzero polynomial denominator. -/
theorem exists_polynomial_fraction (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      g = Polynomial.aeval baseCoordinate P / Polynomial.aeval baseCoordinate Q := by
  obtain ⟨s, rfl⟩ := spherePullbackAlgHom_surjective g
  obtain ⟨P, Q, hQ, hs⟩ := HolomorphicMeromorphic.SphereNative.exists_polynomial_fraction s
  refine ⟨P, Q, hQ, ?_⟩
  rw [hs, map_div₀, spherePullback_polynomial, spherePullback_polynomial]

/-- The actual base coordinate is a singleton transcendence basis of
the original full meromorphic field. -/
theorem baseCoordinate_isTranscendenceBasis :
    IsTranscendenceBasis ℂ (fun _ : Unit => baseCoordinate) := by
  simpa only [meromorphicFieldEquiv, AlgEquiv.symm_symm, rationalFunctionEquiv_X] using
    HolomorphicMeromorphic.Transcendence.isTranscendenceBasis_of_algEquiv_ratFunc
      meromorphicFieldEquiv

/-- Source Theorem 9.7: the actual meromorphic transcendence degree is one. -/
theorem meromorphic_trdeg_eq_one :
    Algebra.trdeg ℂ (HolomorphicMeromorphic.Function IF Threefold.Space) = 1 :=
  HolomorphicMeromorphic.Transcendence.trdeg_eq_one_of_algEquiv_ratFunc meromorphicFieldEquiv

/-- The natural-number-valued algebraic dimension is one as well. -/
theorem meromorphic_trdeg_toNat_eq_one :
    Cardinal.toNat (Algebra.trdeg ℂ (HolomorphicMeromorphic.Function IF Threefold.Space)) = 1 :=
  HolomorphicMeromorphic.Transcendence.trdeg_toNat_eq_one_of_algEquiv_ratFunc meromorphicFieldEquiv

end MeromorphicRational

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
