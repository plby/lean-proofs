import Wikipedia.NoExoticSixSphere.OrthogonalFirstVariation

/-!
# Exponential paths are stationary for fixed-endpoint energy

For an arbitrary smooth variation with fixed endpoint slices, a base path of
the form `b * exp(t K)` has zero first variation. This is a statement about the
actual integral energy, not a definition of geodesic or of criticality.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  HilbertSchmidt OrthogonalPathEnergy OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ} {a : ℝ × ℝ → OrthogonalOperators n}
  (ha : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a))

include ha

theorem second_velocity_eq_zero_of_constant (s : ℝ)
    (K : Vector n →L[ℝ] Vector n) (hK : ∀ t, velocity a (s, t) = K) (t : ℝ) :
    second (velocity a) (s, t) = 0 := by
  have hd := hasDerivAt_second (((contDiff_velocity ha).differentiable (by simp)) (s, t))
  have heq : (fun r ↦ velocity a (s, r)) = (fun _ : ℝ ↦ K) := funext hK
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const t K)

theorem hasDerivAt_energy_zero_of_constantVelocity (s l u : ℝ)
    (hl : ∀ r, a (r, l) = a (s, l)) (hu : ∀ r, a (r, u) = a (s, u))
    (K : Vector n →L[ℝ] Vector n) (hK : ∀ t, velocity a (s, t) = K) :
    HasDerivAt (fun r ↦ energy (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) l u)
      0 s := by
  have hd := hasDerivAt_energy_fixedEndpoints ha s l u hl hu
  have hz (A : Vector n →L[ℝ] Vector n) : innerForm 0 A = 0 := by simp [innerForm]
  simpa only [second_velocity_eq_zero_of_constant ha s K hK, hz,
    intervalIntegral.integral_zero, mul_zero] using hd

theorem velocity_of_exponential_slice (s : ℝ) (b : OrthogonalOperators n)
    (K : SkewOperators n) (hpath : ∀ t, a (s, t) = b * exp (t • K)) (t : ℝ) :
    velocity a (s, t) = (K : Vector n →L[ℝ] Vector n) := by
  have hd : HasDerivAt (fun r ↦ OrthogonalMaurerCartan.operator a (s, r))
      (second (OrthogonalMaurerCartan.operator a) (s, t)) t :=
    hasDerivAt_second ((ha.differentiable (by simp)) (s, t))
  have heq : (fun r ↦ OrthogonalMaurerCartan.operator a (s, r)) =
      (fun r ↦ (b * exp (r • K)).1.1) := by
    funext r
    exact congrArg (fun q : OrthogonalOperators n ↦ q.1.1) (hpath r)
  rw [heq] at hd
  have hderiv := hd.unique (hasDerivAt_left_exp b K t)
  unfold velocity
  rw [hderiv]
  apply ContinuousLinearMap.ext
  intro x
  have hx : b.1.1 ((exp (t • K)).1.1 ((K : Vector n →L[ℝ] Vector n) x)) =
      (a (s, t)).1.1 ((K : Vector n →L[ℝ] Vector n) x) := by
    rw [hpath]
    rfl
  change (inverse (a (s, t))).1.1
    (b.1.1 ((exp (t • K)).1.1 ((K : Vector n →L[ℝ] Vector n) x))) = _
  rw [hx, inverse_apply_self]

/-- Every smooth fixed-endpoint variation through an exponential base path has zero derivative. -/
theorem hasDerivAt_energy_zero_of_exponential (s l u : ℝ)
    (hl : ∀ r, a (r, l) = a (s, l)) (hu : ∀ r, a (r, u) = a (s, u))
    (b : OrthogonalOperators n) (K : SkewOperators n)
    (hpath : ∀ t, a (s, t) = b * exp (t • K)) :
    HasDerivAt (fun r ↦ energy (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) l u)
      0 s :=
  hasDerivAt_energy_zero_of_constantVelocity ha s l u hl hu K
    (velocity_of_exponential_slice ha s b K hpath)

end NoExoticSixSphere.OrthogonalFirstVariation
