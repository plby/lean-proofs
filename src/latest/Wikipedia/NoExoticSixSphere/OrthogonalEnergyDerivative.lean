import Wikipedia.NoExoticSixSphere.OrthogonalExponentialStationarity

/-!
# Differentiating the first variation of orthogonal energy

The derivative of energy is represented by a smooth acceleration pairing.
Differentiation under the integral then computes its actual second derivative,
before making any assumption about the base path.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization HilbertSchmidt OrthogonalPathEnergy
  OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ}

noncomputable def accelerationPairing (a : ℝ × ℝ → OrthogonalOperators n)
    (p : ℝ × ℝ) : ℝ :=
  innerForm (second (velocity a) p) (variation a p)

variable {a : ℝ × ℝ → OrthogonalOperators n}
  (ha : ContDiff ℝ ∞ (operator a))

include ha

theorem contDiff_accelerationPairing : ContDiff ℝ ∞ (accelerationPairing a) :=
  ContDiff.comp
    (g := fun q : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
      innerForm q.1 q.2)
    (f := fun p ↦ (second (velocity a) p, variation a p))
    (contDiff_innerForm (n := n))
    ((contDiff_second (contDiff_velocity ha)).prodMk (contDiff_variation ha))

theorem first_accelerationPairing (p : ℝ × ℝ) :
    first (accelerationPairing a) p =
      innerForm (second (velocity a) p) (first (variation a) p) +
        innerForm (first (second (velocity a)) p) (variation a p) := by
  exact (hasDerivAt_first
    (((contDiff_accelerationPairing ha).differentiable (by simp)) p)).unique
      (hasDerivAt_innerForm
        (hasDerivAt_first
          (((contDiff_second (contDiff_velocity ha)).differentiable (by simp)) p))
        (hasDerivAt_first (((contDiff_variation ha).differentiable (by simp)) p)))

theorem deriv_energy_eq (l u : ℝ)
    (hl : ∀ r, a (r, l) = a (0, l)) (hu : ∀ r, a (r, u) = a (0, u)) (s : ℝ) :
    deriv (fun r ↦ energy (fun t ↦ operator a (r, t)) l u) s =
      -2 * ∫ t in l..u, accelerationPairing a (s, t) :=
  (hasDerivAt_energy_fixedEndpoints ha s l u
    (fun r ↦ (hl r).trans (hl s).symm) (fun r ↦ (hu r).trans (hu s).symm)).deriv

theorem hasDerivAt_deriv_energy (l u : ℝ)
    (hl : ∀ r, a (r, l) = a (0, l)) (hu : ∀ r, a (r, u) = a (0, u)) (s : ℝ) :
    HasDerivAt (deriv (fun r ↦ energy (fun t ↦ operator a (r, t)) l u))
      (-2 * ∫ t in l..u, first (accelerationPairing a) (s, t)) s := by
  have heq : deriv (fun r ↦ energy (fun t ↦ operator a (r, t)) l u) =
      (fun r ↦ -2 * ∫ t in l..u, accelerationPairing a (r, t)) := by
    funext r
    exact deriv_energy_eq ha l u hl hu r
  rw [heq]
  exact (SmoothIntervalIntegral.hasDerivAt_integral
    (contDiff_accelerationPairing ha) s l u).const_mul (-2)

end NoExoticSixSphere.OrthogonalFirstVariation
