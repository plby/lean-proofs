import Wikipedia.HopfProblem.OrbitPairSpherePathEnergy

/-!
# The sphere index form is an actual second energy derivative

For a smooth family of unit vectors with fixed endpoints, at a constant-speed
great-circle slice the second derivative is twice the integral of
`‖V'‖² - w² ‖V‖²`. Here `V` and all mixed derivatives are derivatives of the
given family. Integration by parts retains and then discharges both endpoint
terms. This does not postulate a path-space deformation theorem.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy

open NoExoticSixSphere TwoParameterCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem first_first_second {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A) (p : ℝ × ℝ) :
    first (first (second A)) p = second (first (first A)) p := by
  have he : first (second A) = second (first A) := funext (first_second hA)
  rw [he, first_second (contDiff_first hA)]

theorem hasDerivAt_deriv_energy_of_geodesic {A : ℝ × ℝ → E}
    (hA : ContDiff ℝ ∞ A) (hunit : ∀ p, ‖A p‖ = 1) (s l u w : ℝ)
    (hl : ∀ r, A (r, l) = A (s, l)) (hu : ∀ r, A (r, u) = A (s, u))
    (hacc : ∀ t, second (second A) (s, t) = (-w ^ 2) • A (s, t)) :
    HasDerivAt (deriv (fun r => energy (fun t => A (r, t)) l u))
      (2 * ∫ t in l..u,
        (‖second (first A) (s, t)‖ ^ 2 - w ^ 2 * ‖first A (s, t)‖ ^ 2)) s := by
  have hV := contDiff_second hA
  have hW := contDiff_first (contDiff_first hA)
  have hV' := contDiff_second hV
  have hW' := contDiff_second hW
  have hs : Continuous (fun t : ℝ => (s, t)) := continuous_const.prodMk continuous_id
  have hparts := integral_inner_derivative
    (hV.continuous.comp hs) (hW.continuous.comp hs)
    (hV'.continuous.comp hs) (hW'.continuous.comp hs)
    (fun t => hasDerivAt_second ((hV.differentiable (by simp)) (s, t)))
    (fun t => hasDerivAt_second ((hW.differentiable (by simp)) (s, t))) l u
  simp only [Function.comp_apply] at hparts
  rw [first_first_eq_zero_of_constant_slice hA s u hu,
    first_first_eq_zero_of_constant_slice hA s l hl,
    inner_zero_right, inner_zero_right, sub_self, zero_sub] at hparts
  have hpair (t : ℝ) :
      inner ℝ (second (second A) (s, t)) (first (first A) (s, t)) =
        w ^ 2 * ‖first A (s, t)‖ ^ 2 := by
    rw [hacc, real_inner_smul_left, inner_first_first_of_unit hA hunit]
    ring
  simp_rw [hpair] at hparts
  have hn : Continuous (fun t => ‖second (first A) (s, t)‖ ^ 2) :=
    ((contDiff_second (contDiff_first hA)).continuous.comp hs).norm.pow 2
  have hp : Continuous (fun t => w ^ 2 * ‖first A (s, t)‖ ^ 2) :=
    continuous_const.mul (((contDiff_first hA).continuous.comp hs).norm.pow 2)
  have hq : Continuous (fun t =>
      inner ℝ (second A (s, t)) (second (first (first A)) (s, t))) :=
    (hV.continuous.comp hs).inner (hW'.continuous.comp hs)
  have hd := hasDerivAt_deriv_energy hA s l u
  simp_rw [first_first_second hA, first_second hA] at hd
  rw [intervalIntegral.integral_add (hn.intervalIntegrable l u)
    (hq.intervalIntegrable l u), hparts] at hd
  rw [intervalIntegral.integral_sub (hn.intervalIntegrable l u)
    (hp.intervalIntegrable l u), sub_eq_add_neg]
  exact hd

end Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy
