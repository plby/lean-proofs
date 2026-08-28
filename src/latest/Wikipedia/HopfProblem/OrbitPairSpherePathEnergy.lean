import Wikipedia.NoExoticSixSphere.SmoothIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual first and second derivatives of sphere-path energy

The energy is the integral of the squared norm of the actual time derivative.
These formulas apply to any smooth two-parameter Euclidean family. They are
the analytic input for the sphere path-space suspension argument; no
suspension theorem or homotopy-group calculation is assumed here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy

open NoExoticSixSphere TwoParameterCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def energy (γ : ℝ → E) (l u : ℝ) : ℝ :=
  ∫ t in l..u, ‖deriv γ t‖ ^ 2

theorem energy_eq_partial {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A) (s l u : ℝ) :
    energy (fun t => A (s, t)) l u = ∫ t in l..u, ‖second A (s, t)‖ ^ 2 := by
  unfold energy
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [(hasDerivAt_second ((hA.differentiable (by simp)) (s, t))).deriv]

theorem hasDerivAt_energy {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A) (s l u : ℝ) :
    HasDerivAt (fun r => energy (fun t => A (r, t)) l u)
      (2 * ∫ t in l..u, inner ℝ (second A (s, t)) (first (second A) (s, t))) s := by
  have hV := contDiff_second hA
  have hW := contDiff_first hV
  have hd (r t : ℝ) :=
    (hasDerivAt_first ((hV.differentiable (by simp)) (r, t))).norm_sq
  have h := SmoothIntervalIntegral.hasDerivAt_integral_of_continuous
    (hV.continuous.norm.pow 2)
    (continuous_const.mul (hV.continuous.inner hW.continuous)) hd s l u
  have he : (fun r => energy (fun t => A (r, t)) l u) =
      (fun r => ∫ t in l..u, ‖second A (r, t)‖ ^ 2) := by
    funext r
    exact energy_eq_partial hA r l u
  rw [he, ← intervalIntegral.integral_const_mul]
  exact h

theorem hasDerivAt_deriv_energy {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A)
    (s l u : ℝ) :
    HasDerivAt (deriv (fun r => energy (fun t => A (r, t)) l u))
      (2 * ∫ t in l..u,
        (‖first (second A) (s, t)‖ ^ 2 +
          inner ℝ (second A (s, t)) (first (first (second A)) (s, t)))) s := by
  have hV := contDiff_second hA
  have hW := contDiff_first hV
  have hZ := contDiff_first hW
  have hd (r t : ℝ) :
      HasDerivAt (fun q => inner ℝ (second A (q, t)) (first (second A) (q, t)))
        (‖first (second A) (r, t)‖ ^ 2 +
          inner ℝ (second A (r, t)) (first (first (second A)) (r, t))) r := by
    simpa only [real_inner_self_eq_norm_sq, add_comm] using
      (hasDerivAt_first ((hV.differentiable (by simp)) (r, t))).inner ℝ
        (hasDerivAt_first ((hW.differentiable (by simp)) (r, t)))
  have h := SmoothIntervalIntegral.hasDerivAt_integral_of_continuous
    (hV.continuous.inner hW.continuous)
    ((hW.continuous.norm.pow 2).add (hV.continuous.inner hZ.continuous)) hd s l u
  have he : deriv (fun r => energy (fun t => A (r, t)) l u) =
      (fun r => 2 * ∫ t in l..u,
        inner ℝ (second A (r, t)) (first (second A) (r, t))) := by
    funext r
    exact (hasDerivAt_energy hA r l u).deriv
  rw [he]
  exact h.const_mul 2

theorem integral_inner_derivative {V W V' W' : ℝ → E}
    (hV : Continuous V) (hW : Continuous W) (hV' : Continuous V') (hW' : Continuous W')
    (hdV : ∀ t, HasDerivAt V (V' t) t) (hdW : ∀ t, HasDerivAt W (W' t) t)
    (l u : ℝ) :
    (∫ t in l..u, inner ℝ (V t) (W' t)) =
      inner ℝ (V u) (W u) - inner ℝ (V l) (W l) -
        ∫ t in l..u, inner ℝ (V' t) (W t) := by
  have hleft : Continuous (fun t => inner ℝ (V' t) (W t)) := hV'.inner hW
  have hright : Continuous (fun t => inner ℝ (V t) (W' t)) := hV.inner hW'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := l) (b := u) (fun t _ => (hdV t).inner ℝ (hdW t))
    ((hright.intervalIntegrable l u).add (hleft.intervalIntegrable l u))
  rw [intervalIntegral.integral_add (hright.intervalIntegrable l u)
    (hleft.intervalIntegrable l u)] at h
  linarith

theorem first_eq_zero_of_constant_slice {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A)
    (s t : ℝ) (h : ∀ r, A (r, t) = A (s, t)) : first A (s, t) = 0 := by
  have hd := hasDerivAt_first ((hA.differentiable (by simp)) (s, t))
  have he : (fun r => A (r, t)) = (fun _ : ℝ => A (s, t)) := funext h
  rw [he] at hd
  exact hd.unique (hasDerivAt_const s _)

theorem first_first_eq_zero_of_constant_slice {A : ℝ × ℝ → E}
    (hA : ContDiff ℝ ∞ A) (s t : ℝ) (h : ∀ r, A (r, t) = A (s, t)) :
    first (first A) (s, t) = 0 := by
  have hz (r : ℝ) : first A (r, t) = 0 :=
    first_eq_zero_of_constant_slice hA r t (fun q => (h q).trans (h r).symm)
  exact first_eq_zero_of_constant_slice (contDiff_first hA) s t
    (fun r => (hz r).trans (hz s).symm)

theorem inner_first_eq_zero_of_unit {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A)
    (hunit : ∀ p, ‖A p‖ = 1) (s t : ℝ) : inner ℝ (A (s, t)) (first A (s, t)) = 0 := by
  have hd := (hasDerivAt_first ((hA.differentiable (by simp)) (s, t))).norm_sq
  have he : (fun r => ‖A (r, t)‖ ^ 2) = (fun _ : ℝ => (1 : ℝ)) := by
    funext r
    rw [hunit, one_pow]
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const s 1)
  linarith

theorem inner_first_first_of_unit {A : ℝ × ℝ → E} (hA : ContDiff ℝ ∞ A)
    (hunit : ∀ p, ‖A p‖ = 1) (s t : ℝ) :
    inner ℝ (A (s, t)) (first (first A) (s, t)) = -‖first A (s, t)‖ ^ 2 := by
  have hd := (hasDerivAt_first ((hA.differentiable (by simp)) (s, t))).inner ℝ
    (hasDerivAt_first (((contDiff_first hA).differentiable (by simp)) (s, t)))
  have he : (fun r => inner ℝ (A (r, t)) (first A (r, t))) = (fun _ : ℝ => (0 : ℝ)) :=
    funext (fun r => inner_first_eq_zero_of_unit hA hunit r t)
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const s 0)
  rw [real_inner_self_eq_norm_sq] at hz
  linarith

end Wikipedia.HopfProblem.OrbitPair.SpherePathEnergy
