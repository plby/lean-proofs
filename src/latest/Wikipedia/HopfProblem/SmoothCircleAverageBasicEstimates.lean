import Wikipedia.HopfProblem.SmoothCircleAverageBasic
import Mathlib.Tactic.Linarith

/-!
# Error and nonvanishing estimates for the actual circle average

These estimates use the literal interval integral from `SmoothCircleAverage`.
They require no action law or periodicity. To deduce an orbitwise bound from
a global approximation bound, the reference map is explicitly required to
be invariant under the given action. In particular, averaging an arbitrary
unit-valued map is not asserted to be nonzero.
-/

noncomputable section

open MeasureTheory Set

namespace Wikipedia.HopfProblem.SmoothCircleAverage

variable {M F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {g : M → F}

/-- Subtracting a constant commutes with the actual unit-length average. -/
theorem average_sub_eq_integral_sub (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (x : M) (c : F) :
    average act g x - c = ∫ t in (0 : ℝ)..1, g (act t x) - c := by
  rw [intervalIntegral.integral_sub (orbit_intervalIntegrable act hact hg x 0 1)
    intervalIntegrable_const, intervalIntegral.integral_const]
  simp only [average, sub_zero, one_smul]

/-- A uniform error along the original orbit bounds the error of its average. -/
theorem dist_average_le_of_orbit_bound (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (x : M) (c : F) {ε : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, dist (g (act t x)) c ≤ ε) :
    dist (average act g x) c ≤ ε := by
  rw [dist_eq_norm, average_sub_eq_integral_sub act hact hg x c]
  have hnorm : ∀ t ∈ uIoc (0 : ℝ) 1, ‖g (act t x) - c‖ ≤ ε := by
    intro t ht
    rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    simpa only [dist_eq_norm] using hbound t ⟨ht.1.le, ht.2⟩
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hnorm

/-- Invariance is the essential step turning a global approximation into
an approximation of the unchanged value at the original point. -/
theorem dist_average_le_of_invariant_bound (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (f : M → F) (hinv : ∀ (t : ℝ) (z : M), f (act t z) = f z)
    {ε : ℝ} (hbound : ∀ z, dist (g z) (f z) ≤ ε) (x : M) :
    dist (average act g x) (f x) ≤ ε := by
  apply dist_average_le_of_orbit_bound act hact hg x (f x)
  intro t _
  simpa only [hinv t x] using hbound (act t x)

theorem dist_average_le_half_of_invariant_close (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (f : M → F) (hinv : ∀ (t : ℝ) (z : M), f (act t z) = f z)
    (hclose : ∀ z, dist (g z) (f z) < (1 / 2 : ℝ)) (x : M) :
    dist (average act g x) (f x) ≤ (1 / 2 : ℝ) :=
  dist_average_le_of_invariant_bound act hact hg f hinv (fun z => (hclose z).le) x

/-- Averaging stays at distance at least one half from zero when the
invariant reference value is a unit vector. -/
theorem norm_average_ge_half_of_invariant_close (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (f : M → F) (hinv : ∀ (t : ℝ) (z : M), f (act t z) = f z)
    (hclose : ∀ z, dist (g z) (f z) < (1 / 2 : ℝ))
    (x : M) (hunit : ‖f x‖ = 1) :
    (1 / 2 : ℝ) ≤ ‖average act g x‖ := by
  have hd : dist (f x) (average act g x) ≤ (1 / 2 : ℝ) := by
    simpa only [dist_comm] using
      dist_average_le_half_of_invariant_close act hact hg f hinv hclose x
  have ht : ‖f x‖ ≤ ‖average act g x‖ + (1 / 2 : ℝ) :=
    norm_le_norm_add_const_of_dist_le hd
  rw [hunit] at ht
  linarith

theorem average_ne_zero_of_invariant_close (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (f : M → F) (hinv : ∀ (t : ℝ) (z : M), f (act t z) = f z)
    (hclose : ∀ z, dist (g z) (f z) < (1 / 2 : ℝ))
    (x : M) (hunit : ‖f x‖ = 1) : average act g x ≠ 0 := by
  intro hz
  have hn := norm_average_ge_half_of_invariant_close act hact hg f hinv hclose x hunit
  rw [hz, norm_zero] at hn
  norm_num at hn

end Wikipedia.HopfProblem.SmoothCircleAverage
