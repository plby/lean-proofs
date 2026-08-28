import Wikipedia.HopfProblem.SpecialPeriodsModularCusp
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspLog

/-!
# Comparing the actual modular lifts at a cusp

The actual modular j-function is injective in a sufficiently small
q-coordinate disc. Thus two upper-half-plane-valued lifts of the same
j-function in this cusp region have equal normalized exponentials.
Continuity and preconnectedness then give one constant integral shift.
-/

open Function Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

/-- The q-expansion represents the actual modular j-function at every
upper-half-plane value. -/
theorem modularJInQ_exponential {z : ℂ} (hz : 0 < z.im) :
    modularJInQ (exponential z) = modularJ (UpperHalfPlane.ofComplex z) := by
  simpa only [Periodic.qParam, Complex.ofReal_one, div_one, exponential,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
      modularJInQ_qParam (UpperHalfPlane.ofComplex z)

/-- Injectivity of the actual q-expansion converts equality of actual
j-values in the cusp region into equality of normalized exponentials. -/
theorem exponential_eq_of_modularJ_eq {R : ℝ}
    (hR : Set.InjOn modularJInQ (Metric.ball 0 R)) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im)
    (hzR : ‖exponential z‖ < R) (hwR : ‖exponential w‖ < R)
    (hj : modularJ (UpperHalfPlane.ofComplex z) =
      modularJ (UpperHalfPlane.ofComplex w)) : exponential z = exponential w := by
  apply hR
  · simpa only [Metric.mem_ball, dist_zero_right] using hzR
  · simpa only [Metric.mem_ball, dist_zero_right] using hwR
  · rw [modularJInQ_exponential hz, modularJInQ_exponential hw]
    exact hj

/-- Continuous lifts of equal actual modular j-values in a fixed injective
cusp region differ by a single integer on a nonempty preconnected space. -/
theorem high_cusp_lifts_eq_int_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {R : ℝ} (hR : Set.InjOn modularJInQ (Metric.ball 0 R))
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ x, 0 < (f x).im) (hgpos : ∀ x, 0 < (g x).im)
    (hfR : ∀ x, ‖exponential (f x)‖ < R)
    (hgR : ∀ x, ‖exponential (g x)‖ < R)
    (hj : ∀ x, modularJ (UpperHalfPlane.ofComplex (f x)) =
      modularJ (UpperHalfPlane.ofComplex (g x))) :
    ∃ k : ℤ, ∀ x, f x = g x + k := by
  apply continuous_exponential_eq_int_constant hf hg
  intro x
  exact exponential_eq_of_modularJ_eq hR (hfpos x) (hgpos x) (hfR x) (hgR x) (hj x)

universe u

/-- One positive cusp radius works for every nonempty preconnected domain
and every pair of continuous upper-half-plane-valued lifts. The input is
equality of actual modular j-values, not an assumed equality of q-values. -/
theorem exists_high_cusp_comparison_radius :
    ∃ R : ℝ, 0 < R ∧
      ∀ {X : Type u} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
        {f g : X → ℂ}, Continuous f → Continuous g →
        (∀ x, 0 < (f x).im) → (∀ x, 0 < (g x).im) →
        (∀ x, ‖exponential (f x)‖ < R) → (∀ x, ‖exponential (g x)‖ < R) →
        (∀ x, modularJ (UpperHalfPlane.ofComplex (f x)) =
          modularJ (UpperHalfPlane.ofComplex (g x))) →
        ∃ k : ℤ, ∀ x, f x = g x + k := by
  obtain ⟨R, hR, hinj⟩ := modularJInQ_injOn_small_disc
  refine ⟨R, hR, ?_⟩
  intro X _ _ _ f g hf hg hfpos hgpos hfR hgR hj
  exact high_cusp_lifts_eq_int_constant hinj hf hg hfpos hgpos hfR hgR hj

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
