import Wikipedia.HopfProblem.ToricMonomialDerivative
import Wikipedia.HopfProblem.ToricFan
import Wikipedia.HopfProblem.ToricSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Determinant

/-!
# The signed holomorphic volume coordinates of the toric cusp charts

The Jacobian of a height-one monomial coordinate change has constant
determinant.  We first compute the actual Fréchet derivative on the dense
torus, then extend the determinant identity to the whole open chart overlap,
including all boundary strata.  The signs of the ray determinants give the
precise gluing rule for coordinate volume elements.

This file proves the derivative and gluing identities; it does not assert a
global canonical-bundle trivialization without constructing one.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem

namespace ToricCharts

theorem monomial_prod_heightOne (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : HeightOne A)
    {z : CoordinateSpace 3} (hz : z ∈ torus) :
    (∏ i, monomial A z i) = ∏ j, z j := by
  change (∏ i, ∏ j, z j ^ A i j) = _
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  have he := congrArg (fun k : ℤ => z j ^ k) (hA j)
  simpa [Fin.sum_univ_succ, Fin.prod_univ_succ, zpow_add₀ (hz j)] using he

/-- The height-one condition exactly cancels the logarithmic coordinate
denominators in the Jacobian determinant. -/
theorem monomial_jacobian_det_on_torus (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : HeightOne A) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    (jacobianMatrix (monomial A) z).det = (A.det : ℂ) := by
  rw [jacobianMatrix_monomial A hz, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, monomial_prod_heightOne A hA hz]
  have hcast : (A.map (Int.castRingHom ℂ)).det = (A.det : ℂ) :=
    (Int.castRingHom ℂ |>.map_det A).symm
  rw [hcast, Finset.prod_inv_distrib]
  have hprod : (∏ j, z j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hz j
  calc
    (∏ j, z j) * (A.det : ℂ) * (∏ j, z j)⁻¹ =
        (A.det : ℂ) * ((∏ j, z j) * (∏ j, z j)⁻¹) := by ring
    _ = (A.det : ℂ) := by rw [mul_inv_cancel₀ hprod, mul_one]

theorem jacobianMatrix_continuousOn {d : ℕ}
    {f : CoordinateSpace d → CoordinateSpace d} {S : Set (CoordinateSpace d)}
    (hf : ContDiffOn ℂ ω f S) (hS : IsOpen S) :
    ContinuousOn (jacobianMatrix f) S := by
  have hd := hf.continuousOn_fderiv_of_isOpen hS (by simp)
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (continuous_apply i).comp_continuousOn (hd.clm_apply continuousOn_const)

theorem jacobianMatrix_det_continuousOn {d : ℕ}
    {f : CoordinateSpace d → CoordinateSpace d} {S : Set (CoordinateSpace d)}
    (hf : ContDiffOn ℂ ω f S) (hS : IsOpen S) :
    ContinuousOn (fun z => (jacobianMatrix f z).det) S :=
  (continuous_id.matrix_det :
    Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => A.det)).comp_continuousOn
    (jacobianMatrix_continuousOn hf hS)

/-- The determinant identity also holds at points with zero coordinates,
provided the monomial substitution is holomorphic there. -/
theorem monomial_jacobian_det (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : HeightOne A)
    {z : CoordinateSpace 3} (hz : z ∈ domain A) :
    (jacobianMatrix (monomial A) z).det = (A.det : ℂ) := by
  have he : EqOn (fun w => (jacobianMatrix (monomial A) w).det)
      (fun _ => (A.det : ℂ)) (domain A ∩ torus) :=
    fun _ hw => monomial_jacobian_det_on_torus A hA hw.2
  exact he.of_subset_closure
    (jacobianMatrix_det_continuousOn (monomial_contDiffOn A ω) (domain_open A))
    continuousOn_const inter_subset_left
    (torus_dense.open_subset_closure_inter (domain_open A)) hz

/-- This determinant is the usual determinant of the complex Fréchet
derivative, not an independently specified exponent-matrix quantity. -/
theorem jacobianMatrix_det_eq_fderiv_det {d : ℕ}
    (f : CoordinateSpace d → CoordinateSpace d) (z : CoordinateSpace d) :
    (jacobianMatrix f z).det = LinearMap.det (fderiv ℂ f z).toLinearMap := by
  have he : jacobianMatrix f z = LinearMap.toMatrix' (fderiv ℂ f z).toLinearMap := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [he, LinearMap.det_toMatrix']

end ToricCharts

namespace ToricFan.Triangle

open ToricCharts

/-- The sign of a coordinate transition is the ratio of its two ray-basis
orientations. This integral identity also avoids choosing either sign. -/
theorem rays_det_mul_transition_det (s t : Triangle) :
    t.rays.det * (transition s t).det = s.rays.det := by
  simpa only [Matrix.det_mul] using congrArg Matrix.det (transition_covariance s t)

theorem transition_det_eq_div (s t : Triangle) :
    ((transition s t).det : ℂ) = (s.rays.det : ℂ) / (t.rays.det : ℂ) := by
  have ht : (t.rays.det : ℂ) ≠ 0 := by exact_mod_cast t.rays_unimodular.ne_zero
  apply (eq_div_iff ht).mpr
  rw [mul_comm]
  exact_mod_cast rays_det_mul_transition_det s t

theorem transition_det_eq_one_or_neg_one (s t : Triangle) :
    (transition s t).det = 1 ∨ (transition s t).det = -1 := by
  have he := rays_det_mul_transition_det s t
  rw [rays_det, rays_det] at he
  cases hs : s.upper <;> cases ht : t.upper <;> simp_all
  omega

/-- The actual analytic chart changes have constant complex Jacobian,
on their whole open source, including boundary points. -/
theorem chartChange_jacobian_det (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    (jacobianMatrix (chartChange s t) z).det = ((transition s t).det : ℂ) := by
  exact monomial_jacobian_det (transition s t) (transition_heightOne s t)
    (by simpa only [chartChange_source] using hz)

theorem chartChange_det_fderiv (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    LinearMap.det (fderiv ℂ (chartChange s t) z).toLinearMap =
      (s.rays.det : ℂ) / (t.rays.det : ℂ) := by
  rw [← jacobianMatrix_det_eq_fderiv_det, chartChange_jacobian_det s t hz,
    transition_det_eq_div]

theorem chartChange_det_fderivWithin (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    LinearMap.det (fderivWithin ℂ (chartChange s t) (chartChange s t).source z).toLinearMap =
      (s.rays.det : ℂ) / (t.rays.det : ℂ) := by
  rw [fderivWithin_of_isOpen (chartChange s t).open_source hz]
  exact chartChange_det_fderiv s t hz

theorem chartChange_jacobian_det_eq_one_or_neg_one (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    (jacobianMatrix (chartChange s t) z).det = 1 ∨
      (jacobianMatrix (chartChange s t) z).det = -1 := by
  rw [chartChange_jacobian_det s t hz]
  rcases transition_det_eq_one_or_neg_one s t with he | he
  · left
    simp only [he, Int.cast_one]
  · right
    simp only [he, Int.cast_neg, Int.cast_one]

/-- The constant signed coordinate-volume coefficients obey exactly the
Jacobian gluing identity. Each coefficient is nonzero by unimodularity. -/
theorem chartChange_signed_volume (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    (t.rays.det : ℂ) * (jacobianMatrix (chartChange s t) z).det = (s.rays.det : ℂ) := by
  rw [chartChange_jacobian_det s t hz]
  exact_mod_cast rays_det_mul_transition_det s t

theorem signed_volume_coefficient_ne_zero (s : Triangle) : (s.rays.det : ℂ) ≠ 0 := by
  exact_mod_cast s.rays_unimodular.ne_zero

end ToricFan.Triangle

namespace ToricSpace

open ToricCharts ToricFan Triangle

/-- The derivative of the transition between the actual charts of the glued
space is the derivative of its displayed monomial substitution. -/
theorem parametrization_transition_fderiv (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ ((parametrization s).trans (parametrization t).symm).source) :
    fderiv ℂ ((parametrization s).trans (parametrization t).symm) z =
      fderiv ℂ (chartChange s t) z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((parametrization s).trans (parametrization t).symm).open_source.mem_nhds hz]
    with w hw
  exact (parametrization_transition s t (by simpa using hw.2)).2

theorem parametrization_transition_det_fderiv (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ ((parametrization s).trans (parametrization t).symm).source) :
    LinearMap.det
      (fderiv ℂ ((parametrization s).trans (parametrization t).symm) z).toLinearMap =
        (s.rays.det : ℂ) / (t.rays.det : ℂ) := by
  rw [parametrization_transition_fderiv s t hz]
  exact chartChange_det_fderiv s t
    (parametrization_transition s t (by simpa using hz.2)).1

/-- Signed volume coefficients glue for the genuine holomorphic atlas of
the toric space, including overlap points on its boundary divisor. -/
theorem parametrization_transition_signed_volume (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ ((parametrization s).trans (parametrization t).symm).source) :
    (t.rays.det : ℂ) * LinearMap.det
      (fderiv ℂ ((parametrization s).trans (parametrization t).symm) z).toLinearMap =
        (s.rays.det : ℂ) := by
  rw [parametrization_transition_fderiv s t hz, ← jacobianMatrix_det_eq_fderiv_det]
  exact chartChange_signed_volume s t
    (parametrization_transition s t (by simpa using hz.2)).1

end ToricSpace

end Wikipedia.HopfProblem
