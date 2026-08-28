import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFrames
import Mathlib.Analysis.Meromorphic.Order

/-!
# The actual sphere coordinates for the global base twist

The finite and reciprocal coordinates are functions on the existing
Riemann sphere.  Each is holomorphic on its own actual affine chart.
Their assigned values at the missing chart points are only total-function
conventions, not assertions of holomorphic extension there.  On the
actual overlap the two coordinates are nonzero and mutually inverse.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open RiemannSphere
open HolomorphicFunctionSheaf.SphereH1
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The finite coordinate, assigned the arbitrary value zero at infinity. -/
def finiteCoordinate : RiemannSphere → ℂ := fromFinite id 0

/-- The reciprocal coordinate, assigned zero at the omitted finite origin.
Its value zero at infinity is its actual holomorphic chart value. -/
def infinityCoordinate : RiemannSphere → ℂ := fromFinite (fun z => z⁻¹) 0

@[simp] theorem finiteCoordinate_coe (z : ℂ) :
    finiteCoordinate (z : RiemannSphere) = z := rfl

@[simp] theorem finiteCoordinate_infty : finiteCoordinate (∞ : RiemannSphere) = 0 := rfl

@[simp] theorem infinityCoordinate_coe (z : ℂ) :
    infinityCoordinate (z : RiemannSphere) = z⁻¹ := rfl

@[simp] theorem infinityCoordinate_infty :
    infinityCoordinate (∞ : RiemannSphere) = 0 := rfl

/-- The reciprocal coordinate is exactly the parameter of the existing
infinity chart, including its centre. -/
@[simp] theorem infinityCoordinate_infinityParametrization (u : ℂ) :
    infinityCoordinate (infinityParametrization u) = u :=
  infinityFrame_parametrization infinityChart le_rfl u (infinityParametrization_mem u)

/-- In the reciprocal chart the finite coordinate has its usual pole
formula; the equality also holds at zero with the total-function convention. -/
@[simp] theorem finiteCoordinate_onparam (u : ℂ) :
    finiteCoordinate (infinityParametrization u) = u⁻¹ := by
  by_cases hu : u = 0
  · subst u
    simp only [infinityParametrization_zero, finiteCoordinate_infty, inv_zero]
  · exact fromFinite_infinityParametrization id 0 hu

theorem infinityCoordinate_eq_inv_finiteCoordinate (p : RiemannSphere) :
    infinityCoordinate p = (finiteCoordinate p)⁻¹ := by
  induction p using OnePoint.rec with
  | infty => simp only [infinityCoordinate_infty, finiteCoordinate_infty, inv_zero]
  | coe z => rfl

/-- Holomorphicity in the original finite affine chart. -/
theorem finiteCoordinate_holomorphicOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω finiteCoordinate (finiteChart : Set RiemannSphere) := by
  intro p hp
  induction p using OnePoint.rec with
  | infty => exact (infty_not_mem_finiteChart hp).elim
  | coe z =>
    exact (fromFinite_contMDiffAt_coe id 0 z analyticAt_id).contMDiffWithinAt

/-- Holomorphicity in the original reciprocal chart, obtained from its
already proved holomorphic ideal-sheaf frame. -/
theorem infinityCoordinate_holomorphicOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω infinityCoordinate (infinityChart : Set RiemannSphere) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun p : infinityChart => infinityCoordinate (p : RiemannSphere)) :=
    (infinityFrame infinityChart le_rfl).val.contMDiff
  intro p hp
  exact (contMDiffAt_subtype_iff.mp (h ⟨p, hp⟩)).contMDiffWithinAt

/-- The actual finite chart is dense in the existing sphere topology. -/
theorem finiteChart_dense : Dense (finiteChart : Set RiemannSphere) :=
  OnePoint.denseRange_coe

theorem finiteCoordinate_ne_zero {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    finiteCoordinate p ≠ 0 := by
  induction p using OnePoint.rec with
  | infty => exact (infty_not_mem_finiteChart hp.1).elim
  | coe z => exact (coe_mem_infinityChart_iff z).mp hp.2

theorem infinityCoordinate_ne_zero {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    infinityCoordinate p ≠ 0 := by
  rw [infinityCoordinate_eq_inv_finiteCoordinate]
  exact inv_ne_zero (finiteCoordinate_ne_zero hp)

theorem finiteCoordinate_mul_infinityCoordinate {p : RiemannSphere}
    (hp : p ∈ chartOverlap) : finiteCoordinate p * infinityCoordinate p = 1 := by
  rw [infinityCoordinate_eq_inv_finiteCoordinate]
  exact mul_inv_cancel₀ (finiteCoordinate_ne_zero hp)

theorem infinityCoordinate_mul_finiteCoordinate {p : RiemannSphere}
    (hp : p ∈ chartOverlap) : infinityCoordinate p * finiteCoordinate p = 1 := by
  rw [mul_comm]
  exact finiteCoordinate_mul_infinityCoordinate hp

/-- The finite coordinate has meromorphic order minus one at infinity,
computed in the actual reciprocal-coordinate parametrization. -/
theorem finiteCoordinate_meromorphicOrderAt_infty :
    meromorphicOrderAt (fun u : ℂ => finiteCoordinate (infinityParametrization u)) 0 = -1 := by
  have h : (fun u : ℂ => finiteCoordinate (infinityParametrization u)) =
      (id : ℂ → ℂ)⁻¹ := funext finiteCoordinate_onparam
  rw [h, meromorphicOrderAt_inv, meromorphicOrderAt_id]

/-- The reciprocal local fraction `1/w` used for the infinity divisor
has its genuine simple pole, in the same actual infinity chart. -/
theorem inverse_infinityCoordinate_meromorphicOrderAt_infty :
    meromorphicOrderAt (fun u : ℂ =>
      (infinityCoordinate (infinityParametrization u))⁻¹) 0 = -1 := by
  have h : (fun u : ℂ => (infinityCoordinate (infinityParametrization u))⁻¹) =
      (id : ℂ → ℂ)⁻¹ := by
    funext u
    exact congrArg Inv.inv (infinityCoordinate_infinityParametrization u)
  rw [h, meromorphicOrderAt_inv, meromorphicOrderAt_id]

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
