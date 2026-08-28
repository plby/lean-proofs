import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Normalized complex phases, with their exact unit-circle covariance -/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.OrbitPair

def complexPhase (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)])⟩

theorem complexPhase_congr {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (h : z = w) :
    complexPhase z hz = complexPhase w hw := by
  apply Circle.ext
  change ‖z‖⁻¹ • z = ‖w‖⁻¹ • w
  rw [h]

theorem complexPhase_mul_circle (u : Circle) (z : ℂ) (hz : z ≠ 0) :
    complexPhase ((u : ℂ) * z) (mul_ne_zero u.coe_ne_zero hz) = u * complexPhase z hz := by
  apply Circle.ext
  change ‖(u : ℂ) * z‖⁻¹ • ((u : ℂ) * z) = (u : ℂ) * (‖z‖⁻¹ • z)
  rw [norm_mul, Circle.norm_coe, one_mul, mul_smul_comm]

theorem complexPhase_positive_real (r : ℝ) (hr : 0 < r) :
    complexPhase (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') = 1 := by
  apply Circle.ext
  change ‖(r : ℂ)‖⁻¹ • (r : ℂ) = 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.real_smul,
    Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')]

theorem complexPhase_continuous {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (hn : ∀ x, f x ≠ 0) : Continuous (fun x => complexPhase (f x) (hn x)) :=
  ((hf.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hn x))).smul hf).subtype_mk _

end Wikipedia.HopfProblem.OrbitPair
