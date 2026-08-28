import Wikipedia.NoExoticSixSphere.QuadraticRadialCompression

/-!
# Successive quadratic radial compressions add their denominators

This identity allows a cylindrical tube to be compressed in the newly
adjoined normal direction while retaining its original transverse tube.
The quadratic forms may be degenerate; no positive-definiteness premise
or artificial lower bound is introduced.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.QuadraticCompression

open NoExoticSixSphere.QuadraticRadialCompression

theorem sqrt_sum_factor (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (1 + a / (1 + b)) * Real.sqrt (1 + b) =
      Real.sqrt (1 + (a + b)) := by
  have hden : 0 < 1 + b := by linarith
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp
  ring

variable {B E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (q₀ q₁ : B × E → ℝ)
  (h₀ : ∀ b c v, q₀ (b, c • v) = c ^ 2 * q₀ (b, v))
  (hn₀ : ∀ p, 0 ≤ q₀ p) (hn₁ : ∀ p, 0 ≤ q₁ p)

include h₀ hn₁ in
theorem quadratic_after_compress (p : B × E) :
    q₀ (compress q₁ p) = q₀ p / (1 + q₁ p) := by
  change q₀ (p.1, (Real.sqrt (1 + q₁ p))⁻¹ • p.2) = _
  rw [h₀, inv_pow, Real.sq_sqrt (by linarith [hn₁ p])]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

include h₀ hn₀ hn₁ in
theorem compress_compress (p : B × E) :
    compress q₀ (compress q₁ p) = compress (fun z ↦ q₀ z + q₁ z) p := by
  refine Prod.ext rfl ?_
  change (Real.sqrt (1 + q₀ (compress q₁ p)))⁻¹ •
    ((Real.sqrt (1 + q₁ p))⁻¹ • p.2) =
      (Real.sqrt (1 + (q₀ p + q₁ p)))⁻¹ • p.2
  rw [quadratic_after_compress q₀ q₁ h₀ hn₁, smul_smul, ← mul_inv,
    sqrt_sum_factor (q₀ p) (q₁ p) (hn₀ p) (hn₁ p)]

theorem compress_zero (p : B × E) : compress (fun _ : B × E ↦ (0 : ℝ)) p = p := by
  refine Prod.ext rfl ?_
  change (Real.sqrt (1 + 0))⁻¹ • p.2 = p.2
  rw [add_zero, Real.sqrt_one, inv_one, one_smul]

end Wikipedia.HopfProblem.DegreeCollapse.QuadraticCompression
