import Wikipedia.HopfProblem.PeriodTorusThetaNorm
import Wikipedia.HopfProblem.PeriodTorusThetaLine
import Wikipedia.HopfProblem.PeriodTorusThetaGaussian

/-!
# Positivity forced by a genuine nonzero entire theta function

Appell--Humbert automorphy on the actual full period lattice gives a
globally bounded weighted norm. A negative Hermitian direction would
then give a normalized entire function of one complex variable with
Gaussian decay. Liouville's theorem forces that function to vanish,
contradicting the chosen nonzero value of the original theta function.

Only the explicit transformation law is used: no classification of
line bundles or identification of their holomorphic sections is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

/-- A nonzero entire theta function forces the actual Hermitian form to
be nonnegative on every diagonal, hence positive semidefinite. -/
theorem hermitian_nonnegative_of_nonzero_theta (p : PeriodDomain)
    (H : HermitianForm) (hH : IsHermitian H)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p H α θ)
    (hNonzero : ∃ z, θ z ≠ 0) (v : ComplexPlane₂) : 0 ≤ (H v v).re := by
  by_contra hNeg
  have hv : (H v v).re < 0 := lt_of_not_ge hNeg
  obtain ⟨C, hC, hbound⟩ := theta_norm_bound p H hH α hα θ hθ.continuous hAuto
  obtain ⟨z, hz⟩ := hNonzero
  have hC0 : 0 ≤ C * Real.exp ((Real.pi / 2) * (H z z).re) :=
    mul_nonneg hC.le (Real.exp_pos _).le
  have ha : (Real.pi / 2) * (H v v).re < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hv
  have hzero := gaussian_decay_entire_zero (normalizedLine H θ z v)
    (differentiable_normalizedLine H θ hθ z v)
    (C * Real.exp ((Real.pi / 2) * (H z z).re)) ((Real.pi / 2) * (H v v).re)
    hC0 ha (normalizedLine_norm_bound H hH θ C hbound z v)
  exact hz (by simpa using hzero)

/-- A single actual negative direction excludes every nonzero entire theta function. -/
theorem theta_eq_zero_of_negative_direction (p : PeriodDomain)
    (H : HermitianForm) (hH : IsHermitian H)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p H α θ)
    (v : ComplexPlane₂) (hv : (H v v).re < 0) : θ = 0 := by
  funext z
  by_contra hz
  have hNonzero : ∃ w, θ w ≠ 0 := ⟨z, hz⟩
  exact (not_le_of_gt hv)
    (hermitian_nonnegative_of_nonzero_theta p H hH α hα θ hθ hAuto hNonzero v)

end Wikipedia.HopfProblem.PeriodTorusTheta
