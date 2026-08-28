import Wikipedia.HopfProblem.PeriodTorusThetaNorm
import Mathlib.Analysis.Complex.Liouville

/-!
# Entire theta functions for the zero Hermitian form

For the actual full period lattice, a unitary transformation law with
zero Hermitian form makes the norm periodic. The resulting global bound
and Liouville's theorem force the entire function to be constant. If it
is nonzero, its actual multiplier is identically one.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

theorem zero_isHermitian : IsHermitian (0 : HermitianForm) := by
  intro x y
  simp

/-- A genuine entire theta function for the zero form is constant. -/
theorem theta_eq_at_zero_of_zero_form (p : PeriodDomain)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p 0 α θ) (z : ComplexPlane₂) :
    θ z = θ 0 := by
  obtain ⟨C, _, hC⟩ := theta_norm_bound p 0 zero_isHermitian α hα θ hθ.continuous hAuto
  have hb : Bornology.IsBounded (Set.range θ) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa using hC w
  exact hθ.apply_eq_apply_of_bounded hb z 0

/-- Nonzero constancy forces the actual unitary multiplier to be trivial. -/
theorem multiplier_eq_one_of_zero_form (p : PeriodDomain)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p 0 α θ)
    (hNonzero : ∃ z, θ z ≠ 0) (l : p.lattice) : α l = 1 := by
  have hc := theta_eq_at_zero_of_zero_form p α hα θ hθ hAuto
  have h0 : θ 0 ≠ 0 := by
    obtain ⟨z, hz⟩ := hNonzero
    simpa only [hc z] using hz
  have hm : α l * θ 0 = θ 0 := by
    calc
      α l * θ 0 = θ (0 + (l : ComplexPlane₂)) := by
        simpa using (hAuto l 0).symm
      _ = θ 0 := hc _
  apply mul_right_cancel₀ h0
  simpa using hm

theorem exists_nonzero_const_of_zero_form (p : PeriodDomain)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p 0 α θ)
    (hNonzero : ∃ z, θ z ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ θ = (fun _ => c) ∧ ∀ l, α l = 1 := by
  have hc := theta_eq_at_zero_of_zero_form p α hα θ hθ hAuto
  refine ⟨θ 0, ?_, funext hc, multiplier_eq_one_of_zero_form p α hα θ hθ hAuto hNonzero⟩
  obtain ⟨z, hz⟩ := hNonzero
  simpa only [hc z] using hz

end Wikipedia.HopfProblem.PeriodTorusTheta
