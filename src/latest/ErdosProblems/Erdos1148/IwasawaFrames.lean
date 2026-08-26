import ErdosProblems.Erdos1148.RotationFrames
import ErdosProblems.Erdos1148.ModularCompactCore

/-! # Upper-half-plane and angular coordinates for modular frames -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem rotation_entries_of_fix_I (g : SL(2, ℝ)) (hg : g • UpperHalfPlane.I = UpperHalfPlane.I) :
    g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  have h := congrArg (fun z : UpperHalfPlane => (z : ℂ)) hg
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h
  change ((g 0 0 : ℂ) * Complex.I + (g 0 1 : ℂ)) /
    ((g 1 0 : ℂ) * Complex.I + (g 1 1 : ℂ)) = Complex.I at h
  have hden : (g 1 0 : ℂ) * Complex.I + (g 1 1 : ℂ) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero
      (Matrix.SpecialLinearGroup.mapGL ℝ g) UpperHalfPlane.I
  have heq := (div_eq_iff hden).mp h
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_sub,
    add_zero, zero_add, mul_one, one_mul, Complex.add_im, Complex.mul_im] at hre him
  exact ⟨him, hre⟩

theorem exists_upperHalfPlane_rotation_frame (g : SL(2, ℝ)) :
    ∃ θ ∈ Set.Icc (-Real.pi) Real.pi,
      g = (g • UpperHalfPlane.I).toSL2R * rotationFrame θ := by
  let z := g • UpperHalfPlane.I
  let k := z.toSL2R⁻¹ * g
  have hk : k • UpperHalfPlane.I = UpperHalfPlane.I := by
    dsimp only [k]
    rw [mul_smul]
    change z.toSL2R⁻¹ • z = UpperHalfPlane.I
    simpa only [inv_smul_smul] using
      (congrArg (fun w : UpperHalfPlane => z.toSL2R⁻¹ • w)
        (UpperHalfPlane.toSL2R_smul_I z)).symm
  obtain ⟨ha, hb⟩ := rotation_entries_of_fix_I k hk
  obtain ⟨θ, hθ, hrot⟩ := exists_rotationFrame_of_entries k ha hb
  refine ⟨θ, hθ, ?_⟩
  rw [hrot]
  change g = z.toSL2R * (z.toSL2R⁻¹ * g)
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

theorem exists_modular_fundamental_frame (x : ModularOrbitSpace) :
    ∃ (z : UpperHalfPlane) (θ : ℝ), z ∈ ModularGroup.fd ∧
      θ ∈ Set.Icc (-Real.pi) Real.pi ∧ modularMk (z.toSL2R * rotationFrame θ) = x := by
  let g : SL(2, ℝ) := x.out
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd (g • UpperHalfPlane.I)
  let g' : SL(2, ℝ) := (γ : SL(2, ℝ)) * g
  have hfd : g' • UpperHalfPlane.I ∈ ModularGroup.fd := by
    change ((γ : SL(2, ℝ)) * g) • UpperHalfPlane.I ∈ _
    rw [mul_smul]
    convert hγ using 1
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    congr 1
  obtain ⟨θ, hθ, hg'⟩ := exists_upperHalfPlane_rotation_frame g'
  refine ⟨g' • UpperHalfPlane.I, θ, hfd, hθ, ?_⟩
  rw [← hg']
  exact (modularMk_integral_mul γ g).trans (Quotient.out_eq x)

end Erdos1148.DukeArithmetic
