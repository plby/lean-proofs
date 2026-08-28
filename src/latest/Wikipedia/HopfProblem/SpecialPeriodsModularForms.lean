import Wikipedia.HopfProblem.SpecialPeriodsLocal
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The elliptic values of the normalized Eisenstein series

The series in this file are Mathlib's actual level-one forms, not abstract
functions with prescribed values.  Their vanishing at the elliptic points
follows from the modular transformation law.  The complementary values are
nonzero because the modular discriminant has no zeros in the upper half-plane.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The paper's order-three elliptic point, as an upper-half-plane point. -/
def rhoPoint : ℍ := ⟨rho, rho_im_pos⟩

@[simp] theorem coe_rhoPoint : (rhoPoint : ℂ) = rho := rfl

theorem rho_ne_zero : rho ≠ 0 := rhoPoint.ne_zero

theorem rho_fourth : rho ^ 4 = -rho := by
  calc
    rho ^ 4 = rho ^ 3 * rho := by ring
    _ = -rho := by rw [rho_cube]; ring

theorem rho_fourth_ne_one : rho ^ 4 ≠ 1 := by
  intro h
  have hr : rho = -1 := neg_eq_iff_eq_neg.mp (rho_fourth.symm.trans h)
  have := rho_im_pos
  simp [hr] at this

/-- The matrix `TS` fixes the paper's point `ρ = exp(πi/3)`. -/
theorem TS_smul_rhoPoint : (T * S) • rhoPoint = rhoPoint := by
  rw [mul_smul, modular_T_smul, modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [coe_vadd, Complex.ofReal_one, coe_rhoPoint, inv_neg]
  field_simp [rho_ne_zero]
  linear_combination -rho_sq

/-- The matrix `S` fixes `i`. -/
theorem S_smul_I : S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [coe_I, inv_neg, Complex.inv_I, neg_neg]

/-- The standard modular transformation law, with an explicit integral matrix. -/
theorem levelOne_transform {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (g : SL(2, ℤ)) (z : ℍ) :
    f (g • z) = (denom g z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn'' f
    (show (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨g, rfl⟩) z

/-- The weight-four normalized Eisenstein series vanishes at `ρ`. -/
theorem E₄_rhoPoint : E₄ rhoPoint = 0 := by
  have h := levelOne_transform E₄ (T * S) rhoPoint
  rw [TS_smul_rhoPoint] at h
  have hd : denom (T * S : SL(2, ℤ)) rhoPoint = rho := by
    have h10 : (T * S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (T * S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [denom_apply, h10, h11]
    simp
  rw [hd, zpow_ofNat] at h
  exact (mul_eq_zero.mp (show (rho ^ 4 - 1) * E₄ rhoPoint = 0 by
    linear_combination -h)).resolve_left (sub_ne_zero.mpr rho_fourth_ne_one)

/-- The weight-six normalized Eisenstein series vanishes at `i`. -/
theorem E₆_I : E₆ UpperHalfPlane.I = 0 := by
  have h := levelOne_transform E₆ S UpperHalfPlane.I
  rw [S_smul_I, denom_S, coe_I, zpow_ofNat] at h
  have hi : Complex.I ^ 6 = -1 := by norm_num [Complex.I_sq, pow_succ]
  rw [hi] at h
  linear_combination h / 2

/-- `E₄` and `E₆` cannot vanish simultaneously anywhere in `ℍ`. -/
theorem E₄_E₆_not_both_zero (z : ℍ) : E₄ z ≠ 0 ∨ E₆ z ≠ 0 := by
  by_contra! h
  have hd := discriminant_ne_zero z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h.1, h.2] at hd
  norm_num at hd

/-- The complementary Eisenstein value at `ρ` is nonzero. -/
theorem E₆_rhoPoint_ne_zero : E₆ rhoPoint ≠ 0 := by
  simpa only [E₄_rhoPoint, ne_self_iff_false, false_or] using
    E₄_E₆_not_both_zero rhoPoint

/-- The complementary Eisenstein value at `i` is nonzero. -/
theorem E₄_I_ne_zero : E₄ UpperHalfPlane.I ≠ 0 := by
  simpa only [E₆_I, ne_self_iff_false, or_false] using
    E₄_E₆_not_both_zero UpperHalfPlane.I

/-- Below weight twelve, the constant Fourier coefficient determines a
level-one modular form. -/
theorem levelOne_eq_of_qExpansion_coeff_zero {k : ℤ} (hk : k < 12)
    (f g : ModularForm 𝒮ℒ k)
    (hfg : (qExpansion 1 f).coeff 0 = (qExpansion 1 g).coeff 0) : f = g := by
  have hq : (qExpansion 1 (f - g)).coeff 0 = 0 := by
    rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      map_sub, hfg, sub_self]
  have hzero : toCuspForm (f - g) hq = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  ext z
  have hz := congrArg (fun F : CuspForm 𝒮ℒ k => F z) hzero
  exact sub_eq_zero.mp hz

/-- A modular form is analytic in the usual complex coordinate at every
upper-half-plane point. -/
theorem modularForm_analyticAt {k : ℤ} (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    AnalyticAt ℂ (f ∘ ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticOnNhd
    isOpen_upperHalfPlaneSet _ z.im_pos

end Wikipedia.HopfProblem.SpecialPeriods
