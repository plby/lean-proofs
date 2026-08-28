import Wikipedia.HopfProblem.PeriodTori
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Appell--Humbert automorphy on the actual period lattice

The forms are complex-linear in the first argument and conjugate-linear
in the second.  The automorphy datum `α` is not asserted to be additive:
the norm-one condition used later is a separate hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

abbrev HermitianForm := ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ

/-- Hermitian symmetry in the source's linear-first convention. -/
def IsHermitian (H : HermitianForm) : Prop :=
  ∀ x y, H y x = star (H x y)

/-- The actual Appell--Humbert transformation law for every lattice vector. -/
def AppellHumbertAutomorphy (p : PeriodDomain) (H : HermitianForm)
    (α : p.lattice → ℂ) (θ : ComplexPlane₂ → ℂ) : Prop :=
  ∀ (l : p.lattice) z, θ (z + l) = α l *
    Complex.exp ((Real.pi : ℂ) * H z l + ((Real.pi : ℂ) / 2) * H l l) * θ z

/-- Every sesquilinear form on this finite-dimensional space has the usual
finite coordinate expansion. -/
theorem hermitianForm_eq_sum (H : HermitianForm) (x y : ComplexPlane₂) :
    H x y = ∑ i : Fin 2, ∑ j : Fin 2,
      x i * star (y j) * H (Pi.single i 1) (Pi.single j 1) := by
  have hx : ∑ i : Fin 2, x i • Pi.single i (1 : ℂ) = x := by
    ext i
    fin_cases i <;> simp
  have hy : ∑ j : Fin 2, y j • Pi.single j (1 : ℂ) = y := by
    ext j
    fin_cases j <;> simp
  calc
    H x y = H (∑ i : Fin 2, x i • Pi.single i 1)
        (∑ j : Fin 2, y j • Pi.single j 1) := by rw [hx, hy]
    _ = _ := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        map_smulₛₗ, starRingEnd_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Joint continuity follows from the actual finite coordinate expansion. -/
theorem hermitianForm_continuous (H : HermitianForm) :
    Continuous (fun q : ComplexPlane₂ × ComplexPlane₂ => H q.1 q.2) := by
  have hc : Continuous (fun q : ComplexPlane₂ × ComplexPlane₂ =>
      ∑ i : Fin 2, ∑ j : Fin 2,
        q.1 i * star (q.2 j) * H (Pi.single i 1) (Pi.single j 1)) := by
    fun_prop
  convert hc using 1
  funext q
  exact hermitianForm_eq_sum H q.1 q.2

theorem hermitianForm_diagonal_continuous (H : HermitianForm) :
    Continuous (fun z : ComplexPlane₂ => H z z) :=
  (hermitianForm_continuous H).comp (continuous_id.prodMk continuous_id)

theorem IsHermitian.diagonal_im (H : HermitianForm) (hH : IsHermitian H)
    (z : ComplexPlane₂) : (H z z).im = 0 := by
  have h := congrArg Complex.im (hH z z)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- The real quadratic term changes by precisely the automorphy cross term. -/
theorem IsHermitian.diagonal_add_re (H : HermitianForm) (hH : IsHermitian H)
    (z w : ComplexPlane₂) :
    (H (z + w) (z + w)).re =
      (H z z).re + 2 * (H z w).re + (H w w).re := by
  simp only [map_add, LinearMap.add_apply, Complex.add_re, hH z w,
    Complex.star_def, Complex.conj_re]
  ring

/-- The weighted norm whose lattice periodicity is forced by automorphy. -/
def weightedNorm (H : HermitianForm) (θ : ComplexPlane₂ → ℂ) (z : ComplexPlane₂) : ℝ :=
  ‖θ z‖ * Real.exp (-(Real.pi / 2) * (H z z).re)

theorem weightedNorm_continuous (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (hθ : Continuous θ) : Continuous (weightedNorm H θ) :=
  hθ.norm.mul (Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_re.comp (hermitianForm_diagonal_continuous H))))

theorem weightedNorm_nonneg (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (z : ComplexPlane₂) : 0 ≤ weightedNorm H θ z :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

end Wikipedia.HopfProblem.PeriodTorusTheta
