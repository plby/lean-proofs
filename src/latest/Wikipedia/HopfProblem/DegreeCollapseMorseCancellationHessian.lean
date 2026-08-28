import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationModel
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Nondegeneracy of the cubic model away from the cancellation parameter

The Hessian is the actual second Frechet derivative, not an assigned matrix.
Evaluating it on the scalar and transverse coordinate vectors proves
injectivity; equality with the dual dimension gives bijectivity.
-/

noncomputable section

open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare

variable {m : ℕ} (σ : Fin m → ℝ)

def hessian (p : Model m) : Model m →L[ℝ] Model m →L[ℝ] ℝ :=
  (2 * p.1) • (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).smulRight
    (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) +
  ∑ i, (2 * σ i) •
    (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).smulRight
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))

theorem hessian_apply (p v w : Model m) :
    hessian σ p v w = 2 * p.1 * v.1 * w.1 +
      ∑ i, 2 * σ i * v.2 i * w.2 i := by
  simp [hessian, mul_assoc]

theorem hasFDerivAt_differential (t : ℝ) (p : Model m) :
    HasFDerivAt (differential σ t) (hessian σ p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  let L (i : Fin m) : Model m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
  have hq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (((L i).hasFDerivAt (x := p)).const_mul (2 * σ i)).smul_const (L i))
  convert (((hx.pow 2).add_const t).smul_const
    (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))).add hq using 1 <;>
    first
    | rfl
    | (apply ContinuousLinearMap.ext; intro v
       apply ContinuousLinearMap.ext; intro w
       simp [hessian, L, mul_assoc])

theorem fderiv_cubic_hessian (t : ℝ) (p : Model m) :
    fderiv ℝ (fderiv ℝ (cubic σ t)) p = hessian σ p := by
  rw [show fderiv ℝ (cubic σ t) = differential σ t from funext (fderiv_cubic σ t)]
  exact (hasFDerivAt_differential σ t p).fderiv

theorem hessian_bijective (hσ : ∀ i, σ i ≠ 0) {p : Model m} (hp : p.1 ≠ 0) :
    Function.Bijective (hessian σ p) := by
  have hi : Function.Injective (hessian σ p) := by
    apply (injective_iff_map_eq_zero (hessian σ p)).mpr
    intro v hv
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hv
    have hx' : 2 * p.1 * v.1 = 0 := by simpa [hessian_apply] using hx
    have hvx : v.1 = 0 :=
      (mul_eq_zero.mp hx').resolve_left (mul_ne_zero (by norm_num) hp)
    apply Prod.ext hvx
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hv
    have hy' : 2 * σ i * v.2 i = 0 := by
      simpa [hessian_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  have hd : Module.finrank ℝ (Model m) = Module.finrank ℝ (Model m →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Model m →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = _ := (LinearMap.toContinuousLinearMap :
        (Model m →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Model m →L[ℝ] ℝ)).finrank_eq
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (hessian σ p).toLinearMap) hd).mp hi⟩

/-- Both nonzero sides of the parameter family are genuine Morse functions. -/
theorem cubic_isMorse (hσ : ∀ i, σ i ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    MorsePerturbation.IsMorse (cubic σ t) := by
  intro p hcrit
  rw [fderiv_cubic_hessian]
  apply hessian_bijective σ hσ
  intro hp
  have h := ((critical_iff σ hσ t p).mp hcrit).1
  exact ht (by simpa [hp] using h)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
