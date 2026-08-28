import Wikipedia.HopfProblem.ToricCharts
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Jacobians of Laurent monomial maps

On the dense torus the derivative of a monomial substitution is its exponent
matrix multiplied by the image-coordinate and inverse-coordinate diagonal
factors. The matrix below is formed from the actual Fréchet derivative.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricCharts

variable {d : ℕ}

def jacobianMatrix (f : CoordinateSpace d → CoordinateSpace d) (z : CoordinateSpace d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (fderiv ℂ f z) (Pi.single j 1) i

theorem monomial_hasFDerivAt (A : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) :
    HasFDerivAt (monomial A)
      (ContinuousLinearMap.pi fun i => ∑ j,
        (monomial A z i * (A i j : ℂ) * (z j)⁻¹) •
          (ContinuousLinearMap.proj j : CoordinateSpace d →L[ℂ] ℂ)) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hj (j : Fin d) : HasFDerivAt (fun w : CoordinateSpace d => w j ^ A i j)
      (((A i j : ℂ) * z j ^ (A i j - 1)) •
        (ContinuousLinearMap.proj j : CoordinateSpace d →L[ℂ] ℂ)) z := by
    convert! (hasDerivAt_zpow (A i j) (z j) (Or.inl (hz j))).comp_hasFDerivAt z
      (hasFDerivAt_apply (𝕜 := ℂ) j z) using 1
  have hp := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hj j)
  convert! hp using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rw [zpow_sub_one₀ (hz j)]
  have hprod := Finset.prod_erase_mul (s := Finset.univ)
    (fun k => z k ^ A i k) (Finset.mem_univ j)
  change monomial A z i * (A i j : ℂ) * (z j)⁻¹ = _
  calc
    monomial A z i * (A i j : ℂ) * (z j)⁻¹ =
        ((∏ k ∈ Finset.univ.erase j, z k ^ A i k) * z j ^ A i j) *
          (A i j : ℂ) * (z j)⁻¹ := by rw [hprod]; rfl
    _ = _ := by ring

theorem jacobianMatrix_monomial_apply (A : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) (i j : Fin d) :
    jacobianMatrix (monomial A) z i j = monomial A z i * (A i j : ℂ) * (z j)⁻¹ := by
  rw [jacobianMatrix, (monomial_hasFDerivAt A hz).fderiv]
  simp [Pi.single_apply]

theorem jacobianMatrix_monomial (A : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) :
    jacobianMatrix (monomial A) z =
      Matrix.diagonal (monomial A z) * A.map (Int.castRingHom ℂ) *
        Matrix.diagonal (fun j => (z j)⁻¹) := by
  ext i j
  simp [jacobianMatrix_monomial_apply A hz, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Wikipedia.HopfProblem.ToricCharts
