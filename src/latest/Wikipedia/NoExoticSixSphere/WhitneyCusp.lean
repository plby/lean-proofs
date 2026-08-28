import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# An explicit three-dimensional cusp family in Euclidean six-space

The polynomial family has coordinates
`(x₀, x₁, x₂², x₀*x₂, x₁*x₂, x₂³ - t*x₂)`.
Its actual derivative is computed here. Singular-locus and double-point
statements, and the relation with the geometric parity, are separate proofs.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization

def map (t : ℝ) (x : Vector 3) : Vector 6 :=
  WithLp.toLp 2 ![x 0, x 1, x 2 ^ 2, x 0 * x 2, x 1 * x 2, x 2 ^ 3 - t * x 2]

def row (t : ℝ) (x : Vector 3) : Fin 6 → Vector 3 →L[ℝ] ℝ :=
  ![PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0,
    PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1,
    (2 * x 2) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    x 2 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 +
      x 0 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    x 2 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 +
      x 1 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    (3 * x 2 ^ 2 - t) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2]

def differential (t : ℝ) (x : Vector 3) : Vector 3 →L[ℝ] Vector 6 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (row t x))

theorem differential_coord (t : ℝ) (x : Vector 3) (i : Fin 6) :
    (PiLp.proj 2 (fun _ : Fin 6 ↦ ℝ) i).comp (differential t x) = row t x i := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem differential_apply (t : ℝ) (x v : Vector 3) (i : Fin 6) :
    differential t x v i =
      ![v 0, v 1, 2 * x 2 * v 2, x 2 * v 0 + x 0 * v 2,
        x 2 * v 1 + x 1 * v 2, (3 * x 2 ^ 2 - t) * v 2] i := by
  fin_cases i <;> rfl

theorem contDiff_map : ContDiff ℝ ∞ (Function.uncurry map) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × Vector 3 ↦ q.2 i) :=
    (contDiff_piLp_apply 2).comp contDiff_snd
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact (hc 2).pow 2
  · exact (hc 0).mul (hc 2)
  · exact (hc 1).mul (hc 2)
  · exact ((hc 2).pow 3).sub (contDiff_fst.mul (hc 2))

theorem hasStrictFDerivAt_map (t : ℝ) (x : Vector 3) :
    HasStrictFDerivAt (map t) (differential t x) x := by
  have hc (i : Fin 3) := PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x i
  apply (hasStrictFDerivAt_piLp 2).mpr
  intro i
  rw [differential_coord]
  fin_cases i
  · exact hc 0
  · exact hc 1
  · simpa [map, row, smul_smul] using (hc 2).pow 2
  · apply ((hc 0).smul (hc 2)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [row]
    ring
  · apply ((hc 1).smul (hc 2)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [row]
    ring
  · apply (((hc 2).pow 3).sub ((hc 2).const_smul t)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [row]
    ring

theorem fderiv_map (t : ℝ) (x : Vector 3) : fderiv ℝ (map t) x = differential t x :=
  (hasStrictFDerivAt_map t x).hasFDerivAt.fderiv

end NoExoticSixSphere.WhitneyCusp
