import Wikipedia.NoExoticSixSphere.WhitneyCuspSingularLocus

/-!
# Deforming the actual cusp derivative on the punctured parameter space

The deformation retains the first two coordinate projections and replaces
the remaining column by a nonzero residual vector. At parameter one it is
the actual cusp derivative; at parameter zero the first two columns are
fixed coordinate axes. Injectivity is proved throughout, not assumed.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization

def source (q : Vector 4) : Vector 3 := WithLp.toLp 2 ![q 1, q 2, q 3]

def deformationRow (s : ℝ) (q : Vector 4) : Fin 6 → Vector 3 →L[ℝ] ℝ :=
  ![PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0,
    PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1,
    ((1 + s) * q 3) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    (s * q 3) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 +
      q 1 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    (s * q 3) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 +
      q 2 • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
    (3 * s * q 3 ^ 2 - q 0) • PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2]

def deformation (s : ℝ) (q : Vector 4) : Vector 3 →L[ℝ] Vector 6 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (deformationRow s q))

theorem deformation_apply (s : ℝ) (q : Vector 4) (v : Vector 3) (i : Fin 6) :
    deformation s q v i =
      ![v 0, v 1, (1 + s) * q 3 * v 2, s * q 3 * v 0 + q 1 * v 2,
        s * q 3 * v 1 + q 2 * v 2, (3 * s * q 3 ^ 2 - q 0) * v 2] i := by
  fin_cases i <;> rfl

theorem contDiff_deformation_apply (v : Vector 3) :
    ContDiff ℝ ∞ (fun p : ℝ × Vector 4 ↦ deformation p.1 p.2 v) := by
  have hc (i : Fin 4) : ContDiff ℝ ∞ (fun p : ℝ × Vector 4 ↦ p.2 i) :=
    (contDiff_piLp_apply 2).comp contDiff_snd
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact ((contDiff_const.add contDiff_fst).mul (hc 3)).mul contDiff_const
  · exact (((contDiff_fst.mul (hc 3)).mul contDiff_const).add ((hc 1).mul contDiff_const))
  · exact (((contDiff_fst.mul (hc 3)).mul contDiff_const).add ((hc 2).mul contDiff_const))
  · exact ((((contDiff_const.mul contDiff_fst).mul ((hc 3).pow 2)).sub (hc 0)).mul
      contDiff_const)

theorem continuous_deformation :
    Continuous (fun p : ℝ × Vector 4 ↦ deformation p.1 p.2) :=
  continuous_clm_apply.mpr (fun v ↦ (contDiff_deformation_apply v).continuous)

theorem deformation_one (q : Vector 4) :
    deformation 1 q = fderiv ℝ (map (q 0)) (source q) := by
  rw [fderiv_map]
  apply ContinuousLinearMap.ext
  intro v
  ext i
  rw [deformation_apply, differential_apply]
  fin_cases i <;> dsimp [source] <;> ring

theorem injective_deformation (s : ℝ) (hs : 0 ≤ s) (q : Vector 4) (hq : q ≠ 0) :
    Injective (deformation s q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have h₀ : v 0 = 0 := congrArg (fun w : Vector 6 ↦ w 0) hv
  have h₁ : v 1 = 0 := congrArg (fun w : Vector 6 ↦ w 1) hv
  by_cases hz : v 2 = 0
  · ext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact hz
  · have h₂ : (1 + s) * q 3 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 2) hv
    have h₃ : s * q 3 * v 0 + q 1 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 3) hv
    have h₄ : s * q 3 * v 1 + q 2 * v 2 = 0 := congrArg (fun w : Vector 6 ↦ w 4) hv
    have h₅ : (3 * s * q 3 ^ 2 - q 0) * v 2 = 0 :=
      congrArg (fun w : Vector 6 ↦ w 5) hv
    have hq₃ : q 3 = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_right hz)).resolve_left (by linarith)
    have hq₁ : q 1 = 0 := by
      rw [h₀, mul_zero, zero_add] at h₃
      exact (mul_eq_zero.mp h₃).resolve_right hz
    have hq₂ : q 2 = 0 := by
      rw [h₁, mul_zero, zero_add] at h₄
      exact (mul_eq_zero.mp h₄).resolve_right hz
    have hq₀ : q 0 = 0 := by
      have h := (mul_eq_zero.mp h₅).resolve_right hz
      rw [hq₃] at h
      nlinarith
    exfalso
    apply hq
    ext i
    fin_cases i
    · exact hq₀
    · exact hq₁
    · exact hq₂
    · exact hq₃

end NoExoticSixSphere.WhitneyCusp
