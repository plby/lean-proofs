import Wikipedia.SmoothSixDPoincare.MorseHandleAmbient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth ambient coordinates for the whole curved Morse handle

The triangular handle map and its explicit inverse are smooth because their
radial factors are square roots of strictly positive smooth functions. On the
lower quadratic level, the inverse negative coordinate lies on the actual
unit sphere. These facts retain the full transverse attaching coordinates.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

section Coordinates

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The entire spherical face, with arbitrary transverse coordinate, lies on the lower level. -/
theorem ambientMap_lower_sphere {ρ : ℝ} (hρ : 0 < ρ) (u : sphere (0 : N) 1) (v : P) :
    -‖(ambientMap ρ ((u : N), v)).1‖ ^ 2 +
      ‖(ambientMap ρ ((u : N), v)).2‖ ^ 2 = -(ρ ^ 2) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  simp only [ambientMap, norm_smul, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hρ,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖v‖ ^ 2 by positivity)]
  ring

/-- The standard Morse block contains a uniform transverse margin beyond the closed unit face. -/
theorem ambientMap_sphere_mem_product {ρ : ℝ} (hρ : 0 < ρ)
    (u : sphere (0 : N) 1) (v : P) (hv : ‖v‖ ≤ (3 / 2 : ℝ)) :
    ambientMap ρ ((u : N), v) ∈ closedBall (0 : N) (2 * ρ) ×ˢ
      closedBall (0 : P) (2 * ρ) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg v]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖v‖ ^ 2)) • (u : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
    calc
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hs hρ.le
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hm := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

/-- The inverse coordinate on the lower quadratic level has negative norm exactly one. -/
theorem norm_ambientInverse_fst_of_lower {ρ : ℝ} (hρ : 0 < ρ) (z : N × P)
    (hz : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -(ρ ^ 2)) :
    ‖(ambientInverse ρ z).1‖ = 1 := by
  let A : ℝ := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hn : ‖z.1‖ = A := by
    nlinarith [norm_nonneg z.1]
  change ‖A⁻¹ • z.1‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), hn,
    inv_mul_cancel₀ hA.ne']

theorem norm_ambientInverse_snd_lt_one {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ‖(ambientInverse ρ z).2‖ < 1 ↔ ‖z.2‖ < ρ := by
  change ‖ρ⁻¹ • z.2‖ < 1 ↔ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_one₀ hρ]

end Coordinates

section Smooth

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The original curved coordinate map is globally smooth, including its zero section. -/
theorem contDiff_ambientMap (ρ : ℝ) : ContDiff ℝ ∞ (ambientMap (N := N) (P := P) ρ) :=
  ((contDiff_const.mul ((contDiff_const.add (contDiff_snd.norm_sq ℝ)).sqrt
    (fun z : N × P => by positivity))).smul contDiff_fst).prodMk
      (contDiff_const.smul contDiff_snd)

/-- The explicit inverse is globally smooth; its scalar denominator never vanishes. -/
theorem contDiff_ambientInverse {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (ambientInverse (N := N) (P := P) ρ) := by
  have hv : ContDiff ℝ ∞ (fun z : N × P => ρ⁻¹ • z.2) := contDiff_const.smul contDiff_snd
  have hA : ContDiff ℝ ∞ (fun z : N × P => ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)) :=
    contDiff_const.mul ((contDiff_const.add (hv.norm_sq ℝ)).sqrt (fun _ => by positivity))
  have hApos (z : N × P) : 0 < ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  exact ((hA.inv (fun z => (hApos z).ne')).smul contDiff_fst).prodMk hv

/-- The ambient homeomorphism of the curved handle is a genuine smooth diffeomorphism. -/
def ambientDiffeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    Diffeomorph 𝓘(ℝ, N × P) 𝓘(ℝ, N × P) (N × P) (N × P) ∞ where
  toEquiv := (ambientHomeomorph ρ hρ).toEquiv
  contMDiff_toFun := (contDiff_ambientMap ρ).contMDiff
  contMDiff_invFun := (contDiff_ambientInverse hρ).contMDiff

theorem ambientDiffeomorph_apply (ρ : ℝ) (hρ : 0 < ρ) (z : N × P) :
    ambientDiffeomorph ρ hρ z = ambientMap ρ z := rfl

theorem ambientDiffeomorph_symm_apply (ρ : ℝ) (hρ : 0 < ρ) (z : N × P) :
    (ambientDiffeomorph ρ hρ).symm z = ambientInverse ρ z := rfl

end Smooth

end Wikipedia.SmoothSixDPoincare.MorseHandle
