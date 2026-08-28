import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The local attaching-handle model

An explicit curved product of disks puts the whole negative boundary on
one level of the quadratic Morse function. Its intersection with the lower
sublevel is exactly that boundary, and the whole handle lies in the upper
sublevel. These are local model facts, not the global handle-attachment theorem.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

abbrev UnitDisk (V : Type*) [NormedAddCommGroup V] := closedBall (0 : V) 1

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The radius of the negative disk depends on the positive coordinate. -/
def modelMap (ρ : ℝ) (z : UnitDisk N × UnitDisk P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N), ρ • (z.2 : P))

theorem continuous_modelMap (ρ : ℝ) : Continuous (modelMap (N := N) (P := P) ρ) := by
  have hu : Continuous (fun z : UnitDisk N × UnitDisk P => (z.1 : N)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun z : UnitDisk N × UnitDisk P => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))).smul hu).prodMk
      (continuous_const.smul hv)

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem negative_scale_pos {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    0 < ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
  mul_pos hρ (Real.sqrt_pos.mpr (by positivity))

theorem modelMap_injective {ρ : ℝ} (hρ : 0 < ρ) :
    Function.Injective (modelMap (N := N) (P := P) ρ) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : (v : P) = (v' : P) := by
    have hh := congrArg (fun z : N × P => ρ⁻¹ • z.2) h
    simpa only [modelMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hh
  have hv' : v = v' := Subtype.ext hv
  subst v'
  have hu : (u : N) = (u' : N) := by
    have hh := congrArg
      (fun z : N × P => (ρ * Real.sqrt (1 + ‖(v : P)‖ ^ 2))⁻¹ • z.1) h
    simpa only [modelMap, smul_smul,
      inv_mul_cancel₀ (negative_scale_pos hρ (u, v)).ne', one_smul] using hh
  exact Prod.ext (Subtype.ext hu) rfl

theorem modelMap_mem_product {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hs : Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (negative_scale_pos hρ z)]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
        mul_le_of_le_one_right (negative_scale_pos hρ z).le hu
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hs hρ.le
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • (z.2 : P)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

/-- Exact height in the quadratic Morse form. -/
theorem modelMap_height {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 =
      ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) := by
  simp only [modelMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (negative_scale_pos hρ z), abs_of_pos hρ, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 by positivity)]
  ring

/-- The lower sublevel meets the local handle in exactly the negative boundary face. -/
theorem modelMap_lower_iff {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ -(ρ ^ 2) ↔
      ‖(z.1 : N)‖ = 1 := by
  rw [modelMap_height hρ z]
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hu₀ := norm_nonneg (z.1 : N)
  have hpos : 0 < ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2) :=
    mul_pos (sq_pos_of_pos hρ) (by positivity)
  constructor
  · intro h
    have hp : (ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2)) * (1 - ‖(z.1 : N)‖ ^ 2) ≤ 0 := by
      calc
        _ = ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) + ρ ^ 2 := by ring
        _ ≤ 0 := by linarith
    have hm : 1 - ‖(z.1 : N)‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hpos).mp (by
      simpa only [mul_zero] using hp)
    nlinarith
  · intro h
    simp only [h, one_pow, sub_self, mul_zero, zero_sub, mul_neg, mul_one, le_refl]

/-- The complete local handle is contained in the upper sublevel. -/
theorem modelMap_upper {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ ρ ^ 2 := by
  rw [modelMap_height hρ z]
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hu₂ : 0 ≤ ‖(z.1 : N)‖ ^ 2 := sq_nonneg _
  have hfactor : 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 := by positivity
  have hsmall : (1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1 ≤ 1 := by
    nlinarith [mul_nonneg hfactor hu₂]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (sq_nonneg ρ)

end Wikipedia.SmoothSixDPoincare.MorseHandle
