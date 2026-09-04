import Mathlib.Analysis.Complex.Angle
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Planar angular separation for Erdős 957

The complex numbers are used as Mathlib's concrete real Euclidean plane.  This file proves the
standard planar kissing-number bound needed for the closest-distance graph: a one-separated set
has at most six points on any unit circle.  It also records the equality-case regular-hexagon
classification used by the remaining Erdős 957 development.
-/

open scoped ComplexConjugate Real RealInnerProductSpace
open Set

namespace Erdos957Angle

open InnerProductGeometry

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two unit vectors at distance at least one have inner product at most `1 / 2`. -/
lemma inner_le_half_of_unit_norm_of_one_le_norm_sub {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : 1 ≤ ‖x - y‖) :
    ⟪x, y⟫ ≤ (1 / 2 : ℝ) := by
  have hsq : 1 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y)]
  rw [norm_sub_sq_real, hx, hy] at hsq
  norm_num at hsq ⊢
  linarith

/-- Two unit vectors at distance at least one subtend an angle of at least `π / 3`. -/
lemma pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : 1 ≤ ‖x - y‖) :
    Real.pi / 3 ≤ angle x y := by
  have hinner := inner_le_half_of_unit_norm_of_one_le_norm_sub hx hy hxy
  rw [angle, hx, hy]
  norm_num
  calc
    Real.pi / 3 = Real.arccos (1 / 2 : ℝ) := by
      rw [← Real.cos_pi_div_three, Real.arccos_cos] <;> nlinarith [Real.pi_pos]
    _ ≤ Real.arccos ⟪x, y⟫ := Real.arccos_le_arccos hinner

end InnerProduct

section ComplexPlane

/-- The argument in the half-open interval `[-π, π)`.  Mathlib's `Complex.arg` instead uses
`(-π, π]`, so only the endpoint representing the negative real ray is changed. -/
noncomputable def principalPhase (z : ℂ) : ℝ :=
  if z.arg = Real.pi then -Real.pi else z.arg

lemma principalPhase_mem_Ico (z : ℂ) :
    principalPhase z ∈ Ico (-Real.pi) Real.pi := by
  by_cases h : z.arg = Real.pi
  · simp [principalPhase, h, Real.pi_pos]
  · simp only [principalPhase, h, ↓reduceIte, mem_Ico]
    exact ⟨(Complex.neg_pi_lt_arg z).le, lt_of_le_of_ne (Complex.arg_le_pi z) h⟩

lemma exp_principalPhase_mul_I {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (principalPhase z * Complex.I) = z := by
  have harg : Complex.exp (z.arg * Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  by_cases h : z.arg = Real.pi
  · simp only [principalPhase, h, if_pos]
    calc
      Complex.exp ((-Real.pi : ℝ) * Complex.I) =
          Complex.exp (-(Real.pi * Complex.I)) := by
            congr 1
            push_cast
            ring
      _ = -1 := Complex.exp_neg_pi_mul_I
      _ = z := by simpa [h, Complex.exp_pi_mul_I] using harg
  · simpa [principalPhase, h] using harg

/-- The angular bin in the partition of `[-π,π)` into six intervals of width `π/3`. -/
noncomputable def phaseBin (z : ℂ) : Fin 6 :=
  ⟨⌊3 * (principalPhase z + Real.pi) / Real.pi⌋₊, by
    have hp := principalPhase_mem_Ico z
    have hnonneg : 0 ≤ 3 * (principalPhase z + Real.pi) / Real.pi := by
      exact div_nonneg (mul_nonneg (by norm_num) (by linarith [hp.1])) Real.pi_pos.le
    rw [Nat.floor_lt hnonneg]
    rw [div_lt_iff₀ Real.pi_pos]
    norm_num
    nlinarith [Real.pi_pos, hp.2]⟩

private lemma principalPhase_nonneg_shift (z : ℂ) :
    0 ≤ 3 * (principalPhase z + Real.pi) / Real.pi := by
  have hp := (principalPhase_mem_Ico z).1
  exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) Real.pi_pos.le

/-- A vector in the strict lower half-plane belongs to one of the first three phase bins. -/
lemma phaseBin_val_lt_three_of_im_neg {z : ℂ} (hz : z.im < 0) :
    (phaseBin z).val < 3 := by
  have harg : z.arg < 0 := Complex.arg_neg_iff.2 hz
  have hphase : principalPhase z = z.arg := by
    simp [principalPhase, ne_of_lt (harg.trans (Real.pi_pos))]
  have hp := principalPhase_mem_Ico z
  have hnonneg := principalPhase_nonneg_shift z
  change ⌊3 * (principalPhase z + Real.pi) / Real.pi⌋₊ < 3
  rw [Nat.floor_lt hnonneg, div_lt_iff₀ Real.pi_pos]
  rw [hphase]
  norm_num
  nlinarith [Real.pi_pos]

/-- Membership in a phase bin gives the corresponding explicit half-open sector bounds. -/
lemma principalPhase_bounds_of_phaseBin_eq {z : ℂ} {i : Fin 6} (hbin : phaseBin z = i) :
    -Real.pi + (i : ℝ) * Real.pi / 3 ≤ principalPhase z ∧
      principalPhase z < -Real.pi + ((i : ℕ) + 1 : ℝ) * Real.pi / 3 := by
  have hnonneg := principalPhase_nonneg_shift z
  have hfloor : ⌊3 * (principalPhase z + Real.pi) / Real.pi⌋₊ = (i : ℕ) := by
    simpa [phaseBin] using congrArg Fin.val hbin
  have hb := (Nat.floor_eq_iff hnonneg).1 hfloor
  have hlo : (i : ℝ) * Real.pi ≤ 3 * (principalPhase z + Real.pi) :=
    (le_div_iff₀ Real.pi_pos).1 hb.1
  have hhi : 3 * (principalPhase z + Real.pi) < ((i : ℕ) + 1 : ℝ) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).1 (by simpa using hb.2)
  constructor <;> norm_num at hlo hhi ⊢ <;> nlinarith

/-- Equal angular bins imply that the two principal phases differ by less than `π / 3`. -/
lemma abs_principalPhase_sub_lt_of_phaseBin_eq {x y : ℂ} (hbin : phaseBin x = phaseBin y) :
    |principalPhase x - principalPhase y| < Real.pi / 3 := by
  let tx : ℝ := 3 * (principalPhase x + Real.pi) / Real.pi
  let ty : ℝ := 3 * (principalPhase y + Real.pi) / Real.pi
  have htx0 : 0 ≤ tx := principalPhase_nonneg_shift x
  have hty0 : 0 ≤ ty := principalPhase_nonneg_shift y
  have hfloor : ⌊tx⌋₊ = ⌊ty⌋₊ := by
    simpa [phaseBin, tx, ty] using congrArg Fin.val hbin
  have hxy : tx < ty + 1 := by
    calc
      tx < (⌊tx⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one tx
      _ = (⌊ty⌋₊ : ℝ) + 1 := by rw [hfloor]
      _ ≤ ty + 1 := by simpa [add_comm] using add_le_add_right (Nat.floor_le hty0) 1
  have hyx : ty < tx + 1 := by
    calc
      ty < (⌊ty⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ty
      _ = (⌊tx⌋₊ : ℝ) + 1 := by rw [hfloor]
      _ ≤ tx + 1 := by simpa [add_comm] using add_le_add_right (Nat.floor_le htx0) 1
  have hxy' : 3 * (principalPhase x + Real.pi) <
      (3 * (principalPhase y + Real.pi) / Real.pi + 1) * Real.pi := by
    exact (div_lt_iff₀ Real.pi_pos).mp (by simpa [tx, ty] using hxy)
  have hyx' : 3 * (principalPhase y + Real.pi) <
      (3 * (principalPhase x + Real.pi) / Real.pi + 1) * Real.pi := by
    exact (div_lt_iff₀ Real.pi_pos).mp (by simpa [tx, ty] using hyx)
  have hupper : principalPhase x - principalPhase y < Real.pi / 3 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    field_simp at hxy' hyx'
    nlinarith
  have hyxUpper : principalPhase y - principalPhase x < Real.pi / 3 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    field_simp at hxy' hyx'
    nlinarith
  have hlower : -(Real.pi / 3) < principalPhase x - principalPhase y := by
    linarith
  exact abs_lt.2 ⟨hlower, hupper⟩

/-- On one angular bin, the unoriented angle is the ordinary absolute phase difference. -/
lemma angle_eq_abs_principalPhase_sub_of_phaseBin_eq {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hbin : phaseBin x = phaseBin y) :
    angle x y = |principalPhase x - principalPhase y| := by
  have hclose := abs_principalPhase_sub_lt_of_phaseBin_eq hbin
  have hdiff : principalPhase x - principalPhase y ∈ Ioc (-Real.pi) Real.pi := by
    have hb := abs_lt.1 hclose
    exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  calc
    angle x y = angle (Complex.exp (principalPhase x * Complex.I))
        (Complex.exp (principalPhase y * Complex.I)) := by
      rw [exp_principalPhase_mul_I hx, exp_principalPhase_mul_I hy]
    _ = |principalPhase x - principalPhase y| := by
      rw [Complex.angle_exp_exp, (toIocMod_eq_self Real.two_pi_pos).2]
      simpa [two_mul] using hdiff

/-- For two phases in increasing order with gap less than `π`, the vector angle is that gap. -/
lemma angle_eq_principalPhase_sub_of_le_of_sub_lt_pi {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hle : principalPhase x ≤ principalPhase y)
    (hlt : principalPhase y - principalPhase x < Real.pi) :
    angle x y = principalPhase y - principalPhase x := by
  have hdiff : principalPhase x - principalPhase y ∈ Ioc (-Real.pi) Real.pi := by
    exact ⟨by linarith, by nlinarith [Real.pi_pos]⟩
  calc
    angle x y = angle (Complex.exp (principalPhase x * Complex.I))
        (Complex.exp (principalPhase y * Complex.I)) := by
      rw [exp_principalPhase_mul_I hx, exp_principalPhase_mul_I hy]
    _ = |principalPhase x - principalPhase y| := by
      rw [Complex.angle_exp_exp, (toIocMod_eq_self Real.two_pi_pos).2]
      simpa [two_mul] using hdiff
    _ = principalPhase y - principalPhase x := by
      rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]

/-- Across the branch cut, if the positive wrap-around gap is less than `π`, the vector angle is
that wrap-around gap. -/
lemma angle_eq_principalPhase_wrap_of_pos_of_lt_pi {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hpos : 0 < principalPhase y + 2 * Real.pi - principalPhase x)
    (hlt : principalPhase y + 2 * Real.pi - principalPhase x < Real.pi) :
    angle x y = principalPhase y + 2 * Real.pi - principalPhase x := by
  have hmod : toIocMod Real.two_pi_pos (-Real.pi)
      (principalPhase x - principalPhase y) =
      principalPhase x - principalPhase y - 2 * Real.pi := by
    apply (toIocMod_eq_iff Real.two_pi_pos).2
    constructor
    · change principalPhase x - principalPhase y - 2 * Real.pi ∈
        Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)
      constructor <;> nlinarith
    · refine ⟨1, ?_⟩
      norm_num
  calc
    angle x y = angle (Complex.exp (principalPhase x * Complex.I))
        (Complex.exp (principalPhase y * Complex.I)) := by
      rw [exp_principalPhase_mul_I hx, exp_principalPhase_mul_I hy]
    _ = |principalPhase x - principalPhase y - 2 * Real.pi| := by
      rw [Complex.angle_exp_exp, hmod]
    _ = principalPhase y + 2 * Real.pi - principalPhase x := by
      rw [abs_of_nonpos (by linarith), neg_sub]
      ring

/-- The six-bin map is injective on every one-separated finite set of unit vectors. -/
lemma phaseBin_injOn_of_unit_oneSeparated (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    Set.InjOn phaseBin S := by
  intro x hx y hy hbin
  by_contra hxy
  have hangle_ge := pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
    (hnorm x hx) (hnorm y hy) (hsep x hx y hy hxy)
  have hangle_eq := angle_eq_abs_principalPhase_sub_of_phaseBin_eq
    (hnorm x hx) (hnorm y hy) hbin
  have hangle_lt := abs_principalPhase_sub_lt_of_phaseBin_eq hbin
  linarith

/-- A one-separated finite set of unit vectors in the real plane has cardinality at most six. -/
theorem card_le_six_of_unit_oneSeparated (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) :
    S.card ≤ 6 := by
  have hcard := Finset.card_le_card_of_injOn phaseBin
    (s := S) (t := Finset.univ) (by simp [Set.MapsTo])
    (phaseBin_injOn_of_unit_oneSeparated S hnorm hsep)
  simpa using hcard

/-- In the equality case, the six angular bins are occupied exactly once. -/
theorem phaseBin_bijective_of_card_eq_six (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖)
    (hcard : S.card = 6) :
    Function.Bijective (fun z : S ↦ phaseBin z) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact phaseBin_injOn_of_unit_oneSeparated S hnorm hsep x.prop y.prop hxy
  · simpa [hcard]

/-- Equivalently, a sharp six-point configuration has a unique point in every angular bin. -/
theorem existsUnique_mem_phaseBin_of_card_eq_six (S : Finset ℂ)
    (hnorm : ∀ z ∈ S, ‖z‖ = 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖)
    (hcard : S.card = 6) (i : Fin 6) :
    ∃! z : ℂ, z ∈ S ∧ phaseBin z = i := by
  have hbij := phaseBin_bijective_of_card_eq_six S hnorm hsep hcard
  obtain ⟨z, hz⟩ := hbij.2 i
  refine ⟨z, ⟨z.prop, hz⟩, ?_⟩
  intro w hw
  have heq : (⟨w, hw.1⟩ : S) = z := hbij.1 (hw.2.trans hz.symm)
  exact congrArg Subtype.val heq

/-- If six unit vectors are indexed by their six occupied phase bins, their phases are exactly
`π/3` apart.  This is the regular-hexagon equality case of the planar kissing bound. -/
theorem principalPhase_eq_regular_of_six_indexed (v : Fin 6 → ℂ)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖)
    (hbin : ∀ i, phaseBin (v i) = i) :
    ∀ i, principalPhase (v i) =
      principalPhase (v 0) + (i : ℝ) * Real.pi / 3 := by
  have b0 := principalPhase_bounds_of_phaseBin_eq (hbin 0)
  have b1 := principalPhase_bounds_of_phaseBin_eq (hbin 1)
  have b2 := principalPhase_bounds_of_phaseBin_eq (hbin 2)
  have b3 := principalPhase_bounds_of_phaseBin_eq (hbin 3)
  have b4 := principalPhase_bounds_of_phaseBin_eq (hbin 4)
  have b5 := principalPhase_bounds_of_phaseBin_eq (hbin 5)
  norm_num at b0 b1 b2 b3 b4 b5
  have gap01 : Real.pi / 3 ≤ principalPhase (v 1) - principalPhase (v 0) := by
    have hle : principalPhase (v 0) ≤ principalPhase (v 1) := by linarith
    have hlt : principalPhase (v 1) - principalPhase (v 0) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_sub_of_le_of_sub_lt_pi (hnorm 0) (hnorm 1) hle hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 0) (hnorm 1) (hsep 0 1 (by decide))
  have gap12 : Real.pi / 3 ≤ principalPhase (v 2) - principalPhase (v 1) := by
    have hle : principalPhase (v 1) ≤ principalPhase (v 2) := by linarith
    have hlt : principalPhase (v 2) - principalPhase (v 1) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_sub_of_le_of_sub_lt_pi (hnorm 1) (hnorm 2) hle hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 1) (hnorm 2) (hsep 1 2 (by decide))
  have gap23 : Real.pi / 3 ≤ principalPhase (v 3) - principalPhase (v 2) := by
    have hle : principalPhase (v 2) ≤ principalPhase (v 3) := by linarith
    have hlt : principalPhase (v 3) - principalPhase (v 2) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_sub_of_le_of_sub_lt_pi (hnorm 2) (hnorm 3) hle hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 2) (hnorm 3) (hsep 2 3 (by decide))
  have gap34 : Real.pi / 3 ≤ principalPhase (v 4) - principalPhase (v 3) := by
    have hle : principalPhase (v 3) ≤ principalPhase (v 4) := by linarith
    have hlt : principalPhase (v 4) - principalPhase (v 3) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_sub_of_le_of_sub_lt_pi (hnorm 3) (hnorm 4) hle hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 3) (hnorm 4) (hsep 3 4 (by decide))
  have gap45 : Real.pi / 3 ≤ principalPhase (v 5) - principalPhase (v 4) := by
    have hle : principalPhase (v 4) ≤ principalPhase (v 5) := by linarith
    have hlt : principalPhase (v 5) - principalPhase (v 4) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_sub_of_le_of_sub_lt_pi (hnorm 4) (hnorm 5) hle hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 4) (hnorm 5) (hsep 4 5 (by decide))
  have gap50 : Real.pi / 3 ≤
      principalPhase (v 0) + 2 * Real.pi - principalPhase (v 5) := by
    have hpos : 0 < principalPhase (v 0) + 2 * Real.pi - principalPhase (v 5) := by
      linarith
    have hlt : principalPhase (v 0) + 2 * Real.pi - principalPhase (v 5) < Real.pi := by
      nlinarith [Real.pi_pos]
    rw [← angle_eq_principalPhase_wrap_of_pos_of_lt_pi (hnorm 5) (hnorm 0) hpos hlt]
    exact pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      (hnorm 5) (hnorm 0) (hsep 5 0 (by decide))
  have gap01eq : principalPhase (v 1) - principalPhase (v 0) = Real.pi / 3 := by
    nlinarith
  have gap12eq : principalPhase (v 2) - principalPhase (v 1) = Real.pi / 3 := by
    nlinarith
  have gap23eq : principalPhase (v 3) - principalPhase (v 2) = Real.pi / 3 := by
    nlinarith
  have gap34eq : principalPhase (v 4) - principalPhase (v 3) = Real.pi / 3 := by
    nlinarith
  have gap45eq : principalPhase (v 5) - principalPhase (v 4) = Real.pi / 3 := by
    nlinarith
  have phase1 : principalPhase (v 1) = principalPhase (v 0) + Real.pi / 3 := by
    linarith
  have phase2 : principalPhase (v 2) = principalPhase (v 0) + 2 * Real.pi / 3 := by
    linarith
  have phase3 : principalPhase (v 3) = principalPhase (v 0) + 3 * Real.pi / 3 := by
    linarith
  have phase4 : principalPhase (v 4) = principalPhase (v 0) + 4 * Real.pi / 3 := by
    linarith
  have phase5 : principalPhase (v 5) = principalPhase (v 0) + 5 * Real.pi / 3 := by
    linarith
  intro i
  fin_cases i
  · norm_num
  · simpa using phase1
  · simpa using phase2
  · simpa using phase3
  · simpa using phase4
  · simpa using phase5

/-- Vector-valued form of the preceding equality case: the indexed vectors are the six vertices
of a rotated regular hexagon on the unit circle. -/
theorem eq_exp_regular_hexagon_of_six_indexed (v : Fin 6 → ℂ)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖)
    (hbin : ∀ i, phaseBin (v i) = i) :
    ∀ i, v i = Complex.exp
      ((principalPhase (v 0) + (i : ℝ) * Real.pi / 3) * Complex.I) := by
  intro i
  have hphase := principalPhase_eq_regular_of_six_indexed v hnorm hsep hbin i
  calc
    v i = Complex.exp (principalPhase (v i) * Complex.I) :=
      (exp_principalPhase_mul_I (hnorm i)).symm
    _ = Complex.exp
        ((principalPhase (v 0) + (i : ℝ) * Real.pi / 3) * Complex.I) := by
      rw [hphase]
      push_cast
      rfl

private lemma one_sub_exp_pi_div_three_mul_I :
    1 - Complex.exp ((Real.pi / 3) * Complex.I) =
      Complex.exp ((-Real.pi / 3) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I,
    show (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) by push_cast; rfl,
    show -(Real.pi : ℂ) / 3 = ((-Real.pi / 3 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (-Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring,
    Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- Subtracting the next unit vector at a `π/3` turn gives the preceding unit vector. -/
lemma exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) -
        Complex.exp ((θ + Real.pi / 3) * Complex.I) =
      Complex.exp ((θ - Real.pi / 3) * Complex.I) := by
  calc
    Complex.exp (θ * Complex.I) -
        Complex.exp ((θ + Real.pi / 3) * Complex.I) =
        Complex.exp (θ * Complex.I) *
          (1 - Complex.exp ((Real.pi / 3) * Complex.I)) := by
      have hadd : ((θ : ℂ) + Real.pi / 3) * Complex.I =
          θ * Complex.I + (Real.pi / 3) * Complex.I := by ring
      rw [hadd, Complex.exp_add]
      ring
    _ = Complex.exp (θ * Complex.I) *
        Complex.exp ((-Real.pi / 3) * Complex.I) := by
      rw [one_sub_exp_pi_div_three_mul_I]
    _ = Complex.exp ((θ - Real.pi / 3) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Consecutive vertices in the indexed equality case satisfy the six hexagonal completion
identities.  These identities are convenient when a geometric argument constructs the missing
neighbor as a vector difference. -/
theorem regular_hexagon_sub_next_identities (v : Fin 6 → ℂ)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖)
    (hbin : ∀ i, phaseBin (v i) = i) :
    v 0 - v 1 = v 5 ∧
    v 1 - v 2 = v 0 ∧
    v 2 - v 3 = v 1 ∧
    v 3 - v 4 = v 2 ∧
    v 4 - v 5 = v 3 ∧
    v 5 - v 0 = v 4 := by
  set θ := principalPhase (v 0)
  have hv := eq_exp_regular_hexagon_of_six_indexed v hnorm hsep hbin
  have hv' : ∀ i, v i = Complex.exp
      ((θ + (i : ℝ) * Real.pi / 3) * Complex.I) := by
    intro i
    simpa [θ] using hv i
  have hperiod : Complex.exp ((θ - Real.pi / 3) * Complex.I) =
      Complex.exp ((θ + 5 * Real.pi / 3) * Complex.I) := by
    have hp := Complex.exp_mul_I_periodic (θ - Real.pi / 3)
    symm
    convert hp using 1 <;> ring_nf
  have hperiod0 : Complex.exp (θ * Complex.I) =
      Complex.exp ((θ + 6 * Real.pi / 3) * Complex.I) := by
    have hp := Complex.exp_mul_I_periodic θ
    symm
    convert hp using 1 <;> ring_nf
  constructor
  · rw [hv' 0, hv' 1, hv' 5]
    norm_num
    rw [exp_mul_I_sub_exp_add_pi_div_three_mul_I, hperiod]
  constructor
  · rw [hv' 1, hv' 2, hv' 0]
    norm_num
    convert exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ + Real.pi / 3) using 1 <;>
      congr 1 <;> push_cast <;> ring_nf
  constructor
  · rw [hv' 2, hv' 3, hv' 1]
    norm_num
    convert exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ + 2 * Real.pi / 3) using 1 <;>
      congr 1 <;> push_cast <;> ring_nf
  constructor
  · rw [hv' 3, hv' 4, hv' 2]
    norm_num
    convert exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ + 3 * Real.pi / 3) using 1 <;>
      congr 1 <;> push_cast <;> ring_nf
  constructor
  · rw [hv' 4, hv' 5, hv' 3]
    norm_num
    convert exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ + 4 * Real.pi / 3) using 1 <;>
      congr 1 <;> push_cast <;> ring_nf
  · rw [hv' 5, hv' 0, hv' 4]
    norm_num
    rw [hperiod0]
    convert exp_mul_I_sub_exp_add_pi_div_three_mul_I (θ + 5 * Real.pi / 3) using 1 <;>
      congr 1 <;> push_cast <;> ring_nf

/-- A finite planar point set is one-separated if every pair of distinct points has distance at
least one. -/
def IsOneSeparated (A : Finset ℂ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y

/-- The points of `A` at unit distance from `p`. -/
noncomputable def unitNeighbors (A : Finset ℂ) (p : ℂ) : Finset ℂ :=
  A.filter fun q ↦ dist p q = 1

/-- Unit neighbors lying strictly below their center. -/
noncomputable def lowerUnitNeighbors (A : Finset ℂ) (p : ℂ) : Finset ℂ :=
  (unitNeighbors A p).filter fun q ↦ (q - p).im < 0

/-- Unit-distance neighbors around a common point have inner product at most `1/2` after
translation to that point. -/
lemma inner_sub_le_half_of_mem_unitNeighbors {A : Finset ℂ} {p x y : ℂ}
    (hA : IsOneSeparated A) (hx : x ∈ unitNeighbors A p) (hy : y ∈ unitNeighbors A p)
    (hxy : x ≠ y) :
    ⟪x - p, y - p⟫ ≤ (1 / 2 : ℝ) := by
  have hxA : x ∈ A := (Finset.mem_filter.1 hx).1
  have hyA : y ∈ A := (Finset.mem_filter.1 hy).1
  have hxnorm : ‖x - p‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.1 hx).2
  have hynorm : ‖y - p‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.1 hy).2
  apply inner_le_half_of_unit_norm_of_one_le_norm_sub hxnorm hynorm
  simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using hA x hxA y hyA hxy

/-- Unit-distance neighbors around a common point are angularly separated by at least `π/3`. -/
lemma pi_div_three_le_angle_sub_of_mem_unitNeighbors {A : Finset ℂ} {p x y : ℂ}
    (hA : IsOneSeparated A) (hx : x ∈ unitNeighbors A p) (hy : y ∈ unitNeighbors A p)
    (hxy : x ≠ y) :
    Real.pi / 3 ≤ angle (x - p) (y - p) := by
  have hxnorm : ‖x - p‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.1 hx).2
  have hynorm : ‖y - p‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.1 hy).2
  apply pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub hxnorm hynorm
  simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
    hA x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy

/-- Every point has at most six unit-distance neighbors in a one-separated planar set. -/
theorem card_unitNeighbors_le_six {A : Finset ℂ} (hA : IsOneSeparated A) (p : ℂ) :
    (unitNeighbors A p).card ≤ 6 := by
  let N := unitNeighbors A p
  let D : Finset ℂ := N.image fun q ↦ q - p
  have hcardD : D.card = N.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact sub_left_inj.mp hxy
  have hnorm : ∀ z ∈ D, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.1 hq).2
  have hsep : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_image.1 hx with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨r, hr, rfl⟩
    have hqr : q ≠ r := by
      intro h
      subst r
      exact hxy rfl
    simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
      hA q (Finset.mem_filter.1 hq).1 r (Finset.mem_filter.1 hr).1 hqr
  rw [← hcardD]
  exact card_le_six_of_unit_oneSeparated D hnorm hsep

/-- At most three one-separated unit neighbors of a point lie in any fixed strict lower
half-plane.  (Rotating coordinates gives the corresponding statement for every open
semicircle.) -/
theorem card_lowerUnitNeighbors_le_three {A : Finset ℂ} (hA : IsOneSeparated A) (p : ℂ) :
    (lowerUnitNeighbors A p).card ≤ 3 := by
  let L := lowerUnitNeighbors A p
  let f : L → Fin 3 := fun q ↦
    ⟨(phaseBin ((q : ℂ) - p)).val,
      phaseBin_val_lt_three_of_im_neg (Finset.mem_filter.1 q.prop).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hbin : phaseBin ((x : ℂ) - p) = phaseBin ((y : ℂ) - p) := by
      apply Fin.ext
      have hv := congrArg Fin.val hxy
      simpa [f] using hv
    have hxN : (x : ℂ) ∈ unitNeighbors A p := (Finset.mem_filter.1 x.prop).1
    have hyN : (y : ℂ) ∈ unitNeighbors A p := (Finset.mem_filter.1 y.prop).1
    have hxnorm : ‖(x : ℂ) - p‖ = 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using (Finset.mem_filter.1 hxN).2
    have hynorm : ‖(y : ℂ) - p‖ = 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using (Finset.mem_filter.1 hyN).2
    have hpoints : (x : ℂ) ≠ (y : ℂ) := by
      exact hne
    have hdist : 1 ≤ ‖((x : ℂ) - p) - ((y : ℂ) - p)‖ := by
      simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
        hA x (Finset.mem_filter.1 hxN).1 y (Finset.mem_filter.1 hyN).1 hpoints
    have hangle_ge := pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hxnorm hynorm hdist
    have hangle_eq := angle_eq_abs_principalPhase_sub_of_phaseBin_eq hxnorm hynorm hbin
    have hangle_lt := abs_principalPhase_sub_lt_of_phaseBin_eq hbin
    linarith
  simpa [L] using Fintype.card_le_of_injective f hf

/-- If a point has six unit-distance neighbors, translation followed by angular binning is a
bijection from those neighbors to the six sectors. -/
theorem phaseBin_sub_bijective_of_card_unitNeighbors_eq_six {A : Finset ℂ}
    (hA : IsOneSeparated A) (p : ℂ) (hcard : (unitNeighbors A p).card = 6) :
    Function.Bijective
      (fun q : unitNeighbors A p ↦ phaseBin ((q : ℂ) - p)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hxnorm : ‖(x : ℂ) - p‖ = 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using (Finset.mem_filter.1 x.prop).2
    have hynorm : ‖(y : ℂ) - p‖ = 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using (Finset.mem_filter.1 y.prop).2
    have hdist : 1 ≤ ‖((x : ℂ) - p) - ((y : ℂ) - p)‖ := by
      simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
        hA x (Finset.mem_filter.1 x.prop).1 y (Finset.mem_filter.1 y.prop).1 hne
    have hangle_ge := pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hxnorm hynorm hdist
    have hangle_eq := angle_eq_abs_principalPhase_sub_of_phaseBin_eq hxnorm hynorm hxy
    have hangle_lt := abs_principalPhase_sub_lt_of_phaseBin_eq hxy
    linarith
  · simpa [hcard]

/-- Thus every one of the six half-open `π/3` sectors contains a unique unit neighbor in the
degree-six case. -/
theorem existsUnique_mem_unitNeighbors_phaseBin_of_card_eq_six {A : Finset ℂ}
    (hA : IsOneSeparated A) (p : ℂ) (hcard : (unitNeighbors A p).card = 6)
    (i : Fin 6) :
    ∃! q : ℂ, q ∈ unitNeighbors A p ∧ phaseBin (q - p) = i := by
  have hbij := phaseBin_sub_bijective_of_card_unitNeighbors_eq_six hA p hcard
  obtain ⟨q, hq⟩ := hbij.2 i
  refine ⟨q, ⟨q.prop, hq⟩, ?_⟩
  intro r hr
  have heq : (⟨r, hr.1⟩ : unitNeighbors A p) = q :=
    hbij.1 (hr.2.trans hq.symm)
  exact congrArg Subtype.val heq

/-- A degree-six unit-neighbor set can be indexed by its phase sectors; in that indexing the
translated neighbor vectors satisfy all six regular-hexagon completion identities. -/
theorem exists_unitNeighborEquiv_with_regular_hexagon_identities {A : Finset ℂ}
    (hA : IsOneSeparated A) (p : ℂ) (hcard : (unitNeighbors A p).card = 6) :
    ∃ e : Fin 6 ≃ unitNeighbors A p,
      (∀ i, phaseBin (((e i : unitNeighbors A p) : ℂ) - p) = i) ∧
      (((e 0 : unitNeighbors A p) : ℂ) - p) - (((e 1 : unitNeighbors A p) : ℂ) - p) =
          ((e 5 : unitNeighbors A p) : ℂ) - p ∧
      (((e 1 : unitNeighbors A p) : ℂ) - p) - (((e 2 : unitNeighbors A p) : ℂ) - p) =
          ((e 0 : unitNeighbors A p) : ℂ) - p ∧
      (((e 2 : unitNeighbors A p) : ℂ) - p) - (((e 3 : unitNeighbors A p) : ℂ) - p) =
          ((e 1 : unitNeighbors A p) : ℂ) - p ∧
      (((e 3 : unitNeighbors A p) : ℂ) - p) - (((e 4 : unitNeighbors A p) : ℂ) - p) =
          ((e 2 : unitNeighbors A p) : ℂ) - p ∧
      (((e 4 : unitNeighbors A p) : ℂ) - p) - (((e 5 : unitNeighbors A p) : ℂ) - p) =
          ((e 3 : unitNeighbors A p) : ℂ) - p ∧
      (((e 5 : unitNeighbors A p) : ℂ) - p) - (((e 0 : unitNeighbors A p) : ℂ) - p) =
          ((e 4 : unitNeighbors A p) : ℂ) - p := by
  let f : unitNeighbors A p → Fin 6 := fun q ↦ phaseBin ((q : ℂ) - p)
  have hf : Function.Bijective f :=
    phaseBin_sub_bijective_of_card_unitNeighbors_eq_six hA p hcard
  let e : Fin 6 ≃ unitNeighbors A p := (Equiv.ofBijective f hf).symm
  let v : Fin 6 → ℂ := fun i ↦ ((e i : unitNeighbors A p) : ℂ) - p
  have hbin : ∀ i, phaseBin (v i) = i := by
    intro i
    exact (Equiv.ofBijective f hf).apply_symm_apply i
  have hnorm : ∀ i, ‖v i‖ = 1 := by
    intro i
    rw [← dist_eq_norm]
    simpa [v, dist_comm] using (Finset.mem_filter.1 (e i).prop).2
  have hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖ := by
    intro i j hij
    have hpoints : (e i : ℂ) ≠ (e j : ℂ) := by
      intro heq
      apply hij
      apply e.injective
      exact Subtype.ext heq
    simpa only [v, sub_sub_sub_cancel_right, dist_eq_norm] using
      hA (e i) (Finset.mem_filter.1 (e i).prop).1
        (e j) (Finset.mem_filter.1 (e j).prop).1 hpoints
  refine ⟨e, ?_, ?_⟩
  · exact hbin
  · exact regular_hexagon_sub_next_identities v hnorm hsep hbin

end ComplexPlane

end Erdos957Angle
