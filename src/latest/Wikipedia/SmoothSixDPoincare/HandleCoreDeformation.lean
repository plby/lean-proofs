import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Wikipedia.SmoothSixDPoincare.RadialCoreShrink
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Basic

/-!
# Collapsing a handle onto its attaching face and core

An explicit continuous map sends the product handle onto the union of its
negative boundary and its zero positive-coordinate core. It fixes that
entire union. Convex interpolation gives a strong deformation relative to
the same union, so it can be glued to the unchanged lower sublevel.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped Topology unitInterval

namespace Wikipedia.SmoothSixDPoincare.HandleCoreDeformation

open MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def denominator (z : UnitDisk N × UnitDisk P) : ℝ :=
  max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem denominator_pos (z : UnitDisk N × UnitDisk P) : 0 < denominator z := by
  have hy : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have h := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  dsimp [denominator]
  linarith

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem continuous_denominator : Continuous (denominator (N := N) (P := P)) :=
  (continuous_subtype_val.comp continuous_fst).norm.max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).norm.div_const 2))

def negative (z : UnitDisk N × UnitDisk P) : UnitDisk N :=
  ⟨(denominator z)⁻¹ • (z.1 : N), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (denominator_pos z))]
    calc
      _ ≤ (denominator z)⁻¹ * denominator z :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_pos.mpr (denominator_pos z)).le
      _ = 1 := inv_mul_cancel₀ (denominator_pos z).ne'⟩

def positive (z : UnitDisk N × UnitDisk P) : UnitDisk P :=
  ⟨RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P),
    mem_closedBall_zero_iff.mpr ((RadialCoreShrink.norm_shrink_le _ _).trans
      (mem_closedBall_zero_iff.mp z.2.property))⟩

omit [NormedSpace ℝ P] in
theorem continuous_negative : Continuous (negative (N := N) (P := P)) :=
  ((continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _

omit [NormedSpace ℝ N] in
theorem continuous_positive : Continuous (positive (N := N) (P := P)) :=
  (RadialCoreShrink.continuous_shrink.comp
    ((continuous_const.mul (continuous_const.sub
      (continuous_subtype_val.comp continuous_fst).norm)).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _

def collapse : C(UnitDisk N × UnitDisk P, UnitDisk N × UnitDisk P) :=
  ⟨fun z => (negative z, positive z), continuous_negative.prodMk continuous_positive⟩

def faceCore : Set (UnitDisk N × UnitDisk P) :=
  {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

theorem collapse_mem (z : UnitDisk N × UnitDisk P) : collapse z ∈ faceCore := by
  rcases le_total (1 - ‖(z.2 : P)‖ / 2) ‖(z.1 : N)‖ with h | h
  · left
    have hx : 0 < ‖(z.1 : N)‖ := by
      have hpos := denominator_pos z
      rwa [denominator, max_eq_left h] at hpos
    change ‖(denominator z)⁻¹ • (z.1 : N)‖ = 1
    rw [denominator, max_eq_left h, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']
  · right
    apply RadialCoreShrink.shrink_eq_zero
    linarith

theorem collapse_face (z : UnitDisk N × UnitDisk P) (hz : ‖(z.1 : N)‖ = 1) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, max_eq_left]
    linarith [norm_nonneg (z.2 : P)]
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, sub_self, mul_zero, RadialCoreShrink.shrink_zero_parameter]

theorem collapse_core (z : UnitDisk N × UnitDisk P) (hz : (z.2 : P) = 0) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, norm_zero, zero_div, sub_zero]
    exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, RadialCoreShrink.shrink_zero]

theorem collapse_fixed (z : UnitDisk N × UnitDisk P) (hz : z ∈ faceCore) :
    collapse z = z := hz.elim (collapse_face z) (collapse_core z)

section Blend

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def diskBlend (t : I) (x y : UnitDisk V) : UnitDisk V :=
  ⟨(1 - (t : ℝ)) • (x : V) + (t : ℝ) • (y : V),
    (convex_closedBall (0 : V) 1) x.property y.property
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))⟩

theorem continuous_diskBlend :
    Continuous (fun q : I × (UnitDisk V × UnitDisk V) => diskBlend q.1 q.2.1 q.2.2) :=
  (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd.fst)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd.snd))).subtype_mk _

@[simp] theorem diskBlend_zero (x y : UnitDisk V) : diskBlend 0 x y = x := by
  apply Subtype.ext
  simp [diskBlend]

@[simp] theorem diskBlend_one (x y : UnitDisk V) : diskBlend 1 x y = y := by
  apply Subtype.ext
  simp [diskBlend]

@[simp] theorem diskBlend_self (t : I) (x : UnitDisk V) : diskBlend t x x = x := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • (x : V) + (t : ℝ) • (x : V) = (x : V)
  rw [← add_smul, sub_add_cancel, one_smul]

end Blend

/-- The full handle deforms onto the face/core union, fixed on every point of that union. -/
def deformation :
    (ContinuousMap.id (UnitDisk N × UnitDisk P)).HomotopyRel collapse faceCore where
  toFun q := (diskBlend q.1 q.2.1 (collapse q.2).1,
    diskBlend q.1 q.2.2 (collapse q.2).2)
  continuous_toFun :=
    (continuous_diskBlend.comp (continuous_fst.prodMk
      (continuous_snd.fst.prodMk (collapse.continuous.comp continuous_snd).fst))).prodMk
    (continuous_diskBlend.comp (continuous_fst.prodMk
      (continuous_snd.snd.prodMk (collapse.continuous.comp continuous_snd).snd)))
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' t z hz := by
    change (diskBlend t z.1 (collapse z).1, diskBlend t z.2 (collapse z).2) = z
    rw [collapse_fixed z hz]
    simp

end Wikipedia.SmoothSixDPoincare.HandleCoreDeformation
