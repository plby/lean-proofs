import Wikipedia.SmoothSixDPoincare.FlowCollarCoordinates

/-!
# Rescaling a flow collar into an intermediate absorbing region

The map preserves trajectories and the core, but compresses the outer collar
by the positive continuous factor determined by the intermediate boundary.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
  (d : FlowCollarData F A B)

/-- Nonnegative time by which the collar rescaling moves a point. -/
def shift (x : B) : ℝ := d.duration x * (1 - d.factor x)

theorem shift_nonneg (x : B) : 0 ≤ d.shift x :=
  mul_nonneg (d.duration_nonneg x) (sub_nonneg.mpr (d.factor_le_one x))

theorem shift_le_duration (x : B) : d.shift x ≤ d.duration x := by
  dsimp [shift]
  nlinarith [mul_nonneg (d.duration_nonneg x) (d.factor_pos x).le]

theorem continuous_shift : Continuous d.shift :=
  d.continuous_duration.mul (continuous_const.sub d.continuous_factor)

/-- Rescaling as a continuous self-map of the outer region. -/
def rescale : C(B, B) where
  toFun x := ⟨F (d.shift x) x.1, d.forward_outer x.1 x.2 _ (d.shift_nonneg x)⟩
  continuous_toFun := (F.continuous d.continuous_shift continuous_subtype_val).subtype_mk _

theorem rescale_from_origin (x : B) :
    (d.rescale x).1 = F (d.time - d.duration x * d.factor x) (d.origin x).1 := by
  change F (d.shift x) x.1 = _
  conv_lhs => rw [← d.origin_reconstruct x]
  rw [← F.map_add]
  congr 1
  dsimp [shift]
  ring

theorem rescale_mem_inner (x : B) : (d.rescale x).1 ∈ A := by
  rw [d.rescale_from_origin]
  have hh : d.delay x ≤ d.time - d.duration x * d.factor x := by
    have h := mul_le_mul_of_nonneg_right (d.duration_le x) (d.factor_pos x).le
    rw [d.time_mul_factor] at h
    linarith
  exact (entryTime_le_iff F d.closed_inner d.forward_inner (d.hits_inner (d.origin x).2)
    ((d.delay_nonneg x).trans hh)).mp hh

theorem duration_rescale (x : B) :
    d.duration (d.rescale x) = d.duration x * d.factor x := by
  change entryTime F d.core (F (d.shift x) x.1) = _
  rw [entryTime_flow_of_le F d.closed_core (d.hits_core x.2)
    (d.shift_nonneg x) (d.shift_le_duration x)]
  change d.duration x - d.shift x = _
  dsimp [shift]
  ring

theorem origin_rescale (x : B) : d.origin (d.rescale x) = d.origin x := by
  apply Subtype.ext
  change F (d.duration (d.rescale x) - d.time) (F (d.shift x) x.1) =
    F (d.duration x - d.time) x.1
  rw [d.duration_rescale, ← F.map_add]
  congr 1
  dsimp [shift]
  ring

theorem factor_rescale (x : B) : d.factor (d.rescale x) = d.factor x := by
  unfold factor delay
  rw [d.origin_rescale]

/-- The actual rescaling is injective, including on the fixed inner core. -/
theorem rescale_injective : Function.Injective d.rescale := by
  intro x y h
  have hfactor : d.factor x = d.factor y := by
    rw [← d.factor_rescale x, ← d.factor_rescale y, h]
  have hdur : d.duration x = d.duration y := by
    have he := congrArg d.duration h
    rw [d.duration_rescale, d.duration_rescale, hfactor] at he
    exact mul_right_cancel₀ (d.factor_pos y).ne' he
  have horigin : d.origin x = d.origin y := by
    rw [← d.origin_rescale x, ← d.origin_rescale y, h]
  apply Subtype.ext
  rw [← d.origin_reconstruct x, ← d.origin_reconstruct y, hdur, horigin]

theorem rescale_eq_self_of_duration_eq_zero (x : B) (hx : d.duration x = 0) :
    d.rescale x = x := by
  apply Subtype.ext
  change F (d.shift x) x.1 = x.1
  simp only [shift, hx, zero_mul, F.map_zero_apply]

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
