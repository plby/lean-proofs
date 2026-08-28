import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UnitInterval

/-!
# Time collars for relative cylinder homotopies

A clamped affine reparametrization makes a cylinder map constant in time near
each end. Interpolation from the original time to this reparametrization fixes
the two endpoint slices throughout. All constructions use the usual interval
and product topologies.
-/

open Set unitInterval

namespace NoExoticSixSphere.CylinderTime

noncomputable section

/-- A real time parameter that has constant collars before one third and after two thirds. -/
def collar (t : ℝ) : I := projIcc 0 1 zero_le_one (3 * t - 1)

theorem continuous_collar : Continuous collar :=
  continuous_projIcc.comp ((continuous_const.mul continuous_id).sub continuous_const)

theorem collar_left {t : ℝ} (ht : t ≤ 1 / 3) : collar t = 0 :=
  projIcc_of_le_left zero_le_one (by linarith)

theorem collar_right {t : ℝ} (ht : 2 / 3 ≤ t) : collar t = 1 :=
  projIcc_of_right_le zero_le_one (by linarith)

theorem collar_zero : collar 0 = 0 := collar_left (by norm_num)

theorem collar_one : collar 1 = 1 := collar_right (by norm_num)

/-- Interpolate the time with its collared version, retaining values in the unit interval. -/
def blend (s t : I) : I :=
  projIcc 0 1 zero_le_one ((1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) * (collar (t : ℝ) : ℝ))

theorem continuous_blend : Continuous (fun p : I × I ↦ blend p.1 p.2) := by
  have hs : Continuous (fun p : I × I ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun p : I × I ↦ (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_projIcc.comp
    (((continuous_const.sub hs).mul ht).add
      (hs.mul (continuous_subtype_val.comp (continuous_collar.comp ht))))

theorem blend_zero (t : I) : blend 0 t = t := by
  change projIcc 0 1 zero_le_one
    ((1 - (0 : ℝ)) * (t : ℝ) + (0 : ℝ) * (collar (t : ℝ) : ℝ)) = t
  rw [sub_zero, one_mul, zero_mul, add_zero]
  exact projIcc_val zero_le_one t

theorem blend_one (t : I) : blend 1 t = collar (t : ℝ) := by
  change projIcc 0 1 zero_le_one
    ((1 - (1 : ℝ)) * (t : ℝ) + (1 : ℝ) * (collar (t : ℝ) : ℝ)) = collar (t : ℝ)
  rw [sub_self, zero_mul, one_mul, zero_add]
  exact projIcc_val zero_le_one (collar (t : ℝ))

theorem blend_left (s : I) : blend s 0 = 0 := by
  change projIcc 0 1 zero_le_one ((1 - (s : ℝ)) * 0 + (s : ℝ) * (collar 0 : ℝ)) = 0
  rw [collar_zero]
  change projIcc 0 1 zero_le_one ((1 - (s : ℝ)) * 0 + (s : ℝ) * 0) = 0
  rw [mul_zero, mul_zero, zero_add]
  exact projIcc_left (show (0 : ℝ) ≤ 1 from zero_le_one)

theorem blend_right (s : I) : blend s 1 = 1 := by
  change projIcc 0 1 zero_le_one ((1 - (s : ℝ)) * 1 + (s : ℝ) * (collar 1 : ℝ)) = 1
  rw [collar_one]
  change projIcc 0 1 zero_le_one ((1 - (s : ℝ)) * 1 + (s : ℝ) * 1) = 1
  rw [mul_one, mul_one, sub_add_cancel]
  exact projIcc_right (show (0 : ℝ) ≤ 1 from zero_le_one)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The two endpoint slices of a cylinder. -/
def boundary : Set (I × X) := {p | p.1 = 0 ∨ p.1 = 1}

/-- A cylinder map extended to real time with constant end collars. -/
def realCollaredMap (H : C(I × X, Y)) : C(ℝ × X, Y) :=
  H.comp ⟨fun p ↦ (collar p.1, p.2),
    (continuous_collar.comp continuous_fst).prodMk continuous_snd⟩

/-- The ordinary cylinder inside its real-time extension. -/
def inclusion : C(I × X, ℝ × X) :=
  ⟨fun p ↦ ((p.1 : ℝ), p.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

def collaredMap (H : C(I × X, Y)) : C(I × X, Y) := (realCollaredMap H).comp inclusion

/-- Adding time collars is a native homotopy relative to both endpoint slices. -/
def collarHomotopy (H : C(I × X, Y)) : H.HomotopyRel (collaredMap H) boundary where
  toFun p := H (blend p.1 p.2.1, p.2.2)
  continuous_toFun := H.continuous.comp
    ((continuous_blend.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))
  map_zero_left p := by
    change H (blend 0 p.1, p.2) = H p
    rw [blend_zero]
  map_one_left p := by
    change H (blend 1 p.1, p.2) = H (collar (p.1 : ℝ), p.2)
    rw [blend_one]
  prop' s p hp := by
    rcases p with ⟨t, x⟩
    rcases hp with ht | ht
    · change t = 0 at ht
      subst t
      change H (blend s 0, x) = H (0, x)
      rw [blend_left]
    · change t = 1 at ht
      subst t
      change H (blend s 1, x) = H (1, x)
      rw [blend_right]

end

end NoExoticSixSphere.CylinderTime
