import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Smooth coordinates on the open unit interval

The tangent and arctangent formulas give a genuine smooth coordinate change
between `(0,1)` and the real line. Both inverse identities and the exact
domains are proved. These coordinates will be used on the original cube
interior; no smoothness is claimed for a merely topological interval map.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothInterval

def angle (t : ℝ) : ℝ := Real.pi * (t - 1 / 2)

def coordinate (t : ℝ) : ℝ := Real.tan (angle t)

def parameter (x : ℝ) : ℝ := Real.arctan x / Real.pi + 1 / 2

theorem angle_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    angle t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  unfold angle
  constructor <;> nlinarith [Real.pi_pos, mul_pos Real.pi_pos ht.1,
    mul_pos Real.pi_pos (sub_pos.mpr ht.2)]

theorem parameter_mem (x : ℝ) : parameter x ∈ Ioo (0 : ℝ) 1 := by
  have h := Real.arctan_mem_Ioo x
  have hlow : -(1 / 2 : ℝ) < Real.arctan x / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    nlinarith [h.1]
  have hhigh : Real.arctan x / Real.pi < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [h.2]
  constructor <;> dsimp [parameter] <;> linarith

theorem parameter_coordinate {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    parameter (coordinate t) = t := by
  rw [parameter, coordinate, Real.arctan_tan (angle_mem ht).1 (angle_mem ht).2]
  unfold angle
  field_simp
  <;> ring

theorem coordinate_parameter (x : ℝ) : coordinate (parameter x) = x := by
  have ha : angle (parameter x) = Real.arctan x := by
    unfold angle parameter
    field_simp
    <;> ring
  rw [coordinate, ha, Real.tan_arctan]

theorem contDiffOn_coordinate : ContDiffOn ℝ ∞ coordinate (Ioo (0 : ℝ) 1) := by
  intro t ht
  have hc := (Real.cos_pos_of_mem_Ioo (angle_mem ht)).ne'
  exact ((Real.contDiffAt_tan.mpr hc).comp t
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).contDiffAt)).contDiffWithinAt

theorem contDiff_parameter : ContDiff ℝ ∞ parameter :=
  (Real.contDiff_arctan.div_const Real.pi).add contDiff_const

def coordinates : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun := coordinate
  invFun := parameter
  source := Ioo 0 1
  target := univ
  map_source' _ _ := mem_univ _
  map_target' x _ := parameter_mem x
  left_inv' _ ht := parameter_coordinate ht
  right_inv' x _ := coordinate_parameter x
  open_source := isOpen_Ioo
  open_target := isOpen_univ
  contMDiffOn_toFun := contDiffOn_coordinate.contMDiffOn
  contMDiffOn_invFun := contDiff_parameter.contMDiff.contMDiffOn

def homeomorph : Ioo (0 : ℝ) 1 ≃ₜ ℝ where
  toFun t := coordinate t
  invFun x := ⟨parameter x, parameter_mem x⟩
  left_inv t := Subtype.ext (parameter_coordinate t.property)
  right_inv x := coordinate_parameter x
  continuous_toFun := contDiffOn_coordinate.continuousOn.comp_continuous
    continuous_subtype_val (fun t ↦ t.property)
  continuous_invFun := contDiff_parameter.continuous.subtype_mk _

end NoExoticSixSphere.SmoothInterval
