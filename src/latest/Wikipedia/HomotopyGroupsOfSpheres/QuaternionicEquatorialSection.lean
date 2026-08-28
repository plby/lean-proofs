import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRealRepresentation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A continuous contraction of the completion section on equatorial columns

The real part of the distinguished coordinate is zero. A quarter-circle
rotation from the axis to the column stays in the section chart throughout.
Applying the original completion section gives an actual path from the
identity to that section, continuously in the whole column family.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

abbrev EquatorialColumn (j : N) := {v : UnitColumn N // (v.val j).re = 0}

def quarterColumnVector (j : N) (t : I) (v : EquatorialColumn j) : N → ℍ :=
  Real.cos ((t : ℝ) * (Real.pi / 2)) • axis j +
    Real.sin ((t : ℝ) * (Real.pi / 2)) • v.val.val

theorem quarterColumnVector_unit (j : N) (t : I) (v : EquatorialColumn j) :
    pairing (quarterColumnVector j t v) (quarterColumnVector j t v) = 1 := by
  apply (pairing_self_eq_one_iff_norm _).mpr
  let a : PiLp 2 (fun _ : N ↦ ℍ) := WithLp.toLp 2 (axis j)
  let b : PiLp 2 (fun _ : N ↦ ℍ) := WithLp.toLp 2 v.val.val
  have ha : ‖a‖ = 1 := (pairing_self_eq_one_iff_norm _).mp (pairing_axis j)
  have hb : ‖b‖ = 1 := (pairing_self_eq_one_iff_norm _).mp v.val.property
  have hab : inner ℝ a b = 0 := by
    rw [inner_eq_re_pairing]
    simpa [pairing, axis, Pi.single_apply, apply_ite] using v.property
  let c := Real.cos ((t : ℝ) * (Real.pi / 2))
  let s := Real.sin ((t : ℝ) * (Real.pi / 2))
  have hn : ‖c • a + s • b‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, hab, ha, hb]
    simp only [mul_zero, add_zero, mul_one, Real.norm_eq_abs, sq_abs]
    exact Real.cos_sq_add_sin_sq _
  change ‖c • a + s • b‖ = 1
  nlinarith [norm_nonneg (c • a + s • b)]

theorem quarterColumnVector_re (j : N) (t : I) (v : EquatorialColumn j) :
    (quarterColumnVector j t v j).re = Real.cos ((t : ℝ) * (Real.pi / 2)) := by
  simp [quarterColumnVector, v.property, Quaternion.re_one]

theorem quarterColumnVector_mem_chart (j : N) (t : I) (v : EquatorialColumn j) :
    quarterColumnVector j t v j ≠ -1 := by
  have hc : 0 ≤ Real.cos ((t : ℝ) * (Real.pi / 2)) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]
  intro he
  have hr := congrArg (fun q : ℍ ↦ q.re) he
  rw [quarterColumnVector_re] at hr
  change Real.cos ((t : ℝ) * (Real.pi / 2)) = -1 at hr
  linarith

def equatorialColumnPath (j : N) : C(I × EquatorialColumn j, columnChart j) where
  toFun p := ⟨⟨quarterColumnVector j p.1 p.2, quarterColumnVector_unit j p.1 p.2⟩,
    quarterColumnVector_mem_chart j p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold quarterColumnVector
    have hv : Continuous (fun p : I × EquatorialColumn j ↦ p.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : I × EquatorialColumn j ↦
        (p.1 : ℝ) * (Real.pi / 2)) :=
      (continuous_subtype_val.comp continuous_fst).mul_const _
    exact ((Real.continuous_cos.comp ht).smul continuous_const).add
      ((Real.continuous_sin.comp ht).smul hv)

theorem equatorialColumnPath_zero (j : N) (v : EquatorialColumn j) :
    equatorialColumnPath j (0, v) = ⟨axisColumn j, axisColumn_mem_chart j⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  simp [equatorialColumnPath, quarterColumnVector, axisColumn]

theorem equatorialColumnPath_one (j : N) (v : EquatorialColumn j) :
    (equatorialColumnPath j (1, v)).val = v.val := by
  apply Subtype.ext
  simp [equatorialColumnPath, quarterColumnVector]

def equatorialSectionPath (j : N) : C(I × EquatorialColumn j, SpGroup N) :=
  ⟨fun p ↦ sectionMap j (equatorialColumnPath j p),
    (continuous_sectionMap j).comp (equatorialColumnPath j).continuous⟩

theorem equatorialSectionPath_zero (j : N) (v : EquatorialColumn j) :
    equatorialSectionPath j (0, v) = 1 := by
  change sectionMap j (equatorialColumnPath j (0, v)) = 1
  rw [equatorialColumnPath_zero, sectionMap_axis]

theorem equatorialSectionPath_one (j : N) (v : EquatorialColumn j)
    (hv : v.val ∈ columnChart j) :
    equatorialSectionPath j (1, v) = sectionMap j ⟨v.val, hv⟩ := by
  apply congrArg (sectionMap j)
  exact Subtype.ext (equatorialColumnPath_one j v)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
