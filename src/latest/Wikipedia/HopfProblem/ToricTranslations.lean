import Wikipedia.HopfProblem.ToricHausdorff

/-!
# Integral translations of the toric cusp charts

Translating the A₂ triangles gives actual holomorphic automorphisms of the
glued toric space. They preserve the function `t`. These are the shears in
Lemma 4.3 before the additional holomorphic torus multipliers are inserted.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem

namespace ToricFan.Triangle

def shift (s : Triangle) (v : Fin 2 → ℤ) : Triangle :=
  ⟨s.a + v 0, s.b + v 1, s.upper⟩

@[simp] theorem shift_zero (s : Triangle) : s.shift 0 = s := by
  ext <;> simp [shift]

theorem shift_add (s : Triangle) (v w : Fin 2 → ℤ) :
    (s.shift v).shift w = s.shift (v + w) := by
  ext <;> simp [shift, add_assoc]

def shear (v : Fin 2 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, v 0; 0, 1, v 1; 0, 0, 1]

@[simp] theorem shear_zero : shear 0 = 1 := by decide

theorem shear_add (v w : Fin 2 → ℤ) : shear v * shear w = shear (v + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

theorem rays_shift (s : Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).rays = shear v * s.rays := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [rays, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem dual_shift (s : Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).dual = s.dual * shear (-v) := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [dual, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem transition_shift (s t : Triangle) (v : Fin 2 → ℤ) :
    transition (s.shift v) (t.shift v) = transition s t := by
  rw [transition, dual_shift, rays_shift, Matrix.mul_assoc,
    ← Matrix.mul_assoc (shear (-v)), shear_add]
  simp [transition]

theorem chartChange_shift_source (s t : Triangle) (v : Fin 2 → ℤ) :
    (chartChange (s.shift v) (t.shift v)).source = (chartChange s t).source := by
  simp [transition_shift]

theorem chartChange_shift_apply (s t : Triangle) (v : Fin 2 → ℤ)
    (z : ToricCharts.CoordinateSpace 3) :
    chartChange (s.shift v) (t.shift v) z = chartChange s t z := by
  change ToricCharts.monomial (transition (s.shift v) (t.shift v)) z =
    ToricCharts.monomial (transition s t) z
  rw [transition_shift]

end ToricFan.Triangle

namespace ToricSpace

open ToricCharts ToricFan Triangle

theorem translation_compatible (v : Fin 2 → ℤ) (s t : Triangle)
    (z : CoordinateSpace 3) (hz : z ∈ (chartChange s t).source) :
    inclusion (t.shift v) (chartChange s t z) = inclusion (s.shift v) z := by
  apply ((inclusion_eq_iff (s.shift v) (t.shift v) z _).mpr ?_).symm
  exact ⟨by simpa only [chartChange_shift_source] using hz, chartChange_shift_apply s t v z⟩

def translate (v : Fin 2 → ℤ) : Space → Space :=
  descend (fun s z => inclusion (s.shift v) z)

@[simp] theorem translate_inclusion (v : Fin 2 → ℤ) (s : Triangle)
    (z : CoordinateSpace 3) : translate v (inclusion s z) = inclusion (s.shift v) z :=
  descend_inclusion _ (translation_compatible v) s z

theorem translate_holomorphic (v : Fin 2 → ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (translate v) :=
  descend_holomorphic _ _ (translation_compatible v) (fun s => inclusion_holomorphic (s.shift v))

@[simp] theorem translate_zero (x : Space) : translate 0 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

theorem translate_add (v w : Fin 2 → ℤ) (x : Space) :
    translate v (translate w x) = translate (v + w) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [shift_add, add_comm v w]

def translationHomeomorph (v : Fin 2 → ℤ) : Space ≃ₜ Space where
  toFun := translate v
  invFun := translate (-v)
  left_inv x := by rw [translate_add]; simp
  right_inv x := by rw [translate_add]; simp
  continuous_toFun := (translate_holomorphic v).continuous
  continuous_invFun := (translate_holomorphic (-v)).continuous

@[simp] theorem time_translate (v : Fin 2 → ℤ) (x : Space) : time (translate v x) = time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

end ToricSpace

end Wikipedia.HopfProblem
