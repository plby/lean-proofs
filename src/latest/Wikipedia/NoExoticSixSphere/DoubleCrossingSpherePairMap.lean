import Wikipedia.NoExoticSixSphere.WhitneySphereDerivative
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# An explicit pair of embedded three-spheres in a six-dimensional product

In the original sphere's head-tail coordinates the maps are
`(t,u) ↦ (u,(t+1)e)` and `(t,u) ↦ ((t+1)e,u)`, with a fixed unit vector `e`.
Both are restrictions of injective affine maps, so no embedding assertion is
inferred merely from an immersion or a local sheet chart.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereCylinder
open WhitneySphere (head head_apply join_head_tail)

def axis : Vector 3 := (spherePole 2).val

theorem norm_axis : ‖axis‖ = 1 := ClosedHemisphere.unit_norm (spherePole 2)

theorem axis_ne_zero : axis ≠ 0 := ne_zero_of_mem_unit_sphere (spherePole 2)

def leftLinear : Vector 4 →L[ℝ] (Vector 3 × Vector 3) :=
  (tail 2).prod (head.smulRight axis)

def rightLinear : Vector 4 →L[ℝ] (Vector 3 × Vector 3) :=
  (head.smulRight axis).prod (tail 2)

theorem leftLinear_apply (v : Vector 4) : leftLinear v = (tail 2 v, head v • axis) := rfl

theorem rightLinear_apply (v : Vector 4) : rightLinear v = (head v • axis, tail 2 v) := rfl

theorem injective_leftLinear : Injective leftLinear := by
  intro v w h
  have ht : tail 2 v = tail 2 w := congrArg Prod.fst h
  have hh : head v = head w :=
    smul_left_injective ℝ axis_ne_zero (congrArg Prod.snd h)
  rw [← join_head_tail v, ← join_head_tail w, hh, ht]

theorem injective_rightLinear : Injective rightLinear := by
  intro v w h
  have ht : tail 2 v = tail 2 w := congrArg (fun p : Vector 3 × Vector 3 ↦ p.2) h
  have hh : head v = head w :=
    smul_left_injective ℝ axis_ne_zero (congrArg Prod.fst h)
  rw [← join_head_tail v, ← join_head_tail w, hh, ht]

def leftAmbient (v : Vector 4) : Vector 3 × Vector 3 := leftLinear v + (0, axis)

def rightAmbient (v : Vector 4) : Vector 3 × Vector 3 := rightLinear v + (axis, 0)

theorem leftAmbient_apply (v : Vector 4) :
    leftAmbient v = (tail 2 v, (head v + 1) • axis) := by
  simp only [leftAmbient, leftLinear_apply, Prod.mk_add_mk, add_zero, add_smul, one_smul]

theorem rightAmbient_apply (v : Vector 4) :
    rightAmbient v = ((head v + 1) • axis, tail 2 v) := by
  simp only [rightAmbient, rightLinear_apply, Prod.mk_add_mk, add_zero, add_smul, one_smul]

theorem contDiff_leftAmbient : ContDiff ℝ ∞ leftAmbient :=
  leftLinear.contDiff.add contDiff_const

theorem contDiff_rightAmbient : ContDiff ℝ ∞ rightAmbient :=
  rightLinear.contDiff.add contDiff_const

def left (x : Sphere 3) : Vector 3 × Vector 3 := leftAmbient x.val

def right (x : Sphere 3) : Vector 3 × Vector 3 := rightAmbient x.val

theorem contMDiff_left : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ left := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact contDiff_leftAmbient.contMDiff.comp contMDiff_coe_sphere

theorem contMDiff_right : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ right := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact contDiff_rightAmbient.contMDiff.comp contMDiff_coe_sphere

def leftMap : C(Sphere 3, Vector 3 × Vector 3) := ⟨left, contMDiff_left.continuous⟩

def rightMap : C(Sphere 3, Vector 3 × Vector 3) := ⟨right, contMDiff_right.continuous⟩

theorem injective_left : Injective left := by
  intro x y h
  apply Subtype.ext
  exact injective_leftLinear (add_right_cancel h)

theorem injective_right : Injective right := by
  intro x y h
  apply Subtype.ext
  exact injective_rightLinear (add_right_cancel h)

theorem head_sq_add_tail_sq (x : Sphere 3) : head x.val ^ 2 + ‖tail 2 x.val‖ ^ 2 = 1 := by
  have h := norm_join_sq 2 (head x.val) (tail 2 x.val)
  rw [join_head_tail, ClosedHemisphere.unit_norm, one_pow] at h
  exact h.symm

theorem head_bounds (x : Sphere 3) : -1 ≤ head x.val ∧ head x.val ≤ 1 := by
  have h := head_sq_add_tail_sq x
  constructor <;> nlinarith [sq_nonneg ‖tail 2 x.val‖]

theorem norm_tail_le_one (x : Sphere 3) : ‖tail 2 x.val‖ ≤ 1 := by
  have h := head_sq_add_tail_sq x
  nlinarith [sq_nonneg (head x.val), norm_nonneg (tail 2 x.val)]

theorem norm_left_le_two (x : Sphere 3) : ‖left x‖ ≤ 2 := by
  rw [left, leftAmbient_apply, Prod.norm_def, max_le_iff]
  refine ⟨(norm_tail_le_one x).trans (by norm_num), ?_⟩
  rw [norm_smul, norm_axis, mul_one, Real.norm_eq_abs, abs_of_nonneg]
  · linarith [(head_bounds x).2]
  · linarith [(head_bounds x).1]

theorem norm_right_le_two (x : Sphere 3) : ‖right x‖ ≤ 2 := by
  rw [right, rightAmbient_apply, Prod.norm_def, max_le_iff]
  refine ⟨?_, (norm_tail_le_one x).trans (by norm_num)⟩
  rw [norm_smul, norm_axis, mul_one, Real.norm_eq_abs, abs_of_nonneg]
  · linarith [(head_bounds x).2]
  · linarith [(head_bounds x).1]

def secondSource : Sphere 3 :=
  ⟨join 2 (0, axis), by
    have h := norm_join_sq 2 0 axis
    rw [norm_axis] at h
    have hn : ‖join 2 (0, axis)‖ = 1 := by nlinarith [norm_nonneg (join 2 (0, axis))]
    simpa only [mem_sphere, dist_zero_right] using hn⟩

theorem head_secondSource : head secondSource.val = 0 := rfl

theorem tail_secondSource : tail 2 secondSource.val = axis := tail_join 2 0 axis

theorem first_ne_second : endPole 2 false ≠ secondSource := by
  intro h
  have hh := congrArg (fun x : Sphere 3 ↦ head x.val) h
  norm_num [head_apply, endPole_head, secondSource] at hh

theorem left_first : left (endPole 2 false) = 0 := by
  simp only [left, leftAmbient_apply, tail_endPole, head_apply, endPole_head,
    Bool.false_eq_true, ↓reduceIte, neg_add_cancel, zero_smul]
  rfl

theorem right_first : right (endPole 2 false) = 0 := by
  simp only [right, rightAmbient_apply, tail_endPole, head_apply, endPole_head,
    Bool.false_eq_true, ↓reduceIte, neg_add_cancel, zero_smul]
  rfl

theorem left_second : left secondSource = (axis, axis) := by
  simp only [left, leftAmbient_apply, head_secondSource, tail_secondSource, zero_add, one_smul]

theorem right_second : right secondSource = (axis, axis) := by
  simp only [right, rightAmbient_apply, head_secondSource, tail_secondSource, zero_add, one_smul]

end NoExoticSixSphere.DoubleCrossingSpherePair
