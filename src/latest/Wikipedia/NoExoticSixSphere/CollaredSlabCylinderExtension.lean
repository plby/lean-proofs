import Wikipedia.NoExoticSixSphere.CylinderTime
import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryPuncture

/-!
# Proper continuous cylinders with exact original endpoint collars

Reparametrize the given homotopy to be constant near its endpoints, then
apply the actual inward slab push with clock `4u(1-u)`. The original
endpoint maps are retained exactly, while every interior parameter maps
to the strict-time interior. The collar formulas retain the original
spatial maps, and the construction is homotopic to the input relative
to both ends. Smoothness and genericity are not asserted here.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.CylinderTime

def interiorClock (u : unitInterval) : unitInterval :=
  ⟨4 * (u : ℝ) * (1 - (u : ℝ)), by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) u.property.1)
        (sub_nonneg.mpr u.property.2)
    · nlinarith [sq_nonneg (2 * (u : ℝ) - 1)]⟩

theorem interiorClock_val (u : unitInterval) :
    (interiorClock u : ℝ) = 4 * (u : ℝ) * (1 - (u : ℝ)) := rfl

theorem continuous_interiorClock : Continuous interiorClock :=
  (((continuous_const.mul continuous_subtype_val).mul
    (continuous_const.sub continuous_subtype_val))).subtype_mk _

theorem interiorClock_zero : interiorClock 0 = 0 := by
  apply Subtype.ext
  norm_num [interiorClock]

theorem interiorClock_one : interiorClock 1 = 0 := by
  apply Subtype.ext
  norm_num [interiorClock]

theorem interiorClock_pos (u : unitInterval) (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1) :
    0 < (interiorClock u : ℝ) :=
  mul_pos (mul_pos (by norm_num) hu.1) (sub_pos.mpr hu.2)

theorem interiorClock_injectiveOn_left :
    Set.InjOn interiorClock {u : unitInterval | (u : ℝ) ≤ 1 / 3} := by
  intro u hu v hv he
  apply Subtype.ext
  have he' : 4 * (u : ℝ) * (1 - (u : ℝ)) = 4 * (v : ℝ) * (1 - (v : ℝ)) :=
    congrArg Subtype.val he
  rcases lt_trichotomy (u : ℝ) (v : ℝ) with h | h | h
  · have hp := mul_pos (sub_pos.mpr h) (show 0 < 1 - (u : ℝ) - (v : ℝ) by
      change (u : ℝ) ≤ 1 / 3 at hu
      change (v : ℝ) ≤ 1 / 3 at hv
      linarith)
    nlinarith
  · exact h
  · have hp := mul_pos (sub_pos.mpr h) (show 0 < 1 - (u : ℝ) - (v : ℝ) by
      change (u : ℝ) ≤ 1 / 3 at hu
      change (v : ℝ) ≤ 1 / 3 at hv
      linarith)
    nlinarith

theorem interiorClock_injectiveOn_right :
    Set.InjOn interiorClock {u : unitInterval | 2 / 3 ≤ (u : ℝ)} := by
  intro u hu v hv he
  apply Subtype.ext
  have he' : 4 * (u : ℝ) * (1 - (u : ℝ)) = 4 * (v : ℝ) * (1 - (v : ℝ)) :=
    congrArg Subtype.val he
  rcases lt_trichotomy (u : ℝ) (v : ℝ) with h | h | h
  · have hp := mul_pos (sub_pos.mpr h) (show 0 < (u : ℝ) + (v : ℝ) - 1 by
      change 2 / 3 ≤ (u : ℝ) at hu
      change 2 / 3 ≤ (v : ℝ) at hv
      linarith)
    nlinarith
  · exact h
  · have hp := mul_pos (sub_pos.mpr h) (show 0 < (u : ℝ) + (v : ℝ) - 1 by
      change 2 / 3 ≤ (u : ℝ) at hu
      change 2 / 3 ≤ (v : ℝ) at hv
      linarith)
    nlinarith

theorem interiorClock_lt_one_left (u : unitInterval) (hu : (u : ℝ) ≤ 1 / 3) :
    (interiorClock u : ℝ) < 1 := by
  rw [interiorClock_val]
  have hsq := sq_pos_of_pos (show 0 < 1 - 2 * (u : ℝ) by linarith)
  nlinarith

theorem interiorClock_lt_one_right (u : unitInterval) (hu : 2 / 3 ≤ (u : ℝ)) :
    (interiorClock u : ℝ) < 1 := by
  rw [interiorClock_val]
  have hsq := sq_pos_of_pos (show 0 < 2 * (u : ℝ) - 1 by linarith)
  nlinarith

end NoExoticSixSphere.CylinderTime

namespace NoExoticSixSphere.CylinderFiberSlab.InteriorPush

variable {M N X : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))
  {f₀ f₁ : C(X, slab F z s t)} (H : f₀.Homotopy f₁)

def collaredCylinder : f₀.Homotopy f₁ where
  toFun p := map F z s t a b hsa hab hbt hleft hright
    (CylinderTime.interiorClock p.1, H (CylinderTime.collar (p.1 : ℝ), p.2))
  continuous_toFun := (map F z s t a b hsa hab hbt hleft hright).continuous.comp
    ((CylinderTime.continuous_interiorClock.comp continuous_fst).prodMk
      (H.continuous.comp ((CylinderTime.continuous_collar.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)))
  map_zero_left x := by
    rw [CylinderTime.interiorClock_zero]
    change map F z s t a b hsa hab hbt hleft hright
      (0, H (CylinderTime.collar 0, x)) = f₀ x
    rw [CylinderTime.collar_zero, H.apply_zero, map_zero]
  map_one_left x := by
    rw [CylinderTime.interiorClock_one]
    change map F z s t a b hsa hab hbt hleft hright
      (0, H (CylinderTime.collar 1, x)) = f₁ x
    rw [CylinderTime.collar_one, H.apply_one, map_zero]

theorem collaredCylinder_interior (u : unitInterval)
    (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1) (x : X) :
    collaredCylinder F z s t a b hsa hab hbt hleft hright H (u, x) ∈
      interiorDomain F z s t :=
  map_mem_interior_of_pos F z s t a b hsa hab hbt hleft hright
    (H (CylinderTime.collar (u : ℝ), x)) (CylinderTime.interiorClock u)
    (CylinderTime.interiorClock_pos u hu)

theorem collaredCylinder_left (u : unitInterval) (hu : (u : ℝ) ≤ 1 / 3)
    (x : X) (hx : (f₀ x).val.val.1 = s) :
    (collaredCylinder F z s t a b hsa hab hbt hleft hright H (u, x)).val.val =
      (s + (4 * (u : ℝ) * (1 - (u : ℝ))) * (a - s), (f₀ x).val.val.2) := by
  change (map F z s t a b hsa hab hbt hleft hright
    (CylinderTime.interiorClock u, H (CylinderTime.collar (u : ℝ), x))).val.val = _
  rw [CylinderTime.collar_left hu, H.apply_zero]
  apply Prod.ext
  · change (1 - (CylinderTime.interiorClock u : ℝ)) * (f₀ x).val.val.1 +
        (CylinderTime.interiorClock u : ℝ) *
          (projIcc a b hab (f₀ x).val.val.1 : ℝ) = _
    rw [CylinderTime.interiorClock_val, hx, projIcc_of_le_left hab hsa.le]
    ring
  · rfl

theorem collaredCylinder_right (u : unitInterval) (hu : 2 / 3 ≤ (u : ℝ))
    (x : X) (hx : (f₁ x).val.val.1 = t) :
    (collaredCylinder F z s t a b hsa hab hbt hleft hright H (u, x)).val.val =
      (t + (4 * (u : ℝ) * (1 - (u : ℝ))) * (b - t), (f₁ x).val.val.2) := by
  change (map F z s t a b hsa hab hbt hleft hright
    (CylinderTime.interiorClock u, H (CylinderTime.collar (u : ℝ), x))).val.val = _
  rw [CylinderTime.collar_right hu, H.apply_one]
  apply Prod.ext
  · change (1 - (CylinderTime.interiorClock u : ℝ)) * (f₁ x).val.val.1 +
        (CylinderTime.interiorClock u : ℝ) *
          (projIcc a b hab (f₁ x).val.val.1 : ℝ) = _
    rw [CylinderTime.interiorClock_val, hx, projIcc_of_right_le hab hbt.le]
    ring
  · rfl

def collaredCylinderHomotopy : H.toContinuousMap.HomotopyRel
    (collaredCylinder F z s t a b hsa hab hbt hleft hright H).toContinuousMap
      CylinderTime.boundary where
  toFun p := map F z s t a b hsa hab hbt hleft hright
    (p.1 * CylinderTime.interiorClock p.2.1, H (CylinderTime.blend p.1 p.2.1, p.2.2))
  continuous_toFun := by
    have hclock : Continuous (fun p : unitInterval × (unitInterval × X) ↦
        p.1 * CylinderTime.interiorClock p.2.1) :=
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (CylinderTime.continuous_interiorClock.comp
          (continuous_fst.comp continuous_snd)))).subtype_mk _
    exact (map F z s t a b hsa hab hbt hleft hright).continuous.comp
      (hclock.prodMk (H.continuous.comp ((CylinderTime.continuous_blend.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          (continuous_snd.comp continuous_snd))))
  map_zero_left p := by
    rw [zero_mul, CylinderTime.blend_zero, map_zero]
    rfl
  map_one_left p := by
    rw [one_mul, CylinderTime.blend_one]
    rfl
  prop' u p hp := by
    change map F z s t a b hsa hab hbt hleft hright
      (u * CylinderTime.interiorClock p.1, H (CylinderTime.blend u p.1, p.2)) = H (p.1, p.2)
    rcases hp with hp | hp
    · change p.1 = 0 at hp
      rw [hp, CylinderTime.interiorClock_zero, mul_zero, CylinderTime.blend_left, map_zero]
    · change p.1 = 1 at hp
      rw [hp, CylinderTime.interiorClock_one, mul_zero, CylinderTime.blend_right, map_zero]

theorem collaredCylinder_boundary_iff
    (h₀ : ∀ x, f₀ x ∈ BoundaryPush.ends F z s t)
    (h₁ : ∀ x, f₁ x ∈ BoundaryPush.ends F z s t) (u : unitInterval) (x : X) :
    collaredCylinder F z s t a b hsa hab hbt hleft hright H (u, x) ∈
      BoundaryPush.ends F z s t ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro hb
    by_contra hn
    push Not at hn
    have hu₀ : (u : ℝ) ≠ 0 := fun h ↦ hn.1 (Subtype.ext h)
    have hu₁ : (u : ℝ) ≠ 1 := fun h ↦ hn.2 (Subtype.ext h)
    have hi := collaredCylinder_interior F z s t a b hsa hab hbt hleft hright H u
      ⟨lt_of_le_of_ne u.property.1 hu₀.symm, lt_of_le_of_ne u.property.2 hu₁⟩ x
    exact hb.elim (ne_of_gt hi.1) (ne_of_lt hi.2)
  · rintro (rfl | rfl)
    · rw [(collaredCylinder F z s t a b hsa hab hbt hleft hright H).apply_zero]
      exact h₀ x
    · rw [(collaredCylinder F z s t a b hsa hab hbt hleft hright H).apply_one]
      exact h₁ x

end NoExoticSixSphere.CylinderFiberSlab.InteriorPush
