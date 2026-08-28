import Wikipedia.NoExoticSixSphere.CollaredSlabInteriorHomotopy
import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryRetraction
import Mathlib.Tactic.Linarith

/-!
# Deleting an actual boundary point preserves the slab's homotopy type

At every positive homotopy time the original collar push is strictly
interior. It therefore preserves the complement of any boundary point,
and gives a homotopy inverse to that complement's original inclusion.
-/

noncomputable section

open Set
open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.CollaredIntervalPush

theorem time_mem_Ioo_of_pos (a b : ℝ) (hab : a ≤ b) {s t r : ℝ}
    (hsa : s < a) (hbt : b < t) (hr : r ∈ Icc s t)
    (u : unitInterval) (hu : 0 < (u : ℝ)) : time a b hab (u, r) ∈ Ioo s t := by
  have hc : s < (projIcc a b hab r : ℝ) ∧ (projIcc a b hab r : ℝ) < t :=
    ⟨hsa.trans_le (projIcc a b hab r).property.1,
      (projIcc a b hab r).property.2.trans_lt hbt⟩
  have h₁ := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hr.1)
  have h₂ := mul_pos hu (sub_pos.mpr hc.1)
  have h₃ := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hr.2)
  have h₄ := mul_pos hu (sub_pos.mpr hc.2)
  change s < (1 - (u : ℝ)) * r + (u : ℝ) * (projIcc a b hab r : ℝ) ∧
    (1 - (u : ℝ)) * r + (u : ℝ) * (projIcc a b hab r : ℝ) < t
  constructor <;> nlinarith

end NoExoticSixSphere.CollaredIntervalPush

namespace NoExoticSixSphere.CylinderFiberSlab.InteriorPush

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))

theorem map_mem_interior_of_pos (p : slab F z s t) (u : unitInterval) (hu : 0 < (u : ℝ)) :
    map F z s t a b hsa hab hbt hleft hright (u, p) ∈ interiorDomain F z s t :=
  CollaredIntervalPush.time_mem_Ioo_of_pos a b hab hsa hbt p.property u hu

include hsa hab hbt hleft hright in
theorem exists_interior_mem_open (O : Set (slab F z s t)) (hO : IsOpen O)
    (p : slab F z s t) (hp : p ∈ O) :
    ∃ y : slab F z s t, y ∈ O ∧ y ∈ interiorDomain F z s t := by
  let f : C(unitInterval, slab F z s t) :=
    (map F z s t a b hsa hab hbt hleft hright).comp
      ⟨fun u ↦ (u, p), continuous_id.prodMk continuous_const⟩
  have hzero : (0 : unitInterval) ∈ f ⁻¹' O := by
    change map F z s t a b hsa hab hbt hleft hright (0, p) ∈ O
    rw [map_zero]
    exact hp
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((hO.preimage f.continuous).mem_nhds hzero)
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  let u : unitInterval := ⟨r, hr.le, (min_le_right _ _).trans (by norm_num)⟩
  have hu : u ∈ Metric.ball (0 : unitInterval) ε := by
    change |r - 0| < ε
    rw [sub_zero, abs_of_pos hr]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  exact ⟨f u, hball hu,
    map_mem_interior_of_pos F z s t a b hsa hab hbt hleft hright p u hr⟩

variable (w : slab F z s t) (hw : w ∈ BoundaryPush.ends F z s t)

include hw in
theorem map_ne_boundary_of_pos (p : slab F z s t) (u : unitInterval) (hu : 0 < (u : ℝ)) :
    map F z s t a b hsa hab hbt hleft hright (u, p) ≠ w := by
  intro he
  have hi : w ∈ interiorDomain F z s t :=
    he ▸ map_mem_interior_of_pos F z s t a b hsa hab hbt hleft hright p u hu
  change s < w.val.val.1 ∧ w.val.val.1 < t at hi
  change w.val.val.1 = s ∨ w.val.val.1 = t at hw
  exact hw.elim (ne_of_gt hi.1) (ne_of_lt hi.2)

include hw in
theorem map_preserves_boundary_puncture (p : ({w}ᶜ : Set (slab F z s t)))
    (u : unitInterval) :
    map F z s t a b hsa hab hbt hleft hright (u, p.val) ∈ ({w}ᶜ : Set (slab F z s t)) := by
  change map F z s t a b hsa hab hbt hleft hright (u, p.val) ≠ w
  by_cases hu : u = 0
  · subst u
    rw [map_zero]
    exact p.property
  · have hu' : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
      intro he
      exact hu (Subtype.ext he.symm))
    exact map_ne_boundary_of_pos F z s t a b hsa hab hbt hleft hright w hw p.val u hu'

def puncturePush : C(slab F z s t, ({w}ᶜ : Set (slab F z s t))) where
  toFun p := ⟨map F z s t a b hsa hab hbt hleft hright (1, p),
    map_ne_boundary_of_pos F z s t a b hsa hab hbt hleft hright w hw p 1 (by norm_num)⟩
  continuous_toFun := ((map F z s t a b hsa hab hbt hleft hright).continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

def punctureDeformation :
    (ContinuousMap.id ({w}ᶜ : Set (slab F z s t))).Homotopy
      ((puncturePush F z s t a b hsa hab hbt hleft hright w hw).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(({w}ᶜ : Set (slab F z s t)), slab F z s t))) where
  toFun p := ⟨map F z s t a b hsa hab hbt hleft hright (p.1, p.2.val),
    map_preserves_boundary_puncture F z s t a b hsa hab hbt hleft hright w hw p.2 p.1⟩
  continuous_toFun := ((map F z s t a b hsa hab hbt hleft hright).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := Subtype.ext (map_zero F z s t a b hsa hab hbt hleft hright p.val)
  map_one_left _ := rfl

def boundaryPunctureHomotopyEquiv : ({w}ᶜ : Set (slab F z s t)) ≃ₕ slab F z s t where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := puncturePush F z s t a b hsa hab hbt hleft hright w hw
  left_inv := ⟨(punctureDeformation F z s t a b hsa hab hbt hleft hright w hw).symm⟩
  right_inv := ⟨(deformation F z s t a b hsa hab hbt hleft hright).symm⟩

end NoExoticSixSphere.CylinderFiberSlab.InteriorPush
