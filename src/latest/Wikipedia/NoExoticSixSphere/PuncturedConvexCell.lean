import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

/-!
# Boundary-fixing radial deformation of a punctured convex cell

The cell is a closed bounded convex neighborhood of the origin, not
necessarily a Euclidean ball. Its Minkowski gauge gives the actual radial
retraction onto its frontier. Positive interpolation avoids the puncture
and fixes every boundary point throughout the homotopy.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.PuncturedConvexCell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Space (s : Set E) := {x : E // x ∈ s ∧ x ≠ 0}

variable (s : Set E) (hc : Convex ℝ s) (hs : IsClosed s)
  (h0 : s ∈ 𝓝 (0 : E)) (hb : Bornology.IsVonNBounded ℝ s)

def radial (x : E) : E := (gauge s x)⁻¹ • x

include h0 hb in
theorem gauge_positive {x : E} (hx : x ≠ 0) : 0 < gauge s x :=
  (gauge_pos (absorbent_nhds_zero h0) hb).mpr hx

include hc h0 hb in
theorem radial_mem_frontier {x : E} (hx : x ≠ 0) : radial s x ∈ frontier s := by
  apply (gauge_eq_one_iff_mem_frontier hc h0).mp
  have hg := gauge_positive s h0 hb hx
  simp only [radial, gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul,
    inv_mul_cancel₀ hg.ne']

include hc h0 in
theorem radial_of_mem_frontier {x : E} (hx : x ∈ frontier s) : radial s x = x := by
  simp only [radial, (gauge_eq_one_iff_mem_frontier hc h0).mpr hx, inv_one, one_smul]

include h0 in
theorem frontier_ne_zero {x : E} (hx : x ∈ frontier s) : x ≠ 0 := by
  intro he
  subst x
  exact hx.2 (mem_interior_iff_mem_nhds.mpr h0)

def inclusion : C(frontier s, Space s) :=
  ⟨fun x ↦ ⟨x.val, (by simpa only [hs.closure_eq] using x.property.1),
      frontier_ne_zero s h0 x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def retraction : C(Space s, frontier s) :=
  ⟨fun x ↦ ⟨radial s x.val, radial_mem_frontier s hc h0 hb x.property.2⟩,
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀
      (fun x ↦ (gauge_positive s h0 hb x.property.2).ne')).smul
        continuous_subtype_val |>.subtype_mk _⟩

theorem retraction_inclusion (x : frontier s) :
    retraction s hc h0 hb (inclusion s hs h0 x) = x := by
  exact Subtype.ext (radial_of_mem_frontier s hc h0 x.property)

def blendVector (q : I × Space s) : E :=
  (1 - (q.1 : ℝ)) • q.2.val + (q.1 : ℝ) • radial s q.2.val

include hc h0 hb in
theorem continuous_blendVector : Continuous (blendVector s) := by
  have ht : Continuous (fun q : I × Space s ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun q : I × Space s ↦ q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hr : Continuous (fun q : I × Space s ↦ radial s q.2.val) :=
    (((continuous_gauge hc h0).comp hx).inv₀
      (fun q ↦ (gauge_positive s h0 hb q.2.property.2).ne')).smul hx
  exact ((continuous_const.sub ht).smul hx).add (ht.smul hr)

include hc hs h0 hb in
theorem blendVector_mem (q : I × Space s) : blendVector s q ∈ s := by
  have hr : radial s q.2.val ∈ s :=
    by simpa only [hs.closure_eq] using (radial_mem_frontier s hc h0 hb q.2.property.2).1
  exact hc q.2.property.1 hr (sub_nonneg.mpr q.1.property.2) q.1.property.1
    (sub_add_cancel 1 (q.1 : ℝ))

include h0 hb in
theorem blendVector_ne_zero (q : I × Space s) : blendVector s q ≠ 0 := by
  have hg := gauge_positive s h0 hb q.2.property.2
  have hp : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (gauge s q.2.val)⁻¹ := by
    have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ))
      (by norm_num : (1 : ℝ) ∈ Ioi 0) (inv_pos.mpr hg)
      (sub_nonneg.mpr q.1.property.2) q.1.property.1
      (sub_add_cancel 1 (q.1 : ℝ))
    simpa only [mem_Ioi, smul_eq_mul, mul_one] using h
  simpa only [blendVector, radial, smul_smul, ← add_smul] using
    smul_ne_zero hp.ne' q.2.property.2

def deformation : (ContinuousMap.id (Space s)).Homotopy
    ((inclusion s hs h0).comp (retraction s hc h0 hb)) where
  toFun q := ⟨blendVector s q, blendVector_mem s hc hs h0 hb q,
    blendVector_ne_zero s h0 hb q⟩
  continuous_toFun := (continuous_blendVector s hc h0 hb).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left x := by
    apply Subtype.ext
    change blendVector s (1, x) = radial s x.val
    simp [blendVector]

theorem deformation_fixed (t : I) (x : Space s) (hx : x.val ∈ frontier s) :
    deformation s hc hs h0 hb (t, x) = x := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • x.val + (t : ℝ) • radial s x.val = x.val
  rw [radial_of_mem_frontier s hc h0 hx, ← add_smul, sub_add_cancel, one_smul]

def deformationRel : (ContinuousMap.id (Space s)).HomotopyRel
    ((inclusion s hs h0).comp (retraction s hc h0 hb)) (Set.range (inclusion s hs h0)) :=
  ⟨deformation s hc hs h0 hb, by
    rintro t x ⟨y, rfl⟩
    exact deformation_fixed s hc hs h0 hb t _ y.property⟩

end NoExoticSixSphere.PuncturedConvexCell
