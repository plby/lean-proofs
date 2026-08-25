import Wikipedia.SchoenfliesTheorem.ModelCurve
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.Interval.Set.Infinite

/-!
# Spokes in a punctured model square

Three distinct points of the model square's boundary can be joined to a common
interior point by straight segments which avoid the origin.  The hub is chosen
on a horizontal line away from the three forbidden lines through the origin.
-/

open Set

namespace Schoenflies

private theorem convex_frontier_segments_inter_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x y z : E} (hS : Convex ℝ S)
    (hx : x ∈ interior S) (hy : y ∈ frontier S) (hz : z ∈ frontier S)
    (hyz : y ≠ z) : segment ℝ x y ∩ segment ℝ x z = {x} := by
  apply Subset.antisymm
  · rintro w ⟨hwy, hwz⟩
    apply mem_singleton_iff.mpr
    by_contra hwx
    have hxy : x ≠ y := fun h => hy.2 (h ▸ hx)
    have hxz : x ≠ z := fun h => hz.2 (h ▸ hx)
    have hray : SameRay ℝ (y -ᵥ x) (z -ᵥ x) :=
      (mem_segment_iff_wbtw.mp hwy).sameRay_vsub_left.symm.trans
        (mem_segment_iff_wbtw.mp hwz).sameRay_vsub_left
        (fun h => False.elim (hwx (vsub_eq_zero_iff_eq.mp h)))
    rcases wbtw_total_of_sameRay_vsub_left hray with hybtw | hzbtw
    · exact hy.2 (hS.openSegment_interior_closure_subset_interior hx hz.1
        (mem_openSegment_of_ne_left_right hxy hyz.symm hybtw.mem_segment))
    · exact hz.2 (hS.openSegment_interior_closure_subset_interior hx hy.1
        (mem_openSegment_of_ne_left_right hxz hyz hzbtw.mem_segment))
  · exact singleton_subset_iff.mpr
      ⟨left_mem_segment ℝ x y, left_mem_segment ℝ x z⟩

private theorem exists_model_hub_parameter (b : Fin 3 → Plane)
    (hb : ∀ i, b i ∈ modelCurve) :
    ∃ t ∈ Ioo (-1 : ℝ) 1, ∀ i, 2 * t * b i 1 ≠ b i 0 := by
  obtain ⟨t, ht, havoid⟩ :=
    (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).exists_notMem_finite
      (Set.finite_range (fun i : Fin 3 => b i 0 / (2 * b i 1)))
  refine ⟨t, ht, ?_⟩
  intro i heq
  by_cases hi : b i 1 = 0
  · have hi0 : b i 0 = 0 := by simpa only [hi, mul_zero] using heq.symm
    have hframe : max |b i 0| |b i 1| = 1 := hb i
    norm_num [hi0, hi] at hframe
  · apply havoid
    refine ⟨i, (div_eq_iff (mul_ne_zero (by norm_num) hi)).mpr ?_⟩
    nlinarith [heq]

private theorem model_spoke_avoids_zero {t : ℝ} {b : Plane}
    (hdet : 2 * t * b 1 ≠ b 0) :
    (0 : Plane) ∉ segment ℝ !₂[t, (1 / 2 : ℝ)] b := by
  intro hzero
  rw [segment_eq_image' ℝ] at hzero
  obtain ⟨a, _, ha⟩ := hzero
  have h0 := congrArg (fun z : Plane => z 0) ha
  have h1 := congrArg (fun z : Plane => z 1) ha
  change t + a * (b 0 - t) = 0 at h0
  change (1 / 2 : ℝ) + a * (b 1 - 1 / 2) = 0 at h1
  have ha0 : a ≠ 0 := by
    intro heq
    norm_num [heq] at h1
  have hscaled := congrArg (fun z : ℝ => 2 * t * z) h1
  have heq : a * (2 * t * b 1) = a * b 0 := by nlinarith [hscaled]
  exact hdet (mul_left_cancel₀ ha0 heq)

private theorem model_spoke_sdiff_subset {x b : Plane}
    (hx : x ∈ Plane.openSquare 0 1) (hb : b ∈ modelCurve) :
    segment ℝ x b \ {b} ⊆ Plane.openSquare 0 1 := by
  intro z hz
  have hzb : z ≠ b := by simpa only [mem_singleton_iff] using hz.2
  rcases eq_or_ne z x with rfl | hzx
  · exact hx
  · rw [← interior_closedSquare_zero_one] at hx ⊢
    exact (Plane.convex_closedSquare 0 1).openSegment_interior_self_subset_interior
      hx (modelCurve_subset_closedSquare hb)
      (mem_openSegment_of_ne_left_right hzx.symm hzb.symm hz.1)

/-- Three distinct boundary points of the model square admit disjoint spokes
from a common interior point, with every spoke avoiding the origin. -/
theorem exists_modelSquare_punctured_spokes (b : Fin 3 → Plane)
    (hb : ∀ i, b i ∈ modelCurve) (hinj : Function.Injective b) :
    ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∈ Plane.openSquare 0 1 ∧ x ≠ 0 ∧
      (∀ i, IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ Plane.openSquare 0 1) ∧
      (∀ i, 0 ∉ A i) ∧ ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  obtain ⟨t, ht, hdet⟩ := exists_model_hub_parameter b hb
  let x : Plane := !₂[t, (1 / 2 : ℝ)]
  have hx : x ∈ Plane.openSquare 0 1 := by
    rw [mem_openSquare_zero_one]
    change max |t| |(1 / 2 : ℝ)| < 1
    exact max_lt (abs_lt.mpr ht) (by norm_num)
  have hx0 : x ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : Plane => z 1) h
    change (1 / 2 : ℝ) = 0 at h1
    norm_num at h1
  have hxint : x ∈ interior (Plane.closedSquare 0 1) := by
    rwa [interior_closedSquare_zero_one]
  have hxb (i : Fin 3) : x ≠ b i := by
    intro h
    exact notMem_interior_closedSquare (hb i) (h ▸ hxint)
  refine ⟨x, fun i => segment ℝ x (b i), hx, hx0,
    fun i => isArcBetween_segment (hxb i),
    fun i => model_spoke_sdiff_subset hx (hb i),
    fun i => model_spoke_avoids_zero (hdet i), ?_⟩
  intro i j hij
  exact convex_frontier_segments_inter_singleton (Plane.convex_closedSquare 0 1)
    hxint (modelCurve_eq_frontier ▸ hb i) (modelCurve_eq_frontier ▸ hb j)
    (fun h => hij (hinj h))

end Schoenflies
