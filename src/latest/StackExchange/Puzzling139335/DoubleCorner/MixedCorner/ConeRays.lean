import StackExchange.Puzzling139335.AcuteCorner.Defs
import StackExchange.Puzzling139335.BoundaryGerm

/-!
# Actual straight rays of an isometric forty-five-degree cone

The source cone contains its horizontal boundary ray.  An affine isometry
transports this actual segment to the frontier of the image cone; no
polygonality assumption on any dissection piece is involved.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner.MixedCorner

open AcuteCorner

theorem isClosed_cone45 : IsClosed cone45 :=
  (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).inter
    (isClosed_le (EuclideanSpace.proj 1).continuous (EuclideanSpace.proj 0).continuous)

theorem zero_mem_cone45 : (0 : Plane) ∈ cone45 := by
  exact ⟨le_rfl, le_rfl⟩

/-- A point on the nonnegative horizontal ray belongs to the cone frontier. -/
theorem horizontal_mem_frontier_cone45 {p : Plane} (hp0 : 0 ≤ p 0)
    (hp1 : p 1 = 0) : p ∈ frontier cone45 := by
  have hp : p ∈ cone45 := by
    change 0 ≤ p 1 ∧ p 1 ≤ p 0
    rw [hp1]
    exact ⟨le_rfl, hp0⟩
  apply (mem_frontier_iff_notMem_interior hp).mpr
  intro hpi
  let f : ℝ → Plane := fun t => !₂[p 0, t]
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hopen : IsOpen (f ⁻¹' interior cone45) := isOpen_interior.preimage hf
  have hsub : f ⁻¹' interior cone45 ⊆ Ici (0 : ℝ) := by
    intro t ht
    exact (interior_subset ht).1
  have hf0 : f 0 = p := by
    ext k
    fin_cases k
    · rfl
    · exact hp1.symm
  have hzero : (0 : ℝ) ∈ f ⁻¹' interior cone45 := by
    change f 0 ∈ interior cone45
    rwa [hf0]
  have hzero' := (hopen.subset_interior_iff.mpr hsub) hzero
  simpa only [interior_Ici, mem_Ioi, lt_self_iff_false] using hzero'

theorem horizontal_segment_subset_frontier_cone45 :
    segment ℝ (0 : Plane) (corner 1) ⊆ frontier cone45 := by
  rintro p ⟨a, b, _ha, hb, _hab, rfl⟩
  apply horizontal_mem_frontier_cone45
  · simpa [corner, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hb
  · simp [corner, PiLp.smul_apply, smul_eq_mul]

theorem isStraightAt_frontier_cone45 : IsStraightAt (frontier cone45) 0 := by
  refine ⟨corner 1, ?_, horizontal_segment_subset_frontier_cone45⟩
  intro h
  have h0 := congrArg (fun p : Plane => p 0) h
  norm_num [corner] at h0

/-- Every isometric image of the cone fixing the origin has an actual
nondegenerate straight initial segment in its frontier there. -/
theorem isStraightAt_frontier_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he0 : e 0 = 0) : IsStraightAt (frontier (e '' cone45)) 0 := by
  have h := isStraightAt_frontier_cone45.image_affineIsometry e
  have hf : e '' frontier cone45 = frontier (e '' cone45) :=
    e.toHomeomorph.image_frontier cone45
  rwa [hf, he0] at h

/-- The frontier segment can be chosen inside any prescribed positive ball. -/
theorem exists_frontier_segment_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he0 : e 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ a : Plane, a ≠ 0 ∧ segment ℝ 0 a ⊆ frontier (e '' cone45) ∩ ball 0 r := by
  obtain ⟨w, hw, hseg⟩ := isStraightAt_frontier_image_cone45 e he0
  obtain ⟨a, ha, hasub⟩ := exists_initial_segment_subset_ball hw hr
  exact ⟨a, ha, fun p hp => ⟨hseg (hasub hp).1, (hasub hp).2⟩⟩

theorem isClosed_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    IsClosed (e '' cone45) := e.toHomeomorph.isClosedMap cone45 isClosed_cone45

theorem zero_mem_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) :
    (0 : Plane) ∈ e '' cone45 := ⟨0, zero_mem_cone45, he0⟩

end Puzzling139335.DoubleCorner.MixedCorner
