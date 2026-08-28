import Wikipedia.SmoothSixDPoincare.ProjectionTransportOnHomotopy
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Smooth frames of projection ranges over compact star-convex regions

Radial contraction gives the projection homotopy. Compact transport constructs
an invertible ambient operator family smooth on a genuine open neighborhood.
Transporting the center fiber yields an injective smooth family with exactly
the required ranges at all points of the region, including its boundary.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Radial contraction constructs smooth ambient range transport over a compact star-convex
region without imposing a manifold structure on that closed region. -/
theorem nonempty_transportOn_starConvex {K U : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x))
    (hs : ContDiffOn ℝ ∞ P U) :
    Nonempty (SmoothRangeTransportOn K (fun _ => P 0) P) := by
  let Q (t : unitInterval) (x : E) := P ((t : ℝ) • x)
  have hQ : ∀ t x, x ∈ K → IsIdempotentElem (Q t x) :=
    fun t x hx => hP _ (hstar.smul_mem hx t.property.1 t.property.2)
  have hmul : Continuous (fun q : unitInterval × K => (q.1 : ℝ) • (q.2 : E)) :=
    (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun q : unitInterval × K => Q q.1 q.2.1) :=
    hs.continuousOn.comp_continuous hmul
      (fun q => hKU (hstar.smul_mem q.2.property q.1.property.1 q.1.property.2))
  have hslice : ∀ t, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ ∞ (Q t) V := by
    intro t
    let V : Set E := (fun x : E => (t : ℝ) • x) ⁻¹' U
    have hV : IsOpen V := hU.preimage (continuous_const.smul continuous_id)
    have hKV : K ⊆ V := fun x hx => hKU (hstar.smul_mem hx t.property.1 t.property.2)
    exact ⟨V, hV, hKV, hs.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => hx)⟩
  have hstart : Q 0 = fun _ => P 0 := by
    funext x
    change P ((0 : ℝ) • x) = P 0
    rw [zero_smul]
  have hend : Q 1 = P := by
    funext x
    change P ((1 : ℝ) • x) = P x
    rw [one_smul]
  simpa only [hstart, hend] using
    nonempty_smoothRangeTransportOn_of_homotopy hK Q hQ hc hslice 0 1

/-- The center projection range gives a fixed frame model for the entire compact region.
The frame is an actual operator-valued function smooth on an open ambient neighborhood. -/
theorem exists_smooth_frame_near_starConvex {K U : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x))
    (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∃ A : E → (P 0).range →L[ℝ] F, ContDiffOn ℝ ∞ A V ∧
        ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨a⟩ := nonempty_transportOn_starConvex hK hstar hU hKU P hP hs
  let A (x : E) : (P 0).range →L[ℝ] F := (a.toFun x).comp (P 0).range.subtypeL
  refine ⟨a.neighborhood, a.open_neighborhood, a.contains, A,
    a.smooth.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨(a.invertible x hx).injective.comp Subtype.val_injective, ?_⟩
  change ((a.toFun x).toLinearMap.comp (P 0).range.subtype).range = (P x).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact a.map_range x hx

variable [FiniteDimensional ℝ E]

/-- In particular a smooth projection family near the actual closed unit disk has a smooth
frame on a neighborhood of that disk, including all its boundary fibers. -/
theorem exists_smooth_frame_near_closedBall {U : Set E} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : E) 1 ⊆ U) (P : E → F →L[ℝ] F)
    (hP : ∀ x ∈ Metric.closedBall (0 : E) 1, IsIdempotentElem (P x))
    (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E, IsOpen V ∧ Metric.closedBall (0 : E) 1 ⊆ V ∧
      ∃ A : E → (P 0).range →L[ℝ] F, ContDiffOn ℝ ∞ A V ∧
        ∀ x ∈ Metric.closedBall (0 : E) 1,
          Function.Injective (A x) ∧ (A x).range = (P x).range :=
  exists_smooth_frame_near_starConvex (isCompact_closedBall 0 1)
    ((convex_closedBall (0 : E) 1).starConvex (Metric.mem_closedBall_self zero_le_one))
    hU hballU P hP hs

end Wikipedia.SmoothSixDPoincare.DiskFraming
