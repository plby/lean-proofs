import StackExchange.Puzzling139335.JordanSubarc
import StackExchange.Puzzling139335.Definitions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Connected components cut from a simple arc by a ball

The component containing the center of a positive-radius ball contains a
relative neighborhood in the arc.  This uses the interval topology of an arc,
and does not require differentiability or finite length.
-/

open Set

namespace Puzzling139335.CentralRotation

theorem isClosed_connectedComponentIn_of_isClosed {S : Set Plane}
    (hS : IsClosed S) {z : Plane} (hz : z ∈ S) :
    IsClosed (connectedComponentIn S z) := by
  apply closure_subset_iff_isClosed.mp
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hz))
    (closure_minimal (connectedComponentIn_subset S z) hS)

theorem isCompact_connectedComponentIn_of_isCompact {S : Set Plane}
    (hS : IsCompact S) {z : Plane} (hz : z ∈ S) :
    IsCompact (connectedComponentIn S z) :=
  hS.of_isClosed_subset (isClosed_connectedComponentIn_of_isClosed hS.isClosed hz)
    (connectedComponentIn_subset S z)

/-- The component cut out by a positive-radius ball contains an arc-relative
neighborhood of its center. -/
theorem arc_ball_component_contains_neighborhood {A C : Set Plane} {z : Plane}
    (hA : Schoenflies.IsArc A) (hAC : A ⊆ C) (hz : z ∈ A)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, Metric.ball z ε ∩ A ⊆
      connectedComponentIn (C ∩ Metric.closedBall z r) z := by
  obtain ⟨f, hf, hfi, rfl⟩ := hA
  obtain ⟨a, b, hzU, hUball⟩ := Schoenflies.basic_piece_inside_ball hf hz hr
  have hUconn : IsPreconnected (f '' (Ioo a b ∩ unitInterval)) := by
    apply IsPreconnected.image _ _ (hf.mono inter_subset_right)
    exact ((ordConnected_Ioo : (Ioo a b).OrdConnected).inter ordConnected_Icc).isPreconnected
  have hUsub : f '' (Ioo a b ∩ unitInterval) ⊆ C ∩ Metric.closedBall z r := by
    intro x hx
    exact ⟨hAC (image_mono inter_subset_right hx), Metric.ball_subset_closedBall (hUball hx)⟩
  have hUcomp := hUconn.subset_connectedComponentIn hzU hUsub
  obtain ⟨ε, hε, hεsub⟩ :=
    Schoenflies.exists_ball_inter_subset_image hf hfi isOpen_Ioo hzU
  exact ⟨ε, hε, hεsub.trans hUcomp⟩

/-- A small closed ball meets the Jordan curve only in the overlap of two
subarcs, provided its center is internal to each. -/
theorem exists_closedBall_inter_subset_arc_overlap {C A B : Set Plane}
    {p q u v z : Plane} (hC : Schoenflies.IsJordanCurve C)
    (hA : Schoenflies.IsArcBetween A p q) (hB : Schoenflies.IsArcBetween B u v)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hzA : z ∈ A \ {p, q})
    (hzB : z ∈ B \ {u, v}) :
    ∃ r > 0, C ∩ Metric.closedBall z r ⊆ A ∩ B := by
  obtain ⟨rA, hrA, hballA⟩ := hC.exists_ball_inter_subset_arc hA hAC hzA
  obtain ⟨rB, hrB, hballB⟩ := hC.exists_ball_inter_subset_arc hB hBC hzB
  refine ⟨min rA rB / 2, by positivity, ?_⟩
  rintro x ⟨hxC, hxball⟩
  have hrA' : min rA rB / 2 < rA := by
    have := min_le_left rA rB
    linarith
  have hrB' : min rA rB / 2 < rB := by
    have := min_le_right rA rB
    linarith
  have hxdist := Metric.mem_closedBall.mp hxball
  exact ⟨hballA ⟨Metric.mem_ball.mpr (hxdist.trans_lt hrA'), hxC⟩,
    hballB ⟨Metric.mem_ball.mpr (hxdist.trans_lt hrB'), hxC⟩⟩

/-- If an isometry matches the two local arcs and fixes the center, the entire
small curve-and-ball intersection is invariant. -/
theorem affineIsometry_image_curve_inter_closedBall {C A B : Set Plane}
    {z : Plane} {r : ℝ} (k : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hmap : k '' A = B) (hfix : k z = z)
    (hsmall : C ∩ Metric.closedBall z r ⊆ A ∩ B) :
    k '' (C ∩ Metric.closedBall z r) = C ∩ Metric.closedBall z r := by
  have hdist (x : Plane) : dist (k x) z = dist x z := by
    calc
      dist (k x) z = dist (k x) (k z) := by rw [hfix]
      _ = dist x z := k.isometry.dist_eq x z
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hBC ?_, ?_⟩
    · rw [← hmap]
      exact mem_image_of_mem k (hsmall hx).1
    · simpa only [Metric.mem_closedBall, hdist] using hx.2
  · intro x hx
    obtain ⟨y, hyA, hyx⟩ : x ∈ k '' A := hmap ▸ (hsmall hx).2
    refine ⟨y, ⟨hAC hyA, ?_⟩, hyx⟩
    have hyball : k y ∈ Metric.closedBall z r := hyx.symm ▸ hx.2
    simpa only [Metric.mem_closedBall, hdist] using hyball

/-- The fixed-point component is compact, connected, invariant, and contains a
relative neighborhood in the source arc. -/
theorem exists_invariant_arc_component {C A B : Set Plane} {p q u v z : Plane}
    (hC : Schoenflies.IsJordanCurve C) (hA : Schoenflies.IsArcBetween A p q)
    (hB : Schoenflies.IsArcBetween B u v) (hAC : A ⊆ C) (hBC : B ⊆ C)
    (k : Plane ≃ᵃⁱ[ℝ] Plane) (hmap : k '' A = B) (hzA : z ∈ A \ {p, q})
    (hzB : z ∈ B \ {u, v}) (hfix : k z = z) :
    ∃ E, IsCompact E ∧ IsConnected E ∧ E ⊆ A ∩ B ∧
      (∃ ε > 0, Metric.ball z ε ∩ A ⊆ E) ∧ k '' E = E := by
  obtain ⟨r, hr, hsmall⟩ :=
    exists_closedBall_inter_subset_arc_overlap hC hA hB hAC hBC hzA hzB
  let S := C ∩ Metric.closedBall z r
  have hzS : z ∈ S := ⟨hAC hzA.1, Metric.mem_closedBall_self hr.le⟩
  have hcompactS : IsCompact S := hC.isCompact.inter_right Metric.isClosed_closedBall
  have hmapS : k '' S = S :=
    affineIsometry_image_curve_inter_closedBall k hAC hBC hmap hfix hsmall
  refine ⟨connectedComponentIn S z,
    isCompact_connectedComponentIn_of_isCompact hcompactS hzS,
    isConnected_connectedComponentIn_iff.mpr hzS,
    (connectedComponentIn_subset S z).trans hsmall,
    arc_ball_component_contains_neighborhood hA.isArc hAC hzA.1 hr, ?_⟩
  simpa only [AffineIsometryEquiv.coe_toHomeomorph, hmapS, hfix] using
    k.toHomeomorph.image_connectedComponentIn hzS

end Puzzling139335.CentralRotation
