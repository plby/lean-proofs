import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBasins
import Mathlib.Topology.GDelta.Basic

/-!
# Compact stable-plane pieces are nowhere dense at positive Morse index

A compact coordinate set with empty interior remains nowhere dense under
the inverse native chart. The positive-coordinate plane has empty interior
when the negative-coordinate space is nontrivial.
-/

noncomputable section

open Set Metric Function Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem compact_partial_chart_image_nowhereDense {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X A) {K : Set A} (hK : IsCompact K)
    (hKt : K ⊆ e.target) (hKi : interior K = ∅) : IsNowhereDense (e.symm '' K) := by
  have hclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)).isClosed
  apply hclosed.isNowhereDense_iff.mpr
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  have hopen : IsOpen (e '' interior (e.symm '' K)) :=
    e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsource)
  have hsub : e '' interior (e.symm '' K) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := interior_subset hx
    rw [← hzx, e.right_inv (hKt hz)]
    exact hz
  have hinto : e '' interior (e.symm '' K) ⊆ interior K := hopen.subset_interior_iff.mpr hsub
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hinto (mem_image_of_mem e hx)
  exact (Set.eq_empty_iff_forall_notMem.mp hKi) _ hh

theorem interior_zero_product_empty {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Nontrivial A] [TopologicalSpace B] (s : Set B) :
    interior (({0} : Set A) ×ˢ s) = ∅ := by
  rw [interior_prod_eq, interior_singleton, empty_prod]

theorem native_positive_plane_piece_nowhereDense {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)
    (hindex : 0 < Module.finrank ℝ c.NegativeCoordinates) {r : ℝ}
    (hblock : ({0} : Set c.NegativeCoordinates) ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
      c.splitChart.target) :
    IsNowhereDense (c.splitChart.symm ''
      (({0} : Set c.NegativeCoordinates) ×ˢ closedBall (0 : c.PositiveCoordinates) r)) := by
  let : Nontrivial c.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  exact compact_partial_chart_image_nowhereDense c.splitChart.toOpenPartialHomeomorph
    (isCompact_singleton.prod (isCompact_closedBall _ _)) hblock (interior_zero_product_empty _)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
