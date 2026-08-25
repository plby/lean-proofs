import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry.VerticalIntervals
import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry.TopIntervals

/-!
# Side geometry derived from the actual reflected-singleton configuration

The record below packages conclusions of the side partition theorems.  Its
existence is proved from actual corner incidences, placement identities, and
the two singleton contact hypotheses for the cornerless piece.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

/-- Exact side contacts and actual source endpoints in the normalized case. -/
structure SideContactGeometry (d : SquareDissection) (θ u v l T : ℝ) : Prop where
  l_bounds : l ∈ Ioo (0 : ℝ) (1 / 2)
  T_bounds : T ∈ Ioo (0 : ℝ) (1 / 2)
  vertical : VerticalContactIntervals d l
  top_left : ∀ x ∈ Icc (0 : ℝ) 1,
    ((!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T)
  top_right : ∀ x ∈ Icc (0 : ℝ) 1,
    ((!₂[x, 1] : Plane) ∈ d.piece 1 ↔ 1 - T ≤ x)
  top_middle : ∀ x ∈ Icc (0 : ℝ) 1,
    ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T)
  source_left_endpoint : (!₂[0, l] : Plane) ∈ d.piece 0
  source_right_endpoint : (!₂[1, l] : Plane) ∈ d.piece 0
  incoming_endpoint : incomingEnd θ u v (1 - l) ∈ d.piece 0
  outgoing_endpoint : outgoingEnd θ u v T ∈ d.piece 0
  middle_left_endpoint : (!₂[T, 1] : Plane) ∈ d.piece 3
  middle_right_endpoint : (!₂[1 - T, 1] : Plane) ∈ d.piece 3

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

/-- All side intervals and arm endpoints are consequences of the geometric
configuration.  No protected-center hypothesis is needed for this step. -/
theorem exists_side_geometry (h : SourceData d θ u v) (hcfg : Configuration d)
    (hDl : (d.piece 3 ∩ {p : Plane | p 0 = 0}).Subsingleton)
    (hDr : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton) :
    ∃ l T : ℝ, SideContactGeometry d θ u v l T := by
  obtain ⟨l, hl, hvert, hL, hR, hE⟩ := h.exists_vertical_geometry hcfg hDl hDr
  obtain ⟨T, hT, htop, hDL, hDR, hF⟩ := h.exists_top_geometry hcfg
  exact ⟨l, T, {
    l_bounds := hl
    T_bounds := hT
    vertical := hvert
    top_left := fun x hx => (htop x hx).1
    top_right := fun x hx => (htop x hx).2.1
    top_middle := fun x hx => (htop x hx).2.2
    source_left_endpoint := hL
    source_right_endpoint := hR
    incoming_endpoint := hE
    outgoing_endpoint := hF
    middle_left_endpoint := hDL
    middle_right_endpoint := hDR }⟩

/-- The incoming source support line meets the source in exactly the arm
of length `1-l`, including both endpoints. -/
theorem incomingEnd_mem_iff (h : SourceData d θ u v) {l T R : ℝ}
    (g : SideContactGeometry d θ u v l T) :
    incomingEnd θ u v R ∈ d.piece 0 ↔ 0 ≤ R ∧ R ≤ 1 - l := by
  rw [← h.rightMap_mem_iff, rightMap_incomingEnd]
  constructor
  · intro hp
    have hs := d.piece_subset 1 hp
    have hI : 1 - R ∈ Icc (0 : ℝ) 1 := hs.2
    have hl := (g.vertical.right_singleton (1 - R) hI).mp hp
    exact ⟨by linarith [hI.2], by linarith⟩
  · rintro ⟨hR0, hRl⟩
    have hI : 1 - R ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [g.l_bounds.1], by linarith⟩
    exact (g.vertical.right_singleton (1 - R) hI).mpr (by linarith)

/-- The outgoing source support line meets the source in exactly the arm
of length `T`, including both endpoints. -/
theorem outgoingEnd_mem_iff (h : SourceData d θ u v) {l T R : ℝ}
    (g : SideContactGeometry d θ u v l T) :
    outgoingEnd θ u v R ∈ d.piece 0 ↔ 0 ≤ R ∧ R ≤ T := by
  rw [← h.rightMap_mem_iff, rightMap_outgoingEnd]
  constructor
  · intro hp
    have hs := d.piece_subset 1 hp
    have hI : 1 - R ∈ Icc (0 : ℝ) 1 := hs.1
    have hT := (g.top_right (1 - R) hI).mp hp
    exact ⟨by linarith [hI.2], by linarith⟩
  · rintro ⟨hR0, hRT⟩
    have hI : 1 - R ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [g.T_bounds.2], by linarith⟩
    exact (g.top_right (1 - R) hI).mpr (by linarith)

end SourceData

end Puzzling139335.N4TwoOneOne
