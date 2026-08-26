import ErdosProblems.Erdos633b.TouchingEdgeOrientation

/-! A group-1 tiling has a genuine two-coloring: distinct tiles whose open
edges meet have opposite colors. No edge-to-edge hypothesis is used. -/

namespace Erdos633b.Tiling

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem exists_groupOne_coloring {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) :
    ∃ c : Fin n → ZMod 2, ∀ a b, a ≠ b → ∀ i j p,
      p ∈ (d.tile.move (d.place a)).openEdge j →
      p ∈ (d.tile.move (d.place b)).openEdge i → c a = c b + 1 := by
  obtain ⟨f, hf, ht, _⟩ := d.tile.exists_groupOne_direction_color hrel hirr
  let c (a : Fin n) := f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0)
  have hc (a : Fin n) (j : Fin 3) :
      f ((d.tile.move (d.place a)).positiveEdgeDirection o u j) = c a := by
    apply Triangle.positive_edge_color _ o hu f hf
    intro x k
    simpa only [Triangle.angle_move] using ht x k
  refine ⟨c, fun a b hab i j p hpa hpb => ?_⟩
  have hd : Disjoint (interior (d.tile.move (d.place a)).support)
      (interior (d.tile.move (d.place b)).support) := by
    simpa only [Triangle.support_move] using d.disjoint_interiors hab
  have h := (d.tile.move (d.place a)).touching_positive_edge_color
    (d.tile.move (d.place b)) o hu f hf hd i j hpa hpb
  simpa only [hc] using h

theorem exists_groupOne_proper_coloring {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) :
    ∃ c : Fin n → ZMod 2, ∀ a b, a ≠ b → ∀ i j p,
      p ∈ (d.tile.move (d.place a)).openEdge j →
      p ∈ (d.tile.move (d.place b)).openEdge i → c a ≠ c b := by
  obtain ⟨c, hc⟩ := d.exists_groupOne_coloring o hu hrel hirr
  refine ⟨c, fun a b hab i j p hpa hpb he => ?_⟩
  have h := hc a b hab i j p hpa hpb
  rw [he] at h
  have hz : (0 : ZMod 2) = 1 := add_left_cancel (by simpa only [add_zero] using h)
  exact (by decide : (0 : ZMod 2) ≠ 1) hz

end Erdos633b.Tiling
