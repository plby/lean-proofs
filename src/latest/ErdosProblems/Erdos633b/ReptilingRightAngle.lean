import ErdosProblems.Erdos633b.BoundaryStarAngles
import ErdosProblems.Erdos633b.BoundaryVertexCollision

/-! The reference triangle of every scalene ordered nonsquare reptiling is
right-angled. The two largest corners and their straight-angle sum are proved geometrically. -/

namespace Erdos633b.Tiling

theorem right_of_two_largest_boundary_vertices {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i)
    (a b : Fin n) (hab : a ≠ b)
    (ha : d.place a (d.tile.points 2) = p) (hb : d.place b (d.tile.points 2) = p)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    d.tile.angle 2 = Real.pi / 2 := by
  classical
  let e : d.VertexPiece p := ⟨(a, 2), ha⟩
  let f : d.VertexPiece p := ⟨(b, 2), hb⟩
  have hef : e ≠ f := by intro h; exact hab (congrArg (fun g : d.VertexPiece p => g.val.1) h)
  have hsum := d.boundary_vertex_angle_sum i hp a 2 ha
  have hmin (j : Fin 3) : d.tile.angle 0 ≤ d.tile.angle j := by
    fin_cases j
    · exact le_rfl
    · exact h01.le
    · exact (h01.trans h12).le
  have hall (g : d.VertexPiece p) : g = e ∨ g = f := by
    by_contra hn
    push Not at hn
    have hge : g ≠ e := hn.1
    have hgf : g ≠ f := hn.2
    have hbound : d.tile.angle 2 + d.tile.angle 2 + d.tile.angle g.val.2 ≤ Real.pi := by
      calc
        _ = ∑ x ∈ ({e, f, g} : Finset (d.VertexPiece p)), d.tile.angle x.val.2 := by
          have hefg : e ∉ ({f, g} : Finset (d.VertexPiece p)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hef, hge.symm⟩
          rw [Finset.sum_insert hefg, Finset.sum_pair hgf.symm]
          change d.tile.angle 2 + d.tile.angle 2 + d.tile.angle g.val.2 =
            d.tile.angle 2 + (d.tile.angle 2 + d.tile.angle g.val.2)
          ring
        _ ≤ ∑ x : d.VertexPiece p, d.tile.angle x.val.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => (d.tile.angle_pos x.val.2).le)
        _ = Real.pi := hsum
    have hm := hmin g.val.2
    have hs := d.tile.angle_sum
    linarith
  have hset : (Finset.univ : Finset (d.VertexPiece p)) = {e, f} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall g
  rw [hset, Finset.sum_pair hef] at hsum
  change d.tile.angle 2 + d.tile.angle 2 = Real.pi at hsum
  linarith

theorem reptiling_right_angle {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    d.tile.angle 2 = Real.pi / 2 := by
  obtain ⟨a, b, hab, p, hp, ha, hb⟩ := d.reptiling_two_largest_vertices hn h h01 h12
  exact d.right_of_two_largest_boundary_vertices 2 hp a b hab ha hb h01 h12

end Erdos633b.Tiling
