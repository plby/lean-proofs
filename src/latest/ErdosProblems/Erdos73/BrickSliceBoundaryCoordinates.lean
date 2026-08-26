import ErdosProblems.Erdos73.BrickColumnSlice
import ErdosProblems.Erdos73.SubdivisionBoundary
import ErdosProblems.Erdos73.BlockBoundaryPaths

/-! A horizontally interior slice branch retains every original pattern neighbor. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

theorem rawBrickWall_adj_numeric {c r : ℕ} {x y : Fin r × Fin (2 * c)}
    (hxy : (rawBrickWall c r).Adj x y) :
    (x.1.val = y.1.val ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.2.val = y.2.val ∧
        ((x.1.val + 1 = y.1.val ∧ (x.2.val + x.1.val) % 2 = 1) ∨
          (y.1.val + 1 = x.1.val ∧ (y.2.val + y.1.val) % 2 = 1))) := by
  rcases hxy with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · exact Or.inl ⟨congrArg Fin.val hr, pathGraph_adj.mp hc⟩
  · exact Or.inr ⟨congrArg Fin.val hc, hr⟩

theorem brickColumnSliceCopy_lifts_interior_neighbors {c r : ℕ}
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (u : ElementaryWallVertex (d + 1) r)
    (hleft : 1 < u.val.2.val) (hright : u.val.2.val + 2 < 2 * (d + 1))
    (z : ElementaryWallVertex c r)
    (huz : (elementaryWall c r).Adj (brickColumnSliceCopy a d hc u) z) :
    ∃ v : ElementaryWallVertex (d + 1) r,
      (elementaryWall (d + 1) r).Adj u v ∧ brickColumnSliceCopy a d hc v = z := by
  have hn := rawBrickWall_adj_numeric huz
  change ((2 * 0 + u.val.1.val = z.val.1.val ∧
      (2 * a + u.val.2.val + 1 = z.val.2.val ∨
        z.val.2.val + 1 = 2 * a + u.val.2.val)) ∨
      (2 * a + u.val.2.val = z.val.2.val ∧
        ((2 * 0 + u.val.1.val + 1 = z.val.1.val ∧
          (2 * a + u.val.2.val + (2 * 0 + u.val.1.val)) % 2 = 1) ∨
          (z.val.1.val + 1 = 2 * 0 + u.val.1.val ∧
            (z.val.2.val + z.val.1.val) % 2 = 1)))) at hn
  simp only [Nat.mul_zero, Nat.zero_add] at hn
  have hzlo : 2 * a < z.val.2.val := by omega
  have hzhi : z.val.2.val + 1 < 2 * a + 2 * (d + 1) := by omega
  let w : Fin r × Fin (2 * (d + 1)) :=
    (z.val.1, ⟨z.val.2.val - 2 * a, by omega⟩)
  let v : ElementaryWallVertex (d + 1) r := ⟨w,
    rawBrickWall_degree_ge_two_of_interior w (by change 0 < z.val.2.val - 2 * a; omega)
      (by change z.val.2.val - 2 * a + 1 < 2 * (d + 1); omega)⟩
  refine ⟨v, ?_, ?_⟩
  · rcases hn with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
    · refine Or.inl ⟨Fin.ext hrow, pathGraph_adj.mpr ?_⟩
      change u.val.2.val + 1 = z.val.2.val - 2 * a ∨
        z.val.2.val - 2 * a + 1 = u.val.2.val
      omega
    · refine Or.inr ⟨Fin.ext (by change u.val.2.val = z.val.2.val - 2 * a; omega), ?_⟩
      change ((u.val.1.val + 1 = z.val.1.val ∧ (u.val.2.val + u.val.1.val) % 2 = 1) ∨
        (z.val.1.val + 1 = u.val.1.val ∧
          (z.val.2.val - 2 * a + z.val.1.val) % 2 = 1))
      omega
  · apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change 2 * 0 + z.val.1.val = z.val.1.val
      omega
    · apply Fin.ext
      change 2 * a + (z.val.2.val - 2 * a) = z.val.2.val
      omega

theorem brickColumnSlice_boundary_column {V : Type*} {G : SimpleGraph V} {c r : ℕ}
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (u : ElementaryWallVertex (d + 1) r)
    (hu : (S.restrictCopy (brickColumnSliceCopy a d hc)).branchVertex u ∈
      internalVertexBoundary S.actualEdgeGraph
        (S.restrictCopy (brickColumnSliceCopy a d hc)).vertexSet) :
    u.val.2.val ≤ 1 ∨ 2 * d ≤ u.val.2.val := by
  by_contra hn
  have hlo : 1 < u.val.2.val := by omega
  have hhi : u.val.2.val + 2 < 2 * (d + 1) := by omega
  obtain ⟨_, y, hy, hxy⟩ := mem_filter.mp hu
  apply hy
  exact S.neighbor_mem_restrictCopy_of_lifted_pattern_neighbors (brickColumnSliceCopy a d hc) u
    (brickColumnSliceCopy_lifts_interior_neighbors a d hc u hlo hhi) hxy

end
end Erdos73
