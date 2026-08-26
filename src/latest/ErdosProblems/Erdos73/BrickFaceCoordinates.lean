import ErdosProblems.Erdos73.BrickFullVertexCoverage

/-! Coordinate forms of face copies and the row/column choices for horizontal edges. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

def brickFaceCopyAt {c r : ℕ} (i : Fin (r - 1) × Fin (c - 1)) :
    (cycleGraph 6).Copy (elementaryWall c r) :=
  elementaryBrickFaceCopy i.1.val (brickFaceColumn i.1.val i.2.val)
    (by have hi := i.1.isLt; omega)
    (by have hi := i.2.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega)

theorem brickFaceCopyAt_eq_of_coordinates {c r : ℕ}
    (a : Fin (r - 1)) (j : Fin (c - 1)) (l : Fin 6) (x : ElementaryWallVertex c r)
    (hrow : a.val + (brickFacePosition l).1 = x.val.1.val)
    (hcol : brickFaceColumn a.val j.val + (brickFacePosition l).2 = x.val.2.val) :
    brickFaceCopyAt (a, j) l = x := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext hrow) (Fin.ext hcol)

theorem brickFacePosition_horizontal_adj : ∀ i j : Fin 6,
    (brickFacePosition i).1 = (brickFacePosition j).1 →
    (brickFacePosition i).2 + 1 = (brickFacePosition j).2 → (cycleGraph 6).Adj i j := by decide

theorem brickFacePosition_vertical_adj : ∀ i j : Fin 6,
    (brickFacePosition i).1 = 0 → (brickFacePosition j).1 = 1 →
    (brickFacePosition i).2 = (brickFacePosition j).2 →
    (brickFacePosition i).2 % 2 = 0 → (cycleGraph 6).Adj i j := by decide

theorem exists_faceColumn_cover_horizontal {c q x : ℕ}
    (hlo : q ≤ x) (hhi : x + 1 ≤ 2 * (c - 1) + q) :
    ∃ j : Fin (c - 1), ∃ e : Fin 2, x = 2 * j.val + q + e.val := by
  refine ⟨⟨(x - q) / 2, by omega⟩, ⟨(x - q) % 2, by omega⟩, ?_⟩
  dsimp only
  omega

theorem exists_faceRow_cover_horizontal {c r : ℕ} (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x y : ElementaryWallVertex c r) (hrow : x.val.1 = y.val.1)
    (hcol : x.val.2.val + 1 = y.val.2.val) :
    ∃ a : Fin (r - 1), ∃ d : Fin 2,
      x.val.1.val = a.val + d.val ∧
      (a.val + 1) % 2 ≤ x.val.2.val ∧ y.val.2.val ≤ 2 * (c - 1) + (a.val + 1) % 2 := by
  by_cases hx : x.val.2.val = 0
  · obtain ⟨a, d, ha, hp⟩ := boundary_vertex_has_vertical_face_row x (Or.inl hx)
    exact ⟨a, d, ha, by omega, by omega⟩
  · by_cases hy : y.val.2.val + 1 = 2 * c
    · obtain ⟨a, d, ha, hp⟩ := boundary_vertex_has_vertical_face_row y (Or.inr hy)
      have he := congrArg Fin.val hrow
      exact ⟨a, d, he.trans ha, by omega, by omega⟩
    · obtain ⟨a, d, ha⟩ := exists_faceRow_cover hr x.val.1
      have hyl := y.val.2.isLt
      exact ⟨a, d, ha, by omega, by omega⟩

end
end Erdos73
