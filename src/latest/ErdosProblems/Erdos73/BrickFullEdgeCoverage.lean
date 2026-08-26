import ErdosProblems.Erdos73.BrickFaceCoordinates

/-! Every edge of the trimmed elementary wall lies on an indexed hexagonal face. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {c r : ℕ}

theorem exists_brickFace_at_horizontal (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x y : ElementaryWallVertex c r) (hrow : x.val.1 = y.val.1)
    (hcol : x.val.2.val + 1 = y.val.2.val) :
    ∃ a : Fin (r - 1), ∃ j : Fin (c - 1), ∃ i l : Fin 6,
      (cycleGraph 6).Adj i l ∧ brickFaceCopyAt (a, j) i = x ∧ brickFaceCopyAt (a, j) l = y := by
  obtain ⟨a, d, ha, hlo, hhi⟩ := exists_faceRow_cover_horizontal hc hr x y hrow hcol
  obtain ⟨j, e, he⟩ := exists_faceColumn_cover_horizontal hlo (hcol ▸ hhi)
  let e0 : Fin 3 := ⟨e.val, by have hh := e.isLt; omega⟩
  let e1 : Fin 3 := ⟨e.val + 1, by have hh := e.isLt; omega⟩
  obtain ⟨i, hi⟩ := brickFacePosition_covers_rectangle d e0
  obtain ⟨l, hl⟩ := brickFacePosition_covers_rectangle d e1
  refine ⟨a, j, i, l, ?_, ?_, ?_⟩
  · apply brickFacePosition_horizontal_adj
    · rw [hi, hl]
    · rw [hi, hl]
  · apply brickFaceCopyAt_eq_of_coordinates
    · rw [hi]
      exact ha.symm
    · rw [hi]
      exact he.symm
  · apply brickFaceCopyAt_eq_of_coordinates
    · rw [hl]
      exact (ha.symm.trans (congrArg Fin.val hrow))
    · rw [hl]
      change brickFaceColumn a.val j.val + (e.val + 1) = y.val.2.val
      dsimp only [brickFaceColumn]
      omega

theorem exists_brickFace_at_vertical (hc : 2 ≤ c)
    (x y : ElementaryWallVertex c r) (hrow : x.val.1.val + 1 = y.val.1.val)
    (hcol : x.val.2 = y.val.2) (hp : (x.val.2.val + x.val.1.val) % 2 = 1) :
    ∃ a : Fin (r - 1), ∃ j : Fin (c - 1), ∃ i l : Fin 6,
      (cycleGraph 6).Adj i l ∧ brickFaceCopyAt (a, j) i = x ∧ brickFaceCopyAt (a, j) l = y := by
  let a : Fin (r - 1) := ⟨x.val.1.val, by have hh := y.val.1.isLt; omega⟩
  let q := (a.val + 1) % 2
  have hlo : q ≤ x.val.2.val := by dsimp only [q, a]; omega
  have hhi : x.val.2.val ≤ 2 * (c - 1) + q := by
    have hx := x.val.2.isLt
    dsimp only [q, a]
    omega
  obtain ⟨j, e, he⟩ := exists_faceColumn_cover hc hlo hhi
  have hep : e.val % 2 = 0 := by dsimp only [q, a] at he; omega
  obtain ⟨i, hi⟩ := brickFacePosition_covers_rectangle 0 e
  obtain ⟨l, hl⟩ := brickFacePosition_covers_rectangle 1 e
  refine ⟨a, j, i, l, ?_, ?_, ?_⟩
  · apply brickFacePosition_vertical_adj
    · rw [hi]
      rfl
    · rw [hl]
      rfl
    · rw [hi, hl]
    · simpa only [hi] using hep
  · apply brickFaceCopyAt_eq_of_coordinates
    · rw [hi]
      rfl
    · rw [hi]
      exact he.symm
  · apply brickFaceCopyAt_eq_of_coordinates
    · rw [hl]
      exact hrow
    · rw [hl]
      exact he.symm.trans (congrArg Fin.val hcol)

theorem exists_brickFace_at_adj (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x y : ElementaryWallVertex c r) (hxy : (elementaryWall c r).Adj x y) :
    ∃ a : Fin (r - 1), ∃ j : Fin (c - 1), ∃ i l : Fin 6,
      (cycleGraph 6).Adj i l ∧ brickFaceCopyAt (a, j) i = x ∧ brickFaceCopyAt (a, j) l = y := by
  rcases hxy with ⟨hrow, hcol⟩ | ⟨hcol, hrow | hrow⟩
  · rcases pathGraph_adj.mp hcol with hcol | hcol
    · exact exists_brickFace_at_horizontal hc hr x y hrow hcol
    · obtain ⟨a, j, i, l, hadj, hi, hl⟩ :=
        exists_brickFace_at_horizontal hc hr y x hrow.symm hcol
      exact ⟨a, j, l, i, hadj.symm, hl, hi⟩
  · exact exists_brickFace_at_vertical hc x y hrow.1 hcol hrow.2
  · obtain ⟨a, j, i, l, hadj, hi, hl⟩ :=
      exists_brickFace_at_vertical hc y x hrow.1 hcol.symm hrow.2
    exact ⟨a, j, l, i, hadj.symm, hl, hi⟩

end
end Erdos73
