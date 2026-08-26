import ErdosProblems.Erdos73.BrickFaceCoverage

/-! The trimmed boundary vertices, as well as the interior vertices, belong to brick faces. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

theorem boundary_vertex_has_vertical_face_row {c r : ℕ}
    (x : ElementaryWallVertex c r) (hb : x.val.2.val = 0 ∨ x.val.2.val + 1 = 2 * c) :
    ∃ a : Fin (r - 1), ∃ d : Fin 2,
      x.val.1.val = a.val + d.val ∧ (x.val.2.val + a.val) % 2 = 1 := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp
    (show 1 < ((rawBrickWall c r).neighborFinset x.val).card from x.property)
  have hxy := ((rawBrickWall c r).mem_neighborFinset x.val y).mp hy
  have hxz := ((rawBrickWall c r).mem_neighborFinset x.val z).mp hz
  have hv : ∃ y : Fin r × Fin (2 * c), x.val.2 = y.2 ∧
      ((x.val.1.val + 1 = y.1.val ∧ (x.val.2.val + x.val.1.val) % 2 = 1) ∨
        (y.1.val + 1 = x.val.1.val ∧ (y.2.val + y.1.val) % 2 = 1)) := by
    rcases hxy with hxy | hxy
    · rcases hxz with hxz | hxz
      · apply (hyz _).elim
        apply Prod.ext
        · exact hxy.1.symm.trans hxz.1
        · apply Fin.ext
          have hyc := pathGraph_adj.mp hxy.2
          have hzc := pathGraph_adj.mp hxz.2
          have hyb := y.2.isLt
          have hzb := z.2.isLt
          omega
      · exact ⟨z, hxz⟩
    · exact ⟨y, hxy⟩
  obtain ⟨y, hcol, hup | hdown⟩ := hv
  · refine ⟨⟨x.val.1.val, by have hh := y.1.isLt; omega⟩, 0, ?_, hup.2⟩
    simp
  · refine ⟨⟨y.1.val, by have hh := x.val.1.isLt; omega⟩, 1, ?_, ?_⟩
    · exact hdown.1.symm
    · rw [hcol]
      exact hdown.2

theorem exists_brickFace_at_vertex {c r : ℕ} (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x : ElementaryWallVertex c r) :
    ∃ a : Fin (r - 1), ∃ j : Fin (c - 1), ∃ i : Fin 6,
      elementaryBrickFaceCopy a.val (brickFaceColumn a.val j.val)
        (by have ha := a.isLt; omega)
        (by have hj := j.isLt; unfold brickFaceColumn; omega)
        (by unfold brickFaceColumn; omega) i = x := by
  by_cases hint : 0 < x.val.2.val ∧ x.val.2.val + 1 < 2 * c
  · exact exists_brickFace_at_interior_vertex hc hr x hint.1 hint.2
  have hb : x.val.2.val = 0 ∨ x.val.2.val + 1 = 2 * c := by
    have hh := x.val.2.isLt
    omega
  obtain ⟨a, d, ha, hp⟩ := boundary_vertex_has_vertical_face_row x hb
  let q := (a.val + 1) % 2
  have hlo : q ≤ x.val.2.val := by dsimp only [q]; omega
  have hhi : x.val.2.val ≤ 2 * (c - 1) + q := by
    have hh := x.val.2.isLt
    dsimp only [q]
    omega
  obtain ⟨j, e, hj⟩ := exists_faceColumn_cover hc hlo hhi
  obtain ⟨i, hi⟩ := brickFacePosition_covers_rectangle d e
  refine ⟨a, j, i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change a.val + (brickFacePosition i).1 = x.val.1.val
    rw [hi]
    exact ha.symm
  · apply Fin.ext
    change brickFaceColumn a.val j.val + (brickFacePosition i).2 = x.val.2.val
    rw [hi]
    exact hj.symm

end
end Erdos73
