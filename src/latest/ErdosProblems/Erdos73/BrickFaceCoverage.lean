import ErdosProblems.Erdos73.BrickFaceArray

/-! Every horizontally interior wall vertex belongs to an actual face in the rectangular array. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

theorem exists_faceRow_cover {r : ℕ} (hr : 2 ≤ r) (x : Fin r) :
    ∃ a : Fin (r - 1), ∃ d : Fin 2, x.val = a.val + d.val := by
  by_cases hx : x.val < r - 1
  · exact ⟨⟨x.val, hx⟩, 0, by simp⟩
  · refine ⟨⟨r - 2, by omega⟩, 1, ?_⟩
    have hh := x.isLt
    change x.val = r - 2 + 1
    omega

theorem exists_faceColumn_cover {c q x : ℕ} (hc : 2 ≤ c)
    (hlo : q ≤ x) (hhi : x ≤ 2 * (c - 1) + q) :
    ∃ j : Fin (c - 1), ∃ d : Fin 3, x = 2 * j.val + q + d.val := by
  by_cases hx : x - q < 2 * (c - 1)
  · refine ⟨⟨(x - q) / 2, by omega⟩, ⟨(x - q) % 2, by omega⟩, ?_⟩
    dsimp only
    omega
  · refine ⟨⟨c - 2, by omega⟩, 2, ?_⟩
    change x = 2 * (c - 2) + q + 2
    omega

theorem exists_brickFace_at_interior_vertex {c r : ℕ} (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x : ElementaryWallVertex c r) (hl : 0 < x.val.2.val) (hh : x.val.2.val + 1 < 2 * c) :
    ∃ a : Fin (r - 1), ∃ j : Fin (c - 1), ∃ i : Fin 6,
      elementaryBrickFaceCopy a.val (brickFaceColumn a.val j.val)
        (by have ha := a.isLt; omega)
        (by have hj := j.isLt; unfold brickFaceColumn; omega)
        (by unfold brickFaceColumn; omega) i = x := by
  obtain ⟨a, d, ha⟩ := exists_faceRow_cover hr x.val.1
  let q := (a.val + 1) % 2
  have hq : q < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨j, e, hj⟩ := exists_faceColumn_cover hc
    (show q ≤ x.val.2.val by omega) (show x.val.2.val ≤ 2 * (c - 1) + q by omega)
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

theorem interior_branch_mem_faceRegion_union {V : Type*} {G : SimpleGraph V} {c r : ℕ}
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r)
    (x : ElementaryWallVertex c r) (hl : 0 < x.val.2.val) (hh : x.val.2.val + 1 < 2 * c) :
    S.branchVertex x ∈ Finset.univ.biUnion (brickFaceRegion S) := by
  obtain ⟨a, j, i, he⟩ := exists_brickFace_at_interior_vertex hc hr x hl hh
  refine mem_biUnion.mpr ⟨(a, j), mem_univ _, ?_⟩
  rw [← he]
  exact branch_mem_brickFaceSupport S _ _ _ _ _ i

end
end Erdos73
