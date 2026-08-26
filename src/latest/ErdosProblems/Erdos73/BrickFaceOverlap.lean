import ErdosProblems.Erdos73.SubdividedBrickFaces

/-! Adjacent actual brick faces share at least two branch vertices. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

theorem branch_mem_brickFaceSupport (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hpar : (b + a) % 2 = 1) (i : Fin 6) :
    S.branchVertex (elementaryBrickFaceCopy a b hr hc hpar i) ∈
      brickFaceSupport S a b hr hc hpar :=
  ((S.restrictCopy (elementaryBrickFaceCopy a b hr hc hpar)).mem_vertexSet _).mpr
    (Or.inl ⟨i, rfl⟩)

theorem brickFaceSupport_overlap_of_vertices (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b a' b' : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hp : (b + a) % 2 = 1)
    (hr' : a' + 1 < r) (hc' : b' + 2 < 2 * c) (hp' : (b' + a') % 2 = 1)
    (i j i' j' : Fin 6) (hij : i ≠ j)
    (hi : elementaryBrickFaceCopy a b hr hc hp i = elementaryBrickFaceCopy a' b' hr' hc' hp' i')
    (hj : elementaryBrickFaceCopy a b hr hc hp j = elementaryBrickFaceCopy a' b' hr' hc' hp' j') :
    2 ≤ (brickFaceSupport S a b hr hc hp ∩ brickFaceSupport S a' b' hr' hc' hp').card := by
  apply Finset.one_lt_card.mpr
  refine ⟨S.branchVertex (elementaryBrickFaceCopy a b hr hc hp i),
    mem_inter.mpr ⟨branch_mem_brickFaceSupport S a b hr hc hp i, ?_⟩,
    S.branchVertex (elementaryBrickFaceCopy a b hr hc hp j),
    mem_inter.mpr ⟨branch_mem_brickFaceSupport S a b hr hc hp j, ?_⟩, ?_⟩
  · rw [hi]
    exact branch_mem_brickFaceSupport S a' b' hr' hc' hp' i'
  · rw [hj]
    exact branch_mem_brickFaceSupport S a' b' hr' hc' hp' j'
  · intro he
    exact hij ((elementaryBrickFaceCopy a b hr hc hp).injective (S.injective he))

theorem brickFaceSupport_horizontal_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 1 < r) (hc : b + 4 < 2 * c) (hp : (b + a) % 2 = 1) :
    2 ≤ (brickFaceSupport S a b hr (by omega) hp ∩
      brickFaceSupport S a (b + 2) hr (by omega) (by omega)).card := by
  apply brickFaceSupport_overlap_of_vertices S a b a (b + 2) hr (by omega) hp
    hr (by omega) (by omega) 2 3 0 5 (by decide)
  all_goals rfl

theorem brickFaceSupport_diagonal_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 2 < r) (hc : b + 3 < 2 * c) (hp : (b + a) % 2 = 1) :
    2 ≤ (brickFaceSupport S a b (by omega) (by omega) hp ∩
      brickFaceSupport S (a + 1) (b + 1) (by omega) (by omega) (by omega)).card := by
  apply brickFaceSupport_overlap_of_vertices S a b (a + 1) (b + 1) (by omega) (by omega) hp
    (by omega) (by omega) (by omega) 4 3 0 1 (by decide)
  all_goals rfl

theorem brickFaceSupport_diagonal_left_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 2 < r) (hc : b + 3 < 2 * c) (hp : (b + 1 + a) % 2 = 1) :
    2 ≤ (brickFaceSupport S a (b + 1) (by omega) (by omega) hp ∩
      brickFaceSupport S (a + 1) b (by omega) (by omega) (by omega)).card := by
  apply brickFaceSupport_overlap_of_vertices S a (b + 1) (a + 1) b (by omega) (by omega) hp
    (by omega) (by omega) (by omega) 5 4 1 2 (by decide)
  all_goals rfl

theorem brickFaceSupport_horizontal_overlap_of_eq
    (S : GraphSubdivisionModel (elementaryWall c r) G) (a b b' : ℕ)
    (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hp : (b + a) % 2 = 1)
    (hc' : b' + 2 < 2 * c) (hp' : (b' + a) % 2 = 1) (he : b + 2 = b') :
    2 ≤ (brickFaceSupport S a b hr hc hp ∩ brickFaceSupport S a b' hr hc' hp').card := by
  subst b'
  exact brickFaceSupport_horizontal_overlap S a b hr (by omega) hp

theorem brickFaceSupport_vertical_overlap_of_eq
    (S : GraphSubdivisionModel (elementaryWall c r) G) (a a' b b' : ℕ)
    (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hp : (b + a) % 2 = 1)
    (hr' : a' + 1 < r) (hc' : b' + 2 < 2 * c) (hp' : (b' + a') % 2 = 1)
    (ha : a + 1 = a') (hb : b + 1 = b' ∨ b' + 1 = b) :
    2 ≤ (brickFaceSupport S a b hr hc hp ∩ brickFaceSupport S a' b' hr' hc' hp').card := by
  subst a'
  rcases hb with hb | hb
  · subst b'
    exact brickFaceSupport_diagonal_overlap S a b (by omega) (by omega) hp
  · subst b
    exact brickFaceSupport_diagonal_left_overlap S a b' (by omega) (by omega) hp

end
end Erdos73
