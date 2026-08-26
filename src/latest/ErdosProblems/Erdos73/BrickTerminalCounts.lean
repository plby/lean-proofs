import ErdosProblems.Erdos73.BrickStripNetworks
import ErdosProblems.Erdos73.BrickFaceCoverage

/-! Only six branch vertices per forbidden face can escape all available strips. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

def brickFaceBranch (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) (l : Fin 6) : V :=
  S.branchVertex (elementaryBrickFaceCopy i.1.val (brickFaceColumn i.1.val i.2.val)
    (by have hi := i.1.isLt; omega)
    (by have hi := i.2.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega) l)

theorem brickFaceBranch_mem_region (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) (l : Fin 6) :
    brickFaceBranch S i l ∈ brickFaceRegion S i :=
  branch_mem_brickFaceSupport S _ _ _ _ _ l

def forbiddenBrickBranches (S : GraphSubdivisionModel (elementaryWall c r) G)
    (R : Finset (Fin (r - 1))) (C : Finset (Fin (c - 1))) : Finset V :=
  (R ×ˢ C).biUnion fun i => Finset.univ.image (brickFaceBranch S i)

theorem forbiddenBrickBranches_card (S : GraphSubdivisionModel (elementaryWall c r) G)
    (R : Finset (Fin (r - 1))) (C : Finset (Fin (c - 1))) :
    (forbiddenBrickBranches S R C).card ≤ 6 * R.card * C.card := by
  calc
    (forbiddenBrickBranches S R C).card ≤
        ∑ i ∈ R ×ˢ C, (Finset.univ.image (brickFaceBranch S i)).card := card_biUnion_le
    _ ≤ ∑ _i ∈ R ×ˢ C, 6 := by
      apply sum_le_sum
      intro i _
      exact card_image_le.trans (by simp)
    _ = 6 * R.card * C.card := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem interior_branch_outside_available_strips
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r)
    (R : Finset (Fin (r - 1))) (C : Finset (Fin (c - 1)))
    (w : ElementaryWallVertex c r) (hl : 0 < w.val.2.val) (hh : w.val.2.val + 1 < 2 * c)
    (hout : S.branchVertex w ∉ brickStripNetwork S (Finset.univ \ R) (Finset.univ \ C)) :
    S.branchVertex w ∈ forbiddenBrickBranches S R C := by
  obtain ⟨a, j, l, he⟩ := exists_brickFace_at_interior_vertex hc hr w hl hh
  have he' : brickFaceBranch S (a, j) l = S.branchVertex w := congrArg S.branchVertex he
  have hface : S.branchVertex w ∈ brickFaceRegion S (a, j) :=
    he' ▸ brickFaceBranch_mem_region S (a, j) l
  have ha : a ∈ R := by
    by_contra hn
    apply hout
    apply (mem_brickStripNetwork S _ _ _).mpr
    exact Or.inl ⟨a, mem_sdiff.mpr ⟨mem_univ _, hn⟩,
      mem_biUnion.mpr ⟨j, mem_univ _, hface⟩⟩
  have hj : j ∈ C := by
    by_contra hn
    apply hout
    apply (mem_brickStripNetwork S _ _ _).mpr
    exact Or.inr ⟨j, mem_sdiff.mpr ⟨mem_univ _, hn⟩,
      mem_biUnion.mpr ⟨a, mem_univ _, hface⟩⟩
  exact mem_biUnion.mpr ⟨(a, j), mem_product.mpr ⟨ha, hj⟩,
    mem_image.mpr ⟨l, mem_univ _, he'⟩⟩

theorem interior_terminals_outside_available_strips_card
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r)
    (N : Finset V)
    (hN : ∀ x ∈ N, ∃ w : ElementaryWallVertex c r,
      x = S.branchVertex w ∧ 0 < w.val.2.val ∧ w.val.2.val + 1 < 2 * c)
    (R : Finset (Fin (r - 1))) (C : Finset (Fin (c - 1))) :
    (N \ brickStripNetwork S (Finset.univ \ R) (Finset.univ \ C)).card ≤
      6 * R.card * C.card := by
  apply le_trans (card_le_card ?_) (forbiddenBrickBranches_card S R C)
  intro x hx
  obtain ⟨hxN, hxout⟩ := mem_sdiff.mp hx
  obtain ⟨w, rfl, hl, hh⟩ := hN x hxN
  exact interior_branch_outside_available_strips S hc hr R C w hl hh hxout

end
end Erdos73
