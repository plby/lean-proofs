import ErdosProblems.Erdos73.ControlledWallHandles
import ErdosProblems.Erdos73.TileGridAnchors
import ErdosProblems.Erdos73.MonochromaticPathParity

/-! Handle extraction preserves monochromatic wall branches and produces genuinely odd handles. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g n q : ℕ}

theorem WallGridAnchor.exists_wall_with_odd_handles
    {β : Finset (Finset V)} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) (hM : NoGridRowInHavenSmallSide h M)
    (col : BipartiteColoringOn G S.vertexSet) (b : Bool)
    (hb : ∀ w, col.color (S.branchVertex w) = b) (k d t m p u : ℕ)
    (hd : 0 < d) (hnumber : 5 * (2 * k - 2) < t) (hsize : 72 * t * t + t < m)
    (hrows : 2 * t < g - 1) (hwidth : (6 * t + 1) * d ≤ g - 1)
    (hu : 2 * m + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ S' : GraphSubdivisionModel (elementaryWall (d + 1) g) G,
      Nonempty (WallGridAnchor M S') ∧ ∃ col' : BipartiteColoringOn G S'.vertexSet,
      (∀ w, col'.color (S'.branchVertex w) = b) ∧
      ∃ B : Fin k → GraphPath G,
        (∀ i, IsParityBreakingPath col'.color S'.vertexSet (B i)) ∧
        (∀ i, Odd (B i).walk.length) ∧
        Pairwise (fun i j => Disjoint (B i).vertexSet (B j).vertexSet) ∧
        (∀ i, ∃ v w : ElementaryWallVertex (d + 1) g,
          (B i).source = S'.branchVertex v ∧ (B i).target = S'.branchVertex w ∧
          (v.val.2.val ≤ 1 ∨ 2 * d ≤ v.val.2.val) ∧
          (w.val.2.val ≤ 1 ∨ 2 * d ≤ w.val.2.val)) := by
  have hg : 2 ≤ g := by omega
  have hm : 1 ≤ m := by omega
  have hcols : 6 * t < g - 1 := by
    have hh := (Nat.mul_le_mul_left (6 * t + 1) hd).trans hwidth
    simp only [Nat.mul_one] at hh
    omega
  obtain ⟨N, b₀, _, hcolor, hN, P, hP, hdis⟩ :=
    A.exists_monochromatic_odd_terminal_packing hM col m p u hm hu hug huq hodd hno
  obtain ⟨st⟩ := exists_brickStripSelectionState S col.color P N b₀ hg hg hN hcolor hP hdis
    hrows hcols hsize
  obtain ⟨a, hs, B, hB, hBdis, _, _, hends⟩ :=
    st.exists_breaking_slice_handles col k d hg hd hwidth hnumber
  let S' := S.restrictCopy (brickColumnSliceCopy a d hs)
  let col' := col.mono_support (S.restrictCopy_vertexSet_subset_vertexSet (brickColumnSliceCopy a d hs))
  have hb' : ∀ w, col'.color (S'.branchVertex w) = b :=
    fun w => hb (brickColumnSliceCopy a d hs w)
  refine ⟨S', ⟨A.restrictOffsets 0 a (by omega) hs⟩, col', hb', B, hB, ?_, hBdis, hends⟩
  intro i
  apply odd_length_of_parityBreaking_sameColor (hB i).breaking
  obtain ⟨v, w, hv, hw, _, _⟩ := hends i
  rw [hv, hw]
  exact (hb' v).trans (hb' w).symm

end
end Erdos73
