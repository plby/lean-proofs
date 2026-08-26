import ErdosProblems.Erdos73.ControlledCrossingWall
import ErdosProblems.Erdos73.ControlledMonochromaticHandles

/-! An original odd haven forces a crossing wall with even corridors and odd handles. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph ColumnHandleFamily

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {q ell : ℕ}

theorem BrambleHaven.exists_controlled_odd_crossing_wall
    (h : BrambleHaven G (lowOrderOddSides G ell) q) (k d t m p g u a : ℕ)
    (hpk : p ≤ k) (hkd : k + 1 ≤ d)
    (hnumber : 5 * (2 * crossingHandleSelectionBound k - 2) < t)
    (hsize : 72 * t * t + t < m)
    (hrows : 2 * t < g - 1) (hwidth : (6 * t + 1) * d ≤ g - 1)
    (hu : 2 * m + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (hac : 32 * g ≤ a) (har : 12 * (2 ^ (4 * g) * g) ≤ a)
    (horder : controlledGridBrambleBound (2 * (p * a + a)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * a + a))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall (d + 1) g) G,
        Nonempty (WallGridAnchor M S) ∧ ∃ col : BipartiteColoringOn G S.vertexSet,
        (∃ b : Bool, ∀ w, col.color (S.branchVertex w) = b) ∧
        (∀ e, Even (S.edgePath e).walk.length) ∧
        (HasSameSideCrossingHandles (S := S) (col := col) true k ∨
          HasSameSideCrossingHandles (S := S) (col := col) false k ∨
          HasThroughCrossingHandles (S := S) (col := col) k) := by
  obtain ⟨M, hM, S₀, ⟨A₀⟩, hS₀⟩ :=
    h.exists_bipartite_wallSubdivision_with_gridAnchor p a horder hno
  obtain ⟨S₁, ⟨A₁⟩, _, col₁, _, b, hb⟩ :=
    A₀.exists_monochromatic_subwall (bipartiteColoringOnOfBipartite hS₀) g g hac har
  obtain ⟨S, hA, col, hcolor, B, hB, _, hdis, hends⟩ :=
    A₁.exists_wall_with_odd_handles hM col₁ b hb (crossingHandleSelectionBound k)
      d t m p u (by omega) hnumber hsize hrows hwidth hu hug huq
      h.odd_region_of_lowOrderOddSides hno
  have hends' : ∀ i, ∃ v w : ElementaryWallVertex (d + 1) g,
      (B i).source = S.branchVertex v ∧ (B i).target = S.branchVertex w ∧
        OnBrickColumnBoundary v ∧ OnBrickColumnBoundary w := by
    simpa only [OnBrickColumnBoundary, Nat.add_sub_cancel] using hends
  let F := ColumnHandleFamily.of_paths B hB hdis hends'
  obtain hp | hx := F.oddPacking_or_crossing_handles k (by omega) univ
    (by simp only [card_univ, Fintype.card_fin]; exact le_rfl)
  · exact (hno (hp.mono hpk)).elim
  · exact ⟨M, hM, S, hA, col, ⟨b, hcolor⟩,
      S.even_edgePaths_of_monochromaticBranches col b hcolor, hx⟩

def monochromaticWallAmbientSize (g : ℕ) : ℕ := 32 * g + 12 * (2 ^ (4 * g) * g)

def oddCrossingWallHavenBound (k p : ℕ) : ℕ :=
  2 * crossingWallPathCount k + p + controlledGridBrambleBound
    (2 * (p * monochromaticWallAmbientSize (crossingWallRowCount k p) +
      monochromaticWallAmbientSize (crossingWallRowCount k p)))

theorem BrambleHaven.exists_controlled_odd_crossing_wall_of_order
    (h : BrambleHaven G (lowOrderOddSides G ell) q) (k p : ℕ) (hpk : p ≤ k)
    (horder : oddCrossingWallHavenBound k p ≤ q) (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid
        (2 * (p * monochromaticWallAmbientSize (crossingWallRowCount k p) +
          monochromaticWallAmbientSize (crossingWallRowCount k p)))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall (k + 2) (crossingWallRowCount k p)) G,
        Nonempty (WallGridAnchor M S) ∧ ∃ col : BipartiteColoringOn G S.vertexSet,
        (∃ b : Bool, ∀ w, col.color (S.branchVertex w) = b) ∧
        (∀ e, Even (S.edgePath e).walk.length) ∧
        (HasSameSideCrossingHandles (S := S) (col := col) true k ∨
          HasSameSideCrossingHandles (S := S) (col := col) false k ∨
          HasThroughCrossingHandles (S := S) (col := col) k) := by
  apply h.exists_controlled_odd_crossing_wall k (k + 1) (crossingWallStageCount k)
    (crossingWallPathCount k) p (crossingWallRowCount k p) (2 * crossingWallPathCount k + p)
    (monochromaticWallAmbientSize (crossingWallRowCount k p)) hpk le_rfl
    (by dsimp only [crossingWallStageCount]; omega)
    (by dsimp only [crossingWallPathCount]; omega)
    (by dsimp only [crossingWallRowCount]; omega)
    (by dsimp only [crossingWallRowCount]; omega) le_rfl
    (by dsimp only [crossingWallRowCount]; omega)
    (by dsimp only [oddCrossingWallHavenBound] at horder; omega)
    (by dsimp only [monochromaticWallAmbientSize]; omega)
    (by dsimp only [monochromaticWallAmbientSize]; omega)
    (by dsimp only [oddCrossingWallHavenBound] at horder; omega) hno

end
end Erdos73
