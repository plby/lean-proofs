import ErdosProblems.Erdos73.ControlledWallHandles
import ErdosProblems.Erdos73.CrossingHandleExtraction
import ErdosProblems.Erdos73.OddPackingMonotone

/-! The original odd haven forces a controlled wall with an ordered crossing-handle family. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph ColumnHandleFamily

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {q ell : ℕ}

theorem BrambleHaven.exists_controlled_crossing_wall
    (h : BrambleHaven G (lowOrderOddSides G ell) q) (k d t m p g u : ℕ)
    (hpk : p ≤ k) (hkd : k + 1 ≤ d)
    (hnumber : 5 * (2 * crossingHandleSelectionBound k - 2) < t)
    (hsize : 72 * t * t + t < m)
    (hrows : 2 * t < g - 1) (hwidth : (6 * t + 1) * d ≤ g - 1)
    (hu : 2 * m + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * g + g))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall (d + 1) g) G,
        Nonempty (WallGridAnchor M S) ∧ ∃ col : BipartiteColoringOn G S.vertexSet,
          HasSameSideCrossingHandles (S := S) (col := col) true k ∨
          HasSameSideCrossingHandles (S := S) (col := col) false k ∨
          HasThroughCrossingHandles (S := S) (col := col) k := by
  obtain ⟨M, hM, S, hA, col, B, hB, hdis, hends⟩ :=
    h.exists_controlled_wall_with_breaking_handles (crossingHandleSelectionBound k)
      d t m p g u (by omega) hnumber hsize hrows hwidth hu hug huq horder hno
  have hends' : ∀ i, ∃ v w : ElementaryWallVertex (d + 1) g,
      (B i).source = S.branchVertex v ∧ (B i).target = S.branchVertex w ∧
        OnBrickColumnBoundary v ∧ OnBrickColumnBoundary w := by
    simpa only [OnBrickColumnBoundary, Nat.add_sub_cancel] using hends
  let F := ColumnHandleFamily.of_paths B hB hdis hends'
  obtain hp | hx := F.oddPacking_or_crossing_handles k (by omega) univ
    (by simp only [card_univ, Fintype.card_fin]; exact le_rfl)
  · exact (hno (hp.mono hpk)).elim
  · exact ⟨M, hM, S, hA, col, hx⟩

def crossingWallStageCount (k : ℕ) : ℕ := 5 * (2 * crossingHandleSelectionBound k - 2) + 1

def crossingWallPathCount (k : ℕ) : ℕ :=
  72 * crossingWallStageCount k * crossingWallStageCount k + crossingWallStageCount k + 1

def crossingWallRowCount (k p : ℕ) : ℕ :=
  (6 * crossingWallStageCount k + 1) * (k + 1) +
    2 * (2 * crossingWallPathCount k + p) + 2 * crossingWallStageCount k + 4

def crossingWallHavenBound (k p : ℕ) : ℕ :=
  2 * crossingWallPathCount k + p +
    controlledGridBrambleBound (2 * (p * crossingWallRowCount k p + crossingWallRowCount k p))

theorem BrambleHaven.exists_controlled_crossing_wall_of_order
    (h : BrambleHaven G (lowOrderOddSides G ell) q) (k p : ℕ) (hpk : p ≤ k)
    (horder : crossingWallHavenBound k p ≤ q) (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid
        (2 * (p * crossingWallRowCount k p + crossingWallRowCount k p))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall (k + 2) (crossingWallRowCount k p)) G,
        Nonempty (WallGridAnchor M S) ∧ ∃ col : BipartiteColoringOn G S.vertexSet,
          HasSameSideCrossingHandles (S := S) (col := col) true k ∨
          HasSameSideCrossingHandles (S := S) (col := col) false k ∨
          HasThroughCrossingHandles (S := S) (col := col) k := by
  apply h.exists_controlled_crossing_wall k (k + 1) (crossingWallStageCount k)
    (crossingWallPathCount k) p (crossingWallRowCount k p) (2 * crossingWallPathCount k + p)
    hpk le_rfl
    (by dsimp only [crossingWallStageCount]; omega)
    (by dsimp only [crossingWallPathCount]; omega)
    (by dsimp only [crossingWallRowCount]; omega)
    (by dsimp only [crossingWallRowCount]; omega) le_rfl
    (by dsimp only [crossingWallRowCount]; omega)
    (by dsimp only [crossingWallHavenBound] at horder; omega)
    (by dsimp only [crossingWallHavenBound] at horder; omega) hno

end
end Erdos73
