import ErdosProblems.Erdos73.BrickBoundaryRanks
import ErdosProblems.Erdos73.PureEndpointPairs
import ErdosProblems.Erdos73.ParityColoring

/-! Actual disjoint wall handles have distinct endpoint ranks and contain pure subfamilies. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} {G : SimpleGraph V} {c r : ℕ}

structure ColumnHandleFamily (S : GraphSubdivisionModel (elementaryWall c r) G)
    (col : BipartiteColoringOn G S.vertexSet) (I : Type*) where
  path : I → Erdos73Infrastructure.SimpleGraph.GraphPath G
  clean : ∀ i, IsParityBreakingPath col.color S.vertexSet (path i)
  disjoint : Pairwise (fun i j => Disjoint (path i).vertexSet (path j).vertexSet)
  sourceNail : I → ElementaryWallVertex c r
  targetNail : I → ElementaryWallVertex c r
  source_eq : ∀ i, (path i).source = S.branchVertex (sourceNail i)
  target_eq : ∀ i, (path i).target = S.branchVertex (targetNail i)
  source_boundary : ∀ i, OnBrickColumnBoundary (sourceNail i)
  target_boundary : ∀ i, OnBrickColumnBoundary (targetNail i)

namespace ColumnHandleFamily

variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

def of_paths (P : I → Erdos73Infrastructure.SimpleGraph.GraphPath G)
    (hP : ∀ i, IsParityBreakingPath col.color S.vertexSet (P i))
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hends : ∀ i, ∃ u v : ElementaryWallVertex c r,
      (P i).source = S.branchVertex u ∧ (P i).target = S.branchVertex v ∧
      OnBrickColumnBoundary u ∧ OnBrickColumnBoundary v) : ColumnHandleFamily S col I := by
  choose u v hs ht hu hv using hends
  exact ⟨P, hP, hdis, u, v, hs, ht, hu, hv⟩

def endpoint (F : ColumnHandleFamily S col I) (i : I) (b : Bool) : ElementaryWallVertex c r :=
  if b then F.targetNail i else F.sourceNail i

theorem endpoint_boundary (F : ColumnHandleFamily S col I) (i : I) (b : Bool) :
    OnBrickColumnBoundary (F.endpoint i b) := by
  cases b
  · exact F.source_boundary i
  · exact F.target_boundary i

theorem endpoint_mem (F : ColumnHandleFamily S col I) (i : I) (b : Bool) :
    S.branchVertex (F.endpoint i b) ∈ (F.path i).vertexSet := by
  cases b
  · rw [show F.endpoint i false = F.sourceNail i from rfl, ← F.source_eq]
    exact (F.path i).source_mem_vertexSet
  · rw [show F.endpoint i true = F.targetNail i from rfl, ← F.target_eq]
    exact (F.path i).target_mem_vertexSet

theorem endpoint_rank_ne_of_ne_index (F : ColumnHandleFamily S col I) (hc : 2 ≤ c)
    {i j : I} (hij : i ≠ j) (b e : Bool) :
    brickBoundaryRank (F.endpoint i b) ≠ brickBoundaryRank (F.endpoint j e) := by
  intro he
  have hn := brickBoundaryRank_injective_on_boundary hc (F.endpoint_boundary i b)
    (F.endpoint_boundary j e) he
  apply Finset.disjoint_left.mp (F.disjoint hij) (F.endpoint_mem i b)
  rw [hn]
  exact F.endpoint_mem j e

theorem source_rank_ne_target_rank (F : ColumnHandleFamily S col I) (hc : 2 ≤ c) (i : I) :
    brickBoundaryRank (F.sourceNail i) ≠ brickBoundaryRank (F.targetNail i) := by
  intro he
  have hn := brickBoundaryRank_injective_on_boundary hc (F.source_boundary i) (F.target_boundary i) he
  apply (F.clean i).breaking.source_ne_target
  exact (F.source_eq i).trans ((congrArg S.branchVertex hn).trans (F.target_eq i).symm)

def lowerRank (F : ColumnHandleFamily S col I) (i : I) : ℕ :=
  min (brickBoundaryRank (F.sourceNail i)) (brickBoundaryRank (F.targetNail i))

def upperRank (F : ColumnHandleFamily S col I) (i : I) : ℕ :=
  max (brickBoundaryRank (F.sourceNail i)) (brickBoundaryRank (F.targetNail i))

theorem lowerRank_lt_upperRank (F : ColumnHandleFamily S col I) (hc : 2 ≤ c) (i : I) :
    F.lowerRank i < F.upperRank i := by
  have hh := F.source_rank_ne_target_rank hc i
  dsimp only [lowerRank, upperRank]
  omega

theorem sorted_ranks_separate (F : ColumnHandleFamily S col I) (hc : 2 ≤ c)
    {i j : I} (hij : i ≠ j) :
    F.lowerRank i ≠ F.lowerRank j ∧ F.lowerRank i ≠ F.upperRank j ∧
      F.upperRank i ≠ F.lowerRank j ∧ F.upperRank i ≠ F.upperRank j := by
  have hff := F.endpoint_rank_ne_of_ne_index hc hij false false
  have hft := F.endpoint_rank_ne_of_ne_index hc hij false true
  have htf := F.endpoint_rank_ne_of_ne_index hc hij true false
  have htt := F.endpoint_rank_ne_of_ne_index hc hij true true
  simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at hff hft htf htt
  dsimp only [lowerRank, upperRank]
  omega

theorem exists_pure_subfamily (F : ColumnHandleFamily S col I) (hc : 2 ≤ c)
    (s : Finset I) (t : ℕ) (hsize : pureEndpointPairBound t ≤ s.card) :
    ∃ u : Finset I, u ⊆ s ∧ t ≤ u.card ∧ ∃ shape : EndpointPairShape,
      (u : Set I).Pairwise (fun i j => shape.Rel (F.lowerRank i) (F.upperRank i)
        (F.lowerRank j) (F.upperRank j)) :=
  exists_pure_endpoint_pairs s F.lowerRank F.upperRank (fun i _ => F.lowerRank_lt_upperRank hc i)
    (fun _ _ _ _ hij => F.sorted_ranks_separate hc hij) t hsize

end ColumnHandleFamily
end
end Erdos73
