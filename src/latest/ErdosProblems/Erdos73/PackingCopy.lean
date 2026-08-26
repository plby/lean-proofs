/- Copy path packings along ordinary injective graph maps. -/
import ErdosProblems.Erdos73.Paths
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace Erdos73Infrastructure.SimpleGraph
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}

namespace GraphPath

def mapCopy (P : GraphPath G) (e : G.Copy H) : GraphPath H where
  source := e P.source
  target := e P.target
  walk := P.walk.map e.toHom
  isPath := _root_.SimpleGraph.Walk.map_isPath_of_injective e.injective P.isPath

theorem mem_mapCopy_vertexSet (P : GraphPath G) (e : G.Copy H) (z : W) :
    z ∈ (P.mapCopy e).vertexSet ↔ ∃ x ∈ P.vertexSet, e x = z := by
  simp only [mapCopy, vertexSet, List.mem_toFinset,
    _root_.SimpleGraph.Walk.support_map, List.mem_map]
  rfl

theorem mapCopy_vertexSet (P : GraphPath G) (e : G.Copy H) :
    (P.mapCopy e).vertexSet = P.vertexSet.map e.toEmbedding := by
  ext z
  rw [mem_mapCopy_vertexSet, Finset.mem_map]
  rfl

end GraphPath
namespace PathPacking
variable {A B : Finset V}

def mapCopy (P : PathPacking G A B) (e : G.Copy H) :
    PathPacking H (A.map e.toEmbedding) (B.map e.toEmbedding) where
  Index := P.Index
  path i := (P.path i).mapCopy e
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨Finset.mem_map.mpr ⟨_, h.1, rfl⟩,
        Finset.mem_map.mpr ⟨_, h.2, rfl⟩⟩
    · exact Or.inr ⟨Finset.mem_map.mpr ⟨_, h.1, rfl⟩,
        Finset.mem_map.mpr ⟨_, h.2, rfl⟩⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzi hzj
    obtain ⟨x, hx, hxz⟩ := (GraphPath.mem_mapCopy_vertexSet _ _ _).mp hzi
    obtain ⟨y, hy, hyz⟩ := (GraphPath.mem_mapCopy_vertexSet _ _ _).mp hzj
    have heq := e.injective (hxz.trans hyz.symm)
    exact Finset.disjoint_left.mp (P.node_disjoint hij) hx (heq ▸ hy)

@[simp] theorem mapCopy_card (P : PathPacking G A B) (e : G.Copy H) :
    (P.mapCopy e).card = P.card := rfl

end PathPacking
end Erdos73Infrastructure.SimpleGraph
