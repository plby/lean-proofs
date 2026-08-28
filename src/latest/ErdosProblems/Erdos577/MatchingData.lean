import ErdosProblems.Erdos577.ScoredExchange
import ErdosProblems.Erdos577.FourTuples

/-! Two disjoint edges and positive path-remainder reductions for Wang's matching exchange. -/

namespace Erdos577

open Finset

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

structure TwoEdges (G : SimpleGraph V) where
  vertices : Fin 4 ↪ V
  firstEdge : G.Adj (vertices 0) (vertices 1)
  secondEdge : G.Adj (vertices 2) (vertices 3)

namespace TwoEdges

def ofPath (p : FourPath G) : TwoEdges G where
  vertices := p.vertices
  firstEdge := p.adjacent 0
  secondEdge := p.adjacent 2

def support [DecidableEq V] (p : TwoEdges G) : Finset V := tupleSupport p.vertices

lemma card_support [DecidableEq V] (p : TwoEdges G) : p.support.card = 4 :=
  card_tupleSupport p.vertices

lemma ofPath_support [DecidableEq V] (p : FourPath G) : (ofPath p).support = p.support := rfl

def image (p : TwoEdges G) (f : G.Copy H) : TwoEdges H where
  vertices := p.vertices.trans f.toEmbedding
  firstEdge := f.toHom.map_rel' p.firstEdge
  secondEdge := f.toHom.map_rel' p.secondEdge

end TwoEdges

namespace FourPath

def image (p : FourPath G) (f : G.Copy H) : FourPath H where
  vertices := p.vertices.trans f.toEmbedding
  adjacent i := f.toHom.map_rel' (p.adjacent i)

lemma image_support [DecidableEq V] [DecidableEq W] (p : FourPath G) (f : G.Copy H) :
    (p.image f).support = p.support.image f := by
  rw [support, support, image_image]
  rfl

end FourPath

variable [DecidableEq V]

/-- A path remainder and a quadrilateral partition the specified vertices;
the quadrilateral meets the stated positive induced-edge bound. -/
def PathReduction (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (minEdges : ℕ) : Prop :=
  ∃ p : FourPath G, p.support ⊆ s ∧ QuadOn G (s \ p.support) ∧
    minEdges ≤ edgeCount G (s \ p.support)

lemma PathReduction.image [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {s : Finset V} {minEdges : ℕ} (h : PathReduction G s minEdges) (f : G.Copy H) :
    PathReduction H (s.image f) minEdges := by
  obtain ⟨p, hp, hq, he⟩ := h
  have hinj : Function.Injective (f : V → W) := f.injective
  have hdiff : (s \ p.support).image f = s.image f \ (p.image f).support := by
    rw [p.image_support, image_sdiff s p.support hinj]
  refine ⟨p.image f, ?_, ?_, ?_⟩
  · rw [p.image_support]
    exact image_subset_image hp
  · have h := hq.image f
    rw [hdiff] at h
    exact h
  · have h := he.trans (edgeCount_image_le f (s \ p.support))
    rw [hdiff] at h
    exact h

end Erdos577
