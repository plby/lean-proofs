import ErdosProblems.Erdos73.GraphPaths
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-! Turn an injective finite sequence of adjacent vertices into a bundled simple path. -/

namespace Erdos73Infrastructure.SimpleGraph.GraphPath

open _root_.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V} {n : ℕ}

def ofSequence (f : Fin (n + 1) → V) (hf : Function.Injective f)
    (ha : ∀ i (hi : i + 1 < n + 1), G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) :
    GraphPath G where
  source := (List.ofFn f).head (by simp)
  target := (List.ofFn f).getLast (by simp)
  walk := Walk.ofSupport (List.ofFn f) (by simp) (List.isChain_ofFn.mpr ha)
  isPath := by
    rw [Walk.isPath_def, Walk.support_ofSupport]
    exact List.nodup_ofFn.mpr hf

omit [DecidableEq V] in
@[simp] theorem ofSequence_source (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha) :
    (ofSequence (G := G) f hf ha).source = f 0 := by simp [ofSequence]

omit [DecidableEq V] in
@[simp] theorem ofSequence_target (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha) :
    (ofSequence (G := G) f hf ha).target = f (Fin.last n) := by
  exact List.getLast_ofFn_succ f

omit [DecidableEq V] in
@[simp] theorem ofSequence_length (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha) :
    (ofSequence (G := G) f hf ha).walk.length = n := by simp [ofSequence]

theorem mem_ofSequence_vertexSet (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha) (v : V) :
    v ∈ (ofSequence (G := G) f hf ha).vertexSet ↔ ∃ i, f i = v := by
  simp only [ofSequence, vertexSet, Walk.support_ofSupport, List.mem_toFinset, List.mem_ofFn]

omit [DecidableEq V] in
theorem ofSequence_getVert (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha)
    (i : ℕ) (hi : i ≤ n) : (ofSequence (G := G) f hf ha).walk.getVert i = f ⟨i, by omega⟩ := by
  rw [Walk.getVert_eq_support_getElem _ (by simpa only [ofSequence_length] using hi)]
  simp only [ofSequence, Walk.support_ofSupport, List.getElem_ofFn]

theorem ofSequence_edge (f : Fin (n + 1) → V) (hf : Function.Injective f) (ha)
    (i : ℕ) (hi : i < n) :
    s(f ⟨i, by omega⟩, f ⟨i + 1, by omega⟩) ∈ (ofSequence (G := G) f hf ha).edgeSet := by
  let P := ofSequence (G := G) f hf ha
  have hstep := P.walk.toSubgraph_adj_getVert (show i < P.walk.length by
    simpa only [P, ofSequence_length] using hi)
  have hedge := List.mem_toFinset.mpr (Walk.adj_toSubgraph_iff_mem_edges.mp hstep)
  simpa only [P, edgeSet, ofSequence_getVert f hf ha i (by omega),
    ofSequence_getVert f hf ha (i + 1) (by omega)] using hedge

end Erdos73Infrastructure.SimpleGraph.GraphPath
