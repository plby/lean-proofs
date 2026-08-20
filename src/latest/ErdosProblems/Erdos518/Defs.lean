/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 518: basic definitions

A red--blue colouring of the complete graph on `V` is represented by a simple graph `G`:
the red edges are those of `G`, and the blue edges are those of `Gᶜ`. Paths are represented by
nonempty, duplicate-free lists whose consecutive vertices are adjacent.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- A nonempty simple path, represented by its ordered list of vertices. -/
def IsPath (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj

/-- A list of paths covers a graph when every listed object is a path and every vertex occurs in
at least one of the lists. The lists are not required to be mutually disjoint. -/
def IsPathCover (G : SimpleGraph V) (ps : List (List V)) : Prop :=
  (∀ p ∈ ps, IsPath G p) ∧ ∀ v : V, ∃ p ∈ ps, v ∈ p

/-- The vertices of `G` can be covered by at most `k` paths. -/
def HasPathCoverAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ ps : List (List V), ps.length ≤ k ∧ IsPathCover G ps

@[simp] lemma isPath_singleton (G : SimpleGraph V) (v : V) : IsPath G [v] := by
  simp [IsPath]

lemma isPath_reverse {G : SimpleGraph V} {p : List V} (hp : IsPath G p) :
    IsPath G p.reverse := by
  refine ⟨by simpa using hp.1, List.nodup_reverse.mpr hp.2.1, ?_⟩
  rw [List.isChain_reverse]
  exact hp.2.2.imp fun _ _ h ↦ h.symm

/-- Turn a list-path into Mathlib's dependent walk representation. -/
def pathWalk {G : SimpleGraph V} {p : List V} (hp : IsPath G p) :
    G.Walk (p.head hp.1) (p.getLast hp.1) :=
  SimpleGraph.Walk.ofSupport p hp.1 hp.2.2

@[simp] lemma support_pathWalk {G : SimpleGraph V} {p : List V} (hp : IsPath G p) :
    (pathWalk hp).support = p := by
  simp [pathWalk]

lemma isPath_pathWalk {G : SimpleGraph V} {p : List V} (hp : IsPath G p) :
    (pathWalk hp).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  simpa using hp.2.1

/-- Every nonempty finite graph has a longest list-represented path. -/
lemma exists_longest_path (G : SimpleGraph V) [Nonempty V] [Finite V] :
    ∃ p : List V, IsPath G p ∧ ∀ q : List V, IsPath G q → q.length ≤ p.length := by
  obtain ⟨u, v, w, hw, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨w.support, ⟨w.support_ne_nil, hw.support_nodup, w.isChain_adj_support⟩, ?_⟩
  intro q hq
  have hlen := hmax _ _ (pathWalk hq) (isPath_pathWalk hq)
  calc
    q.length = (pathWalk hq).support.length := by simp
    _ = (pathWalk hq).length + 1 := (pathWalk hq).length_support
    _ ≤ w.length + 1 := Nat.add_le_add_right hlen 1
    _ = w.support.length := w.length_support.symm

@[simp] lemma hasPathCoverAtMost_fin_zero (G : SimpleGraph (Fin 0)) :
    HasPathCoverAtMost G 0 := by
  refine ⟨[], by simp, ?_⟩
  constructor
  · simp
  · exact fun v ↦ Fin.elim0 v

/-- The exact statement of Erdős Problem 518 for a particular colouring. -/
def Erdos518ForType [Fintype V] (G : SimpleGraph V) : Prop :=
  HasPathCoverAtMost G (Nat.sqrt (Fintype.card V)) ∨
    HasPathCoverAtMost Gᶜ (Nat.sqrt (Fintype.card V))

/-- The exact statement of Erdős Problem 518 for a particular colouring of `Fin n`. -/
def Erdos518For (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  HasPathCoverAtMost G (Nat.sqrt n) ∨ HasPathCoverAtMost Gᶜ (Nat.sqrt n)

lemma erdos518For_iff_forType (n : ℕ) (G : SimpleGraph (Fin n)) :
    Erdos518For n G ↔ Erdos518ForType G := by
  simp [Erdos518For, Erdos518ForType]

end Erdos518
