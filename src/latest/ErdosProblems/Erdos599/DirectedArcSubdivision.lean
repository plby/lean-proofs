/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Core

/-!
# Subdivision of each directed arc by two private vertices

The two new vertices belong to an oriented arc, not to an unordered edge.
Replacing `x → y` by `x → first e → second e → y` works even for loops.
Finite original paths lift by inserting these private vertices.  The
projection sends both new vertices to the tail of their original arc.
-/

namespace Erdos599
namespace DirectedArcSubdivision

open DirectedPath Set

universe u

variable {V : Type u}

abbrev Arc (D : Digraph V) := {e : V × V // D.Adj e.1 e.2}

/-- Original vertices and the two private vertices of every directed arc. -/
inductive Vertex (D : Digraph V) where
  | original (v : V)
  | first (e : Arc D)
  | second (e : Arc D)

/-- Every directed arc is replaced by its oriented three-edge chain. -/
def graph (D : Digraph V) : Digraph (Vertex D) where
  Adj
    | .original x, .first e => x = e.1.1
    | .first e, .second f => e = f
    | .second e, .original y => e.1.2 = y
    | _, _ => False

/-- Original source and target sets are embedded, not enlarged. -/
def web (G : DWeb V) : DWeb (Vertex G.graph) where
  graph := graph G.graph
  source := Vertex.original '' G.source
  target := Vertex.original '' G.target

/-- Both private vertices project to the tail of their directed arc. -/
def project {D : Digraph V} : Vertex D → V
  | .original x => x
  | .first e => e.1.1
  | .second e => e.1.1

variable {D : Digraph V}

@[simp] theorem predecessor_first (e : Arc D) (v : Vertex D) :
    (graph D).Adj v (.first e) ↔ v = .original e.1.1 := by
  cases v <;> simp [graph]

@[simp] theorem successor_first (e : Arc D) (v : Vertex D) :
    (graph D).Adj (.first e) v ↔ v = .second e := by
  cases v <;> simp [graph, eq_comm]

@[simp] theorem predecessor_second (e : Arc D) (v : Vertex D) :
    (graph D).Adj v (.second e) ↔ v = .first e := by
  cases v <;> simp [graph]

@[simp] theorem successor_second (e : Arc D) (v : Vertex D) :
    (graph D).Adj (.second e) v ↔ v = .original e.1.2 := by
  cases v <;> simp [graph, eq_comm]

/-- Lift a walk by replacing each of its edges by the private chain. -/
def liftWalk : {a b : V} → Walk D a b →
    Walk (graph D) (.original a) (.original b)
  | _, _, .nil => .nil
  | _, _, .cons h p =>
    let e : Arc D := ⟨(_, _), h⟩
    .cons (show (graph D).Adj (.original _) (.first e) from rfl)
      (.cons (show (graph D).Adj (.first e) (.second e) from rfl)
        (.cons (show (graph D).Adj (.second e) (.original _) from rfl)
          (liftWalk p)))

@[simp] theorem original_mem_liftWalk {a b : V} (p : Walk D a b) (x : V) :
    Vertex.original x ∈ (liftWalk p).support ↔ x ∈ p.support := by
  induction p with
  | nil => simp [liftWalk]
  | cons h p ih => simp [liftWalk, ih]

/-- A private first vertex on a lifted walk has its tail on the old walk. -/
theorem tail_mem_of_first_mem_liftWalk {a b : V}
    (p : Walk D a b) (e : Arc D)
    (he : Vertex.first e ∈ (liftWalk p).support) : e.1.1 ∈ p.support := by
  induction p with
  | nil => simp [liftWalk] at he
  | @cons a b c h p ih =>
    simp only [liftWalk, Walk.support_cons, List.mem_cons] at he
    rcases he with he | he | he | he
    · cases he
    · have heq : e = ⟨(a, b), h⟩ := Vertex.first.inj he
      subst e
      simp
    · cases he
    · exact List.mem_cons_of_mem _ (ih he)

/-- The same property for the private second vertex. -/
theorem tail_mem_of_second_mem_liftWalk {a b : V}
    (p : Walk D a b) (e : Arc D)
    (he : Vertex.second e ∈ (liftWalk p).support) : e.1.1 ∈ p.support := by
  induction p with
  | nil => simp [liftWalk] at he
  | @cons a b c h p ih =>
    simp only [liftWalk, Walk.support_cons, List.mem_cons] at he
    rcases he with he | he | he | he
    · cases he
    · cases he
    · have heq : e = ⟨(a, b), h⟩ := Vertex.second.inj he
      subst e
      simp
    · exact List.mem_cons_of_mem _ (ih he)

/-- Projected support of a lifted walk stays on the original walk. -/
theorem project_mem_of_mem_liftWalk {a b : V} (p : Walk D a b)
    {v : Vertex D} (hv : v ∈ (liftWalk p).support) : project v ∈ p.support := by
  cases v with
  | original x => exact (original_mem_liftWalk p x).1 hv
  | first e => exact tail_mem_of_first_mem_liftWalk p e hv
  | second e => exact tail_mem_of_second_mem_liftWalk p e hv

/-- Inserting private arc vertices preserves simplicity. -/
theorem liftWalk_isPath {a b : V} (p : Walk D a b)
    (hp : p.IsPath) : (liftWalk p).IsPath := by
  induction p with
  | nil => simp [Walk.IsPath, liftWalk]
  | @cons a b c h p ih =>
    have hnodup : (a :: p.support).Nodup := hp
    obtain ⟨ha, htail⟩ := List.nodup_cons.1 hnodup
    change (Vertex.original a :: Vertex.first ⟨(a, b), h⟩ ::
      Vertex.second ⟨(a, b), h⟩ :: (liftWalk p).support).Nodup
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_cons.2 ⟨?_, ih htail⟩⟩⟩
    · simp only [List.mem_cons]
      rintro (he | he | he)
      · cases he
      · cases he
      · exact ha ((original_mem_liftWalk p a).1 he)
    · simp only [List.mem_cons]
      rintro (he | he)
      · cases he
      · exact ha (tail_mem_of_first_mem_liftWalk p ⟨(a, b), h⟩ he)
    · intro he
      exact ha (tail_mem_of_second_mem_liftWalk p ⟨(a, b), h⟩ he)

/-- The canonical simple lift of a finite original path. -/
def liftFinitePath (p : FinitePath D) : FinitePath (graph D) where
  start := .original p.start
  finish := .original p.finish
  walk := liftWalk p.walk
  isPath := liftWalk_isPath p.walk p.isPath

@[simp] theorem original_mem_liftFinitePath (p : FinitePath D) (x : V) :
    Vertex.original x ∈ (liftFinitePath p).support ↔ x ∈ p.support :=
  original_mem_liftWalk p.walk x

theorem project_mem_of_mem_liftFinitePath (p : FinitePath D)
    {v : Vertex D} (hv : v ∈ (liftFinitePath p).support) :
    project v ∈ p.support :=
  project_mem_of_mem_liftWalk p.walk hv

#print axioms liftWalk_isPath
#print axioms project_mem_of_mem_liftFinitePath

end DirectedArcSubdivision
end Erdos599
