/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedArcSubdivisionContraction
import ErdosProblems.Erdos599.DirectedMengerSupportTransport

/-!
# Contraction of the full Menger pair after directed-arc subdivision

This is a reduction of the exact theorem, not a cardinality-only statement.
The separator is projected along with the path packing, and uniqueness of
its intersection with every contracted packed path is proved explicitly by
the support-transport theorem.
-/

noncomputable section

namespace Erdos599
namespace DirectedArcSubdivision

open Bridge DirectedPath Set

universe u

variable {V : Type u} {D : Digraph V} {A B : Set V}

/-- Lift a bundled original source--target path to the subdivided graph. -/
def liftABPath (p : DirectedABPath D A B) :
    DirectedABPath (graph D) (Vertex.original '' A) (Vertex.original '' B) where
  path := liftFinitePath p.path
  start_mem := ⟨p.path.start, p.start_mem, rfl⟩
  finish_mem := ⟨p.path.finish, p.finish_mem, rfl⟩

/-- Contract a subdivided source--target path.  Its endpoint memberships
provide the original endpoints; choice is used only to extract them. -/
def contractABPath
    (p : DirectedABPath (graph D) (Vertex.original '' A) (Vertex.original '' B)) :
    DirectedABPath D A B := by
  classical
  let a : V := Classical.choose p.start_mem
  let b : V := Classical.choose p.finish_mem
  have ha : a ∈ A ∧ Vertex.original a = p.path.start :=
    Classical.choose_spec p.start_mem
  have hb : b ∈ B ∧ Vertex.original b = p.path.finish :=
    Classical.choose_spec p.finish_mem
  refine
    { path := contractFinitePath p.path ha.2.symm hb.2.symm
      start_mem := ?_
      finish_mem := ?_ }
  · simpa only [contractFinitePath_start] using ha.1
  · simpa only [contractFinitePath_finish] using hb.1

/-- Contracted support is exactly the original-vertex part of the old path. -/
@[simp] theorem mem_supportSet_contractABPath
    (p : DirectedABPath (graph D) (Vertex.original '' A) (Vertex.original '' B))
    (x : V) :
    x ∈ (contractABPath p).supportSet ↔ Vertex.original x ∈ p.supportSet := by
  unfold contractABPath DirectedABPath.supportSet
  exact mem_support_contractFinitePath_iff p.path
    (Classical.choose_spec p.start_mem).2.symm
    (Classical.choose_spec p.finish_mem).2.symm

/-- No separator point is lost by projection from a subdivided packed path. -/
theorem project_mem_supportSet_contractABPath
    (p : DirectedABPath (graph D) (Vertex.original '' A) (Vertex.original '' B))
    {z : Vertex D} (hz : z ∈ p.supportSet) :
    project z ∈ (contractABPath p).supportSet := by
  unfold contractABPath DirectedABPath.supportSet
  exact project_mem_support_contractFinitePath p.path
    (Classical.choose_spec p.start_mem).2.symm
    (Classical.choose_spec p.finish_mem).2.symm hz

theorem project_mem_supportSet_of_liftABPath
    (p : DirectedABPath D A B) {z : Vertex D}
    (hz : z ∈ (liftABPath p).supportSet) : project z ∈ p.supportSet :=
  project_mem_of_mem_liftFinitePath p.path hz

/-- The exact directed infinite Menger conclusion for the subdivided graph
implies that conclusion for the original graph, with no graph-size bound. -/
theorem directedMenger_of_subdivision
    (h : DirectedMengerConclusion (graph D)
      (Vertex.original '' A) (Vertex.original '' B)) :
    DirectedMengerConclusion D A B :=
  directedMengerConclusion_of_support_transport Vertex.original project
    liftABPath contractABPath
    (fun p x hx ↦ (mem_supportSet_contractABPath p x).1 hx)
    (fun p _ hz ↦ project_mem_supportSet_contractABPath p hz)
    (fun p _ hz ↦ project_mem_supportSet_of_liftABPath p hz) h

#print axioms contractABPath
#print axioms directedMenger_of_subdivision

end DirectedArcSubdivision
end Erdos599

