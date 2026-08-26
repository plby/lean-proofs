/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossInnerCycle

/-! # Ears with prescribed internal paths and disjoint rim arms -/

open SimpleGraph

namespace Erdos1091.Voss.Ear

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Add two distinct attachment endpoints to a path outside the rim. -/
def ofInternalPath {x y a b : V} (p : G.Walk x y) (hp : p.IsPath)
    (hpS : ∀ v ∈ p.support, v ∉ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hax : G.Adj a x) (hyb : G.Adj y b) : Ear G S where
  start := a
  finish := b
  walk := Walk.cons hax (p.concat hyb)
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_cons, List.nodup_cons]
    refine ⟨?_, (hp.concat (fun hm => hpS b hm hb) hyb).support_nodup⟩
    intro hm
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | heq
    · exact hpS a hm ha
    · exact hab heq
  start_mem := ha
  finish_mem := hb
  endpoints_ne := hab
  only_ends := by
    intro v hv hvS
    rw [Walk.support_cons, List.mem_cons, Walk.support_concat,
      List.mem_append, List.mem_singleton] at hv
    rcases hv with heq | hv | heq
    · exact Or.inl heq
    · exact (hpS v hv hvS).elim
    · exact Or.inr heq

theorem ofInternalPath_length {x y a b : V} (p : G.Walk x y) (hp : p.IsPath)
    (hpS : ∀ v ∈ p.support, v ∉ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hax : G.Adj a x) (hyb : G.Adj y b) :
    (ofInternalPath p hp hpS ha hb hab hax hyb).walk.length = p.length + 2 := by
  simp [ofInternalPath, Walk.length_concat, Nat.add_assoc]

theorem mem_ofInternalPath_of_mem {x y a b v : V} (p : G.Walk x y) (hp : p.IsPath)
    (hpS : ∀ v ∈ p.support, v ∉ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hax : G.Adj a x) (hyb : G.Adj y b) (hv : v ∈ p.support) :
    v ∈ (ofInternalPath p hp hpS ha hb hab hax hyb).walk.support := by
  simp only [ofInternalPath, Walk.support_cons, Walk.support_concat, List.mem_cons,
    List.mem_append, List.mem_singleton]
  exact Or.inr (Or.inl hv)

/-- Insert an ear between two disjoint rim paths. All intersections are
at the prescribed endpoints, so the concatenation is still a path. -/
theorem isPath_rim_ear_rim (E : Ear G S) {a b : V}
    (p : G.Walk a E.start) (q : G.Walk E.finish b) (hp : p.IsPath) (hq : q.IsPath)
    (hpS : ∀ v ∈ p.support, v ∈ S) (hqS : ∀ v ∈ q.support, v ∈ S)
    (hpq : p.support.Disjoint q.support) : (p.append (E.walk.append q)).IsPath := by
  have hEq : (E.walk.append q).IsPath := by
    apply Erdos1105.isPath_append_of_inter_eq_end E.isPath hq
    intro v hvE hvq
    rcases E.only_ends v hvE (hqS v hvq) with hv | hv
    · exact (hpq (hv ▸ p.end_mem_support) hvq).elim
    · exact hv
  apply Erdos1105.isPath_append_of_inter_eq_end hp hEq
  intro v hvp hvEq
  rcases (Walk.mem_support_append_iff _ _).mp hvEq with hvE | hvq
  · rcases E.only_ends v hvE (hpS v hvp) with hv | hv
    · exact hv
    · exact (hpq hvp (hv ▸ q.start_mem_support)).elim
  · exact (hpq hvp hvq).elim

theorem ofInternalPath_support {x y a b v : V} (p : G.Walk x y) (hp : p.IsPath)
    (hpS : ∀ v ∈ p.support, v ∉ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hax : G.Adj a x) (hyb : G.Adj y b) :
    v ∈ (ofInternalPath p hp hpS ha hb hab hax hyb).walk.support ↔
      v = a ∨ v ∈ p.support ∨ v = b := by
  simp [ofInternalPath, Walk.support_concat]

end Erdos1091.Voss.Ear

namespace Erdos1091.Voss.CycleArc

/-- A positive index preceding a suffix cannot reappear in that suffix
of a simple cycle, even though the suffix includes the repeated base. -/
theorem getVert_notMem_drop {V : Type*} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) {r j : ℕ} (hr : 0 < r) (hrj : r < j)
    (hj : j ≤ C.length) : C.getVert r ∉ (C.drop j).support := by
  intro hm
  obtain ⟨t, ht, htlen⟩ := Walk.mem_support_iff_exists_getVert.mp hm
  rw [Walk.drop_getVert] at ht
  rw [Walk.drop_length] at htlen
  have heq : j + t = r := hC.getVert_injOn
    (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) ht
  omega

end Erdos1091.Voss.CycleArc

namespace Erdos1091.Voss.AttachmentPath

/-- Transport an attachment path across equal presentations of its rim. -/
def changeSet {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (P : AttachmentPath G S) (hST : ∀ v, v ∈ S ↔ v ∈ T) : AttachmentPath G T where
  start := P.start
  finish := P.finish
  walk := P.walk
  isPath := P.isPath
  start_mem := (hST P.start).mp P.start_mem
  finish_notMem := fun h => P.finish_notMem ((hST P.finish).mpr h)
  only_start := fun v hv hvT => P.only_start v hv ((hST v).mpr hvT)

end Erdos1091.Voss.AttachmentPath
