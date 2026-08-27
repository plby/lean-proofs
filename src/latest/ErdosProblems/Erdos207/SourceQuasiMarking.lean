/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarkingWeight

/-! # Two-colour codes for proper future-pattern extension witnesses

The distinguished triangle is not a selected coordinate. The extension
vertex is recorded explicitly, and is outside the pattern vertex set.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

abbrev SourceQuasiMarking (V : Type*) [DecidableEq V] :=
  V × (TripleOn V × TripleSystemOn V × TripleSystemOn V)

def SourceQuasiMarking.vertex {V : Type*} [DecidableEq V] (x : SourceQuasiMarking V) := x.1
def SourceQuasiMarking.root {V : Type*} [DecidableEq V] (x : SourceQuasiMarking V) := x.2.1
def SourceQuasiMarking.initial {V : Type*} [DecidableEq V] (x : SourceQuasiMarking V) := x.2.2.1
def SourceQuasiMarking.later {V : Type*} [DecidableEq V] (x : SourceQuasiMarking V) := x.2.2.2

def SourceQuasiMarking.system {V : Type*} [DecidableEq V] (x : SourceQuasiMarking V) :
    TripleSystemOn V := insert x.root (x.initial ∪ x.later)

abbrev SourceQuasiCoordinate (V : Type*) [DecidableEq V] :=
  (TripleOn V ⊕ TripleOn V) ⊕ Sym2 V

def sourceQuasiSpokes {V : Type*} [DecidableEq V] (B : Finset V) (u : V) : Finset (Sym2 V) :=
  B.image (fun v ↦ s(u, v))

def SourceQuasiMarking.coordinates {V : Type*} [DecidableEq V]
    (x : SourceQuasiMarking V) (B : Finset V) : Finset (SourceQuasiCoordinate V) :=
  (x.initial.disjSum x.later).disjSum (sourceQuasiSpokes B x.vertex)

structure IsSourceQuasiMarking
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V)
    (S B : Finset V) (x : SourceQuasiMarking V) : Prop where
  vertex_mem : x.vertex ∈ S
  vertex_not_mem : x.vertex ∉ B
  root_vertices : x.root.1 = insert x.vertex e.toFinset
  pin_mem : e ∈ tripleEdgeFinset x.root
  terminal : W.level x.root = Fin.last ell
  root_not_mem : x.root ∉ x.initial ∪ x.later
  disjoint : Disjoint x.initial x.later
  later_nonempty : x.later.Nonempty
  mem_family : x.system ∈ F

def sourceQuasiMarkings
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S B : Finset V) :
    Finset (SourceQuasiMarking V) := univ.filter (IsSourceQuasiMarking W F e S B)

def sourceQuasiUnderlyingRoot {V : Type*} [DecidableEq V]
    (H : Finset (SourceQuasiCoordinate V)) : TripleSystemOn V :=
  H.toLeft.toLeft ∪ H.toLeft.toRight

theorem mem_sourceQuasiMarkings_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} :
    x ∈ sourceQuasiMarkings W F e S B ↔ IsSourceQuasiMarking W F e S B x := by
  simp only [sourceQuasiMarkings, mem_filter, mem_univ, true_and]

theorem sourceQuasiSpokes_card
    {V : Type*} [DecidableEq V] (B : Finset V) (u : V) :
    (sourceQuasiSpokes B u).card = B.card := by
  apply card_image_of_injective
  intro v w heq
  have hh : (u = u ∧ v = w) ∨ (u = w ∧ v = u) := by
    simpa only [Sym2.eq_iff] using heq
  exact hh.elim And.right (fun h ↦ h.2.trans h.1)

theorem sourceQuasiSpokes_not_isDiag
    {V : Type*} [DecidableEq V] {B : Finset V} {u : V} (hu : u ∉ B)
    {e : Sym2 V} (he : e ∈ sourceQuasiSpokes B u) : ¬ e.IsDiag := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp he
  simpa only [Sym2.mk_isDiag_iff] using (show u ≠ v from fun h ↦ hu (h.symm ▸ hv))

theorem SourceQuasiMarking.remainder_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x) :
    x.system \ {x.root} = x.initial ∪ x.later := by
  simp only [system, sdiff_singleton_eq_erase, erase_insert hx.root_not_mem]

theorem SourceQuasiMarking.later_eq_sdiff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x) :
    x.later = (x.system \ {x.root}) \ x.initial := by
  rw [SourceQuasiMarking.remainder_eq hx]
  ext T
  have hd := disjoint_left.mp hx.disjoint
  simp only [mem_union, mem_sdiff]
  constructor
  · intro hT
    exact ⟨Or.inr hT, fun hI ↦ hd hI hT⟩
  · rintro ⟨hI | hD, hnot⟩
    · exact False.elim (hnot hI)
    · exact hD

theorem SourceQuasiMarking.vertex_eq_of_root_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x x' : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    (hx' : IsSourceQuasiMarking W F e S B x') (heB : e.toFinset ⊆ B)
    (heq : x.root = x'.root) : x.vertex = x'.vertex := by
  have hm : x.vertex ∈ insert x'.vertex e.toFinset := by
    rw [← hx'.root_vertices, ← heq, hx.root_vertices]
    exact mem_insert_self _ _
  exact (mem_insert.mp hm).resolve_right (fun h ↦ hx.vertex_not_mem (heB h))

theorem card_sourceQuasiMarkings_system_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (heB : e.toFinset ⊆ B) (E : TripleSystemOn V) :
    ((sourceQuasiMarkings W F e S B).filter (fun x ↦ x.system = E)).card ≤ 2 ^ E.card := by
  calc
    _ ≤ E.powerset.card := by
      apply card_le_card_of_injOn (f := SourceQuasiMarking.initial)
      · intro x hx
        have hs := (mem_filter.mp hx).2
        exact mem_powerset.mpr (hs ▸ (subset_union_left.trans (subset_insert _ _)))
      · intro x hx x' hx' heq
        have hd := mem_sourceQuasiMarkings_iff.mp (mem_filter.mp hx).1
        have hd' := mem_sourceQuasiMarkings_iff.mp (mem_filter.mp hx').1
        have hsys : x.system = x'.system := (mem_filter.mp hx).2.trans (mem_filter.mp hx').2.symm
        have hr : x.root = x'.root :=
          (hpack x.system hd.mem_family).eq_of_common_graph_edge
            (mem_insert_self _ _) (hsys.symm ▸ mem_insert_self _ _) hd.pin_mem hd'.pin_mem
        have hv := SourceQuasiMarking.vertex_eq_of_root_eq hd hd' heB hr
        have hi : x.initial = x'.initial := heq
        have hl : x.later = x'.later := by
          rw [SourceQuasiMarking.later_eq_sdiff hd, SourceQuasiMarking.later_eq_sdiff hd', hsys, hr, hi]
        exact Prod.ext hv (Prod.ext hr (Prod.ext hi hl))
    _ = _ := card_powerset E

end

end Erdos207
