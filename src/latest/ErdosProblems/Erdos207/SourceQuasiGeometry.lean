/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMarking
import ErdosProblems.Erdos207.SourceLinkFanGeometry
import ErdosProblems.Erdos207.SourceRootOmissionMoment

/-! # Root constraints, fan bounds, and polynomially many quasi-moment codes -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiRootFan {V : Type*} [Fintype V] [DecidableEq V]
    (e : Sym2 V) (S : Finset V) : TripleSystemOn V :=
  univ.filter fun T ↦ ∃ u ∈ S, T.1 = insert u e.toFinset

theorem card_sourceQuasiRootFan_le
    {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V) (S : Finset V)
    (hoff : ¬ e.IsDiag) : (sourceQuasiRootFan e S).card ≤ S.card := by
  apply card_fixed_pair_inner_third_vertex_le e.toFinset S
    (Sym2.card_toFinset_of_not_isDiag e hoff)
  · intro T hT
    obtain ⟨u, _, h⟩ := (mem_filter.mp hT).2
    rw [h]
    exact subset_insert _ _
  · intro T hT v hv
    obtain ⟨u, hu, h⟩ := (mem_filter.mp hT).2
    rw [h] at hv
    have heq := (mem_insert.mp (mem_sdiff.mp hv).1).resolve_right (mem_sdiff.mp hv).2
    exact heq.symm ▸ hu

theorem SourceQuasiMarking.root_mem_fan
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x) :
    x.root ∈ sourceQuasiRootFan e S :=
  mem_filter.mpr ⟨mem_univ _, x.vertex, hx.vertex_mem, hx.root_vertices⟩

theorem SourceQuasiMarking.vertex_mem_edge
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (_hx : IsSourceQuasiMarking W F e S B x)
    {H : Finset (SourceQuasiCoordinate V)} (hH : H ⊆ x.coordinates B)
    {a : Sym2 V} (ha : a ∈ H.toRight) : x.vertex ∈ a.toFinset := by
  have hs : H.toRight ⊆ sourceQuasiSpokes B x.vertex := (subset_disjSum.mp hH).2
  obtain ⟨v, _, rfl⟩ := mem_image.mp (hs ha)
  simp

theorem SourceQuasiMarking.rooted_constraints
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    {H : Finset (SourceQuasiCoordinate V)} (hH : H ⊆ x.coordinates B) :
    sourceQuasiUnderlyingRoot H ⊆ x.system \ {x.root} ∧
      Disjoint H.toLeft.toLeft H.toLeft.toRight := by
  have hh : H.toLeft.toLeft ⊆ x.initial ∧ H.toLeft.toRight ⊆ x.later :=
    subset_disjSum.mp (subset_disjSum.mp hH).1
  rw [SourceQuasiMarking.remainder_eq hx]
  exact ⟨union_subset_union hh.1 hh.2, hx.disjoint.mono hh.1 hh.2⟩

theorem SourceQuasiMarking.coordinates_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x) :
    (x.coordinates B).card = x.system.card - 1 + B.card := by
  simp only [coordinates, card_disjSum, sourceQuasiSpokes_card, system,
    card_insert_of_notMem hx.root_not_mem, card_union_of_disjoint hx.disjoint]
  omega

theorem card_sourceQuasiMarkings_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (heB : e.toFinset ⊆ B) :
    (sourceQuasiMarkings W F e S B).card ≤ 2 ^ (j - 2) * (Fintype.card V + 1) ^ (3 * j) := by
  have hsub : (sourceQuasiMarkings W F e S B).image SourceQuasiMarking.system ⊆ F := by
    intro E hE
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hE
    exact (mem_sourceQuasiMarkings_iff.mp hx).mem_family
  have hfiber : ∀ E ∈ (sourceQuasiMarkings W F e S B).image SourceQuasiMarking.system,
      ((sourceQuasiMarkings W F e S B).filter (fun x ↦ x.system = E)).card ≤ 2 ^ (j - 2) := by
    intro E hE
    simpa only [hcard E (hsub hE)] using
      card_sourceQuasiMarkings_system_fiber_le (W := W) (S := S) hpack heB E
  apply (card_le_mul_card_image _ (2 ^ (j - 2)) hfiber).trans
  exact Nat.mul_le_mul_left _ ((card_le_card hsub).trans (card_uniform_source_family_le_polynomial F j hcard))

end

end Erdos207
