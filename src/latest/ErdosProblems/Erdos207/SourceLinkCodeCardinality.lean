/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarking
import ErdosProblems.Erdos207.SourceRootOmissionMoment

/-! # Polynomial index counts for additive-error marked link moments -/

namespace Erdos207

open Finset

noncomputable section

theorem SourceLinkMarking.coordinates_card_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) :
    (x.coordinates e).card ≤ 4 * x.system.card := by
  have ht : x.triangleCoordinates.card = x.system.card := by
    simp only [triangleCoordinates, system, card_disjSum,
      card_union_of_disjoint hx.2.2.1, card_union_of_disjoint hx.2.1, add_assoc]
  have he : (x.edgeCoordinates e).card ≤ 3 * x.candidate.card := by
    apply (card_erase_le (s := x.candidate.biUnion tripleEdgeFinset) (a := e)).trans
    apply card_biUnion_le.trans
    simp only [card_tripleEdgeFinset, sum_const, smul_eq_mul, mul_comm, le_refl]
  have hc : x.candidate.card ≤ x.system.card := card_le_card subset_union_right
  change (x.triangleCoordinates.disjSum (x.edgeCoordinates e)).card ≤ _
  rw [card_disjSum, ht]
  omega

theorem card_sourceLinkMarkings_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2) :
    (sourceLinkMarkings W F e A).card ≤ 4 ^ (j - 2) * F.card := by
  classical
  have hsub : (sourceLinkMarkings W F e A).image SourceLinkMarking.system ⊆ F := by
    intro E hE
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hE
    exact (sourceLinkUnderlyingFamily_data (mem_filter.mp hx).2.1).1
  have hfiber : ∀ E ∈ (sourceLinkMarkings W F e A).image SourceLinkMarking.system,
      ((sourceLinkMarkings W F e A).filter (fun x ↦ x.system = E)).card ≤ 4 ^ (j - 2) := by
    intro E hE
    have hb := card_sourceLinkMarkings_system_fiber_le (W := W) (e := e) (A := A) hpack E
    simpa only [hcard E (hsub hE)] using hb
  exact (card_le_mul_card_image _ (4 ^ (j - 2)) hfiber).trans
    (Nat.mul_le_mul_left _ (card_le_card hsub))

theorem card_sourceLinkMarkings_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2) :
    (sourceLinkMarkings W F e A).card ≤ 4 ^ (j - 2) * (Fintype.card V + 1) ^ (3 * j) :=
  (card_sourceLinkMarkings_le hpack hcard).trans
    (Nat.mul_le_mul_left _ (card_uniform_source_family_le_polynomial F j hcard))

end

end Erdos207
