/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftWedgeCandidates

/-! # Terminal internal-cover success from pair loss and actual left-moment caps -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem internalEdge_terminal_notFailed_of_left_caps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} {G Γ : SimpleGraph V} {U : Finset V}
    {bits : Sym2 V → Bool} {S : Sym2 V → Finset V} {E : Finset (Sym2 V)}
    {hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2} {threshold pairCap leftCap : ℕ}
    {I D A : TripleSystemOn V} {z : InternalEdgeGreedyStateOn V}
    (hclass : z.chosen = I ∪ D) (hpacking : IsPackingOn z.chosen) (havoid : AvoidsForbidden z.chosen F)
    (hbase : G ≤ Γ) (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (hS : ∀ e ∈ E, S e ⊆ U)
    (hA : ∀ e (he : e ∈ E.toList) (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ S e → thirdVertexTriple (hne e he) w ∈ A)
    (hlevel : ∀ T ∈ A, W.level T = Fin.last ell)
    (hinitial : ∀ T ∈ A, ¬ CompletesForbidden F I T)
    (hsupply : ∀ e ∈ E, pairCap+leftCap+threshold ≤
      (activeReserveWedgeVertices G U (S e) e.out.1 e.out.2 bits).card)
    (hpair : ∀ e (he : e ∈ E.toList),
      (edgeBlockedThirdVertices A z.chosen (hne e he)).card ≤ pairCap)
    (hleft : ∀ e ∈ E,
      (sourceLeftObstructedVertices W F e U Γ I D (reserveEdges G U bits)).card ≤ leftCap)
    (hfailure : InternalEdgeFailureCertificate F G U bits S E.toList hne threshold E.toList.length z) :
    z.failed = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hfailed
  obtain ⟨j, hj, _, huncovered, hsmall⟩ := hfailure hfailed
  let e := E.toList.get ⟨j, hj⟩
  have heList : e ∈ E.toList := List.get_mem E.toList ⟨j, hj⟩
  have heE : e ∈ E := by simpa only [mem_toList] using heList
  have hu : ¬ (coveredGraph (I ∪ D)).Adj e.out.1 e.out.2 := by
    simpa only [hclass] using huncovered
  have hpack : IsPackingOn (I ∪ D) := hclass ▸ hpacking
  have hav : AvoidsForbidden (I ∪ D) F := hclass ▸ havoid
  have hc := card_activeReserveWedge_le_legal_add_pair_add_left W F G Γ U (S e) I D A
    (hne e heList) bits hpack hav hu (houter e heE).1 (houter e heE).2 (hS e heE) hbase
    (hA e heList) hlevel hinitial
  have heout : s(e.out.1, e.out.2) = e := by simpa only [Sym2.mk] using e.out_eq
  rw [heout] at hc
  have hpair' : (edgeBlockedThirdVertices A (I ∪ D) (hne e heList)).card ≤ pairCap := by
    simpa only [hclass] using hpair e heList
  have hleft' := hleft e heE
  have hsupply' := hsupply e heE
  have hsmall' : (activeReserveLegalThirdVertices F G U (S e) bits (I ∪ D)
      e.out.1 e.out.2 (hne e heList)).card < threshold := by
    simpa only [hclass] using hsmall
  omega

theorem internalEdge_terminal_notFailed_of_scheduled_left_cap
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} {G Γ : SimpleGraph V} {U : Finset V}
    {bits : Sym2 V → Bool} {S : Sym2 V → Finset V} {E : Finset (Sym2 V)}
    {hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2} {threshold d leftCap : ℕ}
    {I D P0 A : TripleSystemOn V} {z : InternalEdgeGreedyStateOn V}
    (hclass : z.chosen = I ∪ D) (hpacking : IsPackingOn z.chosen) (havoid : AvoidsForbidden z.chosen F)
    (hbase : G ≤ Γ) (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (hS : ∀ e ∈ E, S e ⊆ U)
    (hA : ∀ e (he : e ∈ E.toList) (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ S e → thirdVertexTriple (hne e he) w ∈ A)
    (hlevel : ∀ T ∈ A, W.level T = Fin.last ell)
    (hinitial : ∀ T ∈ A, ¬ CompletesForbidden F I T)
    (hinitialPair : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 z.chosen)
    (hsupply : ∀ e ∈ E, 4*d+leftCap+threshold ≤
      (activeReserveWedgeVertices G U (S e) e.out.1 e.out.2 bits).card)
    (hleft : ∀ e ∈ E,
      (sourceLeftObstructedVertices W F e U Γ I D (reserveEdges G U bits)).card ≤ leftCap)
    (hfailure : InternalEdgeFailureCertificate F G U bits S E.toList hne threshold E.toList.length z) :
    z.failed = false := by
  by_cases hfailed : z.failed = true
  · obtain ⟨j, hj, _, huncovered, hsmall⟩ := hfailure hfailed
    let e := E.toList.get ⟨j, hj⟩
    have heList : e ∈ E.toList := List.get_mem E.toList ⟨j, hj⟩
    have heE : e ∈ E := by simpa only [mem_toList] using heList
    have hleave : (leaveGraph z.chosen).Adj e.out.1 e.out.2 := by
      exact ⟨hne e heList, fun h ↦ huncovered (coveredGraph_adj.mpr h)⟩
    obtain ⟨hdu, hdv⟩ := new_endpoint_stars_le_of_scheduled_incidence hpacking houter huse hincidence heE
    have hp := card_edgeBlockedThirdVertices_le_two_mul_new_star_add hpacking hinitialPair hleave
    have hp' : (edgeBlockedThirdVertices A (I ∪ D) (hne e heList)).card ≤ 4*d := by
      have hb : (edgeBlockedThirdVertices A z.chosen hleave.ne).card ≤ 4*d := by omega
      simpa only [hclass] using hb
    have hu : ¬ (coveredGraph (I ∪ D)).Adj e.out.1 e.out.2 := by simpa only [hclass] using huncovered
    have hc := card_activeReserveWedge_le_legal_add_pair_add_left W F G Γ U (S e) I D A
      (hne e heList) bits (hclass ▸ hpacking) (hclass ▸ havoid) hu (houter e heE).1 (houter e heE).2
      (hS e heE) hbase (hA e heList) hlevel hinitial
    have heout : s(e.out.1, e.out.2) = e := by simpa only [Sym2.mk] using e.out_eq
    rw [heout] at hc
    have hl := hleft e heE
    have hs := hsupply e heE
    have hs' : (activeReserveLegalThirdVertices F G U (S e) bits (I ∪ D)
        e.out.1 e.out.2 (hne e heList)).card < threshold := by simpa only [hclass] using hsmall
    omega
  · exact Bool.eq_false_of_not_eq_true hfailed

end

end Erdos207
