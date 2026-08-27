/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeTerminalRootSuccess
import ErdosProblems.Erdos207.LocalizedNewRootedBlocker

/-!
# Internal-edge success from newly activated rooted caps

The candidate family is legal over the old packing.  Consequently only
forbidden configurations activated by triangles selected during the current
stage can block the terminal internal-edge process.
-/

namespace Erdos207

open Finset

noncomputable section

theorem internalEdge_terminal_notFailed_of_localizedNewRootedCap
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {bits : Sym2 V → Bool} {S : Sym2 V → Finset V}
    {E : Finset (Sym2 V)}
    {hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2}
    {D a d R k : ℕ} {Plegal P0 A : TripleSystemOn V}
    {z : InternalEdgeGreedyStateOn V}
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (havailable : ∀ T ∈ A, ¬ CompletesForbidden F Plegal T)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hsupply : ∀ e ∈ E,
      a + D ≤ (activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 bits).card)
    (hSU : ∀ e, e ∈ E.toList → S e ⊆ U)
    (hA : ∀ e (he : e ∈ E.toList) (w : V), ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (houter e
            (by simpa only [Finset.mem_toList] using he)).1
              (h ▸ hSU e he hw),
          fun h ↦ (houter e
            (by simpa only [Finset.mem_toList] using he)).2
              (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A)
    (hscalar : 4 * d + R * k ≤ a)
    (hinv : InternalEdgeProcessInvariant F P0 E.toList E.toList.length z)
    (hambient : z.chosen ⊆ P0 ∪ A)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 z.chosen)
    (hfailure : InternalEdgeFailureCertificate F G U bits S E.toList hne
      D E.toList.length z)
    (hroot : NewRootedActiveCapsGoodIn F Plegal z.chosen A U R) :
    z.failed = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hfailed
  obtain ⟨j, hj, _hjlen, huncovered, hsmall⟩ := hfailure hfailed
  let e := E.toList.get ⟨j, hj⟩
  have heList : e ∈ E.toList := List.get_mem E.toList ⟨j, hj⟩
  have heE : e ∈ E := by simpa only [Finset.mem_toList] using heList
  have hleave : (leaveGraph z.chosen).Adj e.out.1 e.out.2 := by
    apply leaveGraph_adj.mpr
    refine ⟨hne e heList, ?_⟩
    rintro ⟨T, hT, hu, hv, hneT⟩
    exact huncovered (coveredGraph_adj.mpr ⟨T, hT, hu, hv, hneT⟩)
  obtain ⟨hdu, hdv⟩ := new_endpoint_stars_le_of_scheduled_incidence
    (hinv.1.isPacking hpacking0) houter huse hincidence heE
  have hedgeFull :
      (edgeBlockedThirdVertices A z.chosen hleave.ne).card ≤ 4 * d := by
    have hbound := card_edgeBlockedThirdVertices_le_two_mul_new_star_add
      (hinv.1.isPacking hpacking0) hinitial hleave
    omega
  have hedge :
      (edgeBlockedThirdVerticesIn A z.chosen hleave.ne (S e)).card ≤
        4 * d := by
    apply (card_le_card ?_).trans hedgeFull
    intro w hw
    exact (mem_edgeBlockedThirdVerticesIn_iff.mp hw).1
  have hrootE :
      (rootedNewActiveForbiddenConfigurationsIn
        F Plegal z.chosen A e.out.1 e.out.2 (S e)).card ≤ R := by
    exact (hroot.mono (hSU e heList)) e.out.1 e.out.2 (hne e heList)
  have hforbidden :
      (forbiddenBlockedThirdVerticesIn F A z.chosen hleave.ne (S e)).card ≤
        R * k := by
    apply (card_forbiddenBlockedThirdVerticesIn_le_mul_rooted_new_activeIn
      (F := F) (Pold := Plegal) (P := z.chosen) (A := A)
      hleave.ne (S e) havailable hfamily).trans
    exact Nat.mul_le_mul_right k hrootE
  have hblocked :
      (edgeBlockedThirdVerticesIn A z.chosen hleave.ne (S e) ∪
        forbiddenBlockedThirdVerticesIn F A z.chosen hleave.ne (S e)).card ≤
        a := by
    have hunion := card_union_le
      (edgeBlockedThirdVerticesIn A z.chosen hleave.ne (S e))
      (forbiddenBlockedThirdVerticesIn F A z.chosen hleave.ne (S e))
    omega
  have hcount :
      (edgeBlockedThirdVerticesIn A z.chosen hleave.ne (S e) ∪
          forbiddenBlockedThirdVerticesIn F A z.chosen hleave.ne
            (S e)).card + D ≤
        (activeReserveWedgeVertices G U (S e)
          e.out.1 e.out.2 bits).card :=
    (Nat.add_le_add_right hblocked D).trans (hsupply e heE)
  have hA' : ∀ w, ∀ hwS : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (houter e heE).1 (h ▸ hSU e heList hwS),
          fun h ↦ (houter e heE).2 (h ▸ hSU e heList hwS)⟩
      thirdVertexTriple hleave.ne w' ∈ A := by
    intro w hwS
    have hp : hleave.ne = hne e heList := Subsingleton.elim _ _
    rw [hp]
    exact hA e heList w hwS
  have hlegal :=
    card_activeReserveLegalThirdVertices_ge_of_localized_blocked_add_le
      (hinv.1.isPacking hpacking0) (hinv.1.avoidsForbidden havoid0)
      hleave (houter e heE).1 (houter e heE).2 (hSU e heList) bits hA' D
      hcount
  have hp : hleave.ne = hne e heList := Subsingleton.elim _ _
  rw [hp] at hlegal
  exact (not_lt_of_ge hlegal) (by simpa only [e] using hsmall)

end

end Erdos207
