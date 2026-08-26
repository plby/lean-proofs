/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossInnerCycle
import ErdosProblems.Erdos1091.VossInnerParity

/-! # The first four attachments in Voss's inner-cycle case -/

open SimpleGraph

namespace Erdos1091.Voss

/-- With the first three attachments in cyclic order, the fourth must
follow them, and the three intervening long-ear closures are odd. -/
theorem fourth_attachment_order_and_parity
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 5 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) (hstart : E.start = z)
    (D : G.Walk E.walk.snd E.walk.snd) (hD : D.IsCycle)
    (hDlen : D.length + 1 = E.walk.length)
    (hDout : ∀ v ∈ D.support, v ∉ C.support) (hDsup : D.support ⊆ E.walk.support)
    (hDY : D.getVert 1 = E.walk.penultimate)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) (hjN : j < C.length)
    (hiGet : C.getVert i = E.finish) (hjE : C.getVert j ∉ E.walk.support)
    (hthird : G.Adj (D.getVert 2) (C.getVert j))
    {b : V} (hbC : b ∈ C.support) (hbE : b ∉ E.walk.support)
    (hbj : b ≠ C.getVert j) (hfourth : G.Adj (D.getVert 3) b) :
    ∃ k, j < k ∧ k < C.length ∧ C.getVert k = b ∧
      Odd (E.walk.length + i) ∧ Odd (E.walk.length + (j - i)) ∧
      Odd (E.walk.length + (k - j)) := by
  have he := E.inner_closing_chord C hC hno (by omega) hmax hdegree
  have heEnds := E.edge_ne_endpoints_of_notMem (y := E.walk.penultimate)
    (E.snd_notMem (by omega : 2 ≤ E.walk.length))
  have ho₁ := E.odd_prefix_of_complement_spoke C hC.1 hC.2.1 hno (by omega)
    hstart hi (by omega) hiGet hij.le he heEnds (hDsup (D.getVert_mem_support 2))
    (hDout _ (D.getVert_mem_support 2)) hjE hthird
  have hjB : C.getVert j ≠ E.finish := fun heq => hjE (by rw [heq]; exact E.walk.end_mem_support)
  have hjA : C.getVert j ≠ E.start := fun heq => hjE (by rw [heq]; exact E.walk.start_mem_support)
  have hbB : b ≠ E.finish := fun heq => hbE (by rw [heq]; exact E.walk.end_mem_support)
  have hbA : b ≠ E.start := fun heq => hbE (by rw [heq]; exact E.walk.start_mem_support)
  have hBY : G.Adj E.finish (D.getVert 1) := by
    rw [hDY]
    exact (E.walk.adj_penultimate E.not_nil).symm
  let H := CycleArc.spokeEar D hD hDout (i := 1) (by omega)
    E.finish_mem (C.getVert_mem_support j) hjB hBY hthird
  have hHlen : H.walk.length = E.walk.length := by
    exact (CycleArc.spokeEar_length D hD hDout (i := 1) (by omega)
      E.finish_mem (C.getVert_mem_support j) hjB hBY hthird).trans hDlen
  have hHmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ H.walk.length := by
    intro P
    rw [hHlen]
    exact hmax P
  have heH := H.inner_closing_chord C hC hno (by omega) hHmax hdegree
  have heHEnds := H.edge_ne_endpoints_of_notMem (y := H.walk.penultimate)
    (H.snd_notMem (by omega : 2 ≤ H.walk.length))
  have hzB : z ≠ E.finish := by simpa only [hstart] using E.endpoints_ne
  have hzj : z ≠ C.getVert j := by simpa only [hstart] using hjA.symm
  have hzH : z ∉ H.walk.support := by
    intro hz
    rcases H.only_ends z hz C.start_mem_support with hz | hz
    · exact hzB hz
    · exact hzj hz
  have hXH : E.walk.snd ∈ H.walk.support :=
    CycleArc.mem_spokeEar_of_mem_cycle _ _ _ _ _ _ _ _ _ D.start_mem_support
  have hXout := hDout _ D.start_mem_support
  have hXz : G.Adj E.walk.snd (C.getVert 0) := by
    rw [Walk.getVert_zero]
    simpa only [hstart] using (E.walk.adj_snd E.not_nil).symm
  have ho₂ := H.odd_segment_of_complement_spoke C hC.1 hC.2.1 hno (by omega)
    hij hjN hiGet rfl (k := 0) (Or.inl (Nat.zero_le _)) heH heHEnds hXH hXout
    (by simpa only [Walk.getVert_zero] using hzH) hXz
  obtain ⟨k, hkGet, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hbC
  have hk0 : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    exact hbA (by simpa only [hk, Walk.getVert_zero, ← hstart] using hkGet.symm)
  have hkN : k < C.length := by
    by_contra h
    have hk : k = C.length := by omega
    exact hbA (by simpa only [hk, Walk.getVert_length, ← hstart] using hkGet.symm)
  have hkE : C.getVert k ∉ E.walk.support := by simpa only [hkGet] using hbE
  have hWk : G.Adj (D.getVert 3) (C.getVert k) := hkGet ▸ hfourth
  have hWi := E.external_spoke_index_not_between C hC.1 hno (by omega)
    (i := 0) (j := i) (k := k) (Nat.zero_le _) (by omega)
    (C.getVert_zero.trans hstart.symm) hiGet (by simpa only [Nat.sub_zero] using ho₁)
    he heEnds (hDsup (D.getVert_mem_support 3)) (hDout _ (D.getVert_mem_support 3)) hkE hWk
  have hik : i < k := by omega
  have hbH : b ∉ H.walk.support := by
    intro hb
    rcases H.only_ends b hb hbC with hb | hb
    · exact hbB hb
    · exact hbj hb
  have hWH : D.getVert 3 ∈ H.walk.support :=
    CycleArc.mem_spokeEar_of_mem_cycle _ _ _ _ _ _ _ _ _ (D.getVert_mem_support 3)
  have hWj := H.external_spoke_index_not_between C hC.1 hno (by omega)
    hij.le hjN hiGet rfl ho₂ heH heHEnds hWH (hDout _ (D.getVert_mem_support 3))
    (by simpa only [hkGet] using hbH) hWk
  have hjk : j < k := by omega
  let J := CycleArc.spokeEar D hD hDout (i := 2) (by omega)
    (C.getVert_mem_support j) hbC hbj hthird.symm hfourth
  have hJlen : J.walk.length = E.walk.length :=
    (CycleArc.spokeEar_length D hD hDout (i := 2) (by omega)
      (C.getVert_mem_support j) hbC hbj hthird.symm hfourth).trans hDlen
  have hJmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ J.walk.length := by
    intro P
    rw [hJlen]
    exact hmax P
  have heJ := J.inner_closing_chord C hC hno (by omega) hJmax hdegree
  have heJEnds := J.edge_ne_endpoints_of_notMem (y := J.walk.penultimate)
    (J.snd_notMem (by omega : 2 ≤ J.walk.length))
  have hzJ : z ∉ J.walk.support := by
    intro hz
    rcases J.only_ends z hz C.start_mem_support with hz | hz
    · exact hzj hz
    · exact hbA (hz.symm.trans hstart.symm)
  have hXJ : E.walk.snd ∈ J.walk.support :=
    CycleArc.mem_spokeEar_of_mem_cycle _ _ _ _ _ _ _ _ _ D.start_mem_support
  have ho₃ := J.odd_segment_of_complement_spoke C hC.1 hC.2.1 hno (by omega)
    hjk hkN rfl hkGet (k := 0) (Or.inl (Nat.zero_le _)) heJ heJEnds hXJ hXout
    (by simpa only [Walk.getVert_zero] using hzJ) hXz
  refine ⟨k, hjk, hkN, hkGet, ho₁, ?_, ?_⟩
  · simpa only [hHlen] using ho₂
  · simpa only [hJlen] using ho₃

#print axioms fourth_attachment_order_and_parity

end Erdos1091.Voss
