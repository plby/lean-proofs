/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossEarShift
import ErdosProblems.Erdos1091.VossCycleArcs

/-!
# Graph-level return-edge parity arguments

These are the actual cycle constructions supplying the symbolic length
equations in Voss's final placement cases.
-/

open SimpleGraph

namespace Erdos1091.Voss

/-- Case 2(a)'s first reduction. An internal chord together with an external
return forces both rim arcs through the far attachment to be single edges. -/
theorem rim_arcs_eq_one_of_internal_chord_and_return
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hstart : E.start = z) {j k : ℕ} (hj : 0 < j) (hjk : j < k) (hk : k < C.length)
    (hfinish : C.getVert k = E.finish)
    (hreturn : G.Adj E.walk.snd (C.getVert j))
    {u v : V} (he : E.walk.IsChord s(u, v)) (huS : u ∉ C.support) (hvS : v ∉ C.support) :
    k - j = 1 ∧ C.length - k = 1 ∧ Even (E.walk.length - 2) := by
  have hX : E.walk.snd ∉ C.support := E.snd_notMem (by omega)
  have hDmem := C.getVert_mem_support j
  have hDz : C.getVert j ≠ z := by
    intro heq
    have := (hC.1.getVert_endpoint_iff (by omega : j ≤ C.length)).mp heq
    omega
  have hDs : C.getVert j ≠ E.start := by simpa only [hstart] using hDz
  have hDf : C.getVert j ≠ E.finish := by
    intro heq
    have hidx : j = k := hC.1.getVert_injOn'
      (show j ≤ C.length - 1 by omega) (show k ≤ C.length - 1 by omega)
      (heq.trans hfinish.symm)
    omega
  have hDout : C.getVert j ∉ E.walk.support := by
    intro hD
    rcases E.only_ends _ hD hDmem with heq | heq
    · exact hDs heq
    · exact hDf heq
  have hFz : E.finish ≠ z := by
    intro heq
    have := (hC.1.getVert_endpoint_iff hk.le).mp (hfinish.trans heq)
    omega
  let q₁ := (C.take k).reverse.copy hfinish hstart.symm
  have hq₁ : q₁.IsPath := (Walk.isPath_copy _ _ _).mpr (hC.1.isPath_take hk).reverse
  have hq₁sup : q₁.support = (C.take k).reverse.support := Walk.support_copy _ _ _
  have hq₁C : ∀ w ∈ q₁.support, w ∈ C.support := by
    intro w hw
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse, Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have hDq₁ : C.getVert j ∈ q₁.support := by
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse]
    have hm := (C.take k).getVert_mem_support j
    simpa only [Walk.take_getVert, Nat.min_eq_right hjk.le] using hm
  have hq₁len : q₁.length = k := by
    simp only [q₁, Walk.length_copy, Walk.length_reverse, Walk.take_length, Nat.min_eq_left hk.le]
  have heven₁ := E.even_append_of_chord_and_cross (by omega) q₁ hq₁ hq₁C hno he
    (E.edge_ne_endpoints_of_notMem huS) (E.walk.getVert_mem_support 1) hX
    hDq₁ hDs hDf hreturn
  let F := E.replaceStart hDmem hDf hreturn.symm
  have huStart : u ≠ E.start := fun heq => huS (by rw [heq]; exact E.start_mem)
  have hvStart : v ≠ E.start := fun heq => hvS (by rw [heq]; exact E.start_mem)
  have heF : F.walk.IsChord s(u, v) :=
    E.isChord_replaceStart hDmem hDf hreturn.symm hDout he huStart hvStart
  have hFlen : F.walk.length = E.walk.length := E.replaceStart_length _ _ _
  have hFsnd : F.walk.snd = E.walk.snd := E.replaceStart_snd _ _ _
  let q₂ := (CycleArc.wrap C k j).copy hfinish rfl
  have hq₂ : q₂.IsPath := (Walk.isPath_copy _ _ _).mpr (CycleArc.wrap_isPath C hC.1 hjk hk)
  have hq₂sup : q₂.support = (CycleArc.wrap C k j).support := Walk.support_copy _ _ _
  have hq₂C : ∀ w ∈ q₂.support, w ∈ C.support := by
    intro w hw
    exact CycleArc.wrap_support_subset C k j w (hq₂sup ▸ hw)
  have hzq₂ : z ∈ q₂.support := by
    rw [hq₂sup]
    simpa only [Walk.getVert_zero] using CycleArc.getVert_mem_wrap_of_le_end C k j 0 (Nat.zero_le _)
  have hq₂len : q₂.length = C.length - k + j :=
    (Walk.length_copy _ _ _).trans (CycleArc.wrap_length C k j (by omega))
  have hXz : G.Adj F.walk.snd z := by
    rw [hFsnd]
    simpa only [hstart] using (E.walk.adj_snd E.not_nil).symm
  have hFX : F.walk.snd ∉ C.support := by simpa only [hFsnd] using hX
  have heven₂ := F.even_append_of_chord_and_cross (by omega) q₂ hq₂ hq₂C hno heF
    (F.edge_ne_endpoints_of_notMem huS) (F.walk.getVert_mem_support 1) hFX
    hzq₂ hDz.symm hFz.symm hXz
  have hpLen : (C.take j).length = j := by
    rw [Walk.take_length, Nat.min_eq_left (by omega : j ≤ C.length)]
  have hpC : ∀ w ∈ (C.take j).support, w ∈ C.support := by
    intro w hw
    rw [Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have hmin : Odd (j + 2) → j + (k - j) + (C.length - k) ≤ j + 2 := by
    intro hodd
    have hoddj : Odd (C.take j).length := by
      rw [hpLen, Nat.odd_iff]
      rw [Nat.odd_iff] at hodd
      omega
    have hXz' : G.Adj E.walk.snd z := by simpa only [hFsnd] using hXz
    have hm := hC.le_odd_arc_length_add_two (C.take j) (hC.1.isPath_take (by omega))
      (by omega) hpC hX hXz' hreturn hoddj
    omega
  apply one_external_return_parity (a := j) (b := k - j) (c := C.length - k)
    (s := E.walk.length - 2) (by omega) (by omega) (by omega) ?_ ?_ ?_ hmin
  · have hsum : j + (k - j) + (C.length - k) = C.length := by omega
    rw [hsum]
    exact hC.2.1
  · have heq : E.walk.length - 2 + 2 + j + (k - j) = E.walk.length + q₁.length := by omega
    rwa [heq]
  · have heq : E.walk.length - 2 + 2 + j + (C.length - k) = F.walk.length + q₂.length := by omega
    rwa [heq]

/-- The single-edge arc conclusion expressed as ambient adjacencies. -/
theorem rim_adj_of_indexed_internal_chord_and_return
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hstart : E.start = z) {j k : ℕ} (hj : 0 < j) (hjk : j < k) (hk : k < C.length)
    (hfinish : C.getVert k = E.finish)
    (hreturn : G.Adj E.walk.snd (C.getVert j))
    {u v : V} (he : E.walk.IsChord s(u, v)) (huS : u ∉ C.support) (hvS : v ∉ C.support) :
    G.Adj E.start E.finish ∧ G.Adj (C.getVert j) E.finish ∧ Even (E.walk.length - 2) := by
  obtain ⟨hjkOne, hkOne, heven⟩ := rim_arcs_eq_one_of_internal_chord_and_return
    C hC hno E hlen hstart hj hjk hk hfinish hreturn he huS hvS
  have hjadd : j + 1 = k := by omega
  have hkadd : k + 1 = C.length := by omega
  have hAB := C.adj_getVert_succ hk
  rw [hkadd, Walk.getVert_length, hfinish] at hAB
  have hDB := C.adj_getVert_succ (i := j) (by omega)
  rw [hjadd, hfinish] at hDB
  exact ⟨by simpa only [hstart] using hAB.symm, hDB, heven⟩

theorem IsShortestOddCycle.reverse {V : Type*} {G : SimpleGraph V} {z : V}
    {C : G.Walk z z} (hC : IsShortestOddCycle C) : IsShortestOddCycle C.reverse := by
  refine ⟨hC.1.reverse, ?_, ?_⟩
  · simpa only [Walk.length_reverse] using hC.2.1
  · intro w p hp hodd
    simpa only [Walk.length_reverse] using hC.2.2 w p hp hodd

/-- The orientation-free first conclusion of Case 2(a). -/
theorem rim_adj_of_internal_chord_and_return
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    {d : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hreturn : G.Adj E.walk.snd d)
    {u v : V} (he : E.walk.IsChord s(u, v)) (huS : u ∉ C.support) (hvS : v ∉ C.support) :
    G.Adj E.start E.finish ∧ G.Adj d E.finish ∧ Even (E.walk.length - 2) := by
  classical
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  let R := C.rotate E.start E.start_mem
  have hR : IsShortestOddCycle R := hC.rotate E.start_mem
  let F := E.changeSet (T := {w | w ∈ R.support}) (by intro w; simp [R])
  have hdR : d ∈ R.support := by simpa [R] using hdC
  have hfR : E.finish ∈ R.support := by simpa [R] using E.finish_mem
  obtain ⟨j, hjget, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hdR
  obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hfR
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hds (by simpa only [hj0, Walk.getVert_zero] using hjget.symm)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    exact E.endpoints_ne (by simpa only [hk0, Walk.getVert_zero] using hkget)
  have hjlt : j < R.length := by
    by_contra h
    have hje : j = R.length := by omega
    exact hds (by simpa only [hje, Walk.getVert_length] using hjget.symm)
  have hklt : k < R.length := by
    by_contra h
    have hke : k = R.length := by omega
    exact E.endpoints_ne (by simpa only [hke, Walk.getVert_length] using hkget)
  have hjk : j ≠ k := by
    intro heq
    rw [heq] at hjget
    exact hdf (hjget.symm.trans hkget)
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hret : G.Adj F.walk.snd (R.getVert j) := hjget ▸ hreturn
    have huR : u ∉ R.support := by simpa [R] using huS
    have hvR : v ∉ R.support := by simpa [R] using hvS
    have hres := rim_adj_of_indexed_internal_chord_and_return R hR hno F hlen rfl
      hjpos hjk hklt hkget hret he huR hvR
    simpa only [F, Ear.changeSet, hjget] using hres
  · let F' := E.changeSet (T := {w | w ∈ R.reverse.support}) (by intro w; simp [R])
    have hjget' : R.reverse.getVert (R.length - j) = d := by
      rw [Walk.getVert_reverse, show R.length - (R.length - j) = j by omega, hjget]
    have hkget' : R.reverse.getVert (R.length - k) = E.finish := by
      rw [Walk.getVert_reverse, show R.length - (R.length - k) = k by omega, hkget]
    have hret : G.Adj F'.walk.snd (R.reverse.getVert (R.length - j)) := hjget' ▸ hreturn
    have huR : u ∉ R.reverse.support := by simpa [R] using huS
    have hvR : v ∉ R.reverse.support := by simpa [R] using hvS
    have hklt' : R.length - k < R.reverse.length := by
      rw [Walk.length_reverse]
      omega
    have hres := rim_adj_of_indexed_internal_chord_and_return R.reverse hR.reverse hno F' hlen rfl
      (by omega : 0 < R.length - j) (by omega : R.length - j < R.length - k)
      hklt' hkget' hret he huR hvR
    simpa only [F', Ear.changeSet, hjget'] using hres

#print axioms rim_adj_of_internal_chord_and_return

end Erdos1091.Voss
