/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossReturnParity
import ErdosProblems.Erdos1091.VossSmallCycles

/-! # The return to the initial attachment in Voss's Case 2(b) -/

open SimpleGraph

namespace Erdos1091.Voss

/-- The three concrete doubly-chorded cycles of Case 2(b) force the
shortest odd cycle to be a triangle. -/
theorem triangle_of_return_to_initial_indexed
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hstart : E.start = z) {j k : ℕ} (hj : 0 < j) (hjk : j < k) (hk : k < C.length)
    (hfinish : C.getVert k = E.finish)
    (hreturn : G.Adj E.walk.snd (C.getVert j))
    (hYA : G.Adj E.walk.penultimate E.start)
    (hnotYA : s(E.walk.penultimate, E.start) ∉ E.walk.edges) :
    C.length = 3 ∧ j = 1 ∧ k = 2 := by
  have hX := E.snd_notMem (by omega : 2 ≤ E.walk.length)
  have hY := E.penultimate_notMem (by omega : 2 ≤ E.walk.length)
  have hDmem := C.getVert_mem_support j
  have hDz : C.getVert j ≠ z := by
    intro heq
    have := (hC.1.getVert_endpoint_iff (by omega : j ≤ C.length)).mp heq
    omega
  have hDs : C.getVert j ≠ E.start := by simpa only [hstart] using hDz
  have hDf : C.getVert j ≠ E.finish := by
    intro heq
    have hi : j = k := hC.1.getVert_injOn'
      (show j ≤ C.length - 1 by omega) (show k ≤ C.length - 1 by omega)
      (heq.trans hfinish.symm)
    omega
  have hFz : E.finish ≠ z := by
    intro heq
    have := (hC.1.getVert_endpoint_iff hk.le).mp (hfinish.trans heq)
    omega
  have hDout : C.getVert j ∉ E.walk.support := by
    intro hd
    rcases E.only_ends _ hd hDmem with heq | heq
    · exact hDs heq
    · exact hDf heq
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
  have heOld : E.walk.IsChord s(E.walk.penultimate, E.start) :=
    ⟨hYA, hnotYA, E.walk.getVert_mem_support _, E.walk.start_mem_support⟩
  have heven₁ := E.even_append_of_chord_and_cross (by omega) q₁ hq₁ hq₁C hno heOld
    (E.edge_ne_endpoints_of_notMem hY) (E.walk.getVert_mem_support 1) hX
    hDq₁ hDs hDf hreturn
  let F := E.replaceStart hDmem hDf hreturn.symm
  have hFlen : F.walk.length = E.walk.length := E.replaceStart_length _ _ _
  have hFX : F.walk.snd = E.walk.snd := E.replaceStart_snd _ _ _
  have hFY : F.walk.penultimate = E.walk.penultimate := E.replaceStart_penultimate (by omega) _ _ _
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
    rw [hFX]
    simpa only [hstart] using (E.walk.adj_snd E.not_nil).symm
  have hYz : G.Adj F.walk.penultimate z := by simpa only [hFY, hstart] using hYA
  have hne : s(F.walk.snd, z) ≠ s(F.walk.penultimate, z) := by
    intro heq
    have heq' : s(z, F.walk.snd) = s(z, F.walk.penultimate) :=
      Sym2.eq_swap.trans (heq.trans Sym2.eq_swap)
    exact (F.snd_ne_penultimate (by omega)) ((Sym2.mkEmbedding z).injective heq')
  have heven₂ := F.even_append_of_two_cross_edges (by omega) q₂ hq₂ hq₂C hno
    (F.walk.getVert_mem_support 1) (by simpa only [hFX] using hX)
    (F.walk.getVert_mem_support _) (by simpa only [hFY] using hY)
    hzq₂ hDz.symm hFz.symm hzq₂ hDz.symm hFz.symm hXz hYz hne
  have hAY : G.Adj E.start F.reverse.walk.snd := by
    simpa only [Ear.reverse, Walk.snd_reverse, hFY] using hYA.symm
  let H₀ := F.reverse.replaceStart E.start_mem hDs.symm hAY
  let H := H₀.reverse
  have hHlen : H.walk.length = E.walk.length := by
    calc
      _ = H₀.walk.length := Walk.length_reverse _
      _ = F.reverse.walk.length := F.reverse.replaceStart_length _ _ _
      _ = F.walk.length := Walk.length_reverse _
      _ = E.walk.length := hFlen
  have hAout : E.start ∉ F.reverse.walk.support := by
    simpa only [Ear.reverse, Walk.support_reverse, List.mem_reverse] using
      E.old_start_notMem_replaceStart hDmem hDf hreturn.symm hDs
  have hXs : E.walk.snd ≠ E.start := fun heq => hX (by rw [heq]; exact E.start_mem)
  have hXf : E.walk.snd ≠ E.finish := fun heq => hX (by rw [heq]; exact E.finish_mem)
  have hXinF : E.walk.snd ∈ F.walk.support :=
    E.mem_replaceStart_of_mem_ne_start _ _ _ (E.walk.getVert_mem_support 1) hXs
  have hXinFr : E.walk.snd ∈ F.reverse.walk.support := by
    simpa only [Ear.reverse, Walk.support_reverse, List.mem_reverse] using hXinF
  have hXnotFY : E.walk.snd ≠ F.reverse.walk.snd := by
    simpa only [Ear.reverse, Walk.snd_reverse, hFY] using E.snd_ne_penultimate hlen
  have heH₀ : H₀.walk.IsChord s(E.start, E.walk.snd) :=
    F.reverse.isChord_from_new_start E.start_mem hDs.symm hAY hAout hXinFr hXf hXnotFY
      (E.walk.adj_snd E.not_nil)
  have heH : H.walk.IsChord s(E.walk.snd, E.start) := by
    have he := Ear.isChord_reverse H₀.walk heH₀
    change H₀.walk.reverse.IsChord s(E.walk.snd, E.start)
    simpa only [Sym2.eq_swap] using he
  have hH₀Y : H₀.walk.snd = E.walk.penultimate := by
    exact (F.reverse.replaceStart_snd E.start_mem hDs.symm hAY).trans
      ((Walk.snd_reverse F.walk).trans hFY)
  have hYinH : E.walk.penultimate ∈ H.walk.support := by
    change E.walk.penultimate ∈ H₀.walk.reverse.support
    rw [Walk.support_reverse, List.mem_reverse, ← hH₀Y]
    exact H₀.walk.getVert_mem_support 1
  have hbase : C.getVert 0 = E.start := C.getVert_zero.trans hstart.symm
  let q₃ := (CycleArc.wrap C j 0).reverse.copy hbase rfl
  have hq₃ : q₃.IsPath := (Walk.isPath_copy _ _ _).mpr
    (CycleArc.wrap_isPath C hC.1 hj (by omega)).reverse
  have hq₃sup : q₃.support = (CycleArc.wrap C j 0).reverse.support := Walk.support_copy _ _ _
  have hq₃C : ∀ w ∈ q₃.support, w ∈ C.support := by
    intro w hw
    rw [hq₃sup, Walk.support_reverse, List.mem_reverse] at hw
    exact CycleArc.wrap_support_subset C j 0 w hw
  have hBq₃ : E.finish ∈ q₃.support := by
    rw [hq₃sup, Walk.support_reverse, List.mem_reverse, ← hfinish]
    exact CycleArc.getVert_mem_wrap_of_le C j 0 k hjk.le
  have hq₃len : q₃.length = C.length - j := by
    simp only [q₃, Walk.length_copy, Walk.length_reverse,
      CycleArc.wrap_length C j 0 (Nat.zero_le _), Nat.add_zero]
  have heven₃ := H.even_append_of_chord_and_cross (by omega) q₃ hq₃ hq₃C hno heH
    (H.edge_ne_endpoints_of_notMem hX) hYinH hY hBq₃ hDf.symm E.endpoints_ne.symm
    (E.walk.adj_penultimate E.not_nil)
  have hpLen : (C.take j).length = j := by
    rw [Walk.take_length, Nat.min_eq_left (by omega : j ≤ C.length)]
  have hpC : ∀ w ∈ (C.take j).support, w ∈ C.support := by
    intro w hw
    rw [Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have hrLen : (C.drop k).length = C.length - k := Walk.drop_length _ _
  have hrC : ∀ w ∈ (C.drop k).support, w ∈ C.support := by
    intro w hw
    rw [Walk.drop_support_eq_support_drop_min] at hw
    exact List.mem_of_mem_drop hw
  have hXz' : G.Adj E.walk.snd z := by simpa only [hFX] using hXz
  have hYz' : G.Adj E.walk.penultimate z := by simpa only [hFY] using hYz
  have hYB : G.Adj E.walk.penultimate (C.getVert k) := by
    rw [hfinish]
    exact E.walk.adj_penultimate E.not_nil
  have hsum : j + (k - j) + (C.length - k) = C.length := by omega
  have hminA : Odd (j + 2) → j + (k - j) + (C.length - k) ≤ j + 2 := by
    intro ho
    have hpOdd : Odd (C.take j).length := by
      rw [hpLen, Nat.odd_iff]
      rw [Nat.odd_iff] at ho
      omega
    have hm := hC.le_odd_arc_length_add_two (C.take j) (hC.1.isPath_take (by omega))
      (by omega) hpC hX hXz' hreturn hpOdd
    omega
  have hminC : Odd (C.length - k + 2) →
      j + (k - j) + (C.length - k) ≤ C.length - k + 2 := by
    intro ho
    have hrOdd : Odd (C.drop k).length := by
      rw [hrLen, Nat.odd_iff]
      rw [Nat.odd_iff] at ho
      omega
    have hm := hC.le_odd_arc_length_add_two (C.drop k) (hC.1.isPath_drop (by omega))
      (by omega) hrC hY hYB hYz' hrOdd
    omega
  obtain ⟨haOne, hbOne, hcOne, _⟩ := return_to_initial_parity
    (a := j) (b := k - j) (c := C.length - k) (s := E.walk.length - 2)
    (by omega) (by omega) (by omega) (by rw [hsum]; exact hC.2.1)
    (by
      have heq : E.walk.length - 2 + 2 + j + (C.length - k) = F.walk.length + q₂.length := by omega
      rwa [heq])
    (by
      have heq : E.walk.length - 2 + 2 + (k - j) + (C.length - k) =
          H.walk.length + q₃.length := by omega
      rwa [heq])
    (by
      have heq : E.walk.length - 2 + 2 + j + (k - j) = E.walk.length + q₁.length := by omega
      rwa [heq]) hminA hminC
  omega

/-- Voss's Case 2(b): a terminal return to the initial attachment together
with an external return at the first inner vertex is impossible. -/
theorem mixed_returns_to_initial_impossible
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    {d : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hreturn : G.Adj E.walk.snd d) (hYA : G.Adj E.walk.penultimate E.start)
    (hnotYA : s(E.walk.penultimate, E.start) ∉ E.walk.edges) : False := by
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  obtain ⟨R, hRcycle, hRlen, hRsupp, j, k, hj, hjk, hk, hjget, hkget⟩ :=
    CycleArc.exists_oriented_three C hC.1 E.start_mem hdC E.finish_mem hds E.endpoints_ne hdf
  have hR : IsShortestOddCycle R := by
    refine ⟨hRcycle, ?_, ?_⟩
    · rw [hRlen]; exact hC.2.1
    · intro w p hp ho
      rw [hRlen]
      exact hC.2.2 w p hp ho
  let F := E.changeSet (T := {v | v ∈ R.support}) (fun v => (hRsupp v).symm)
  have hret : G.Adj F.walk.snd (R.getVert j) := hjget ▸ hreturn
  obtain ⟨hRthree, hjOne, hkTwo⟩ := triangle_of_return_to_initial_indexed
    R hR hno F hlen rfl hj hjk hk hkget hret hYA hnotYA
  have hdIndex : R.getVert 1 = d := by simpa only [hjOne] using hjget
  have hbIndex : R.getVert 2 = E.finish := by simpa only [hkTwo] using hkget
  have hAD : G.Adj E.start d := by
    have h := R.adj_snd hRcycle.not_nil
    simpa only [Walk.snd, hdIndex] using h
  have hDB : G.Adj d E.finish := by
    have h := R.adj_getVert_succ (i := 1) (by omega)
    simpa only [hdIndex, hbIndex] using h
  have hBA : G.Adj E.finish E.start := by
    have h := R.adj_getVert_succ (i := 2) (by omega)
    have hlast : 2 + 1 = R.length := by omega
    rw [hlast, Walk.getVert_length, hbIndex] at h
    exact h
  have hX := E.snd_notMem (by omega : 2 ≤ E.walk.length)
  have hY := E.penultimate_notMem (by omega : 2 ≤ E.walk.length)
  have hdX : d ≠ E.walk.snd := fun heq => hdE (by rw [heq]; exact E.walk.getVert_mem_support 1)
  have hdY : d ≠ E.walk.penultimate := fun heq => hdE (by
    rw [heq]
    exact E.walk.getVert_mem_support _)
  have hXA : E.walk.snd ≠ E.start := fun heq => hX (by rw [heq]; exact E.start_mem)
  have hXB : E.walk.snd ≠ E.finish := fun heq => hX (by rw [heq]; exact E.finish_mem)
  have hAY : E.start ≠ E.walk.penultimate := fun heq => hY (by rw [← heq]; exact E.start_mem)
  have hYB : E.walk.penultimate ≠ E.finish := fun heq => hY (by rw [heq]; exact E.finish_mem)
  have hdist : ([d, E.walk.snd, E.start, E.walk.penultimate, E.finish] : List V).Nodup := by
    simp [hdX, hds, hdY, hdf, hXA, E.snd_ne_penultimate hlen, hXB,
      hAY, E.endpoints_ne, hYB]
  exact hno (odd_two_chords_of_five_cycle hdist hreturn.symm
    (E.walk.adj_snd E.not_nil).symm hYA.symm (E.walk.adj_penultimate E.not_nil)
    hDB.symm hAD.symm hBA.symm)

#print axioms mixed_returns_to_initial_impossible

end Erdos1091.Voss
