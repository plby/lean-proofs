/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossCase2
import ErdosProblems.Erdos1091.VossCase2b

/-! # Two external returns in Voss's Case 3 -/

open SimpleGraph

namespace Erdos1091.Voss

/-- Select one spoke at each end of the internal ear path. If an outer
arc contains the other two spoke endpoints in its interior, the resulting
cycle is even. -/
theorem even_of_four_spokes
    {V : Type*} {G : SimpleGraph V} {S : Set V}
    (E : Ear G S) (hlen : 3 ≤ E.walk.length)
    (hno : ¬ HasOddCycleWithTwoChords G) {a b c d : V}
    (ha : a ∈ S) (hb : b ∈ S) (haf : a ≠ E.finish) (hba : b ≠ a)
    (haX : G.Adj a E.walk.snd) (hYb : G.Adj E.walk.penultimate b)
    (q : G.Walk b a) (hq : q.IsPath) (hqS : ∀ v ∈ q.support, v ∈ S)
    (hcq : c ∈ q.support) (hca : c ≠ a) (hcb : c ≠ b)
    (hdq : d ∈ q.support) (hda : d ≠ a) (hdb : d ≠ b)
    (hXc : G.Adj E.walk.snd c) (hYd : G.Adj E.walk.penultimate d) :
    Even (E.walk.length + q.length) := by
  let F := E.replaceStart ha haf haX
  have hFlen : F.walk.length = E.walk.length := E.replaceStart_length _ _ _
  have hFX : F.walk.snd = E.walk.snd := E.replaceStart_snd _ _ _
  have hFY : F.walk.penultimate = E.walk.penultimate := E.replaceStart_penultimate (by omega) _ _ _
  have hFb : G.Adj F.walk.penultimate b := by rwa [hFY]
  let H := F.replaceFinish hb hba hFb
  have hHlen : H.walk.length = E.walk.length := (F.replaceFinish_length _ _ _).trans hFlen
  have hHX : H.walk.snd = E.walk.snd := (F.replaceFinish_snd (by omega) _ _ _).trans hFX
  have hHY : H.walk.penultimate = E.walk.penultimate :=
    (F.replaceFinish_penultimate _ _ _).trans hFY
  have hX := H.snd_notMem (by omega : 2 ≤ H.walk.length)
  have hY := H.penultimate_notMem (by omega : 2 ≤ H.walk.length)
  have hne : s(H.walk.snd, c) ≠ s(H.walk.penultimate, d) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨heq, _⟩ | ⟨heq, _⟩
    · exact H.snd_ne_penultimate (by omega) heq
    · exact hX (heq ▸ hqS d hdq)
  have heven := H.even_append_of_two_cross_edges (by omega) q hq hqS hno
    (H.walk.getVert_mem_support 1) hX (H.walk.getVert_mem_support _) hY
    hcq hca hcb hdq hda hdb
    (by change G.Adj H.walk.snd c; rwa [hHX])
    (by change G.Adj H.walk.penultimate d; rwa [hHY]) hne
  rwa [hHlen] at heven

/-- Coincident external returns reduce to Case 2(b) after replacing the
first attachment by their common endpoint. -/
theorem coincident_external_returns_impossible
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    {d : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hXd : G.Adj E.walk.snd d) (hYd : G.Adj E.walk.penultimate d) : False := by
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdf : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  let F := E.replaceStart hdC hdf hXd.symm
  have hFlen : 3 ≤ F.walk.length := by simpa only [F, Ear.replaceStart_length] using hlen
  have hFX : F.walk.snd = E.walk.snd := E.replaceStart_snd _ _ _
  have hFY : F.walk.penultimate = E.walk.penultimate := E.replaceStart_penultimate (by omega) _ _ _
  have hAout : E.start ∉ F.walk.support := E.old_start_notMem_replaceStart _ _ _ hds
  have hret : G.Adj F.walk.snd E.start := by
    rw [hFX]
    exact (E.walk.adj_snd E.not_nil).symm
  have hYstart : E.walk.penultimate ≠ E.start := fun heq =>
    E.penultimate_notMem (by omega) (by rw [heq]; exact E.start_mem)
  have he : F.walk.IsChord s(d, E.walk.penultimate) := E.isChord_from_new_start
    hdC hdf hXd.symm hdE (E.walk.getVert_mem_support _) hYstart
    (E.snd_ne_penultimate hlen).symm hYd.symm
  have he' : F.walk.IsChord s(F.walk.penultimate, F.start) := by
    change F.walk.IsChord s(F.walk.penultimate, d)
    rw [hFY]
    simpa only [Sym2.eq_swap] using he
  exact mixed_returns_to_initial_impossible C hC hno F hFlen E.start_mem hAout hret
    (Walk.isChord_sym2Mk.mp he').1 he'.2.1

/-- Four even cycles obtained by changing either or both attachment
endpoints contradict the oddness of the crossed outer cycle. -/
theorem crossed_return_parity_contradiction {a b c d s : ℕ}
    (hodd : Odd (a + b + c + d))
    (h₁ : Even (s + 2 + a + b + c)) (h₂ : Even (s + 2 + a + c + d))
    (h₃ : Even (s + 2 + a + b + d)) (h₄ : Even (s + 2 + b + c + d)) : False := by
  simp only [Nat.odd_iff, Nat.even_iff] at hodd h₁ h₂ h₃ h₄
  omega

/-- The noncrossed order `A,D,F,B` of the four attachment vertices is
impossible: two even long cycles force one shorter odd two-spoke cycle. -/
theorem noncrossed_external_returns_indexed_impossible
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hstart : E.start = z) {i j k : ℕ}
    (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < C.length)
    (hfinish : C.getVert k = E.finish)
    (hXD : G.Adj E.walk.snd (C.getVert i))
    (hYF : G.Adj E.walk.penultimate (C.getVert j)) : False := by
  have hinj : ∀ a b : ℕ, a < C.length → b < C.length → a ≠ b →
      C.getVert a ≠ C.getVert b := by
    intro a b ha hb hab heq
    exact hab (hC.1.getVert_injOn' (show a ≤ C.length - 1 by omega)
      (show b ≤ C.length - 1 by omega) heq)
  have hbase : C.getVert 0 = E.start := C.getVert_zero.trans hstart.symm
  have hDA : C.getVert i ≠ E.start := by
    rw [← hbase]
    exact hinj i 0 (by omega) (by omega) (by omega)
  have hDB : C.getVert i ≠ E.finish := by rw [← hfinish]; exact hinj i k (by omega) hk (by omega)
  have hFA : C.getVert j ≠ E.start := by
    rw [← hbase]
    exact hinj j 0 (by omega) (by omega) (by omega)
  have hFB : C.getVert j ≠ E.finish := by rw [← hfinish]; exact hinj j k (by omega) hk (by omega)
  have hFD : C.getVert j ≠ C.getVert i := hinj j i (by omega) (by omega) (by omega)
  let q₁ := (C.take k).reverse.copy hfinish hstart.symm
  have hq₁ : q₁.IsPath := (Walk.isPath_copy _ _ _).mpr (hC.1.isPath_take hk).reverse
  have hq₁sup : q₁.support = (C.take k).reverse.support := Walk.support_copy _ _ _
  have hq₁C : ∀ w ∈ q₁.support, w ∈ C.support := by
    intro w hw
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse, Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have hmem₁ : ∀ t ≤ k, C.getVert t ∈ q₁.support := by
    intro t ht
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse]
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using (C.take k).getVert_mem_support t
  have hq₁len : q₁.length = k := by
    simp only [q₁, Walk.length_copy, Walk.length_reverse, Walk.take_length, Nat.min_eq_left hk.le]
  have heven₁ := even_of_four_spokes E hlen hno E.start_mem E.finish_mem E.endpoints_ne
    E.endpoints_ne.symm (E.walk.adj_snd E.not_nil) (E.walk.adj_penultimate E.not_nil)
    q₁ hq₁ hq₁C (hmem₁ i (by omega)) hDA hDB (hmem₁ j hjk.le) hFA hFB hXD hYF
  let q₂ := CycleArc.wrap C j i
  have hq₂ : q₂.IsPath := CycleArc.wrap_isPath C hC.1 hij (by omega)
  have hq₂C : ∀ w ∈ q₂.support, w ∈ C.support := CycleArc.wrap_support_subset C j i
  have hAq₂ : E.start ∈ q₂.support := by
    rw [← hbase]
    exact CycleArc.getVert_mem_wrap_of_le_end C j i 0 (Nat.zero_le _)
  have hBq₂ : E.finish ∈ q₂.support := by
    rw [← hfinish]
    exact CycleArc.getVert_mem_wrap_of_le C j i k hjk.le
  have hq₂len : q₂.length = C.length - j + i := CycleArc.wrap_length C j i (by omega)
  have heven₂ := even_of_four_spokes E hlen hno (C.getVert_mem_support i)
    (C.getVert_mem_support j) hDB hFD hXD.symm hYF q₂ hq₂ hq₂C
    hAq₂ hDA.symm hFA.symm hBq₂ hDB.symm hFB.symm
    (E.walk.adj_snd E.not_nil).symm (E.walk.adj_penultimate E.not_nil)
  have hpLen : (C.take i).length = i := by rw [Walk.take_length, Nat.min_eq_left (by omega)]
  have hpC : ∀ w ∈ (C.take i).support, w ∈ C.support := by
    intro w hw
    rw [Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  let r := Erdos1105.pathSegment C j k hjk.le
  have hr : r.IsPath := CycleArc.segment_isPath C hC.1 j k hjk.le hk
  have hrLen : r.length = k - j := Erdos1105.pathSegment_length C j k hjk.le hk.le
  have hrC : ∀ w ∈ r.support, w ∈ C.support :=
    Erdos1105.pathSegment_support_subset C j k hjk.le hk.le
  have hsum : i + (j - i) + (k - j) + (C.length - k) = C.length := by omega
  have hXz : G.Adj E.walk.snd z := by simpa only [hstart] using (E.walk.adj_snd E.not_nil).symm
  have hYB : G.Adj E.walk.penultimate (C.getVert k) := by
    rw [hfinish]
    exact E.walk.adj_penultimate E.not_nil
  apply noncrossed_return_parity_contradiction
    (a := i) (b := j - i) (c := k - j) (d := C.length - k) (s := E.walk.length - 2)
    (by omega) (by omega) (by omega) (by omega) (by rw [hsum]; exact hC.2.1)
  · have heq : E.walk.length - 2 + 2 + i + (j - i) + (k - j) =
        E.walk.length + q₁.length := by omega
    rwa [heq]
  · have heq : E.walk.length - 2 + 2 + i + (k - j) + (C.length - k) =
        E.walk.length + q₂.length := by omega
    rwa [heq]
  · intro ho
    have hpOdd : Odd (C.take i).length := by
      rw [hpLen, Nat.odd_iff]
      rw [Nat.odd_iff] at ho
      omega
    have hm := hC.le_odd_arc_length_add_two (C.take i) (hC.1.isPath_take (by omega))
      (by omega) hpC (E.snd_notMem (by omega)) hXz hXD hpOdd
    omega
  · intro ho
    have hrOdd : Odd r.length := by
      rw [hrLen, Nat.odd_iff]
      rw [Nat.odd_iff] at ho
      omega
    have hm := hC.le_odd_arc_length_add_two r hr (by omega) hrC
      (E.penultimate_notMem (by omega)) hYF hYB hrOdd
    omega

/-- The crossed order `A,F,D,B` is impossible by the four concrete
even-cycle identities. -/
theorem crossed_external_returns_indexed_impossible
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : C.IsCycle) (hodd : Odd C.length) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hstart : E.start = z) {i j k : ℕ}
    (hi : 0 < i) (hij : i < j) (hjk : j < k) (hk : k < C.length)
    (hfinish : C.getVert k = E.finish)
    (hXD : G.Adj E.walk.snd (C.getVert j))
    (hYF : G.Adj E.walk.penultimate (C.getVert i)) : False := by
  have hinj : ∀ a b : ℕ, a < C.length → b < C.length → a ≠ b →
      C.getVert a ≠ C.getVert b := by
    intro a b ha hb hab heq
    exact hab (hC.getVert_injOn' (show a ≤ C.length - 1 by omega)
      (show b ≤ C.length - 1 by omega) heq)
  have hbase : C.getVert 0 = E.start := C.getVert_zero.trans hstart.symm
  have hDA : C.getVert j ≠ E.start := by
    rw [← hbase]
    exact hinj j 0 (by omega) (by omega) (by omega)
  have hDB : C.getVert j ≠ E.finish := by rw [← hfinish]; exact hinj j k (by omega) hk (by omega)
  have hFA : C.getVert i ≠ E.start := by
    rw [← hbase]
    exact hinj i 0 (by omega) (by omega) (by omega)
  have hFB : C.getVert i ≠ E.finish := by rw [← hfinish]; exact hinj i k (by omega) hk (by omega)
  have hFD : C.getVert i ≠ C.getVert j := hinj i j (by omega) (by omega) (by omega)
  let q₁ := (C.take k).reverse.copy hfinish hstart.symm
  have hq₁ : q₁.IsPath := (Walk.isPath_copy _ _ _).mpr (hC.isPath_take hk).reverse
  have hq₁sup : q₁.support = (C.take k).reverse.support := Walk.support_copy _ _ _
  have hq₁C : ∀ w ∈ q₁.support, w ∈ C.support := by
    intro w hw
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse, Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have hmem₁ : ∀ t ≤ k, C.getVert t ∈ q₁.support := by
    intro t ht
    rw [hq₁sup, Walk.support_reverse, List.mem_reverse]
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using (C.take k).getVert_mem_support t
  have hq₁len : q₁.length = k := by
    simp only [q₁, Walk.length_copy, Walk.length_reverse, Walk.take_length, Nat.min_eq_left hk.le]
  have heven₁ := even_of_four_spokes E hlen hno E.start_mem E.finish_mem E.endpoints_ne
    E.endpoints_ne.symm (E.walk.adj_snd E.not_nil) (E.walk.adj_penultimate E.not_nil)
    q₁ hq₁ hq₁C (hmem₁ j hjk.le) hDA hDB (hmem₁ i (by omega)) hFA hFB hXD hYF
  let q₂ := (CycleArc.wrap C j i).reverse
  have hq₂ : q₂.IsPath := (CycleArc.wrap_isPath C hC hij (by omega)).reverse
  have hq₂C : ∀ w ∈ q₂.support, w ∈ C.support := by
    intro w hw
    rw [Walk.support_reverse, List.mem_reverse] at hw
    exact CycleArc.wrap_support_subset C j i w hw
  have hAq₂ : E.start ∈ q₂.support := by
    rw [Walk.support_reverse, List.mem_reverse, ← hbase]
    exact CycleArc.getVert_mem_wrap_of_le_end C j i 0 (Nat.zero_le _)
  have hBq₂ : E.finish ∈ q₂.support := by
    rw [Walk.support_reverse, List.mem_reverse, ← hfinish]
    exact CycleArc.getVert_mem_wrap_of_le C j i k hjk.le
  have hq₂len : q₂.length = C.length - j + i := by
    rw [Walk.length_reverse]
    exact CycleArc.wrap_length C j i (by omega)
  have heven₂ := even_of_four_spokes E hlen hno (C.getVert_mem_support j)
    (C.getVert_mem_support i) hDB hFD hXD.symm hYF q₂ hq₂ hq₂C
    hAq₂ hDA.symm hFA.symm hBq₂ hDB.symm hFB.symm
    (E.walk.adj_snd E.not_nil).symm (E.walk.adj_penultimate E.not_nil)
  let q₃ := (CycleArc.wrap C k j).copy hfinish rfl
  have hq₃ : q₃.IsPath := (Walk.isPath_copy _ _ _).mpr (CycleArc.wrap_isPath C hC hjk hk)
  have hq₃sup : q₃.support = (CycleArc.wrap C k j).support := Walk.support_copy _ _ _
  have hq₃C : ∀ w ∈ q₃.support, w ∈ C.support := by
    intro w hw
    exact CycleArc.wrap_support_subset C k j w (hq₃sup ▸ hw)
  have hAq₃ : E.start ∈ q₃.support := by
    rw [hq₃sup, ← hbase]
    exact CycleArc.getVert_mem_wrap_of_le_end C k j 0 (Nat.zero_le _)
  have hFq₃ : C.getVert i ∈ q₃.support := by
    rw [hq₃sup]
    exact CycleArc.getVert_mem_wrap_of_le_end C k j i hij.le
  have hq₃len : q₃.length = C.length - k + j :=
    (Walk.length_copy _ _ _).trans (CycleArc.wrap_length C k j (by omega))
  have heven₃ := even_of_four_spokes E hlen hno (C.getVert_mem_support j)
    E.finish_mem hDB hDB.symm hXD.symm (E.walk.adj_penultimate E.not_nil) q₃ hq₃ hq₃C
    hAq₃ hDA.symm E.endpoints_ne hFq₃ hFD hFB (E.walk.adj_snd E.not_nil).symm hYF
  let q₄ := (C.drop i).copy rfl hstart.symm
  have hq₄ : q₄.IsPath := (Walk.isPath_copy _ _ _).mpr (hC.isPath_drop hi)
  have hq₄sup : q₄.support = (C.drop i).support := Walk.support_copy _ _ _
  have hq₄C : ∀ w ∈ q₄.support, w ∈ C.support := by
    intro w hw
    rw [hq₄sup, Walk.drop_support_eq_support_drop_min] at hw
    exact List.mem_of_mem_drop hw
  have hmem₄ : ∀ t, i ≤ t → C.getVert t ∈ q₄.support := by
    intro t ht
    rw [hq₄sup]
    simpa only [Walk.drop_getVert, Nat.add_sub_of_le ht] using (C.drop i).getVert_mem_support (t - i)
  have hBq₄ : E.finish ∈ q₄.support := by rw [← hfinish]; exact hmem₄ k (by omega)
  have hq₄len : q₄.length = C.length - i :=
    (Walk.length_copy _ _ _).trans (Walk.drop_length _ _)
  have heven₄ := even_of_four_spokes E hlen hno E.start_mem (C.getVert_mem_support i)
    E.endpoints_ne hFA (E.walk.adj_snd E.not_nil) hYF q₄ hq₄ hq₄C
    (hmem₄ j hij.le) hDA hFD.symm hBq₄ E.endpoints_ne.symm hFB.symm
    hXD (E.walk.adj_penultimate E.not_nil)
  have hsum : i + (j - i) + (k - j) + (C.length - k) = C.length := by omega
  apply crossed_return_parity_contradiction
    (a := i) (b := j - i) (c := k - j) (d := C.length - k) (s := E.walk.length - 2)
    (by rw [hsum]; exact hodd)
  · have heq : E.walk.length - 2 + 2 + i + (j - i) + (k - j) =
        E.walk.length + q₁.length := by omega
    rwa [heq]
  · have heq : E.walk.length - 2 + 2 + i + (k - j) + (C.length - k) =
        E.walk.length + q₂.length := by omega
    rwa [heq]
  · have heq : E.walk.length - 2 + 2 + i + (j - i) + (C.length - k) =
        E.walk.length + q₃.length := by omega
    rwa [heq]
  · have heq : E.walk.length - 2 + 2 + (j - i) + (k - j) + (C.length - k) =
        E.walk.length + q₄.length := by omega
    rwa [heq]

/-- Voss's Case 3, with no indexing or orientation assumptions. Both
off-ear returns landing on the shortest odd cycle are impossible. -/
theorem external_returns_impossible
    {V : Type*} {G : SimpleGraph V} {z : V} (C : G.Walk z z)
    (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    {d f : V} (hdC : d ∈ C.support) (hfC : f ∈ C.support)
    (hdE : d ∉ E.walk.support) (hfE : f ∉ E.walk.support)
    (hXd : G.Adj E.walk.snd d) (hYf : G.Adj E.walk.penultimate f) : False := by
  by_cases hdf : d = f
  · exact coincident_external_returns_impossible C hC hno E hlen hdC hdE hXd (hdf ▸ hYf)
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdb : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  have hfs : f ≠ E.start := fun heq => hfE (by rw [heq]; exact E.walk.start_mem_support)
  have hfb : f ≠ E.finish := fun heq => hfE (by rw [heq]; exact E.walk.end_mem_support)
  obtain ⟨R, hRcycle, hRlen, hRsupp, i, k, hi, hik, hk, hiGet, hkGet⟩ :=
    CycleArc.exists_oriented_three C hC.1 E.start_mem hdC E.finish_mem hds E.endpoints_ne hdb
  have hR : IsShortestOddCycle R := by
    refine ⟨hRcycle, ?_, ?_⟩
    · rw [hRlen]; exact hC.2.1
    · intro w p hp ho
      rw [hRlen]
      exact hC.2.2 w p hp ho
  let F := E.changeSet (T := {v | v ∈ R.support}) (fun v => (hRsupp v).symm)
  have hFlen : 3 ≤ F.walk.length := hlen
  have hfR : f ∈ R.support := (hRsupp f).mpr hfC
  obtain ⟨j, hjGet, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hfR
  have hj : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hfs (by simpa only [hj0, Walk.getVert_zero] using hjGet.symm)
  have hjlt : j < R.length := by
    by_contra h
    have hje : j = R.length := by omega
    exact hfs (by simpa only [hje, Walk.getVert_length] using hjGet.symm)
  have hji : j ≠ i := by
    intro heq
    exact hdf (hiGet.symm.trans (heq ▸ hjGet))
  have hjk : j ≠ k := by
    intro heq
    exact hfb (hjGet.symm.trans (heq ▸ hkGet))
  have hXdi : G.Adj F.walk.snd (R.getVert i) := hiGet ▸ hXd
  have hYfj : G.Adj F.walk.penultimate (R.getVert j) := hjGet ▸ hYf
  rcases lt_or_gt_of_ne hji with hji | hij
  · exact crossed_external_returns_indexed_impossible R hRcycle hR.2.1 hno F hlen rfl
      hj hji hik hk hkGet hXdi hYfj
  · rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact noncrossed_external_returns_indexed_impossible R hR hno F hlen rfl
        hi hij hjk hk hkGet hXdi hYfj
    · have hjStart : R.getVert j ≠ F.start := by
        change R.getVert j ≠ E.start
        simpa only [hjGet] using hfs
      let H := F.replaceFinish (R.getVert_mem_support j) hjStart hYfj
      have hHlen : 3 ≤ H.walk.length := by simpa only [H, Ear.replaceFinish_length] using hFlen
      have hHX : H.walk.snd = F.walk.snd := F.replaceFinish_snd (by omega) _ _ _
      have hHY : H.walk.penultimate = F.walk.penultimate := F.replaceFinish_penultimate _ _ _
      have hHXd : G.Adj H.walk.snd (R.getVert i) := by rwa [hHX]
      have hHYb : G.Adj H.walk.penultimate (R.getVert k) := by
        rw [hHY, hkGet]
        exact F.walk.adj_penultimate F.not_nil
      exact noncrossed_external_returns_indexed_impossible R hR hno H hHlen rfl
        hi hik hkj hjlt rfl hHXd hHYb

#print axioms external_returns_impossible

end Erdos1091.Voss
