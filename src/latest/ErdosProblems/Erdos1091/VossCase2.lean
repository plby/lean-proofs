/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossReturnParity
import ErdosProblems.Erdos1091.VossEarRotation

/-!
# Voss's mixed return-edge case

After the first parity calculation, rotate through the internal chord and
show that the new return reaches a previously unused attachment vertex.
-/

open SimpleGraph

namespace Erdos1091.Voss

/-- Once an ear has an internal chord, a vertex not on that chord cannot
have an additional off-ear edge to another vertex of the ear. -/
theorem no_new_chord_at_other_vertex {V : Type*} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) (hodd : Odd C.length)
    (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {e : Sym2 V} (he : E.walk.IsChord e) (heEnds : e ≠ s(E.start, E.finish))
    {x y : V} (hx : x ∈ E.walk.support) (hxS : x ∉ C.support) (hxe : x ∉ e)
    (hy : y ∈ E.walk.support) (hxy : G.Adj x y) (hnot : s(x, y) ∉ E.walk.edges) : False := by
  have hnew : E.walk.IsChord s(x, y) := ⟨hxy, hnot, hx, hy⟩
  have heq := Ear.chords_eq_of_no_odd_two_chords C hC hodd hno E hlen he hnew heEnds
    (E.edge_ne_endpoints_of_notMem hxS)
  apply hxe
  rw [heq]
  simp

/-- The new off-ear edge cannot reach the external attachment of the
first return either: replace the first spoke, retaining the old chord. -/
theorem new_return_ne_old_attachment {V : Type*} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) (hodd : Odd C.length)
    (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {d u v x : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hret : G.Adj E.walk.snd d) (he : E.walk.IsChord s(u, v))
    (huS : u ∉ C.support) (hvS : v ∉ C.support)
    (hx : x ∈ E.walk.support) (hxS : x ∉ C.support) (hxe : x ∉ s(u, v))
    (hxFirst : x ≠ E.walk.snd) (hxd : G.Adj x d)
    (hnot : s(x, d) ∉ E.walk.edges) : False := by
  have hdf : d ≠ E.finish := fun heq => hdE (by rw [heq]; exact E.walk.end_mem_support)
  let F := E.replaceStart hdC hdf hret.symm
  have hFlen : 2 ≤ F.walk.length := by simpa only [F, Ear.replaceStart_length] using hlen
  have huStart : u ≠ E.start := fun heq => huS (by rw [heq]; exact E.start_mem)
  have hvStart : v ≠ E.start := fun heq => hvS (by rw [heq]; exact E.start_mem)
  have hxStart : x ≠ E.start := fun heq => hxS (by rw [heq]; exact E.start_mem)
  have heF : F.walk.IsChord s(u, v) :=
    E.isChord_replaceStart hdC hdf hret.symm hdE he huStart hvStart
  have hxF : x ∈ F.walk.support := E.mem_replaceStart_of_mem_ne_start _ _ _ hx hxStart
  have hnotF : s(x, d) ∉ F.walk.edges := by
    intro hmem
    change s(x, d) ∈ s(d, E.walk.snd) :: E.walk.tail.edges at hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · rcases Sym2.eq_iff.mp heq with ⟨hxd, _⟩ | ⟨hxFirst', _⟩
      · exact hxS (hxd ▸ hdC)
      · exact hxFirst hxFirst'
    · rw [Walk.edges_tail] at htail
      exact hnot (List.mem_of_mem_tail htail)
  exact no_new_chord_at_other_vertex C hC hodd hno F hFlen heF
    (F.edge_ne_endpoints_of_notMem huS) hxF hxS hxe F.walk.start_mem_support hxd hnotF

/-- Rotate through the internal terminal chord and close at the new return.
The resulting ear has the same length and a new internal chord, while its
last attachment is outside the old ear and different from the old return. -/
theorem exists_rotated_ear_of_mixed_returns
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) (hodd : Odd C.length)
    (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    {d t : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hret : G.Adj E.walk.snd d) (ht : t ∈ E.walk.support) (htStart : t ≠ E.start)
    (hyt : G.Adj E.walk.penultimate t) (hnot : s(E.walk.penultimate, t) ∉ E.walk.edges) :
    ∃ F : Ear G {v | v ∈ C.support}, F.start = E.start ∧ F.walk.length = E.walk.length ∧
      F.walk.snd = E.walk.snd ∧ F.finish ∉ E.walk.support ∧ F.finish ≠ d ∧
      ∃ u v, F.walk.IsChord s(u, v) ∧ u ∉ C.support ∧ v ∉ C.support := by
  classical
  have htFinish : t ≠ E.finish := by
    intro heq
    apply hnot
    rw [heq]
    exact E.walk.mk_penultimate_end_mem_edges E.not_nil
  have htS : t ∉ C.support := by
    intro htC
    rcases E.only_ends t ht htC with heq | heq
    · exact htStart heq
    · exact htFinish heq
  have hYS := E.penultimate_notMem (by omega : 2 ≤ E.walk.length)
  have heOld : E.walk.IsChord s(E.walk.penultimate, t) :=
    ⟨hyt, hnot, E.walk.getVert_mem_support _, ht⟩
  let P := E.dropLastPath (by omega : 2 ≤ E.walk.length)
  have hPsub : ∀ v ∈ P.walk.support, v ∈ E.walk.support := by
    intro v hv
    change v ∈ (E.walk.take (E.walk.length - 1)).support at hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have htP : t ∈ P.walk.support := by
    have hm := ht
    rw [← E.walk.support_dropLast_concat E.not_nil, List.mem_append, List.mem_singleton] at hm
    exact hm.resolve_right htFinish
  have hnotP : s(P.finish, t) ∉ P.walk.edges := by
    intro he
    apply hnot
    change s(E.walk.penultimate, t) ∈ (E.walk.take (E.walk.length - 1)).edges at he
    rw [Walk.edges_take] at he
    exact List.mem_of_mem_take he
  obtain ⟨j, hjget, hjpos, hjgap⟩ := exists_index_of_terminal_chord P.walk htP htStart hyt hnotP
  have hjlt : j < P.walk.length := by omega
  have hrotate : G.Adj (P.walk.getVert j) P.finish := by rw [hjget]; exact hyt.symm
  let R := P.rotate j hjlt hrotate
  have hRlen : R.walk.length = P.walk.length := P.rotate_length j hjlt hrotate
  have hPlen : P.walk.length + 1 = E.walk.length := E.dropLastPath_length_add_one _
  have hRsub : ∀ v ∈ R.walk.support, v ∈ E.walk.support := by
    intro v hv
    exact hPsub v ((P.mem_rotate_support_iff j hjlt hrotate v).mp hv)
  have hV : R.finish ∈ E.walk.support := hPsub _ (P.walk.getVert_mem_support (j + 1))
  have hVS : R.finish ∉ C.support := R.finish_notMem
  have hVindex : R.finish = E.walk.getVert (j + 1) :=
    Walk.getVert_dropLast (p := E.walk) (by omega : j + 1 < E.walk.length)
  have hXindex : P.walk.getVert 1 = E.walk.snd :=
    Walk.getVert_dropLast (p := E.walk) (by omega : 1 < E.walk.length)
  have hVFirst : R.finish ≠ E.walk.snd := by
    intro heq
    have hi : j + 1 = 1 := P.isPath.getVert_injOn
      (show j + 1 ≤ P.walk.length by omega) (show 1 ≤ P.walk.length by omega)
      (heq.trans hXindex.symm)
    omega
  have hVY : R.finish ≠ E.walk.penultimate := by
    intro heq
    have hi := (P.isPath.getVert_eq_end_iff (show j + 1 ≤ P.walk.length by omega)).mp heq
    omega
  have hVt : R.finish ≠ t := by
    intro heq
    have hi : j + 1 = j := P.isPath.getVert_injOn
      (show j + 1 ≤ P.walk.length by omega) hjlt.le (heq.trans hjget.symm)
    omega
  have hVe : R.finish ∉ s(E.walk.penultimate, t) := by
    simpa only [Sym2.mem_iff] using not_or.mpr ⟨hVY, hVt⟩
  have hRmax : ∀ Q : AttachmentPath G {v | v ∈ C.support}, Q.walk.length ≤ R.walk.length := by
    intro Q
    have hQ := hmax Q
    omega
  obtain ⟨w, hwAdj, hwNot⟩ := exists_adj_not_mem_path_edges E.walk E.isPath
    (i := j + 1) (by omega) (by omega) (hdegree _)
  rw [← hVindex] at hwAdj hwNot
  have hwE : w ∉ E.walk.support := by
    intro hw
    exact no_new_chord_at_other_vertex C hC hodd hno E (by omega) heOld
      (E.edge_ne_endpoints_of_notMem hYS) hV hVS hVe hw hwAdj hwNot
  have hwd : w ≠ d := by
    intro heq
    subst w
    exact new_return_ne_old_attachment C hC hodd hno E (by omega) hdC hdE hret
      heOld hYS htS hV hVS hVe hVFirst hwAdj hwNot
  have hwC : w ∈ C.support := by
    rcases R.neighbor_mem_of_longest hRmax hwAdj with hwR | hwC
    · exact (hwE (hRsub w hwR)).elim
    · exact hwC
  have hwR : w ∉ R.walk.support := fun hw => hwE (hRsub w hw)
  let F := R.close hwAdj hwR hwC
  have hFlen : F.walk.length = E.walk.length := by
    change (R.walk.concat hwAdj).length = E.walk.length
    rw [Walk.length_concat]
    omega
  have hFsnd : F.walk.snd = E.walk.snd := by
    calc
      _ = R.walk.snd := R.close_snd hwAdj hwR hwC
      _ = P.walk.snd := PathRotation.snd_eq P.walk j hjpos hjlt hrotate
      _ = E.walk.snd := hXindex
  have hcut : R.walk.IsChord s(P.walk.getVert j, R.finish) :=
    PathRotation.cut_isChord P.walk P.isPath j hjgap hrotate
  refine ⟨F, rfl, hFlen, hFsnd, hwE, hwd, P.walk.getVert j, R.finish,
    R.isChord_close hwAdj hwR hwC hcut, ?_, hVS⟩
  simpa only [hjget] using htS

/-- Voss's Case 2(a): one external return and one internal terminal return
not reaching the first attachment are impossible. -/
theorem mixed_returns_internal_not_initial_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    {d t : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hret : G.Adj E.walk.snd d) (ht : t ∈ E.walk.support) (htStart : t ≠ E.start)
    (hyt : G.Adj E.walk.penultimate t)
    (hnot : s(E.walk.penultimate, t) ∉ E.walk.edges) : False := by
  classical
  have htFinish : t ≠ E.finish := by
    intro heq
    apply hnot
    rw [heq]
    exact E.walk.mk_penultimate_end_mem_edges E.not_nil
  have htS : t ∉ C.support := by
    intro htC
    rcases E.only_ends t ht htC with heq | heq
    · exact htStart heq
    · exact htFinish heq
  have heOld : E.walk.IsChord s(E.walk.penultimate, t) :=
    ⟨hyt, hnot, E.walk.getVert_mem_support _, ht⟩
  have hYS := E.penultimate_notMem (by omega : 2 ≤ E.walk.length)
  obtain ⟨hAB, hDB, _⟩ :=
    rim_adj_of_internal_chord_and_return C hC hno E hlen hdC hdE hret heOld hYS htS
  obtain ⟨F, hFstart, hFlen, hFsnd, hFout, hFd, u, v, heF, huS, hvS⟩ :=
    exists_rotated_ear_of_mixed_returns C hC.1 hC.2.1 hno E hlen hmax hdegree
      hdC hdE hret ht htStart hyt hnot
  have hds : d ≠ E.start := fun heq => hdE (by rw [heq]; exact E.walk.start_mem_support)
  have hdF : d ∉ F.walk.support := by
    intro hd
    rcases F.only_ends d hd hdC with heq | heq
    · exact hds (heq.trans hFstart)
    · exact hFd heq.symm
  have hretF : G.Adj F.walk.snd d := by rw [hFsnd]; exact hret
  obtain ⟨hAW, hDW, _⟩ := rim_adj_of_internal_chord_and_return C hC hno F
    (by omega) hdC hdF hretF heF huS hvS
  have hAW' : G.Adj E.start F.finish := by simpa only [hFstart] using hAW
  have hBW : E.finish ≠ F.finish := by
    intro heq
    exact hFout (by rw [← heq]; exact E.walk.end_mem_support)
  let R := C.rotate E.start E.start_mem
  have hR : IsShortestOddCycle R := hC.rotate E.start_mem
  have hBR : E.finish ∈ R.support := by simpa [R] using E.finish_mem
  have hDR : d ∈ R.support := by simpa [R] using hdC
  have hWR : F.finish ∈ R.support := by simpa [R] using F.finish_mem
  have hfour := CycleArc.length_eq_four_of_square R hR.1 hR.isChordless
    hBR hDR hWR hds hBW hAB hDB.symm hDW hAW'.symm
  have hodd : Odd 4 := hfour ▸ hR.2.1
  norm_num at hodd

#print axioms mixed_returns_internal_not_initial_impossible

end Erdos1091.Voss
