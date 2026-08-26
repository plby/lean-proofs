/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.Voss
import ErdosProblems.Erdos1105.PathSegments

/-!
# Indexed arcs of a simple cycle

Forward segments reuse `Erdos1105.pathSegment`. The complementary arc crosses
the chosen starting vertex and has the exact length needed for Voss's parity
calculations.
-/

open SimpleGraph

namespace Erdos1091.Voss.CycleArc

variable {V : Type*} {G : SimpleGraph V} {z : V}

/-- The arc from index `i` back to index `j`, crossing the cycle's base. -/
def wrap (C : G.Walk z z) (i j : ℕ) : G.Walk (C.getVert i) (C.getVert j) :=
  (C.drop i).append (C.take j)

theorem wrap_isPath (C : G.Walk z z) (hC : C.IsCycle) {i j : ℕ}
    (hji : j < i) (hi : i < C.length) : (wrap C i j).IsPath := by
  apply Erdos1105.isPath_append_of_inter_eq_end
    (hC.isPath_drop (by omega)) (hC.isPath_take (by omega))
  intro v hvDrop hvTake
  obtain ⟨a, ha, hale⟩ := Walk.mem_support_iff_exists_getVert.mp hvDrop
  obtain ⟨b, hb, hble⟩ := Walk.mem_support_iff_exists_getVert.mp hvTake
  have hia : i + a ≤ C.length := by rw [Walk.drop_length] at hale; omega
  have hbj : b ≤ j := by rw [Walk.take_length] at hble; omega
  have ha' : C.getVert (i + a) = v := by simpa only [Walk.drop_getVert] using ha
  have hb' : C.getVert b = v := by
    simpa only [Walk.take_getVert, Nat.min_eq_right hbj] using hb
  have hlast : i + a = C.length := by
    by_contra hne
    have heq : i + a = b := hC.getVert_injOn'
      (show i + a ≤ C.length - 1 by omega) (show b ≤ C.length - 1 by omega)
      (ha'.trans hb'.symm)
    omega
  simpa only [hlast, Walk.getVert_length] using ha'.symm

theorem wrap_length (C : G.Walk z z) (i j : ℕ) (hj : j ≤ C.length) :
    (wrap C i j).length = C.length - i + j := by
  simp only [wrap, Walk.length_append, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj]

theorem wrap_support_subset (C : G.Walk z z) (i j : ℕ) :
    ∀ v ∈ (wrap C i j).support, v ∈ C.support := by
  intro v hv
  rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
  · rw [Walk.drop_support_eq_support_drop_min] at hv
    exact List.mem_of_mem_drop hv
  · rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv

theorem getVert_mem_wrap_of_le (C : G.Walk z z) (i j k : ℕ) (hik : i ≤ k) :
    C.getVert k ∈ (wrap C i j).support := by
  apply (Walk.mem_support_append_iff _ _).mpr
  left
  have hm := (C.drop i).getVert_mem_support (k - i)
  simpa only [Walk.drop_getVert, Nat.add_sub_of_le hik] using hm

theorem getVert_mem_wrap_of_le_end (C : G.Walk z z) (i j k : ℕ) (hkj : k ≤ j) :
    C.getVert k ∈ (wrap C i j).support := by
  apply (Walk.mem_support_append_iff _ _).mpr
  right
  have hm := (C.take j).getVert_mem_support k
  simpa only [Walk.take_getVert, Nat.min_eq_right hkj] using hm

/-- A forward segment ending before the repeated base vertex is a path. -/
theorem segment_isPath (C : G.Walk z z) (hC : C.IsCycle) (i j : ℕ)
    (hij : i ≤ j) (hj : j < C.length) :
    (Erdos1105.pathSegment C i j hij).IsPath := by
  by_cases hi : 0 < i
  · exact (Walk.isPath_copy _ _ _).mpr ((hC.isPath_drop hi).take (j - i))
  · have hi0 : i = 0 := by omega
    subst i
    apply (Walk.isPath_copy _ _ _).mpr
    have heq := C.drop_zero
    have htake : ((C.drop 0).take j).IsPath := by
      rw [heq]
      apply Walk.IsPath.mk'
      rw [Walk.support_take, Walk.support_copy]
      simpa only [Walk.support_take] using (hC.isPath_take hj).support_nodup
    simpa only [Nat.sub_zero] using htake

/-- A common cycle-edge neighbour of the two neighbours of the base,
other than the base itself, forces a four-cycle. -/
theorem length_eq_four_of_common_neighbor (C : G.Walk z z) (hC : C.IsCycle)
    {d : V} (hd : d ≠ z) (hfirst : s(C.snd, d) ∈ C.edges)
    (hlast : s(C.penultimate, d) ∈ C.edges) : C.length = 4 := by
  have htailEdge : s(C.snd, d) ∈ C.tail.edges := by
    have hedges := congrArg (fun p : G.Walk z z => p.edges) (C.cons_tail_eq hC.not_nil)
    change s(z, C.snd) :: C.tail.edges = C.edges at hedges
    rw [← hedges, List.mem_cons] at hfirst
    rcases hfirst with heq | he
    · rcases Sym2.eq_iff.mp heq with ⟨hs, _⟩ | ⟨_, hd'⟩
      · exact ((C.adj_snd hC.not_nil).ne hs.symm).elim
      · exact (hd hd').elim
    · exact he
  have htailRev : s(C.snd, d) ∈ C.tail.reverse.edges := by
    simpa only [Walk.edges_reverse, List.mem_reverse] using htailEdge
  have hdFirst := hC.isPath_tail.reverse.eq_penultimate_of_mem_edges htailRev
  have hdTwo : d = C.getVert 2 := by
    simpa only [Walk.penultimate_reverse, Walk.snd, Walk.getVert_tail] using hdFirst
  have hedges : C.edges = C.dropLast.edges ++ [s(C.penultimate, z)] := by
    calc
      _ = (C.dropLast.concat (C.adj_penultimate hC.not_nil)).edges := by rw [Walk.concat_dropLast]
      _ = _ := by simpa only [List.concat_eq_append] using Walk.edges_concat _ _
  have hdropEdge : s(C.penultimate, d) ∈ C.dropLast.edges := by
    rw [hedges, List.mem_append, List.mem_singleton] at hlast
    rcases hlast with he | heq
    · exact he
    · exact (hd ((Sym2.mkEmbedding C.penultimate).injective heq)).elim
  have hdLast := hC.isPath_dropLast.eq_penultimate_of_mem_edges hdropEdge
  have hlen := C.length_dropLast_add_one hC.not_nil
  have hthree := hC.three_le_length
  have hindex : C.dropLast.length - 1 = C.length - 2 := by omega
  have hdEnd : d = C.getVert (C.length - 2) := by
    simpa only [Walk.penultimate, hindex,
      Walk.getVert_dropLast (by omega : C.length - 2 < C.length)] using hdLast
  have heq : 2 = C.length - 2 := hC.getVert_injOn'
    (show 2 ≤ C.length - 1 by omega) (show C.length - 2 ≤ C.length - 1 by omega)
    (hdTwo.symm.trans hdEnd)
  omega

/-- Four distinct cyclic vertices joined in a square exhaust a chordless
cycle. The two explicit inequalities suffice; adjacency supplies the rest. -/
theorem length_eq_four_of_square (C : G.Walk z z) (hC : C.IsCycle)
    (hchordless : C.IsChordless) {b d w : V}
    (hb : b ∈ C.support) (hd : d ∈ C.support) (hw : w ∈ C.support)
    (hdz : d ≠ z) (hbw : b ≠ w)
    (hzb : G.Adj z b) (hbd : G.Adj b d) (hdw : G.Adj d w) (hwz : G.Adj w z) :
    C.length = 4 := by
  have hzbEdge := hchordless.mem_edges C.start_mem_support hb hzb
  have hzwEdge := hchordless.mem_edges C.start_mem_support hw hwz.symm
  have hbdEdge := hchordless.mem_edges hb hd hbd
  have hwdEdge := hchordless.mem_edges hw hd hdw.symm
  rcases cycle_edge_at_base C hC hzbEdge with hbEq | hbEq <;>
    rcases cycle_edge_at_base C hC hzwEdge with hwEq | hwEq
  · exact (hbw (hbEq.trans hwEq.symm)).elim
  · apply length_eq_four_of_common_neighbor C hC hdz
    · simpa only [hbEq] using hbdEdge
    · simpa only [hwEq] using hwdEdge
  · apply length_eq_four_of_common_neighbor C hC hdz
    · simpa only [hwEq] using hwdEdge
    · simpa only [hbEq] using hbdEdge
  · exact (hbw (hbEq.trans hwEq.symm)).elim

/-- Choose a base and orientation so that three distinct marked cycle
vertices occur at indices `0 < j < k < length`. -/
theorem exists_oriented_three (C : G.Walk z z) (hC : C.IsCycle)
    {a d b : V} (ha : a ∈ C.support) (hd : d ∈ C.support) (hb : b ∈ C.support)
    (hda : d ≠ a) (hab : a ≠ b) (hdb : d ≠ b) :
    ∃ R : G.Walk a a, R.IsCycle ∧ R.length = C.length ∧
      (∀ v, v ∈ R.support ↔ v ∈ C.support) ∧ ∃ j k : ℕ,
      0 < j ∧ j < k ∧ k < R.length ∧ R.getVert j = d ∧ R.getVert k = b := by
  classical
  let R := C.rotate a ha
  have hR : R.IsCycle := hC.rotate ha
  have hdR : d ∈ R.support := by simpa [R] using hd
  have hbR : b ∈ R.support := by simpa [R] using hb
  obtain ⟨j, hjget, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hdR
  obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hbR
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hda (by simpa only [hj0, Walk.getVert_zero] using hjget.symm)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    exact hab (by simpa only [hk0, Walk.getVert_zero] using hkget)
  have hjlt : j < R.length := by
    by_contra h
    have hje : j = R.length := by omega
    exact hda (by simpa only [hje, Walk.getVert_length] using hjget.symm)
  have hklt : k < R.length := by
    by_contra h
    have hke : k = R.length := by omega
    exact hab (by simpa only [hke, Walk.getVert_length] using hkget)
  have hjk : j ≠ k := by
    intro heq
    rw [heq] at hjget
    exact hdb (hjget.symm.trans hkget)
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · refine ⟨R, hR, by simp [R], ?_, j, k, hjpos, hjk, hklt, hjget, hkget⟩
    intro v
    simp [R]
  · refine ⟨R.reverse, hR.reverse, by simp [R], ?_, R.length - j, R.length - k,
      by omega, by omega, ?_, ?_, ?_⟩
    · intro v
      simp [R]
    · rw [Walk.length_reverse]
      omega
    · rw [Walk.getVert_reverse, show R.length - (R.length - j) = j by omega, hjget]
    · rw [Walk.getVert_reverse, show R.length - (R.length - k) = k by omega, hkget]

end Erdos1091.Voss.CycleArc
