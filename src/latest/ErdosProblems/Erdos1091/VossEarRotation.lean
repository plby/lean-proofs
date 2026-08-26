/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossEarShift

/-!
# Rotating maximum attachment paths

A chord from a maximum attachment path's last vertex rotates the path to
another maximum attachment path on exactly the same vertex set.
-/

open SimpleGraph

namespace Erdos1091.Voss

namespace AttachmentPath

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

def rotate (P : AttachmentPath G S) (j : ℕ) (hj : j < P.walk.length)
    (h : G.Adj (P.walk.getVert j) P.finish) : AttachmentPath G S where
  start := P.start
  finish := P.walk.getVert (j + 1)
  walk := PathRotation.rotate P.walk j h
  isPath := PathRotation.isPath P.walk P.isPath j hj h
  start_mem := P.start_mem
  finish_notMem := by
    intro hvS
    have hv := P.only_start _ (P.walk.getVert_mem_support (j + 1)) hvS
    have hi : j + 1 = 0 := P.isPath.getVert_injOn
      (show j + 1 ≤ P.walk.length by omega) (show 0 ≤ P.walk.length by omega)
      (hv.trans P.walk.getVert_zero.symm)
    omega
  only_start := by
    intro v hv hvS
    exact P.only_start v ((PathRotation.mem_support_iff P.walk j hj h v).mp hv) hvS

@[simp] theorem rotate_length (P : AttachmentPath G S) (j : ℕ) (hj : j < P.walk.length)
    (h : G.Adj (P.walk.getVert j) P.finish) : (P.rotate j hj h).walk.length = P.walk.length :=
  PathRotation.length_eq P.walk j hj h

theorem mem_rotate_support_iff (P : AttachmentPath G S) (j : ℕ) (hj : j < P.walk.length)
    (h : G.Adj (P.walk.getVert j) P.finish) (v : V) :
    v ∈ (P.rotate j hj h).walk.support ↔ v ∈ P.walk.support :=
  PathRotation.mem_support_iff P.walk j hj h v

theorem isChord_close (P : AttachmentPath G S) {w : V}
    (h : G.Adj P.finish w) (hw : w ∉ P.walk.support) (hwS : w ∈ S)
    {e : Sym2 V} (he : P.walk.IsChord e) : (P.close h hw hwS).walk.IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hnot, hx, hy⟩ := Walk.isChord_sym2Mk.mp he
    refine ⟨hxy, ?_, ?_, ?_⟩
    · intro he
      change s(x, y) ∈ (P.walk.concat h).edges at he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
      rcases he with he | heq
      · exact hnot he
      · rcases Sym2.eq_iff.mp heq with ⟨_, hyw⟩ | ⟨hxw, _⟩
        · exact hw (hyw ▸ hy)
        · exact hw (hxw ▸ hx)
    · change x ∈ (P.walk.concat h).support
      rw [Walk.support_concat]
      exact List.mem_append_left _ hx
    · change y ∈ (P.walk.concat h).support
      rw [Walk.support_concat]
      exact List.mem_append_left _ hy

theorem close_snd (P : AttachmentPath G S) {w : V}
    (h : G.Adj P.finish w) (hw : w ∉ P.walk.support) (hwS : w ∈ S) :
    (P.close h hw hwS).walk.snd = P.walk.snd := by
  have hlen : 1 ≤ P.walk.length := P.length_pos
  simp only [close, Walk.snd, Walk.concat_eq_append, Walk.getVert_append', if_pos hlen]

end AttachmentPath

namespace PathRotation

theorem snd_eq {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (j : ℕ) (hj : 1 ≤ j) (hjl : j < p.length)
    (h : G.Adj (p.getVert j) b) : (rotate p j h).snd = p.snd := by
  simp only [rotate, Walk.snd, Walk.getVert_append', Walk.take_length,
    Nat.min_eq_left hjl.le, if_pos hj, Walk.take_getVert, Nat.min_eq_right hj]

/-- The edge cut by a genuine rotation becomes a chord of the new path. -/
theorem cut_isChord {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (j : ℕ) (hj : j + 1 < p.length)
    (h : G.Adj (p.getVert j) b) :
    (rotate p j h).IsChord s(p.getVert j, p.getVert (j + 1)) := by
  have hj' : j < p.length := by omega
  have hdisj := Erdos1105.path_prefix_suffix_disjoint p hp
    (Nat.lt_succ_self j) (show j + 1 ≤ p.length by omega)
  have hjTake : p.getVert j ∈ (p.take j).support := (p.take j).end_mem_support
  have hjDrop : p.getVert (j + 1) ∈ (p.drop (j + 1)).support :=
    (p.drop (j + 1)).start_mem_support
  refine ⟨p.adj_getVert_succ hj', ?_,
    (mem_support_iff p j hj' h _).mpr (p.getVert_mem_support j),
    (mem_support_iff p j hj' h _).mpr (p.getVert_mem_support (j + 1))⟩
  intro he
  simp only [rotate, Walk.edges_append, Walk.edges_cons, Walk.edges_reverse,
    List.mem_append, List.mem_cons, List.mem_reverse] at he
  rcases he with he | he | he
  · exact hdisj ((p.take j).snd_mem_support_of_mem_edges he) hjDrop
  · have hlast : p.getVert (j + 1) = b := (Sym2.mkEmbedding (p.getVert j)).injective he
    have hidx := (hp.getVert_eq_end_iff (show j + 1 ≤ p.length by omega)).mp hlast
    omega
  · exact hdisj hjTake ((p.drop (j + 1)).fst_mem_support_of_mem_edges he)

end PathRotation

/-- A terminal chord not returning to the start has an internal index
with room for the rotation's new terminal vertex. -/
theorem exists_index_of_terminal_chord {V : Type*} {G : SimpleGraph V} {a b v : V}
    (p : G.Walk a b) (hv : v ∈ p.support) (hvStart : v ≠ a)
    (hadj : G.Adj b v) (hnot : s(b, v) ∉ p.edges) :
    ∃ j, p.getVert j = v ∧ 1 ≤ j ∧ j + 1 < p.length := by
  obtain ⟨j, hjget, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hjpos : 1 ≤ j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hvStart (by simpa only [hj0, Walk.getVert_zero] using hjget.symm)
  have hjlt : j < p.length := by
    by_contra h
    have hje : j = p.length := by omega
    exact hadj.ne (by simpa only [hje, Walk.getVert_length] using hjget)
  have hjgap : j + 1 < p.length := by
    by_contra h
    have hje : j + 1 = p.length := by omega
    apply hnot
    rw [p.mk_mem_edges_iff_exists]
    refine ⟨j, hjlt, ?_⟩
    rw [hje, Walk.getVert_length, hjget]
    exact Sym2.eq_swap
  exact ⟨j, hjget, hjpos, hjgap⟩

/-- An edge of a simple path incident with an internal indexed vertex
joins it to its predecessor or successor. -/
theorem path_edge_at_index {V : Type*} {G : SimpleGraph V} {a b v : V}
    (p : G.Walk a b) (hp : p.IsPath) {i : ℕ} (hi : 0 < i) (hil : i < p.length)
    (he : s(p.getVert i, v) ∈ p.edges) :
    v = p.getVert (i - 1) ∨ v = p.getVert (i + 1) := by
  obtain ⟨k, hk, heq⟩ := p.mk_mem_edges_iff_exists.mp he
  rcases Sym2.eq_iff.mp heq with ⟨hki, hkv⟩ | ⟨hkv, hki⟩
  · have hidx : k = i := hp.getVert_injOn hk.le hil.le hki
    right
    simpa only [hidx] using hkv.symm
  · have hidx : k + 1 = i := hp.getVert_injOn
      (show k + 1 ≤ p.length by omega) hil.le hki
    left
    have he : k = i - 1 := by omega
    simpa only [he] using hkv.symm

/-- Minimum degree three gives an off-path neighbour at any internal
vertex of a simple path. -/
theorem exists_adj_not_mem_path_edges {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) {i : ℕ} (hi : 0 < i) (hil : i < p.length)
    (hdegree : 3 ≤ G.degree (p.getVert i)) :
    ∃ v, G.Adj (p.getVert i) v ∧ s(p.getVert i, v) ∉ p.edges := by
  classical
  have hpair : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card ≤ 2 := by
    simpa using Finset.card_insert_le (p.getVert (i - 1)) ({p.getVert (i + 1)} : Finset V)
  have hsmall : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card <
      (G.neighborFinset (p.getVert i)).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨v, hv, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  refine ⟨v, by simpa using hv, ?_⟩
  intro he
  rcases path_edge_at_index p hp hi hil he with heq | heq
  · exact hnot (by simp [heq])
  · exact hnot (by simp [heq])

end Erdos1091.Voss
