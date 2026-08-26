import ErdosProblems.Erdos118.FiniteGuards

/-!
Preceding siblings in the existing chronological labelled realization
provide numerical anchors. This does not identify the projected commands
or reconstruct their conservative response histories.
-/

namespace Erdos118.FrameAnchors

open LabelledExtensions LabelledFrames LabelledRealization PrefixOrder
open PrefixRealization (Phase run_append)

private theorem length_le_bound (l : List ℕ) (m : ℕ)
    (hp : l.Pairwise (· < ·)) (hb : ∀ x ∈ l, x < m) : l.length ≤ m := by
  have hnd : l.Nodup := hp.imp (fun h ↦ Nat.ne_of_lt h)
  have hs : l.toFinset ⊆ Finset.range m := fun x hx ↦
    Finset.mem_range.mpr (hb x (List.mem_toFinset.mp hx))
  simpa only [List.toFinset_card_of_nodup hnd, Finset.card_range] using
    Finset.card_le_card hs

theorem root_slots_bound (P : Pending) : P.roots.length + 2 ≤ P.position.stem.root := by
  let c := P.position.stem.done.length + 1
  have hp : (0 :: c :: P.roots).Pairwise (· < ·) := by
    rw [List.pairwise_cons, List.pairwise_cons]
    refine ⟨?_, (fun x hx ↦ (P.rootSlots.bounded x hx).1), P.rootSlots.increasing⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.zero_lt_succ _
    · exact (Nat.zero_lt_succ _).trans (P.rootSlots.bounded x hx).1
  have hb : ∀ x ∈ 0 :: c :: P.roots, x < P.position.stem.root := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (Nat.zero_lt_succ _).trans P.position.room
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact P.position.room
      · exact (P.rootSlots.bounded x hx).2.1
  simpa only [List.length_cons, Nat.add_assoc] using length_le_bound _ _ hp hb

theorem leaf_slots_bound (P : Pending) : P.leaves.length + 2 ≤ P.position.size := by
  let c := P.position.entries.length
  have hp : (0 :: c :: P.leaves).Pairwise (· < ·) := by
    rw [List.pairwise_cons, List.pairwise_cons]
    refine ⟨?_, (fun x hx ↦ (P.leafSlots.bounded x hx).1), P.leafSlots.increasing⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact P.position.started
    · exact P.position.started.trans (P.leafSlots.bounded x hx).1
  have hb : ∀ x ∈ 0 :: c :: P.leaves, x < P.position.size := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact P.position.started.trans P.position.unfinished
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact P.position.unfinished
      · exact (P.leafSlots.bounded x hx).2.1
  simpa only [List.length_cons, Nat.add_assoc] using length_le_bound _ _ hp hb

theorem root_sibling_anchor {K : Set ℕ} (hK : K.Infinite) (a : ℕ) :
    ∃ q ∈ K, a + 2 ≤ q ∧ ∀ x ∈ decoratedBlock hK [] (a + 1), q < x := by
  have hf : (frame hK [a]).phase = .pending a 0 := by
    simpa only [Phase.run, Phase.next] using frame_phase hK [a]
  have hs := frame_supported hK [a] (by simp [Phase.run, Phase.next])
  have hb := block_spec hK [] (a + 1) (by trivial)
  cases he : frame hK [a] with
  | initial => simp [he, Frame.phase] at hf
  | terminal S hS => simp [he, Frame.phase] at hf
  | dead => simp [he, Frame.phase] at hf
  | pending P =>
    have hr : P.roots.length = a := (Phase.pending.inj (he ▸ hf)).1
    have hq : P.position.stem.root ∈ (frame hK [a]).decorated := by
      simp [he, Frame.decorated, Position.decorated, Stem.decorated]
    refine ⟨P.position.stem.root, hs _ hq, hr ▸ root_slots_bound P, ?_⟩
    intro x hx
    exact hb.earlier [a] (code_siblings [] (Nat.lt_succ_self a)) _ hq x hx

theorem body_sibling_anchor {K : Set ℕ} (hK : K.Infinite) (p : List ℕ) (r a : ℕ)
    (hp : Phase.root.run p = .pending (r + 1) 0) :
    ∃ q ∈ K, a + 2 ≤ q ∧ ∀ x ∈ decoratedBlock hK p (a + 1), q < x := by
  have hf : (frame hK (p ++ [a])).phase = .pending r a := by
    rw [frame_phase, run_append, hp]
    rfl
  have hv : Phase.root.run (p ++ [a]) ≠ .dead := by
    rw [run_append, hp]
    simp [Phase.run, Phase.next]
  have hs := frame_supported hK (p ++ [a]) hv
  have hb := block_spec hK p (a + 1) (by rw [hp]; trivial)
  cases he : frame hK (p ++ [a]) with
  | initial => simp [he, Frame.phase] at hf
  | terminal S hS => simp [he, Frame.phase] at hf
  | dead => simp [he, Frame.phase] at hf
  | pending P =>
    have hl : P.leaves.length = a := (Phase.pending.inj (he ▸ hf)).2
    have hq : P.position.size ∈ (frame hK (p ++ [a])).decorated := by
      simp [he, Frame.decorated, Position.decorated]
    refine ⟨P.position.size, hs _ hq, hl ▸ leaf_slots_bound P, ?_⟩
    intro x hx
    exact hb.earlier (p ++ [a]) (code_siblings p (Nat.lt_succ_self a)) _ hq x hx

end Erdos118.FrameAnchors
