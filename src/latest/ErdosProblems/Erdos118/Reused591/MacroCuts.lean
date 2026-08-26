import ErdosProblems.Erdos118.Reused591.MacroAncestry

namespace Erdos118.Reused591

/-!
# Actual cross-root cuts end at retained relaxed prefixes

All inputs of one macro are consecutive in construction time. A
coordinate of another root lying between two adjacent coordinates of
a completed branch therefore forces a boundary after an entire macro.
The corresponding retained cursor is relaxed, not complete.
-/

namespace Erdos591.Positive.Game.Macro

theorem Extension.nonterminal {q : ℕ} {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q w xs v) : w.terminal = false := by
  cases h with
  | stop _ _ _ _ _ hr _ _ => exact LabeledWord.read_nonterminal hr
  | more _ _ _ _ _ _ _ hr _ _ _ => exact LabeledWord.read_nonterminal hr

namespace Forest

theorem Expansion.terminal_eq {q : ℕ} {w v : LabeledWord} {xs : Block}
    (h : Expansion q w xs v) (hw : w.terminal = true) : v = w := by
  cases h with
  | idle => rfl
  | live h =>
      have hn := h.nonterminal
      simp [hw] at hn

theorem prefix_length_at_cut {xs pre : List ℕ} (hxs : xs.Nodup)
    (hpre : List.IsPrefix pre xs) {k y : ℕ} (hk : k + 1 < xs.length)
    (hx : xs.getD k 0 ∈ pre) (hbelow : ∀ x ∈ pre, x < y)
    (hy : y < xs.getD (k + 1) 0) : pre.length = k + 1 := by
  have hk' : k < xs.length := by omega
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  rw [List.getD_eq_getElem _ _ hk'] at heq
  have heq' : xs[i]'(hi.trans_le hpre.length_le) = xs[k] :=
    (hpre.getElem hi).symm.trans heq
  have hik : i = k := hxs.getElem_inj_iff.mp heq'
  have hlow : k < pre.length := hik ▸ hi
  have hupp : pre.length ≤ k + 1 := by
    by_contra hn
    have hi' : k + 1 < pre.length := by omega
    have hlt := hbelow _ (List.getElem_mem hi')
    have hgt : y < pre[k + 1] := by
      rw [hpre.getElem hi']
      simpa only [List.getD_eq_getElem _ _ hk] using hy
    exact lt_asymm hlt hgt
  omega

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem Descendant.terminal_cursor_eq {p n : ℕ} (h : Descendant p n)
    (hp : (node hH b p).cursor.terminal = true) : (node hH b n).cursor = (node hH b p).cursor := by
  induction h with
  | refl => rfl
  | @tail n m hn hm ih =>
      obtain ⟨j, rfl⟩ := hm
      have ht : (node hH b n).cursor.terminal = true := by rw [ih]; exact hp
      exact ((child_expansion hH b n j).terminal_eq ht).trans ih

theorem segment_descendant (n : ℕ) (s : Segment) (hs : s ∈ (node hH b n).segments) :
    Descendant (s.1 + 1) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [Node.initial] at hs
      | succ n =>
          rw [node_succ_segments] at hs
          rcases List.mem_append.mp hs with hs | hs
          · have hd := ih (Nat.unpair n).1
              (Nat.lt_succ_of_le (Nat.unpair_left_le n)) hs
            exact hd.tail ⟨(Nat.unpair n).2, by simp [child]⟩
          · have heq : s = (n, (chunkAt hH b n).block) := by simpa using hs
            subst s
            exact .refl

theorem node_succ_coordinates (r : ℕ) : (node hH b (r + 1)).cursor.coordinates =
    (node hH b (Nat.unpair r).1).cursor.coordinates ++ (chunkAt hH b r).block.map Prod.snd := by
  rw [(node hH b (r + 1)).coordinates, Node.atoms, node_succ_segments]
  simp only [List.flatMap_append, List.flatMap_singleton, List.map_append]
  change (node hH b (Nat.unpair r).1).atoms.map Prod.snd ++ _ = _
  rw [← (node hH b (Nat.unpair r).1).coordinates]

theorem value_mem_raw {xs : Block} {x : ℕ} (hx : x ∈ xs.map Prod.snd) : x ∈ raw xs := by
  have hsub : List.Sublist (xs.map Prod.snd) (raw xs) := by
    simpa [raw, Atomic.tag, List.map_map, Function.comp_def] using
      Atomic.values_sublist_inputs (Atomic.tag false xs)
  exact hsub.subset hx

/-- Locate a coordinate in its unique construction block while
retaining the ancestry and root ownership certificates. -/
theorem coordinate_chunk (n : ℕ) {x : ℕ} (hx : x ∈ (node hH b n).cursor.coordinates) :
    ∃ r, Descendant (r + 1) n ∧ root (r + 1) = root n ∧
      x ∈ (chunkAt hH b r).block.map Prod.snd := by
  rw [(node hH b n).coordinates, Node.atoms, List.map_flatMap] at hx
  obtain ⟨s, hs, hxs⟩ := List.mem_flatMap.mp hx
  refine ⟨s.1, segment_descendant hH b n s hs, segment_root hH b n s hs, ?_⟩
  simpa only [node_segment_block hH b n s hs] using hxs

theorem coordinates_below_chunk (n r : ℕ) (hn : n ≤ r) :
    ∀ x ∈ (node hH b n).cursor.coordinates, ∀ y ∈ raw (chunkAt hH b r).block, x < y := by
  intro x hx y hy
  have hx' := node_support_stage hH b n r hn (LabeledWord.coordinate_mem_support hx)
  exact (Finset.le_sup (f := id) hx').trans_lt ((chunkAt hH b r).fresh y hy)

/-- The geometric boundary theorem used by retrospective cut-label
coarsening. Every actual cross-root cut is the end of a retained
selected-leaf prefix with the exact coordinate length. -/
theorem cut_relaxed_prefix (n m : ℕ) (hnm : root n ≠ root m) (k : ℕ)
    (hcut : Payoff.Cut (node hH b n).cursor.coordinates (node hH b m).cursor.coordinates k) :
    ∃ p, Descendant p n ∧ (node hH b p).cursor.relaxed = true ∧
      (node hH b p).cursor.coordinates.length = k + 1 := by
  obtain ⟨hk, y, hy, hxy, hyz⟩ := hcut
  let x := (node hH b n).cursor.coordinates.getD k 0
  have hx : x ∈ (node hH b n).cursor.coordinates := by
    dsimp only [x]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  obtain ⟨r, hr, hrootr, hxr⟩ := coordinate_chunk hH b n hx
  obtain ⟨s, _, hroots, hys⟩ := coordinate_chunk hH b m hy
  have hrs : r ≠ s := by
    intro heq
    exact hnm (hrootr.symm.trans ((congrArg (fun i => root (i + 1)) heq).trans hroots))
  have hrs' : r < s := by
    rcases lt_or_gt_of_ne hrs with hrs | hsr
    · exact hrs
    · have hyx := chunks_separated hH b s r hsr y (value_mem_raw hys) x (value_mem_raw hxr)
      exact (lt_asymm hxy hyx).elim
  have hxpre : x ∈ (node hH b (r + 1)).cursor.coordinates := by
    rw [node_succ_coordinates]
    exact List.mem_append_right _ hxr
  have hlen : (node hH b (r + 1)).cursor.coordinates.length = k + 1 :=
    prefix_length_at_cut (node_coordinates_increasing hH b n).nodup
      (hr.coordinates_prefix hH b) hk hxpre
      (fun a ha => coordinates_below_chunk hH b (r + 1) s hrs' a ha y (value_mem_raw hys)) hyz
  have hnot : (node hH b (r + 1)).cursor.terminal ≠ true := by
    intro ht
    have heq := hr.terminal_cursor_eq hH b ht
    have hl := congrArg (fun w : LabeledWord => w.coordinates.length) heq
    omega
  exact ⟨r + 1, hr, (node_end hH b r).resolve_left hnot, hlen⟩

#print axioms prefix_length_at_cut
#print axioms segment_descendant
#print axioms cut_relaxed_prefix

end Forest

end Erdos591.Positive.Game.Macro

end Erdos118.Reused591
