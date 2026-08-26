import ErdosProblems.Erdos118.SelectedEndpointCounts
import ErdosProblems.Erdos118.PendingCounts

/-! Transfer the finite selected-suffix criterion through actual preserved
root/body annotations and exact pending slot lists. -/

namespace Erdos118.PendingEndpointCounts

open LabelledExtensions LabelledFrames DecisionStates CutIndices SelectedGapCounts
open InsideCounts LastBodyRefinement LastMarkerRefinement LeafSuffixCounts

theorem criterion (P : Pending) (S : Completed) (T : Stem)
    (h : ExactAnnotations S.stem T) (hP : ExactSlots.Exact (.leaf P))
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) :
    (remaining S.stem P.position.stem.done.length P.position.entries.length).card =
        (lastLabel S).length + 1 ↔ ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [] := by
  let i := P.position.stem.done.length
  let j := P.position.entries.length
  have hroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root _ rfl)
  have hS : S.stem.rootLabel ≠ [] := PendingCounts.rootLabel_ne_nil_of_extension P S hext
  have hprefix : P.position.bodyLabels <+: S.stem.bodyLabels := hext.labels.bodies
  have hiP : i < P.position.bodyLabels.length := by
    simp [i, Position.bodyLabels, Stem.bodyLabels]
  have hiS := hiP.trans_le hprefix.length_le
  have hlabel : S.stem.bodyLabels[i] = P.position.label := by
    rw [← hprefix.getElem hiP]
    simp [i, Position.bodyLabels, Stem.bodyLabels]
  have hij : (⟨i, j⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem :=
    (mem_selected _ _ _).mpr ⟨hiS, hlabel ▸ P.leafSelected⟩
  have hcurrent : i + 1 ∈ S.stem.rootLabel := hroot ▸ P.rootSelected
  have hm : S.stem.rootLabel.getLastD 0 ∈ S.stem.rootLabel := by
    cases he : S.stem.rootLabel with
    | nil => exact (hS he).elim
    | cons a l => simpa only [List.getLastD_cons] using List.getLastD_mem_cons (a := a) (l := l)
  have hlastpos : 0 < S.stem.rootLabel.getLastD 0 := by
    have hle := (S.stem.label_pairwise.imp Nat.le_of_lt).rel_getLast hcurrent
    have he : S.stem.rootLabel.getLastD 0 = S.stem.rootLabel.getLast hS := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hS]
      rfl
    rw [he]
    omega
  have hlast : S.stem.rootLabel.getLastD 0 = lastIndex S + 1 := by
    unfold lastIndex
    omega
  rw [SelectedEndpointCounts.remaining_card_iff S T h hS i j hij]
  constructor
  · rintro ⟨hi, hbody, hleaf⟩
    refine ⟨S.stem.rootLabel.getLastD 0, ?_, ?_⟩
    · rw [hP.1]
      apply (P.position.stem.label_pairwise.sublist List.filter_sublist).eq_of_mem_iff (by simp)
      intro x
      constructor
      · intro hx
        obtain ⟨hxr, hxi⟩ := List.mem_filter.mp hx
        have hxi' : i + 1 < x := of_decide_eq_true hxi
        have hxS : x ∈ S.stem.rootLabel := hroot ▸ hxr
        obtain ⟨a, b, hab, hax⟩ := (h.root x).mp hxS
        have haxroot := S.stem.label_before_root x hxS
        have ha : a < S.stem.bodyLabels.length := by
          simp only [Stem.bodyLabels, List.length_map, S.full]
          omega
        have has : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem :=
          (mem_selected _ _ _).mpr ⟨ha, (h.body a ha b).mpr hab⟩
        have hmax : a ≤ lastIndex S := selected_index_le_last S T h hS ⟨a, b⟩ has
        have hae : a = lastIndex S := by
          by_contra hn
          have hle : a ≤ i := hbody ⟨a, b⟩ has (lt_of_le_of_ne hmax hn)
          omega
        exact List.mem_singleton.mpr (by omega)
      · intro hx
        have he := List.mem_singleton.mp hx
        subst x
        exact List.mem_filter.mpr ⟨hroot ▸ hm, decide_eq_true (by change i + 1 < _; omega)⟩
    · rw [hP.2]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨hxl, hxj⟩ := List.mem_filter.mp hx
      have has : (⟨i, x⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem :=
        (mem_selected _ _ _).mpr ⟨hiS, hlabel ▸ hxl⟩
      have hle : x ≤ j := hleaf ⟨i, x⟩ has rfl
      exact (not_lt_of_ge hle) (of_decide_eq_true hxj)
  · rintro ⟨c, hR, hL⟩
    have hc : S.stem.rootLabel.getLastD 0 = c := by
      rw [hroot]
      exact ExactSlots.pending_next_last_root P hP hR
    have hci : i + 1 < c := (P.rootSlots.bounded c (hR ▸ List.mem_singleton_self _)).1
    refine ⟨by omega, ?_, ?_⟩
    · intro a ha hbefore
      by_contra hn
      obtain ⟨hai, haj⟩ := (mem_selected _ _ _).mp ha
      have hacut := (h.body _ hai _).mp haj
      have haroot : a.1 + 1 ∈ P.position.stem.rootLabel :=
        hroot ▸ (h.root _).mpr ⟨a.1, a.2, hacut, rfl⟩
      have hmR : a.1 + 1 ∈ P.roots := by
        rw [hP.1]
        exact List.mem_filter.mpr ⟨haroot, decide_eq_true (by change i + 1 < _; omega)⟩
      rw [hR, List.mem_singleton] at hmR
      omega
    · intro a ha hai
      by_contra hn
      obtain ⟨haS, haj⟩ := (mem_selected _ _ _).mp ha
      have halabel : a.2 ∈ P.position.label := by simpa only [hai, hlabel] using haj
      have hmL : a.2 ∈ P.leaves := by
        rw [hP.2]
        exact List.mem_filter.mpr ⟨halabel, decide_eq_true (show j < a.2 from Nat.lt_of_not_ge hn)⟩
      rw [hL] at hmL
      exact List.not_mem_nil hmL

end Erdos118.PendingEndpointCounts
