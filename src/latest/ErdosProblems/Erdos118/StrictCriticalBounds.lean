import ErdosProblems.Erdos118.CriticalPair
import ErdosProblems.Erdos118.AlignedRootCounts

/-! A strict terminal count puts the critical right pair before the
last selected body, with an additional body if its own leaf is last. -/

namespace Erdos118.StrictCriticalBounds

open Negative Negative.Exact LabelledExtensions DecisionStates CutIndices SelectedGapCounts
open LeafSuffixCounts InsideCounts LastBodyRefinement LastMarkerRefinement CriticalPair

theorem selected_root (S T : Stem) (h : ExactAnnotations S T)
    (p : Σ _ : ℕ, ℕ) (hp : p ∈ selected S) : p.1 + 1 ∈ S.rootLabel := by
  obtain ⟨hi, hj⟩ := (mem_selected S p.1 p.2).mp hp
  exact (h.root _).mpr ⟨p.1, p.2, (h.body p.1 hi p.2).mp hj, rfl⟩

private theorem root_last_mem (S : Stem) (hS : S.rootLabel ≠ []) :
    S.rootLabel.getLastD 0 ∈ S.rootLabel := by
  cases he : S.rootLabel with
  | nil => exact (hS he).elim
  | cons a l => simpa only [List.getLastD_cons] using List.getLastD_mem_cons (a := a) (l := l)

theorem before_last (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    {n : ℕ} {p : Σ _ : ℕ, ℕ} (hp : Spec S.stem n p)
    (hn : (lastLabel S).length < n) : p.1 < lastIndex S := by
  have hr := selected_root S.stem T h p hp.1
  have hS := List.ne_nil_of_mem hr
  have hle := selected_index_le_last S T h hS p hp.1
  by_contra hnlt
  have he : p.1 = lastIndex S := by omega
  have hb := SelectedEndpointCounts.remaining_last_le S T h hS p.2
  rw [← he, hp.2] at hb
  omega

theorem intermediate (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    {n : ℕ} {p : Σ _ : ℕ, ℕ} (hp : Spec S.stem n p)
    (hn : (lastLabel S).length + 1 < n)
    (hlast : ∀ j ∈ S.stem.bodyLabels.getD p.1 [], j ≤ p.2) :
    ∃ a ∈ selected S.stem, p.1 < a.1 ∧ a.1 < lastIndex S := by
  have hr := selected_root S.stem T h p hp.1
  have hS := List.ne_nil_of_mem hr
  have hb := before_last S T h hp (by omega)
  by_contra he
  have hbody : ∀ a ∈ selected S.stem, a.1 < lastIndex S → a.1 ≤ p.1 := by
    intro a ha hal
    by_contra hnot
    exact he ⟨a, ha, by omega, hal⟩
  have hleaf : ∀ a ∈ selected S.stem, a.1 = p.1 → a.2 ≤ p.2 := by
    intro a ha hai
    have hm := (Finset.mem_sigma.mp ha).2
    have hm' : a.2 ∈ S.stem.bodyLabels.getD p.1 [] := by
      simpa only [hai, List.mem_toFinset] using hm
    exact hlast a.2 hm'
  have hc := (SelectedEndpointCounts.remaining_card_iff S T h hS p.1 p.2 hp.1).mpr
    ⟨hb, hbody, hleaf⟩
  rw [hp.2] at hc
  omega

theorem ranks (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T)
    {n : ℕ} (hp : Spec S.stem n (CriticalPair.pair S.stem n))
    (hn : (lastLabel S).length + 1 < n) :
    0 < bodyRank S.stem n ∧ bodyRank S.stem n < S.stem.rootLabel.length ∧
      (last S.stem n = true → bodyRank S.stem n + 1 < S.stem.rootLabel.length) := by
  classical
  let p := CriticalPair.pair S.stem n
  have hr : p.1 + 1 ∈ S.stem.rootLabel := selected_root S.stem T h p hp.1
  have hS := List.ne_nil_of_mem hr
  have hlast := root_last_mem S.stem hS
  have hb : p.1 < lastIndex S := before_last S T h hp (by omega)
  have hmax : p.1 + 1 < S.stem.rootLabel.getLastD 0 := by
    unfold lastIndex at hb
    omega
  let F := S.stem.rootLabel.toFinset.filter (fun i ↦ i ≤ p.1 + 1)
  have hmem : p.1 + 1 ∈ F := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, le_rfl⟩
  have hnot : S.stem.rootLabel.getLastD 0 ∉ F := by
    intro hm
    exact (not_le_of_gt hmax) (Finset.mem_filter.mp hm).2
  have hsub : F ⊆ S.stem.rootLabel.toFinset := Finset.filter_subset _ _
  have hcard : S.stem.rootLabel.toFinset.card = S.stem.rootLabel.length :=
    List.toFinset_card_of_nodup S.stem.label_pairwise.nodup
  have hproper : F.card < S.stem.rootLabel.toFinset.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,
      fun he ↦ hnot (he ▸ List.mem_toFinset.mpr hlast)⟩)
  refine ⟨Finset.card_pos.mpr ⟨_, hmem⟩, by change F.card < _; omega, ?_⟩
  intro hl
  have hl' : ∀ j ∈ S.stem.bodyLabels.getD p.1 [], j ≤ p.2 := by
    simpa only [last, decide_eq_true_eq] using hl
  obtain ⟨a, ha, hpa, hal⟩ := intermediate S T h hp hn hl'
  change p.1 < a.1 at hpa
  have har := selected_root S.stem T h a ha
  have hak : a.1 + 1 ∉ F := by intro hm; have := (Finset.mem_filter.mp hm).2; omega
  have hsub' : insert (a.1 + 1) F ⊆ S.stem.rootLabel.toFinset :=
    Finset.insert_subset (List.mem_toFinset.mpr har) hsub
  have hmaxa : a.1 + 1 < S.stem.rootLabel.getLastD 0 := by unfold lastIndex at hal; omega
  have hnot' : S.stem.rootLabel.getLastD 0 ∉ insert (a.1 + 1) F := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    · exact hnot hm
  have hcard' := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub', fun he ↦ hnot' (he ▸ List.mem_toFinset.mpr hlast)⟩)
  rw [Finset.card_insert_of_notMem hak, hcard] at hcard'
  exact hcard'

theorem terminal (B : SimpleGraph G) (S T : Completed)
    (hp : GraphPayoff.payoff B .inside S T = true)
    (hlen : 1 < S.stem.rootLabel.length) (hstrict : beforeLast S < beforeLast T) :
    3 ≤ (lastLabel S).length ∧
      Spec T.stem (lastLabel S).length (CriticalPair.pair T.stem (lastLabel S).length) ∧
      (CriticalPair.pair T.stem (lastLabel S).length).1 < lastIndex T ∧
      0 < bodyRank T.stem (lastLabel S).length ∧
      bodyRank T.stem (lastLabel S).length < T.stem.rootLabel.length ∧
      (last T.stem (lastLabel S).length = true →
        bodyRank T.stem (lastLabel S).length + 1 < T.stem.rootLabel.length) := by
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hp
  have hpreS := (AlignedRootCounts.beforeLast_pos_iff S T.stem hc.exactLeft).mpr hlen
  have hlenT := (AlignedRootCounts.beforeLast_pos_iff T S.stem hc.exactRight).mp
    (hpreS.trans hstrict)
  have hS : S.stem.rootLabel ≠ [] := by intro he; simp [he] at hlen
  have hT : T.stem.rootLabel ≠ [] := by intro he; simp [he] at hlenT
  have hTpos := List.length_pos_iff.mpr
    (TerminalCountRefinement.lastLabel_nonempty T S.stem hc.exactRight hT)
  have hgap := last_counts_of_before_lt S T hc hr ho hS hT hstrict
  have htotal := selected_inside S T hc hr ho
  have hdecomp := selected_card_decomposition S T.stem hc.exactLeft hS
  have hs := pair_spec T.stem (n := (lastLabel S).length) (by omega) (by omega)
  exact ⟨by omega, hs, before_last T S.stem hc.exactRight hs (by omega),
    ranks T S.stem hc.exactRight hs (by omega)⟩

end Erdos118.StrictCriticalBounds
