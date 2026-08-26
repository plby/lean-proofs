import ErdosProblems.Erdos118.SelectedEndpointCounts
import Mathlib.Order.Interval.Finset.Nat

/-! The selected suffix count is an exact finite rank. The total
critical-pair definition is used only with a proved specification. -/

namespace Erdos118.CriticalPair

open LabelledExtensions SelectedGapCounts LeafSuffixCounts

theorem suffix_card_lt (S : Stem) {p q : Σ _ : ℕ, ℕ}
    (hp : p ∈ selected S) (hpq : p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2) :
    (remaining S q.1 q.2).card < (remaining S p.1 p.2).card := by
  have hsub : remaining S q.1 q.2 ⊆ remaining S p.1 p.2 := by
    intro r hr
    obtain ⟨hm, ha⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hm, by omega⟩
  have hself : p ∈ remaining S p.1 p.2 :=
    Finset.mem_filter.mpr ⟨hp, Or.inr ⟨rfl, le_rfl⟩⟩
  have hnot : p ∉ remaining S q.1 q.2 := by
    intro hm
    have h := (Finset.mem_filter.mp hm).2
    omega
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun he ↦ hnot (he ▸ hself)⟩)

def Spec (S : Stem) (n : ℕ) (p : Σ _ : ℕ, ℕ) : Prop :=
  p ∈ selected S ∧ (remaining S p.1 p.2).card = n

theorem Spec.unique {S : Stem} {n : ℕ} {p q : Σ _ : ℕ, ℕ}
    (hp : Spec S n p) (hq : Spec S n q) : p = q := by
  have hfst : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · have hlt := suffix_card_lt S hp.1 (Or.inl h)
      rw [hp.2, hq.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact h
    · have hlt := suffix_card_lt S hq.1 (Or.inl h)
      rw [hp.2, hq.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  have hsnd : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · have hlt := suffix_card_lt S hp.1 (Or.inr ⟨hfst, h⟩)
      rw [hp.2, hq.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact h
    · have hlt := suffix_card_lt S hq.1 (Or.inr ⟨hfst.symm, h⟩)
      rw [hp.2, hq.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  exact Sigma.ext hfst (heq_of_eq hsnd)

theorem exists_spec (S : Stem) {n : ℕ} (hn : 0 < n) (hbound : n ≤ (selected S).card) :
    ∃ p, Spec S n p := by
  classical
  let count := fun p : Σ _ : ℕ, ℕ ↦ (remaining S p.1 p.2).card
  have hsub : (selected S).image count ⊆ Finset.Icc 1 (selected S).card := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hself : p ∈ remaining S p.1 p.2 :=
      Finset.mem_filter.mpr ⟨hp, Or.inr ⟨rfl, le_rfl⟩⟩
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr ⟨p, hself⟩, Finset.card_filter_le _ _⟩
  have hinj : Set.InjOn count (selected S) := by
    intro p hp q hq he
    exact Spec.unique ⟨hp, rfl⟩ ⟨hq, he.symm⟩
  have he : (selected S).image count = Finset.Icc 1 (selected S).card := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hm : n ∈ (selected S).image count := he ▸ Finset.mem_Icc.mpr ⟨hn, hbound⟩
  obtain ⟨p, hp, hc⟩ := Finset.mem_image.mp hm
  exact ⟨p, hp, hc⟩

noncomputable def pair (S : Stem) (n : ℕ) : Σ _ : ℕ, ℕ := by
  classical
  exact if h : ∃ p, Spec S n p then Classical.choose h else ⟨0, 0⟩

theorem pair_eq_of_spec {S : Stem} {n : ℕ} {p : Σ _ : ℕ, ℕ} (hp : Spec S n p) :
    pair S n = p := by
  classical
  rw [pair, dif_pos ⟨p, hp⟩]
  exact (Classical.choose_spec (show ∃ q, Spec S n q from ⟨p, hp⟩)).unique hp

theorem pair_spec (S : Stem) {n : ℕ} (hn : 0 < n) (hbound : n ≤ (selected S).card) :
    Spec S n (pair S n) := by
  obtain ⟨p, hp⟩ := exists_spec S hn hbound
  rw [pair_eq_of_spec hp]
  exact hp

noncomputable def bodyRank (S : Stem) (n : ℕ) : ℕ :=
  (S.rootLabel.toFinset.filter (fun i ↦ i ≤ (pair S n).1 + 1)).card

noncomputable def leafRank (S : Stem) (n : ℕ) : ℕ :=
  ((S.bodyLabels.getD (pair S n).1 []).toFinset.filter (fun j ↦ j ≤ (pair S n).2)).card

noncomputable def last (S : Stem) (n : ℕ) : Bool := by
  classical
  exact decide (∀ j ∈ S.bodyLabels.getD (pair S n).1 [], j ≤ (pair S n).2)

theorem bodyRank_le (S : Stem) (n : ℕ) : bodyRank S n ≤ S.rootLabel.length := by
  exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)

theorem leafRank_le (S : Stem) (n : ℕ) :
    leafRank S n ≤ (S.bodyLabels.getD (pair S n).1 []).length :=
  (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)

theorem leafRank_pos {S : Stem} {n : ℕ} (h : Spec S n (pair S n)) : 0 < leafRank S n := by
  have hm := (Finset.mem_sigma.mp h.1).2
  exact Finset.card_pos.mpr ⟨(pair S n).2, Finset.mem_filter.mpr ⟨hm, le_rfl⟩⟩

theorem last_iff_leafRank_eq (S : Stem) (n : ℕ) (h : Spec S n (pair S n)) :
    last S n = true ↔ leafRank S n = (S.bodyLabels.getD (pair S n).1 []).length := by
  classical
  have hi : (pair S n).1 < S.bodyLabels.length :=
    (Finset.mem_range.mp (Finset.mem_sigma.mp h.1).1)
  have hnd : (S.bodyLabels.getD (pair S n).1 []).Nodup := by
    rw [List.getD_eq_getElem _ _ hi]
    exact (ProjectionBounds.body_label_pairwise S _ hi).nodup
  rw [← List.toFinset_card_of_nodup hnd]
  simp only [last, leafRank, decide_eq_true_eq, Finset.card_filter_eq_iff,
    List.mem_toFinset]

end Erdos118.CriticalPair
