import ErdosProblems.Erdos118.Reused591.SelectedPairEndpoints
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos118.Reused591

/-!
# Recover a selected body/leaf pair from its remaining-cut count

Suffix cardinality is strictly decreasing in the lexicographic order
on positive selected pairs. Thus any pair with a prescribed remaining
count is unique. The total definition uses a default only when no such
pair exists; every application to an actual critical cursor supplies
and proves the pair specification.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem selectedPairSuffix_card_lt {w : LabeledWord} {p q : Σ _ : ℕ, ℕ}
    (hp : p ∈ w.selectedLeafPairs) (hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    (hq₁ : 0 < q.1) (hq₂ : 0 < q.2)
    (hpq : p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2) :
    (w.selectedLeafPairsFrom (q.1 - 1) (q.2 - 1)).card <
      (w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1)).card := by
  have hsub : w.selectedLeafPairsFrom (q.1 - 1) (q.2 - 1) ⊆
      w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1) := by
    intro r hr
    obtain ⟨hmem, hafter⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    omega
  have hself : p ∈ w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1) :=
    Finset.mem_filter.mpr ⟨hp, Or.inr ⟨by omega, by omega⟩⟩
  have hnot : p ∉ w.selectedLeafPairsFrom (q.1 - 1) (q.2 - 1) := by
    intro h
    have hafter := (Finset.mem_filter.mp h).2
    change q.1 - 1 + 1 < p.1 ∨ q.1 - 1 + 1 = p.1 ∧ q.2 - 1 + 1 ≤ p.2 at hafter
    omega
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hself)⟩

def CriticalPairSpec (w : LabeledWord) (n : ℕ) (p : Σ _ : ℕ, ℕ) : Prop :=
  p ∈ w.selectedLeafPairs ∧ 0 < p.1 ∧ 0 < p.2 ∧
    (w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1)).card = n

theorem CriticalPairSpec.unique {w : LabeledWord} {n : ℕ} {p q : Σ _ : ℕ, ℕ}
    (hp : w.CriticalPairSpec n p) (hq : w.CriticalPairSpec n q) : p = q := by
  have hfst : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · have hlt := selectedPairSuffix_card_lt hp.1 hp.2.1 hp.2.2.1 hq.2.1 hq.2.2.1 (Or.inl h)
      rw [hp.2.2.2, hq.2.2.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact h
    · have hlt := selectedPairSuffix_card_lt hq.1 hq.2.1 hq.2.2.1 hp.2.1 hp.2.2.1 (Or.inl h)
      rw [hp.2.2.2, hq.2.2.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  have hsnd : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · have hlt := selectedPairSuffix_card_lt hp.1 hp.2.1 hp.2.2.1 hq.2.1 hq.2.2.1
        (Or.inr ⟨hfst, h⟩)
      rw [hp.2.2.2, hq.2.2.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    · exact h
    · have hlt := selectedPairSuffix_card_lt hq.1 hq.2.1 hq.2.2.1 hp.2.1 hp.2.2.1
        (Or.inr ⟨hfst.symm, h⟩)
      rw [hp.2.2.2, hq.2.2.2] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  exact Sigma.ext hfst (heq_of_eq hsnd)

theorem exists_criticalPairSpec (w : LabeledWord)
    (hpos : ∀ p ∈ w.selectedLeafPairs, 0 < p.1 ∧ 0 < p.2)
    {n : ℕ} (hn : 0 < n) (hbound : n ≤ w.selectedLeafCount) :
    ∃ p, w.CriticalPairSpec n p := by
  classical
  let count := fun p : Σ _ : ℕ, ℕ =>
    (w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1)).card
  have hsub : w.selectedLeafPairs.image count ⊆ Finset.Icc 1 w.selectedLeafCount := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hp₁, hp₂⟩ := hpos p hp
    have hself : p ∈ w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1) :=
      Finset.mem_filter.mpr ⟨hp, Or.inr ⟨by omega, by omega⟩⟩
    have hpositive := Finset.card_pos.mpr ⟨p, hself⟩
    have hle := Finset.card_filter_le w.selectedLeafPairs
      (fun q => p.1 - 1 + 1 < q.1 ∨ p.1 - 1 + 1 = q.1 ∧ p.2 - 1 + 1 ≤ q.2)
    rw [w.selectedLeafPairs_card] at hle
    exact Finset.mem_Icc.mpr ⟨hpositive, hle⟩
  have hinj : Set.InjOn count w.selectedLeafPairs := by
    intro p hp q hq heq
    exact CriticalPairSpec.unique ⟨hp, (hpos p hp).1, (hpos p hp).2, rfl⟩
      ⟨hq, (hpos q hq).1, (hpos q hq).2, heq.symm⟩
  have hcard := Finset.card_image_of_injOn hinj
  have heq : w.selectedLeafPairs.image count = Finset.Icc 1 w.selectedLeafCount := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard, w.selectedLeafPairs_card, Nat.card_Icc]
    omega
  have hmem : n ∈ w.selectedLeafPairs.image count := by
    rw [heq]
    exact Finset.mem_Icc.mpr ⟨hn, hbound⟩
  obtain ⟨p, hp, hcount⟩ := Finset.mem_image.mp hmem
  exact ⟨p, hp, (hpos p hp).1, (hpos p hp).2, hcount⟩

noncomputable def criticalPair (w : LabeledWord) (n : ℕ) : Σ _ : ℕ, ℕ := by
  classical
  exact if h : ∃ p, w.CriticalPairSpec n p then Classical.choose h else ⟨0, 0⟩

theorem criticalPair_eq_of_spec {w : LabeledWord} {n : ℕ} {p : Σ _ : ℕ, ℕ}
    (hp : w.CriticalPairSpec n p) : w.criticalPair n = p := by
  classical
  rw [criticalPair, dif_pos ⟨p, hp⟩]
  exact (Classical.choose_spec (show ∃ q, w.CriticalPairSpec n q from ⟨p, hp⟩)).unique hp

theorem criticalPair_spec (w : LabeledWord)
    (hpos : ∀ p ∈ w.selectedLeafPairs, 0 < p.1 ∧ 0 < p.2)
    {n : ℕ} (hn : 0 < n) (hbound : n ≤ w.selectedLeafCount) :
    w.CriticalPairSpec n (w.criticalPair n) := by
  obtain ⟨p, hp⟩ := w.exists_criticalPairSpec hpos hn hbound
  rw [criticalPair_eq_of_spec hp]
  exact hp

noncomputable def criticalBodyRank (w : LabeledWord) (n : ℕ) : ℕ :=
  (w.rootLabel.filter (fun i => i ≤ (w.criticalPair n).1)).card

noncomputable def criticalLeafRank (w : LabeledWord) (n : ℕ) : ℕ :=
  ((w.bodyLabels.getD ((w.criticalPair n).1 - 1) ∅).filter
    (fun j => j ≤ (w.criticalPair n).2)).card

noncomputable def criticalLast (w : LabeledWord) (n : ℕ) : Bool := by
  classical
  exact decide (∀ j ∈ w.bodyLabels.getD ((w.criticalPair n).1 - 1) ∅,
    j ≤ (w.criticalPair n).2)

theorem criticalBodyRank_le (w : LabeledWord) (n : ℕ) :
    w.criticalBodyRank n ≤ w.rootLabel.card := Finset.card_filter_le _ _

theorem criticalLeafRank_le (w : LabeledWord) (n : ℕ) :
    w.criticalLeafRank n ≤ (w.bodyLabels.getD ((w.criticalPair n).1 - 1) ∅).card :=
  Finset.card_filter_le _ _

theorem criticalLeafRank_pos {w : LabeledWord} {n : ℕ}
    (h : w.CriticalPairSpec n (w.criticalPair n)) : 0 < w.criticalLeafRank n :=
  Finset.card_pos.mpr ⟨(w.criticalPair n).2,
    Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp h.1).2, le_rfl⟩⟩

theorem criticalLast_iff_leafRank_eq (w : LabeledWord) (n : ℕ) :
    w.criticalLast n = true ↔
      w.criticalLeafRank n = (w.bodyLabels.getD ((w.criticalPair n).1 - 1) ∅).card := by
  classical
  simp only [criticalLast, criticalLeafRank, decide_eq_true_eq, Finset.card_filter_eq_iff]

#print axioms CriticalPairSpec.unique
#print axioms exists_criticalPairSpec
#print axioms criticalPair_eq_of_spec

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
