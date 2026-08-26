import ErdosProblems.Erdos591.StrictCriticalData
import ErdosProblems.Erdos591.FiniteRank
import ErdosProblems.Erdos591.SplicedRootLabels

/-!
# A future nonfinal body leaves two extra pairs in a critical suffix

The full label of a selected body strictly after the critical pair and
strictly before a later selected body embeds into the critical suffix.
The critical pair itself and a selected leaf from that later body are
two distinct additional elements. This gives the exact finite bound
needed before localizing the next upper body's size.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem CriticalPairSpec.future_body_card_add_two_le
    {w : LabeledWord} {n : ℕ} {p : Σ _ : ℕ, ℕ} (hp : w.CriticalPairSpec n p)
    {i z : ℕ} (hi : i ∈ w.rootLabel) (hpi : p.1 < i)
    (hz : z ∈ w.rootLabel) (hiz : i < z)
    (hne : (w.bodyLabels.getD (z - 1) ∅).Nonempty) :
    (w.bodyLabels.getD (i - 1) ∅).card + 2 ≤ n := by
  classical
  let body : Finset (Σ _ : ℕ, ℕ) :=
    ({i} : Finset ℕ).sigma fun k => w.bodyLabels.getD (k - 1) ∅
  obtain ⟨l, hl⟩ := hne
  let later : Σ _ : ℕ, ℕ := ⟨z, l⟩
  have hnotP : p ∉ body := by
    intro h
    have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp h).1
    exact hpi.ne he
  have hnotLater : later ∉ insert p body := by
    intro h
    rcases Finset.mem_insert.mp h with he | h
    · have he' := congrArg Sigma.fst he
      change z = p.1 at he'
      omega
    · have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp h).1
      change z = i at he
      omega
  have hsub : insert later (insert p body) ⊆
      w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_sigma.mpr ⟨hz, hl⟩, Or.inl (by have := hp.2.1; dsimp [later]; omega)⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hp.1, Or.inr ⟨by have := hp.2.1; omega,
        by have := hp.2.2.1; omega⟩⟩
    · obtain ⟨hqFirst, hqLeaf⟩ := Finset.mem_sigma.mp hq
      have he : q.1 = i := Finset.mem_singleton.mp hqFirst
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨he ▸ hi, hqLeaf⟩,
        Or.inl (by have := hp.2.1; omega)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotLater, Finset.card_insert_of_notMem hnotP,
    hp.2.2.2] at hcard
  simpa only [body, Finset.card_sigma, Finset.sum_singleton, Nat.add_assoc] using hcard

end LabeledWord

namespace Payoff

open Erdos591.Negative.Exact

theorem ClearSide.spliced_anchor_card_bound {H : Set ℕ} {B e g j k n : ℕ}
    (U : SplicedRootLabels H B e g j (k + 1)) (hkg : k + 1 < g)
    {w : LabeledWord} {s t : G} (hc : ClearSide w s t)
    (hroot : w.rootLabel = U.upper)
    (hspec : w.CriticalPairSpec n (w.criticalPair n)) (hrank : w.criticalBodyRank n = k) :
    0 < (w.bodyLabels.getD (U.anchor - 1) ∅).card ∧
      (w.bodyLabels.getD (U.anchor - 1) ∅).card + 2 ≤ n := by
  have hanchor : U.anchor ∈ w.rootLabel := hroot ▸ U.anchor_upper
  have hpairRank : (w.rootLabel.filter (fun i => i ≤ (w.criticalPair n).1)).card = k := hrank
  have hsucc := finite_rank_successor w.rootLabel hanchor
    (x := (w.criticalPair n).1)
    (by rw [hroot, U.anchor_upper_rank, ← hroot, hpairRank])
  have hlater : ∃ z ∈ w.rootLabel, U.anchor < z := by
    by_contra hn
    have hall : ∀ z ∈ w.rootLabel, z ≤ U.anchor := by
      intro z hz
      by_contra h
      exact hn ⟨z, hz, lt_of_not_ge h⟩
    have he : w.rootLabel.filter (fun z => z ≤ U.anchor) = w.rootLabel :=
      Finset.filter_eq_self.mpr hall
    rw [hroot] at he
    have heCard := congrArg Finset.card he
    rw [U.anchor_upper_rank, U.upper_card] at heCard
    omega
  obtain ⟨z, hz, haz⟩ := hlater
  exact ⟨hc.selected_body_card_pos hanchor,
    hspec.future_body_card_add_two_le hanchor hsucc.1 hz haz
      (Finset.card_pos.mp (hc.selected_body_card_pos hz))⟩

#print axioms LabeledWord.CriticalPairSpec.future_body_card_add_two_le
#print axioms ClearSide.spliced_anchor_card_bound

end Payoff

end Erdos591.Positive.Game
