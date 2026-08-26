import ErdosProblems.Erdos591.CriticalFutureBodyBound
import ErdosProblems.Erdos591.SelectedSuffixRanks

/-!
# The current critical-body remainder leaves two entries in the suffix

The critical leaf and every later leaf of its current body, together
with one selected leaf of a later body, are distinct members of the
critical suffix. This supplies the two spare S-label entries beta and
gamma after the preliminary lower phase.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem CriticalPairSpec.current_remainder_add_two_le
    {w : LabeledWord} {n : ℕ} {p : Σ _ : ℕ, ℕ} (hp : w.CriticalPairSpec n p)
    {z : ℕ} (hz : z ∈ w.rootLabel) (hpz : p.1 < z)
    (hne : (w.bodyLabels.getD (z - 1) ∅).Nonempty) :
    (w.bodyLabels.getD (p.1 - 1) ∅).card -
        ((w.bodyLabels.getD (p.1 - 1) ∅).filter (fun x => x ≤ p.2)).card + 2 ≤ n := by
  classical
  let C := w.bodyLabels.getD (p.1 - 1) ∅
  let body : Finset (Σ _ : ℕ, ℕ) :=
    ({p.1} : Finset ℕ).sigma fun _ => C.filter (fun x => p.2 ≤ x)
  obtain ⟨l, hl⟩ := hne
  let later : Σ _ : ℕ, ℕ := ⟨z, l⟩
  have hnot : later ∉ body := by
    intro h
    have he := Finset.mem_singleton.mp (Finset.mem_sigma.mp h).1
    change z = p.1 at he
    omega
  have hsub : insert later body ⊆ w.selectedLeafPairsFrom (p.1 - 1) (p.2 - 1) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hz, hl⟩,
        Or.inl (by have := hp.2.1; dsimp [later]; omega)⟩
    obtain ⟨hqFirst, hqLeaf⟩ := Finset.mem_sigma.mp hq
    have he : q.1 = p.1 := Finset.mem_singleton.mp hqFirst
    obtain ⟨hqC, hle⟩ := Finset.mem_filter.mp hqLeaf
    refine Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨he ▸ (Finset.mem_sigma.mp hp.1).1, ?_⟩,
      Or.inr ⟨by have := hp.2.1; omega, by have := hp.2.2.1; omega⟩⟩
    simpa only [he] using hqC
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hp.2.2.2] at hcard
  simp only [body, Finset.card_sigma, Finset.sum_singleton] at hcard
  have hpair : p.2 ∈ C := (Finset.mem_sigma.mp hp.1).2
  have hsum := finite_rank_add_suffix C hpair
  have hrankLe := Finset.card_filter_le C (fun x => x ≤ p.2)
  dsimp only [C] at hcard hsum hrankLe
  omega

#print axioms CriticalPairSpec.current_remainder_add_two_le

end Erdos591.Positive.Game.LabeledWord
