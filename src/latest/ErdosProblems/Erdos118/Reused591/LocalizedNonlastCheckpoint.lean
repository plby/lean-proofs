import ErdosProblems.Erdos118.Reused591.LocalizedCheckpoint
import ErdosProblems.Erdos118.Reused591.SeparatedRootLabels

namespace Erdos118.Reused591

/-! # Localize the nonlast critical leaf, including the first upper body -/

namespace Erdos591.Positive.Game

namespace SeparatedRootLabels

theorem first_upper_rank {H : Set ℕ} {B e d j : ℕ} (U : SeparatedRootLabels H B e d j) :
    (U.upper.filter (fun x => x ≤ U.first)).card = 1 := by
  have heq : U.upper.filter (fun x => x ≤ U.first) = {U.first} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hle⟩
      exact le_antisymm hle (U.upper_first x hx)
    · rintro rfl
      exact ⟨U.first_upper, le_rfl⟩
  rw [heq, Finset.card_singleton]

theorem current_first_of_rank_one {H : Set ℕ} {B e d j : ℕ}
    (U : SeparatedRootLabels H B e d j) (w : LabeledWord)
    (hrel : w.relaxed = true) (hroot : w.rootLabel = U.upper)
    (hrank : (w.rootLabel.filter (fun i => i ≤ w.bodyLabels.length)).card = 1) :
    w.bodyLabels.length = U.first := by
  exact finite_rank_injective w.rootLabel (of_decide_eq_true hrel).2.1
    (hroot ▸ U.first_upper) (hrank.trans (by rw [hroot, U.first_upper_rank]))

#print axioms first_upper_rank
#print axioms current_first_of_rank_one

end SeparatedRootLabels

namespace Payoff

open Erdos591.Negative.Exact

theorem CriticalCheckpoint.localized_body_nonlast {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (h : CriticalCheckpoint p) (hmode : p.position.mode = some true) {k : ℕ}
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    (p.position.board.right.rootLabel.filter
      (fun i => i ≤ p.position.board.right.bodyLabels.length)).card = k ∧
      ¬ p.position.board.right.NoLeafPending := by
  obtain ⟨z, hpz, hz⟩ := hwin.exists_terminal (exactGame N blue) hHN hH
  obtain ⟨_hn, _hd, hpay⟩ := (Concrete.kind_terminal_iff (payoff blue) z true).mp hz
  have hmodeZ := follow_mode_some hpz hmode
  have hwinning : Winning blue true z.position.board := by
    apply (payoff_true_iff blue true _).mp
    simpa only [hmodeZ, Option.getD_some] using hpay
  obtain ⟨s, t, hc, _hblue, hmax⟩ := hwinning
  have hobs := h.terminal_observables (follow_history_path hpz) hc hmax
  refine ⟨hobs.1.symm.trans (hfixed z true hpz hz), ?_⟩
  intro hno
  have ht := hobs.2.2.mpr hno
  rw [hlast z true hpz hz] at ht
  contradiction

#print axioms CriticalCheckpoint.localized_body_nonlast

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
