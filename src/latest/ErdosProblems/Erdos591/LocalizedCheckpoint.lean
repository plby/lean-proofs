import ErdosProblems.Erdos591.CriticalCheckpoint
import ErdosProblems.Erdos591.FiniteRank
import ErdosProblems.Erdos591.SplicedRootLabels

/-! # Local terminal colors determine the current critical body and its next marker -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem CriticalCheckpoint.localized_body_last {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (h : CriticalCheckpoint p) (hmode : p.position.mode = some true) {k : ℕ}
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true) :
    (p.position.board.right.rootLabel.filter
      (fun i => i ≤ p.position.board.right.bodyLabels.length)).card = k ∧
      p.position.board.right.NoLeafPending := by
  obtain ⟨z, hpz, hz⟩ := hwin.exists_terminal (exactGame N blue) hHN hH
  obtain ⟨_hn, _hd, hpay⟩ := (Concrete.kind_terminal_iff (payoff blue) z true).mp hz
  have hmodeZ := follow_mode_some hpz hmode
  have hwinning : Winning blue true z.position.board := by
    apply (payoff_true_iff blue true _).mp
    simpa only [hmodeZ, Option.getD_some] using hpay
  obtain ⟨s, t, hc, _hblue, hmax⟩ := hwinning
  have hobs := h.terminal_observables (follow_history_path hpz) hc hmax
  exact ⟨hobs.1.symm.trans (hfixed z true hpz hz), hobs.2.2.mp (hlast z true hpz hz)⟩

theorem spliced_next_body_of_rank {H : Set ℕ} {B e g j k : ℕ}
    (U : SplicedRootLabels H B e g j (k + 1)) (w : LabeledWord)
    (hroot : w.rootLabel = U.upper)
    (hrank : (w.rootLabel.filter (fun i => i ≤ w.bodyLabels.length)).card = k) :
    LabeledWord.BeforeBody U.anchor w ∧
      ∀ i ∈ w.rootLabel, w.bodyLabels.length < i → U.anchor ≤ i := by
  have hsucc := finite_rank_successor w.rootLabel (hroot ▸ U.anchor_upper)
    (x := w.bodyLabels.length) (by rw [hroot, U.anchor_upper_rank, ← hroot, hrank])
  exact ⟨⟨hroot ▸ U.anchor_upper, hsucc.1⟩, hsucc.2⟩

#print axioms CriticalCheckpoint.localized_body_last
#print axioms spliced_next_body_of_rank

end Erdos591.Positive.Game.Payoff
