import ErdosProblems.Erdos591.ManagedResponse

/-!
# A coupled checkpoint before either managed word completes

Well-founded induction on actual history moves maintains both delayed
upper plays. The selected side uses a managed response and the other
record is unchanged. The run stops when neither word has an unread
selected index, at which point both delayed upper replies can be fired.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_checkpoint {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (targetSide mode : Bool → Bool)
    (other : Bool → LabeledWord) (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmanaged : ∀ s, Nonempty
      (Managed N H blue b σ (targetSide s) (mode s) (other s) (p.position.board.get s))) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ BothLast q.position.board ∧
      ∀ s, Nonempty (Managed N H blue b σ (targetSide s) (mode s) (other s)
        (q.position.board.get s)) := by
  revert hwin hmanaged
  apply (exactGame N blue).wellFounded.induction p
  intro p ih hwin hmanaged
  by_cases hlast : BothLast p.position.board
  · exact ⟨p, .refl, hwin, hlast, hmanaged⟩
  have hmove : ∃ q, (exactGame N blue).FollowStep σ H b p q ∧
      ∀ s, Nonempty (Managed N H blue b σ (targetSide s) (mode s) (other s)
        (q.position.board.get s)) := by
    cases hp : p.position.pending with
    | none =>
        obtain ⟨M⟩ := hmanaged false
        have hnotdone := Board.not_done_of_live
          (M.unfinished ((Position.history_dataInvariant p).2.1 false).1)
        have hk : (exactGame N blue).kind p = .architect :=
          (Concrete.kind_architect_iff (payoff blue) p).mpr ⟨hp, hnotdone⟩
        let q := σ.move p hk
        have hs : (exactGame N blue).FollowStep σ H b p q :=
          FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
        have hboard := (History.Next.position_next (σ.legal p hk)).board_eq_of_no_pending hp
        exact ⟨q, hs, fun s => by simpa only [q, hboard] using hmanaged s⟩
    | some r =>
        obtain ⟨M⟩ := hmanaged r.side
        obtain ⟨q, hs, _hn, ho, hM⟩ := M.respond hHN hH blue hwin hp hlast
        refine ⟨q, hs, fun s => ?_⟩
        by_cases heq : s = r.side
        · simpa [heq] using hM
        · have heq' : s = !r.side := Bool.eq_not_of_ne heq
          simpa only [heq', ho] using hmanaged s
  obtain ⟨q, hs, hM⟩ := hmove
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨z, hpath, hwinz, hz, hMz⟩ :=
    ih q (FiniteResponseGame.FollowStep.next (exactGame N blue) hs) hwinq hM
  exact ⟨z, hpath.head hs, hwinz, hz, hMz⟩

theorem managed_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (targetSide mode : Bool → Bool)
    (other : Bool → LabeledWord) (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmanaged : ∀ s, Nonempty
      (Managed N H blue b σ (targetSide s) (mode s) (other s) (p.position.board.get s))) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ BothLast q.position.board ∧
      ∀ s, ∃ v : Concrete.Hist N, (exactGame N blue).ArchitectWins H b σ v ∧
        v.position.pending = none ∧
        (v.position.board.get (targetSide s)).coordinates = (q.position.board.get s).coordinates ∧
        (v.position.board.get (targetSide s)).relaxed = true ∧
        v.position.board.get (!(targetSide s)) = other s ∧ v.position.mode = some (mode s) := by
  obtain ⟨q, hpq, hw, hl, hm⟩ :=
    managed_checkpoint hHN hH blue targetSide mode other p hwin hmanaged
  refine ⟨q, hpq, hw, hl, fun s => ?_⟩
  obtain ⟨M⟩ := hm s
  exact M.fire hHN ((Position.history_dataInvariant q).2.1 s).2 (hl s)

#print axioms managed_checkpoint
#print axioms managed_forks

end Erdos591.Positive.Game.Relay
