import ErdosProblems.Erdos591.InitialManaged

/-!
# Conservative origins of managed delayed plays

Retain an actual strategy path from each reference history to its saved
upper request. Root-plan transport keeps the request fixed; conversion
to a prepared body appends the proved upper path. Thus terminal data
uniform from the reference history remains available after firing.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_checkpoint_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (targetSide mode : Bool → Bool)
    (other : Bool → LabeledWord) (origin : Bool → Concrete.Hist N) (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmanaged : ∀ s, ∃ M : Managed N H blue b σ (targetSide s) (mode s) (other s)
      (p.position.board.get s),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) (origin s) M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ BothLast q.position.board ∧
      ∀ s, ∃ M : Managed N H blue b σ (targetSide s) (mode s) (other s)
        (q.position.board.get s),
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) (origin s) M.target := by
  revert hwin hmanaged
  apply (exactGame N blue).wellFounded.induction p
  intro p ih hwin hmanaged
  by_cases hlast : BothLast p.position.board
  · exact ⟨p, .refl, hwin, hlast, hmanaged⟩
  have hmove : ∃ q, (exactGame N blue).FollowStep σ H b p q ∧
      ∀ s, ∃ M : Managed N H blue b σ (targetSide s) (mode s) (other s)
        (q.position.board.get s),
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) (origin s) M.target := by
    cases hp : p.position.pending with
    | none =>
        obtain ⟨M, _⟩ := hmanaged false
        have hnotdone := Board.not_done_of_live
          (M.unfinished ((Position.history_dataInvariant p).2.1 false).1)
        have hk : (exactGame N blue).kind p = .architect :=
          (Concrete.kind_architect_iff (payoff blue) p).mpr ⟨hp, hnotdone⟩
        let q := σ.move p hk
        have hs : (exactGame N blue).FollowStep σ H b p q :=
          FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
        have hboard := (History.Next.position_next (σ.legal p hk)).board_eq_of_no_pending hp
        refine ⟨q, hs, fun s => ?_⟩
        dsimp only [q]
        rw [hboard]
        exact hmanaged s
    | some r =>
        obtain ⟨M, hfrom⟩ := hmanaged r.side
        obtain ⟨q, hs, _hn, ho, Q, hQ⟩ :=
          M.respond_from hHN hH blue hwin hp hlast (origin r.side) hfrom
        refine ⟨q, hs, fun s => ?_⟩
        by_cases heq : s = r.side
        · subst s
          exact ⟨Q, hQ⟩
        · have heq' : s = !r.side := Bool.eq_not_of_ne heq
          subst s
          rw [ho]
          exact hmanaged (!r.side)
  obtain ⟨q, hs, hM⟩ := hmove
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨z, hpath, hwinz, hz, hMz⟩ :=
    ih q (FiniteResponseGame.FollowStep.next (exactGame N blue) hs) hwinq hM
  exact ⟨z, hpath.head hs, hwinz, hz, hMz⟩

theorem Managed.first_body_from_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (s : Bool)
    (hp : p.position.pending = none) (hm : (p.position.board.get s).markerEvent = true)
    {t mode : Bool} {other : LabeledWord}
    (M : Managed N H blue b σ t mode other (p.position.board.get s))
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get s).relaxed = true ∧
      q.position.board.get (!s) = p.position.board.get (!s) ∧
      (∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0) ∧
      ∃ Q : Managed N H blue b σ t mode other (q.position.board.get s),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
  obtain ⟨p', d, hrequest, hboard, hpend, hd⟩ :=
    winning_request_at_marker hHN hH blue hwin s hp hm
  have hwin' := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hrequest)
  obtain ⟨M', hfrom'⟩ : ∃ M' : Managed N H blue b σ t mode other (p'.position.board.get s),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M'.target := by
    rw [hboard]
    exact ⟨M, hfrom⟩
  have hm' : (p'.position.board.get s).markerEvent = true := by simpa [hboard] using hm
  have hnot : ¬ BothLast p'.position.board := fun hl => hl s (Macro.marker_pending hm')
  obtain ⟨q, hs, hn, ho, Q, hQ⟩ := M'.respond_from hHN hH blue hwin' hpend hnot origin hfrom'
  have hnext := History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs)
  obtain ⟨u, hr, hf⟩ := hnext.reply_of_pending_fresh hpend
  have hrel := hr.advance_selected_leaf ((Position.history_dataInvariant p').2.1 s).1
    hm' hd (fun x hx => (Nat.zero_le p'.position.bound).trans_lt (hf x hx))
  exact ⟨q, (Relation.ReflTransGen.single hrequest).tail hs, hn, hrel,
    by simpa [hboard] using ho,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation hpend, Q, hQ⟩

theorem Managed.first_body_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (s : Bool)
    (hp : p.position.pending = none) (hm : (p.position.board.get s).markerEvent = true)
    {t mode : Bool} {other : LabeledWord}
    (M : Managed N H blue b σ t mode other (p.position.board.get s))
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get s).relaxed = true ∧
      q.position.board.get (!s) = p.position.board.get (!s) ∧
      ∃ Q : Managed N H blue b σ t mode other (q.position.board.get s),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
  obtain ⟨q, hpath, hn, hr, ho, _hsep, Q, hQ⟩ :=
    M.first_body_from_fresh hHN hH blue hwin s hp hm origin hfrom
  exact ⟨q, hpath, hn, hr, ho, Q, hQ⟩

#print axioms managed_checkpoint_from
#print axioms Managed.first_body_from
#print axioms Managed.first_body_from_fresh

end Erdos591.Positive.Game.Relay
