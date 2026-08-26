import ErdosProblems.Erdos118.Reused591.ManagedOrigins

namespace Erdos118.Reused591

/-!
# A guarded stopping point with one managed opposite word

While a cursor predicate guarantees an unread selection, choose managed
responses on the opposite side and arbitrary conservative responses on
the guarded side. Well-foundedness gives a first response destroying
the predicate. The delayed opposite play keeps its actual origin path.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_guard_boundary_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (side : Bool) (P : LabeledWord → Prop)
    (hPending : ∀ w, P w → Macro.Pending w) {t mode : Bool} {other : LabeledWord}
    (origin : Concrete.Hist N) (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hP : P (p.position.board.get side))
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q z r, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).FollowStep σ H b q z ∧ q.position.pending = some r ∧
      r.side = side ∧ P (q.position.board.get side) ∧ ¬ P (z.position.board.get side) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  classical
  revert hwin hP hmanaged
  apply (exactGame N blue).wellFounded.induction p
  intro p ih hwin hP hmanaged
  cases hp : p.position.pending with
  | none =>
      obtain ⟨M, hfrom⟩ := hmanaged
      have hnotdone := Board.not_done_of_live
        (M.unfinished ((Position.history_dataInvariant p).2.1 (!side)).1)
      have hk : (exactGame N blue).kind p = .architect :=
        (Concrete.kind_architect_iff (payoff blue) p).mpr ⟨hp, hnotdone⟩
      let q := σ.move p hk
      have hs : (exactGame N blue).FollowStep σ H b p q :=
        FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
      have hb := (History.Next.position_next (σ.legal p hk)).board_eq_of_no_pending hp
      have hM : ∃ Q : Managed N H blue b σ t mode other (q.position.board.get (!side)),
          Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
        dsimp only [q]
        rw [hb]
        exact ⟨M, hfrom⟩
      obtain ⟨v, z, r, hqv, hvz, hvp, hside, hPv, hPz, hMv⟩ :=
        ih q (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)
          (hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs))
          (by simpa only [q, hb] using hP) hM
      exact ⟨v, z, r, hqv.head hs, hvz, hvp, hside, hPv, hPz, hMv⟩
  | some r =>
      by_cases hrside : r.side = side
      · have hk : (exactGame N blue).kind p = .builder :=
          (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
        obtain ⟨u, hu, huH, hub⟩ :=
          (exactGame N blue).response_exists_above hHN hH p hk (b p)
        let q := Concrete.response p u
        have hs : (exactGame N blue).FollowStep σ H b p q :=
          FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
        by_cases hPq : P (q.position.board.get side)
        · have ho := (Concrete.response_spec hu).reply_spec hp |>.other_eq
          have hM : ∃ Q : Managed N H blue b σ t mode other (q.position.board.get (!side)),
              Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
            rw [← hrside, ho, hrside]
            exact hmanaged
          obtain ⟨v, z, r', hqv, hvz, hvp, hside, hPv, hPz, hMv⟩ :=
            ih q (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)
              (hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)) hPq hM
          exact ⟨v, z, r', hqv.head hs, hvz, hvp, hside, hPv, hPz, hMv⟩
        · exact ⟨p, q, r, .refl, hs, hp, hrside, hP, hPq, hmanaged⟩
      · have hrs : r.side = !side := Bool.eq_not_of_ne hrside
        have hM : ∃ M : Managed N H blue b σ t mode other (p.position.board.get r.side),
            Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
          rw [hrs]
          exact hmanaged
        obtain ⟨M, hfrom⟩ := hM
        have hnot : ¬ BothLast p.position.board := fun hlast => hlast side (hPending _ hP)
        obtain ⟨q, hs, _hn, ho, Q, hQ⟩ :=
          M.respond_from hHN hH blue hwin hp hnot origin hfrom
        have hother : q.position.board.get side = p.position.board.get side := by
          simpa only [hrs, Bool.not_not] using ho
        have hMq : ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
            Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
          rw [← hrs]
          exact ⟨Q, hQ⟩
        obtain ⟨v, z, r', hqv, hvz, hvp, hside, hPv, hPz, hMv⟩ :=
          ih q (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)
            (hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs))
            (hother ▸ hP) hMq
        exact ⟨v, z, r', hqv.head hs, hvz, hvp, hside, hPv, hPz, hMv⟩

#print axioms managed_guard_boundary_from

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591
