import ErdosProblems.Erdos591.GamePayoff

/-!
# Winning continuations against the architect

Every conservative history following a winning architect strategy has
a finite winning continuation. This uses the actual response-existence
field and well-founded game relation, not a separate determinacy premise.
The concrete specialization recovers the clear blue pair at its endpoint.
-/

namespace Erdos591.Positive.Game

namespace FiniteResponseGame

variable {P : Type*} {N : Set ℕ} (G : FiniteResponseGame P N)

theorem FollowStep.next {H : Set ℕ} {b : P → ℕ} {σ : G.ArchitectStrategy}
    {p q : P} (h : G.FollowStep σ H b p q) : G.next q p := h.1.next G

theorem FollowStep.architect {H : Set ℕ} {b : P → ℕ} (σ : G.ArchitectStrategy)
    (p : P) (hp : G.kind p = .architect) : G.FollowStep σ H b p (σ.move p hp) :=
  ⟨.architect p (σ.move p hp) hp (σ.legal p hp), fun _ => rfl⟩

theorem FollowStep.builder {H : Set ℕ} {b : P → ℕ} (σ : G.ArchitectStrategy)
    (p : P) (u : Finset ℕ) (hp : G.kind p = .builder) (hu : u ∈ G.family p)
    (huH : (↑u : Set ℕ) ⊆ H) (hub : ∀ x ∈ u, b p < x) :
    G.FollowStep σ H b p (G.response p u) := by
  refine ⟨.builder p u hp hu huH hub, ?_⟩
  intro ha
  simp [hp] at ha

theorem FollowStep.mono {H H' : Set ℕ} {b b' : P → ℕ} {σ : G.ArchitectStrategy}
    (hH : H' ⊆ H) (hb : ∀ p, b p ≤ b' p) {p q : P}
    (h : G.FollowStep σ H' b' p q) : G.FollowStep σ H b p q := by
  refine ⟨?_, h.2⟩
  cases h.1 with
  | architect q hp hq => exact .architect _ q hp hq
  | builder u hp hu huH hub =>
      exact .builder _ u hp hu (huH.trans hH) (fun x hx => (hb _).trans_lt (hub x hx))

theorem ArchitectWins.of_reachable {H : Set ℕ} {b : P → ℕ}
    {σ : G.ArchitectStrategy} {p q : P} (hwin : G.ArchitectWins H b σ p)
    (hpq : Relation.ReflTransGen (G.FollowStep σ H b) p q) :
    G.ArchitectWins H b σ q := by
  intro r w hqr hr
  exact hwin r w (hpq.trans hqr) hr

theorem ArchitectWins.mono {H H' : Set ℕ} {b b' : P → ℕ}
    {σ : G.ArchitectStrategy} {p : P} (hwin : G.ArchitectWins H b σ p)
    (hH : H' ⊆ H) (hb : ∀ p, b p ≤ b' p) : G.ArchitectWins H' b' σ p := by
  intro q w hpq hq
  apply hwin q w _ hq
  exact Relation.ReflTransGen.mono (fun _ _ h => FollowStep.mono G hH hb h) _ _ hpq

theorem terminal_reachable_of_infinite {H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (b : P → ℕ) (σ : G.ArchitectStrategy) (p : P) :
    ∃ q w, Relation.ReflTransGen (G.FollowStep σ H b) p q ∧
      G.kind q = .terminal w := by
  apply G.wellFounded.induction p
  intro p ih
  cases hp : G.kind p with
  | terminal w => exact ⟨p, w, .refl, hp⟩
  | architect =>
      obtain ⟨q, w, hpath, hq⟩ := ih (σ.move p hp) (σ.legal p hp)
      refine ⟨q, w, hpath.head ?_, hq⟩
      exact ⟨.architect p (σ.move p hp) hp (σ.legal p hp), fun _ => rfl⟩
  | builder =>
      obtain ⟨u, hu, huH, hub⟩ := G.response_exists_above hHN hH p hp (b p)
      obtain ⟨q, w, hpath, hq⟩ := ih (G.response p u) (G.response_next p u hp hu)
      refine ⟨q, w, hpath.head ?_, hq⟩
      refine ⟨.builder p u hp hu huH hub, ?_⟩
      intro ha
      simp [hp] at ha

theorem ArchitectWins.exists_terminal {H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    {b : P → ℕ} {σ : G.ArchitectStrategy} {p : P}
    (hwin : G.ArchitectWins H b σ p) :
    ∃ q, Relation.ReflTransGen (G.FollowStep σ H b) p q ∧
      G.kind q = .terminal true := by
  obtain ⟨q, w, hpath, hq⟩ := G.terminal_reachable_of_infinite hHN hH b σ p
  exact ⟨q, hpath, (hwin q w hpath hq) ▸ hq⟩

end FiniteResponseGame

namespace Concrete

theorem architect_choice {N : Set ℕ} (payoff : Bool → Board → Bool)
    (σ : (game N payoff).ArchitectStrategy) (p : Hist N)
    (hp : (game N payoff).kind p = .architect) :
    ∃ mode r, ∃ hnext : Position.Next N (p.position.request mode r) p.position,
      σ.move p hp = p.append (p.position.request mode r) hnext := by
  have hturn := ((kind_architect_iff payoff p).mp hp).1
  obtain ⟨q, hq, heq⟩ := σ.legal p hp
  cases hq with
  | request _ mode r ht hl hm hf => exact ⟨mode, r, .request _ mode r ht hl hm hf, heq⟩
  | reply p r u board hpending _ _ _ => simp [hturn] at hpending

theorem kind_terminal_iff {N : Set ℕ} (payoff : Bool → Board → Bool)
    (h : Hist N) (w : Bool) : kind payoff h = .terminal w ↔
      h.position.pending = none ∧ done h.position.board = true ∧
        payoff (h.position.mode.getD false) h.position.board = w := by
  cases hp : h.position.pending with
  | some r => simp [kind, hp]
  | none => cases hd : done h.position.board <;> simp [kind, hp, hd]

end Concrete

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_continuation {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) :
    ∃ q : Concrete.Hist N,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ Concrete.done q.position.board = true ∧
      Winning blue (q.position.mode.getD false) q.position.board := by
  obtain ⟨q, hpath, hq⟩ := hwin.exists_terminal (exactGame N blue) hHN hH
  obtain ⟨hp, hd, hw⟩ := (Concrete.kind_terminal_iff (payoff blue) q true).mp hq
  exact ⟨q, hpath, hp, hd, (payoff_true_iff blue _ _).mp hw⟩

end Payoff

#print axioms FiniteResponseGame.ArchitectWins.exists_terminal
#print axioms Payoff.winning_continuation

end Erdos591.Positive.Game
