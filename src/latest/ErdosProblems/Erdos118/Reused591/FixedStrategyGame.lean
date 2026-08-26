import ErdosProblems.Erdos118.Reused591.ArchitectContinuation

namespace Erdos118.Reused591

/-!
# Fixing architect moves and recoloring terminal positions

This auxiliary finite-response game keeps the actual builder families
and responses. Its only architect move is the given strategy move.
Terminal recoloring is used solely for uniformizing finite observables;
it does not identify the new winner with the original payoff.
-/

namespace Erdos591.Positive.Game.FiniteResponseGame

def recolorKind (color : Bool) : PositionKind → PositionKind
  | .terminal _ => .terminal color
  | .architect => .architect
  | .builder => .builder

@[simp] theorem recolorKind_architect (color : Bool) (k : PositionKind) :
    recolorKind color k = .architect ↔ k = .architect := by cases k <;> simp [recolorKind]

@[simp] theorem recolorKind_builder (color : Bool) (k : PositionKind) :
    recolorKind color k = .builder ↔ k = .builder := by cases k <;> simp [recolorKind]

variable {P : Type*} {N H : Set ℕ}

def fixedStrategyGame (G : FiniteResponseGame P N) (hHN : H ⊆ N)
    (σ : G.ArchitectStrategy) (color : P → Bool) : FiniteResponseGame P H where
  kind p := recolorKind (color p) (G.kind p)
  next q p := G.next q p ∧ ∀ hp : G.kind p = .architect, q = σ.move p hp
  wellFounded := G.wellFounded.mono (fun _ _ h => h.1)
  architect_move p hp := by
    have hk : G.kind p = .architect := (recolorKind_architect _ _).mp hp
    exact ⟨σ.move p hk, σ.legal p hk, fun _ => rfl⟩
  family := G.family
  response := G.response
  response_next p u hp hu := by
    have hk : G.kind p = .builder := (recolorKind_builder _ _).mp hp
    refine ⟨G.response_next p u hk hu, ?_⟩
    intro ha
    simp [hk] at ha
  thin p hp := G.thin p ((recolorKind_builder _ _).mp hp)
  threshold := G.threshold
  response_exists p hp M hMH hM hbound :=
    G.response_exists p ((recolorKind_builder _ _).mp hp) M (hMH.trans hHN) hM hbound

theorem fixedStrategyGame_value_step (G : FiniteResponseGame P N) (hHN : H ⊆ N)
    (σ : G.ArchitectStrategy) (color : P → Bool) {L : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : (G.fixedStrategyGame hHN σ color).ValueSystem L b v) {p q : P}
    (hs : G.FollowStep σ L b p q) : v q = v p := by
  cases hs.1 with
  | architect q hp hnext =>
      have hk : (G.fixedStrategyGame hHN σ color).kind p = .architect := by
        simp [fixedStrategyGame, hp, recolorKind]
      have heq : v p = true ↔ v q = true := by
        rw [hv.2.1 p hk]
        constructor
        · rintro ⟨z, hz, hzv⟩
          have hze : z = q := (hz.2 hp).trans (hs.2 hp).symm
          exact hze ▸ hzv
        · intro hq
          exact ⟨q, ⟨hnext, hs.2⟩, hq⟩
      cases hpv : v p <;> cases hqv : v q <;> simp_all
  | builder u hp hu huL hub =>
      have hk : (G.fixedStrategyGame hHN σ color).kind p = .builder := by
        simp [fixedStrategyGame, hp, recolorKind]
      exact hv.2.2.1 p hk u hu huL hub

#print axioms fixedStrategyGame_value_step

end Erdos591.Positive.Game.FiniteResponseGame

end Erdos118.Reused591
