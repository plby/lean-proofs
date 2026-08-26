import ErdosProblems.Erdos118.Reused591.FixedStrategyGame

namespace Erdos118.Reused591

/-!
# Conservative uniformization of terminal observables for one strategy

Fix the architect's moves in an auxiliary game and apply the proved
value-system theorem. Along the original strategy every conservative
move then preserves the value, so the terminal observable is constant.
The new numerical input bounds dominate the old bounds. No proof-checker
setting or original payoff is altered.
-/

namespace Erdos591.Positive.Game.FiniteResponseGame

variable {P : Type*} [Countable P] {N H : Set ℕ}

theorem terminal_bool_uniformization (G : FiniteResponseGame P N) (hHN : H ⊆ N)
    (hH : H.Infinite) (b : P → ℕ) (σ : G.ArchitectStrategy) (color : P → Bool) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : P → ℕ, (∀ p, b p ≤ c p) ∧ ∃ v : P → Bool,
      ∀ p q w, Relation.ReflTransGen (G.FollowStep σ L c) p q →
        G.kind q = .terminal w → color q = v p := by
  let F := G.fixedStrategyGame hHN σ color
  obtain ⟨L, hLH, hL, c₀, v, hv⟩ := F.exists_valueSystem hH
  let c : P → ℕ := fun p => max (b p) (c₀ p)
  have hv' : F.ValueSystem L c v := hv.mono F hLH hL (Set.Subset.refl L)
    (fun p => le_max_right (b p) (c₀ p))
  refine ⟨L, hLH, hL, c, (fun p => le_max_left (b p) (c₀ p)), v, ?_⟩
  intro p q w hpath hterminal
  have hvalue : v q = v p := by
    clear hterminal
    induction hpath with
    | refl => rfl
    | tail _ hs ih => exact (G.fixedStrategyGame_value_step hHN σ color hv' hs).trans ih
  have hk : F.kind q = .terminal (color q) := by
    simp [F, fixedStrategyGame, recolorKind, hterminal]
  exact (hv'.1 q (color q) hk).symm.trans hvalue

theorem terminal_bool_finset_uniformization (G : FiniteResponseGame P N)
    {I : Type*} (S : Finset I) (hHN : H ⊆ N) (hH : H.Infinite)
    (b : P → ℕ) (σ : G.ArchitectStrategy) (color : I → P → Bool) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : P → ℕ, (∀ p, b p ≤ c p) ∧
      ∀ i ∈ S, ∃ v : P → Bool, ∀ p q w,
        Relation.ReflTransGen (G.FollowStep σ L c) p q →
          G.kind q = .terminal w → color i q = v p := by
  classical
  induction S using Finset.induction_on generalizing H b with
  | empty => exact ⟨H, Set.Subset.refl H, hH, b, fun _ => le_rfl, by simp⟩
  | @insert i S _hi ih =>
      obtain ⟨K, hKH, hK, c₀, hb₀, v, hv⟩ :=
        G.terminal_bool_uniformization hHN hH b σ (color i)
      obtain ⟨L, hLK, hL, c, hc, hS⟩ := ih (hKH.trans hHN) hK c₀
      refine ⟨L, hLK.trans hKH, hL, c, (fun p => (hb₀ p).trans (hc p)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine ⟨v, ?_⟩
        intro p q w hpath hterminal
        exact hv p q w (Relation.ReflTransGen.mono
          (fun _ _ hs => FollowStep.mono G hLK hc hs) _ _ hpath) hterminal
      · exact hS j hj

theorem terminal_finite_uniformization (G : FiniteResponseGame P N)
    {C : Type*} [Finite C] (hHN : H ⊆ N) (hH : H.Infinite)
    (b : P → ℕ) (σ : G.ArchitectStrategy) (color : P → C) (p : P) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : P → ℕ, (∀ q, b q ≤ c q) ∧ ∃ value : C,
      ∀ q w, Relation.ReflTransGen (G.FollowStep σ L c) p q →
        G.kind q = .terminal w → color q = value := by
  classical
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨L, hLH, hL, c, hbc, hall⟩ := G.terminal_bool_finset_uniformization
    (Finset.univ : Finset C) hHN hH b σ (fun i q => decide (color q = i))
  obtain ⟨q₀, w₀, hpath₀, hterm₀⟩ := G.terminal_reachable_of_infinite (hLH.trans hHN) hL c σ p
  obtain ⟨v, hv⟩ := hall (color q₀) (Finset.mem_univ _)
  have hvalue : true = v p := by simpa using hv p q₀ w₀ hpath₀ hterm₀
  refine ⟨L, hLH, hL, c, hbc, color q₀, ?_⟩
  intro q w hpath hterminal
  have he := hv p q w hpath hterminal
  rw [← hvalue] at he
  exact of_decide_eq_true he

#print axioms terminal_bool_uniformization
#print axioms terminal_bool_finset_uniformization
#print axioms terminal_finite_uniformization

end Erdos591.Positive.Game.FiniteResponseGame

end Erdos118.Reused591
