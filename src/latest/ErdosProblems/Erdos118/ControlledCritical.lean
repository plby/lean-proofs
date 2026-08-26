import ErdosProblems.Erdos118.ManagedCritical

/-!
A critical stopped run for a supplied actual right-response selector.
The proof records the new left ordinary suffix and its sampling bound;
blue certificates remain on H while conservative responses use K.
-/

namespace Erdos118.ControlledCritical

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ManagedCritical

def FreshLeft (K : Set ℕ) (d : ℕ) (S T : State) : Prop :=
  ∃ v : List ℕ, T.ordinary = S.ordinary ++ v ∧ ∀ x ∈ v, x ∈ K ∧ d < x

theorem stop_with_entry {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (M : State → Type)
    (respond : ∀ S T : State, Early S → M T →
      RightBlue H (GraphPayoff.payoff B .inside) (S, T) →
      ∃ U : State, Nonempty (M U) ∧
        ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (S, T) (S, U) ∧
        RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true)
    (d : ℕ) (S : State × State) (hS : Early S.1) (mS : M S.2)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside S) true) :
    ∃ T : State × State, ConservativeRuns.Run K (GraphPayoff.payoff B .inside) S T ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside T) true ∧
      Critical T.1 ∧ Nonempty (M T.2) ∧ FreshLeft K d S.1 T.1 ∧
      (T = S ∨ ∃ U, ConservativeRuns.Run K (GraphPayoff.payoff B .inside) S U ∧
        ¬ Critical U.1 ∧ ConservativeRuns.Step K (GraphPayoff.payoff B .inside) U T) := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hc : Critical S.1
    · exact ⟨S, Relation.ReflTransGen.refl, hblue, hc, ⟨mS⟩,
        ⟨[], by simp, by simp⟩, Or.inl rfl⟩
    · rcases blue_command (GraphPayoff.payoff B .inside) S
        (early_nonterminal _ S hS) hblue with hl | hr
      · obtain ⟨R, a, hs, hb, ha⟩ :=
          PreparedRelays.respond_on hK hKH B .inside false S.1 S.2 hl d
        obtain ⟨u, hu, huf⟩ := FreshCheckpoints.response_suffix R a
          (fun x hx ↦ (ha x hx).1) (fun x hx ↦ (ha x hx).2)
        obtain ⟨T, hrun, hbT, hcrit, hmT, ⟨v, hv, hvf⟩, hentry⟩ :=
          ih (R.result a, S.2) hs.pairStep (early_step hS hc (R.step a)) mS hb
        refine ⟨T, Relation.ReflTransGen.head hs hrun, hbT, hcrit, hmT, ?_, ?_⟩
        · exact ⟨u ++ v, by rw [hv, hu, List.append_assoc],
            fun x hx ↦ (List.mem_append.mp hx).elim (huf x) (hvf x)⟩
        · rcases hentry with rfl | ⟨U, hrU, hnU, hsU⟩
          · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hs⟩
          · exact Or.inr ⟨U, Relation.ReflTransGen.head hs hrU, hnU, hsU⟩
      · obtain ⟨U, ⟨mU⟩, hs, hb⟩ := respond S.1 S.2 hS mS hr
        obtain ⟨T, hrun, hbT, hcrit, hmT, hfT, hentry⟩ :=
          ih (S.1, U) hs.pairStep hS mU hb
        refine ⟨T, Relation.ReflTransGen.head hs hrun, hbT, hcrit, hmT, hfT, ?_⟩
        rcases hentry with rfl | ⟨V, hrV, hnV, hsV⟩
        · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hs⟩
        · exact Or.inr ⟨V, Relation.ReflTransGen.head hs hrV, hnV, hsV⟩

theorem stop_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (M : State → Type)
    (respond : ∀ S T : State, Early S → M T →
      RightBlue H (GraphPayoff.payoff B .inside) (S, T) →
      ∃ U : State, Nonempty (M U) ∧
        ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (S, T) (S, U) ∧
        RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true)
    (d : ℕ) (S T : State) (hS : Early S) (mT : M T)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ P : Pending, ∃ U : State, ∃ c : ℕ,
      P.roots = [c] ∧ P.leaves = [] ∧ Nonempty (M U) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (S, T) (.leaf P, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, U)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, U) ∧ FreshLeft K d S (.leaf P) := by
  obtain ⟨V, hrun, hb, hcrit, hmV, hfV, hentry⟩ :=
    stop_with_entry hK hKH B M respond d (S, T) hS mT hblue
  have hh : RightBlue H (GraphPayoff.payoff B .inside) V := by
    rcases hentry with rfl | ⟨W, _, hn, hs⟩
    · exact hready hcrit
    · cases hs with
      | left n R hs hR a haK hlarge =>
        cases he : R.result a with
        | initial => simp only [he, Critical] at hcrit
        | body D => simp only [he, Critical] at hcrit
        | complete C => simp only [he, Critical] at hcrit
        | leaf P =>
          rw [he] at hb
          exact handoff_after_left (hK.mono hKH) B .inside W R a P he hb
      | right n R hs hR a haK hlarge => exact (hn hcrit).elim
  obtain ⟨V, U⟩ := V
  cases V with
  | initial => exact hcrit.elim
  | body D => exact hcrit.elim
  | complete C => exact hcrit.elim
  | leaf P =>
    obtain ⟨c, hR, hL⟩ := hcrit
    exact ⟨P, U, c, hR, hL, hmV, hrun, hb, hh, hfV⟩

end Erdos118.ControlledCritical
