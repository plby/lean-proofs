import ErdosProblems.Erdos118.LeafReplay
import ErdosProblems.Erdos118.FreshCheckpoints
import ErdosProblems.Erdos118.PreparedRelays

/-!
Actual selected-leaf commands give universal bounded setup certificates
including conservative steps and handoffs. Sampling may use K subset H.
-/

namespace Erdos118.SelectedLeafResponses

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem certificate_on {H K : Set ℕ} (hH : H.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (right : Bool)
    (P : Pending) (T : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : CommandBlue H B o right (.leaf P) T) :
    ∃ b : ℕ, ∀ A : LeafResponses.Setup P.position j,
      (∀ x ∈ A.newWord, x ∈ K) → (∀ x ∈ A.newWord, b < x) →
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.leaf P) T)
        (pair right (.leaf (LeafResponses.toPending P j rest hP A)) T) ∧
      Blue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T ∧
      OtherBlue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T := by
  cases right with
  | false =>
    obtain ⟨n, R, hside, hresp, b, hb⟩ := hblue
    let c := pairBound (.leaf P, T)
    let g := ConservativeRuns.leftGuard K (GraphPayoff.payoff B o) (.leaf P, T) n
    have he : R = leafResponse P j rest hP c :=
      Option.some.inj (hresp.symm.trans (LeafReplay.selector P j rest hP c n))
    subst R
    refine ⟨max b (max c g), ?_⟩
    intro A hAK hAb
    have hAc : ∀ x ∈ A.newWord, c < x := fun x hx ↦
      ((le_max_left c g).trans (le_max_right b _)).trans_lt (hAb x hx)
    let a := LeafReplay.member P j rest hP c A hAc
    have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hAK x (List.mem_toFinset.mp hx)
    have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
      (le_max_left _ _).trans_lt (hAb x (List.mem_toFinset.mp hx))
    have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
      ((le_max_right c g).trans (le_max_right b _)).trans_lt
        (hAb x (List.mem_toFinset.mp hx))
    have hnext := hb a (haK.trans hKH) hab
    have hs := ConservativeRuns.Step.left (.leaf P, T) n (leafResponse P j rest hP c)
      hside (LeafReplay.selector P j rest hP c n) a haK hag
    change RamseyGame.Outcome H (GraphPayoff.game B o
      ((leafResponse P j rest hP c).result (LeafReplay.member P j rest hP c A hAc), T)) true
      at hnext
    rw [LeafReplay.member_result] at hnext hs
    exact ⟨hs, hnext, handoff_after_left hH B o (.leaf P, T)
      (leafResponse P j rest hP c) a _ (LeafReplay.member_result P j rest hP c A hAc) hnext⟩
  | true =>
    obtain ⟨n, R, hside, hresp, b, hb⟩ := hblue
    let c := pairBound (T, .leaf P)
    let g := ConservativeRuns.rightGuard K (GraphPayoff.payoff B o) (T, .leaf P) n
    have he : R = leafResponse P j rest hP c :=
      Option.some.inj (hresp.symm.trans (LeafReplay.selector P j rest hP c n))
    subst R
    refine ⟨max b (max c g), ?_⟩
    intro A hAK hAb
    have hAc : ∀ x ∈ A.newWord, c < x := fun x hx ↦
      ((le_max_left c g).trans (le_max_right b _)).trans_lt (hAb x hx)
    let a := LeafReplay.member P j rest hP c A hAc
    have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hAK x (List.mem_toFinset.mp hx)
    have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
      (le_max_left _ _).trans_lt (hAb x (List.mem_toFinset.mp hx))
    have hag : ∀ x ∈ a.1, g < x := fun x hx ↦
      ((le_max_right c g).trans (le_max_right b _)).trans_lt
        (hAb x (List.mem_toFinset.mp hx))
    have hnext := hb a (haK.trans hKH) hab
    have hs := ConservativeRuns.Step.right (T, .leaf P) n (leafResponse P j rest hP c)
      hside (LeafReplay.selector P j rest hP c n) a haK hag
    change RamseyGame.Outcome H (GraphPayoff.game B o
      (T, (leafResponse P j rest hP c).result (LeafReplay.member P j rest hP c A hAc))) true
      at hnext
    rw [LeafReplay.member_result] at hnext hs
    exact ⟨hs, hnext, handoff_after_right hH B o (T, .leaf P)
      (leafResponse P j rest hP c) a _ (LeafReplay.member_result P j rest hP c A hAc) hnext⟩

theorem respond {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (right : Bool)
    (P : Pending) (T : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : CommandBlue H B o right (.leaf P) T) (d : ℕ) :
    ∃ A : LeafResponses.Setup P.position j,
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.leaf P) T)
        (pair right (.leaf (LeafResponses.toPending P j rest hP A)) T) ∧
      Blue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T ∧
      OtherBlue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T ∧
      ∀ x ∈ A.newWord, x ∈ K ∧ d < x := by
  obtain ⟨b, hb⟩ := certificate_on (hK.mono hKH) hKH B o right P T j rest hP hblue
  obtain ⟨A, hf⟩ := LeafResponses.setup_above P.position j hK (max b d)
  obtain ⟨hs, hnext, hh⟩ := hb A (fun x hx ↦ (hf x hx).1)
    (fun x hx ↦ (le_max_left _ _).trans_lt (hf x hx).2)
  exact ⟨A, hs, hnext, hh,
    fun x hx ↦ ⟨(hf x hx).1, (le_max_right _ _).trans_lt (hf x hx).2⟩⟩

end Erdos118.SelectedLeafResponses
