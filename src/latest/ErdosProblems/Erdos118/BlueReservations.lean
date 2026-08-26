import ErdosProblems.Erdos118.SecondWhole

/-!
Reserved labels chosen through actual blue response certificates. The
active command and both finite bounds are known before the marker is
chosen. These local statements do not assert three-game synchronization.
-/

namespace Erdos118.BlueReservations

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses

theorem initial_root_setups {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) :
    ∃ k b : ℕ, ∀ A : RootResponses.Setup k,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true := by
  obtain ⟨k, b, hb⟩ := WholeBlue.initial_root_blue hH B hB o hblue
  refine ⟨k, b, ?_⟩
  intro A hAH hAb
  have hA0 : ∀ x ∈ A.stem.decorated, 0 < x :=
    fun x hx ↦ (Nat.zero_le b).trans_lt (hAb x hx)
  let a := rootMember 0 A hA0
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hAH x (List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦ hAb x (List.mem_toFinset.mp hx)
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (GraphPayoff.game B o
    ((rootResponse k 0).result (rootMember 0 A hA0), .initial)) true at hnext
  rw [rootMember_result] at hnext
  exact hnext

theorem left_body_setups {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (D : BodyDecision) (T : State) (hblue : LeftBlue H payoff (.body D, T)) :
    ∃ k b : ℕ, ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (.leaf (applyBody D A), T)) true := by
  obtain ⟨k, R, _, hR, b, hb⟩ := hblue
  let c := pairBound (.body D, T)
  have he : R = bodyResponse D k c := Option.some.inj hR.symm
  subst R
  refine ⟨k, max b c, ?_⟩
  intro A hAH hAlarge
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hAlarge x hx)
  let a := bodyMember D c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hAH x (List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hAlarge x (List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    ((bodyResponse D k c).result (bodyMember D c A hAc), T)) true at hnext
  rw [bodyMember_result] at hnext
  exact hnext

theorem right_body_setups {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State) (D : BodyDecision) (hblue : RightBlue H payoff (S, .body D)) :
    ∃ k b : ℕ, ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (S, .leaf (applyBody D A))) true := by
  obtain ⟨k, R, _, hR, b, hb⟩ := hblue
  let c := pairBound (S, .body D)
  have he : R = bodyResponse D k c := Option.some.inj hR.symm
  subst R
  refine ⟨k, max b c, ?_⟩
  intro A hAH hAlarge
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hAlarge x hx)
  let a := bodyMember D c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hAH x (List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hAlarge x (List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (AdaptiveGame.game payoff
    (S, (bodyResponse D k c).result (bodyMember D c A hAc))) true at hnext
  rw [bodyMember_result] at hnext
  exact hnext

theorem left_body_reserved {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (D : BodyDecision) (T : State)
    (hblue : LeftBlue H (GraphPayoff.payoff B o) (.body D, T)) (l d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ R : Reserve A.position.label A.position.size l,
        (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ d < x) ∧
        (∀ x ∈ R.label, x ∈ H ∧ d < x) ∧
        (∀ x ∈ D.stem.decorated, ∀ y ∈ R.label, x < y) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.leaf (applyBody D A), T)) true ∧
        RightBlue H (GraphPayoff.payoff B o) (.leaf (applyBody D A), T) := by
  obtain ⟨k, b, hb⟩ := left_body_setups (GraphPayoff.payoff B o) D T hblue
  let c := pairBound (.body D, T)
  obtain ⟨A, R, hA, hreserve, hbefore⟩ := body_reserved D.stem D.room hH (max b (max c d)) k l
  have hAb : ∀ x ∈ BodyResponses.newWord A.position, b < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ ((le_max_left c d).trans (le_max_right b _)).trans_lt (hA x hx).2
  have hd : d ≤ max b (max c d) := (le_max_right c d).trans (le_max_right b _)
  have hnext := hb A (fun x hx ↦ (hA x hx).1) hAb
  refine ⟨k, A, R, fun x hx ↦ ⟨(hA x hx).1, hd.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hreserve x hx).1, hd.trans_lt (hreserve x hx).2⟩, hbefore, hnext, ?_⟩
  exact handoff_after_left hH B o (.body D, T) (bodyResponse D k c)
    (bodyMember D c A hAc) (applyBody D A) (bodyMember_result D c A hAc) hnext

theorem right_body_reserved {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (S : State) (D : BodyDecision)
    (hblue : RightBlue H (GraphPayoff.payoff B o) (S, .body D)) (l d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ R : Reserve A.position.label A.position.size l,
        (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ d < x) ∧
        (∀ x ∈ R.label, x ∈ H ∧ d < x) ∧
        (∀ x ∈ D.stem.decorated, ∀ y ∈ R.label, x < y) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (S, .leaf (applyBody D A))) true ∧
        LeftBlue H (GraphPayoff.payoff B o) (S, .leaf (applyBody D A)) := by
  obtain ⟨k, b, hb⟩ := right_body_setups (GraphPayoff.payoff B o) S D hblue
  let c := pairBound (S, .body D)
  obtain ⟨A, R, hA, hreserve, hbefore⟩ := body_reserved D.stem D.room hH (max b (max c d)) k l
  have hAb : ∀ x ∈ BodyResponses.newWord A.position, b < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ ((le_max_left c d).trans (le_max_right b _)).trans_lt (hA x hx).2
  have hd : d ≤ max b (max c d) := (le_max_right c d).trans (le_max_right b _)
  have hnext := hb A (fun x hx ↦ (hA x hx).1) hAb
  refine ⟨k, A, R, fun x hx ↦ ⟨(hA x hx).1, hd.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hreserve x hx).1, hd.trans_lt (hreserve x hx).2⟩, hbefore, hnext, ?_⟩
  exact handoff_after_right hH B o (S, .body D) (bodyResponse D k c)
    (bodyMember D c A hAc) (applyBody D A) (bodyMember_result D c A hAc) hnext

theorem initial_root_reserved {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (l d : ℕ) :
    ∃ k : ℕ, ∃ A : RootResponses.Setup k,
      ∃ R : Reserve A.stem.rootLabel A.stem.root l,
        (∀ x ∈ A.stem.decorated, x ∈ H ∧ d < x) ∧
        (∀ x ∈ R.label, x ∈ H ∧ d < x) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true := by
  obtain ⟨k, b, hb⟩ := WholeBlue.initial_root_blue hH B hB o hblue
  obtain ⟨A, R, hA, hreserve⟩ := root_reserved hH (max b d) k l
  have hA0 : ∀ x ∈ A.stem.decorated, 0 < x :=
    fun x hx ↦ (Nat.zero_le _).trans_lt (hA x hx).2
  let a := rootMember 0 A hA0
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (GraphPayoff.game B o
    ((rootResponse k 0).result (rootMember 0 A hA0), .initial)) true at hnext
  rw [rootMember_result] at hnext
  exact ⟨k, A, R, fun x hx ↦ ⟨(hA x hx).1, (le_max_right _ _).trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hreserve x hx).1, (le_max_right _ _).trans_lt (hreserve x hx).2⟩, hnext⟩

theorem second_root_setups {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (P : Pending) (hright : RightBlue H (GraphPayoff.payoff B o) (.leaf P, .initial)) :
    ∃ k b : ℕ, ∀ A : RootResponses.Setup k,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .body (ofRoot A))) true := by
  obtain ⟨k, b, hb⟩ := SecondWhole.second_root_blue hH B hB o hblue P hright
  let c := pairBound (.leaf P, .initial)
  refine ⟨k, max b c, ?_⟩
  intro A hAH hAb
  have hAc : ∀ x ∈ A.stem.decorated, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hAb x hx)
  let a := rootMember c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hAH x (List.mem_toFinset.mp hx)
  have hab : ∀ x ∈ a.1, b < x :=
    fun x hx ↦ (le_max_left _ _).trans_lt (hAb x (List.mem_toFinset.mp hx))
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (GraphPayoff.game B o
    (.leaf P, (rootResponse k c).result (rootMember c A hAc))) true at hnext
  rw [rootMember_result] at hnext
  exact hnext

theorem second_root_reserved {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (P : Pending) (hright : RightBlue H (GraphPayoff.payoff B o) (.leaf P, .initial))
    (l d : ℕ) :
    ∃ k : ℕ, ∃ A : RootResponses.Setup k,
      ∃ R : Reserve A.stem.rootLabel A.stem.root l,
        (∀ x ∈ A.stem.decorated, x ∈ H ∧ d < x) ∧
        (∀ x ∈ R.label, x ∈ H ∧ d < x) ∧
        RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .body (ofRoot A))) true := by
  obtain ⟨k, b, hb⟩ := SecondWhole.second_root_blue hH B hB o hblue P hright
  let c := pairBound (.leaf P, .initial)
  obtain ⟨A, R, hA, hreserve⟩ := root_reserved hH (max b (max c d)) k l
  have hAc : ∀ x ∈ A.stem.decorated, c < x :=
    fun x hx ↦ ((le_max_left c d).trans (le_max_right b _)).trans_lt (hA x hx).2
  let a := rootMember c A hAc
  have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1
  have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hA x (List.mem_toFinset.mp hx)).2
  have hnext := hb a haH hab
  change RamseyGame.Outcome H (GraphPayoff.game B o
    (.leaf P, (rootResponse k c).result (rootMember c A hAc))) true at hnext
  rw [rootMember_result] at hnext
  have hd : d ≤ max b (max c d) := (le_max_right c d).trans (le_max_right b _)
  exact ⟨k, A, R, fun x hx ↦ ⟨(hA x hx).1, hd.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hreserve x hx).1, hd.trans_lt (hreserve x hx).2⟩, hnext⟩

end Erdos118.BlueReservations
