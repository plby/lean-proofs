import ErdosProblems.Erdos118.ManagedRelays

/-!
A coupled construction that installs both original words' relay data at
their last body decisions and stops before either word completes. The
result supplies two shared last/first pending positions, not a triangle.
-/

namespace Erdos118.CoupledRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses ManagedRelays

theorem checkpoint {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (S : State × State)
    (M : Managed I S.1) (N : Managed I S.2)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o S) true) :
    ∃ T : State × State, ConservativeRuns.Run H (GraphPayoff.payoff B o) S T ∧
      RamseyGame.Outcome H (GraphPayoff.game B o T) true ∧ BothLast T ∧
      Nonempty (Managed I T.1) ∧ Nonempty (Managed I T.2) := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hlast : BothLast S
    · exact ⟨S, Relation.ReflTransGen.refl, hblue, hlast, ⟨M⟩, ⟨N⟩⟩
    · have hnone : terminalPayoff (GraphPayoff.payoff B o) S = none := by
        obtain ⟨S, T⟩ := S
        cases M <;> cases N <;> rfl
      rcases blue_command (GraphPayoff.payoff B o) S hnone hblue with hl | hr
      · obtain ⟨U, ⟨M'⟩, hs, hb⟩ := respond_side hH I false S.1 S.2 M N hl hlast
        obtain ⟨T, hrun, hblueT, hlastT, hMT, hNT⟩ :=
          ih (U, S.2) hs.pairStep M' N hb
        exact ⟨T, Relation.ReflTransGen.head hs hrun, hblueT, hlastT, hMT, hNT⟩
      · obtain ⟨U, ⟨N'⟩, hs, hb⟩ := respond_side hH I true S.2 S.1 N M hr hlast
        obtain ⟨T, hrun, hblueT, hlastT, hMT, hNT⟩ :=
          ih (S.1, U) hs.pairStep M N' hb
        exact ⟨T, Relation.ReflTransGen.head hs hrun, hblueT, hlastT, hMT, hNT⟩

structure ForkedPair (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation) where
  left : Pending
  right : Pending
  leftLast : left.roots = [] ∧ left.leaves = []
  rightLast : right.roots = [] ∧ right.leaves = []
  blue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf left, .leaf right)) true
  leftRelay : Pending
  rightRelay : Pending
  leftOrdinary : leftRelay.position.ordinary = left.position.ordinary
  rightOrdinary : rightRelay.position.ordinary = right.position.ordinary
  leftBlue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf leftRelay, .initial)) true
  rightBlue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf rightRelay, .initial)) true
  leftHandoff : RightBlue H (GraphPayoff.payoff B o) (.leaf leftRelay, .initial)
  rightHandoff : RightBlue H (GraphPayoff.payoff B o) (.leaf rightRelay, .initial)

theorem forks_of_managed {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (S : State × State)
    (M : Managed I S.1) (N : Managed I S.2)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o S) true) :
    ∃ F : ForkedPair H B o,
      ConservativeRuns.Run H (GraphPayoff.payoff B o) S (.leaf F.left, .leaf F.right) := by
  obtain ⟨⟨U, V⟩, hrun, hb, hlast, ⟨M'⟩, ⟨N'⟩⟩ := checkpoint hH I S M N hblue
  cases U with
  | initial => exact hlast.1.elim
  | body D => exact hlast.1.elim
  | complete C => exact hlast.1.elim
  | leaf P =>
    cases V with
    | initial => exact hlast.2.elim
    | body D => exact hlast.2.elim
    | complete C => exact hlast.2.elim
    | leaf Q =>
      obtain ⟨P', hPord, hPb, hPh⟩ := M'.fire hH hlast.1.1 hlast.1.2
      obtain ⟨Q', hQord, hQb, hQh⟩ := N'.fire hH hlast.2.1 hlast.2.2
      exact ⟨⟨P, Q, hlast.1, hlast.2, hb, P', Q', hPord, hQord, hPb, hQb, hPh, hQh⟩, hrun⟩

theorem initial_forks {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) :
    Nonempty (ForkedPair H B o) := by
  obtain ⟨I⟩ := exists_initial hH B hB o hblue
  obtain ⟨A₀, C₀, hA₀, hC₀⟩ := root_reserved hH I.bound I.size I.size
  let D₀ := ofRoot A₀
  let root₀ : RootPlan I D₀.stem :=
    { reserve := C₀, reserveFresh := hC₀
      ordinaryFresh := fun x hx ↦ hA₀ x (A₀.stem.ordinary_sublist.subset hx) }
  have hD₀ : ExactSlots.Exact (.body D₀) :=
    ExactSlots.step_exact (DecisionStates.Step.root A₀) trivial
  have hb₀ := I.rootBlue A₀ (fun x hx ↦ (hA₀ x hx).1) (fun x hx ↦ (hA₀ x hx).2)
  have hc₀ : PreparedRelays.CommandBlue H B o false (.body D₀) .initial := by
    rcases blue_command (GraphPayoff.payoff B o) (.body D₀, .initial) rfl hb₀ with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨k₁, A₁, M₁, _, hb₁, hh₁⟩ :=
    ManagedRelays.respond_body hH I false D₀ .initial root₀ hD₀ hc₀
  let P₁ := applyBody D₀ A₁
  obtain ⟨k₂, b₂, hb₂⟩ := SecondWhole.second_root_blue hH B hB o hblue P₁ hh₁
  let c₂ := pairBound (.leaf P₁, .initial)
  let L := max I.bound (max b₂ c₂)
  obtain ⟨A₂, C₂, hA₂, hC₂⟩ := root_reserved hH L k₂ I.size
  have hIb : I.bound ≤ L := le_max_left _ _
  have hb₂L : b₂ ≤ L := (le_max_left b₂ c₂).trans (le_max_right I.bound _)
  have hc₂L : c₂ ≤ L := (le_max_right b₂ c₂).trans (le_max_right I.bound _)
  have hA₂c : ∀ x ∈ A₂.stem.decorated, c₂ < x :=
    fun x hx ↦ hc₂L.trans_lt (hA₂ x hx).2
  let a₂ := rootMember c₂ A₂ hA₂c
  have ha₂H : (↑a₂.1 : Set ℕ) ⊆ H := fun x hx ↦ (hA₂ x (List.mem_toFinset.mp hx)).1
  have ha₂b : ∀ x ∈ a₂.1, b₂ < x :=
    fun x hx ↦ hb₂L.trans_lt (hA₂ x (List.mem_toFinset.mp hx)).2
  have hnext := hb₂ a₂ ha₂H ha₂b
  change RamseyGame.Outcome H (GraphPayoff.game B o
    (.leaf P₁, (rootResponse k₂ c₂).result (rootMember c₂ A₂ hA₂c))) true at hnext
  rw [rootMember_result] at hnext
  let root₂ : RootPlan I (ofRoot A₂).stem :=
    { reserve := C₂
      reserveFresh := fun x hx ↦ ⟨(hC₂ x hx).1, hIb.trans_lt (hC₂ x hx).2⟩
      ordinaryFresh := fun x hx ↦
        let h := hA₂ x (A₂.stem.ordinary_sublist.subset hx)
        ⟨h.1, hIb.trans_lt h.2⟩ }
  let M₂ := Managed.body (ofRoot A₂) root₂
    (ExactSlots.step_exact (DecisionStates.Step.root A₂) trivial)
  obtain ⟨F, _⟩ := forks_of_managed hH I (.leaf P₁, .body (ofRoot A₂)) M₁ M₂ hnext
  exact ⟨F⟩

end Erdos118.CoupledRelays
