import ErdosProblems.Erdos118.RetainedController

/-!
Run TU to both last selections while retaining right-word relays into two
fixed left prefixes. The target right versions need not themselves be last.
-/

namespace Erdos118.ReversedForks

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses PreparedRelays ReplaySources RetainedController

structure Forks (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (S₀ S₁ : Pending) where
  T : Pending
  U : Pending
  T₀ : Pending
  U₀ : Pending
  tLast : T.roots = [] ∧ T.leaves = []
  uLast : U.roots = [] ∧ U.leaves = []
  tOrdinary : T₀.position.ordinary = T.position.ordinary
  uOrdinary : U₀.position.ordinary = U.position.ordinary
  blueTU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T, .leaf U)) true
  blueST : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S₀, .leaf T₀)) true
  blueSU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S₁, .leaf U₀)) true
  leftST : LeftBlue H (GraphPayoff.payoff B o) (.leaf S₀, .leaf T₀)
  leftSU : LeftBlue H (GraphPayoff.payoff B o) (.leaf S₁, .leaf U₀)

theorem exists_forks {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (S₀ S₁ : Pending)
    (hS₀ : RightBlue H (GraphPayoff.payoff B o) (.leaf S₀, .initial))
    (hS₁ : RightBlue H (GraphPayoff.payoff B o) (.leaf S₁, .initial)) :
    Nonempty (Forks H B o S₀ S₁) := by
  obtain ⟨kT, bT, hbT⟩ := BlueReservations.second_root_setups hH B hB o hinit S₀ hS₀
  obtain ⟨kU, bU, hbU⟩ := BlueReservations.second_root_setups hH B hB o hinit S₁ hS₁
  let I : Source H B o true S₀ := Source.root kT bT hbT
  let J : Source H B o true S₁ := Source.root kU bU hbU
  obtain ⟨m, At, Ct, hAt, hCt, hblueDt⟩ :=
    BlueReservations.initial_root_reserved hH B hB o hinit kT bT
  let Dt := ofRoot At
  have hDt : ExactSlots.Exact (.body Dt) :=
    ExactSlots.step_exact (DecisionStates.Step.root At) trivial
  let dataT : I.Data Dt.stem :=
    { reserve := Ct, reserveFresh := hCt
      ordinaryFresh := fun x hx ↦ hAt x (At.stem.ordinary_sublist.subset hx) }
  have hcmdDt : CommandBlue H B o false (.body Dt) .initial := by
    rcases blue_command (GraphPayoff.payoff B o) (.body Dt, .initial) rfl hblueDt with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨n, A, M, _, _, hh⟩ :=
    RetainedController.respond_body hH Set.Subset.rfl I false Dt .initial dataT hDt hcmdDt
  let T₁ := applyBody Dt A
  obtain ⟨l, Au, Cu, hAu, hCu, hblueTU⟩ :=
    BlueReservations.second_root_reserved hH B hB o hinit T₁ hh kU bU
  let Du := ofRoot Au
  let dataU : J.Data Du.stem :=
    { reserve := Cu, reserveFresh := hCu
      ordinaryFresh := fun x hx ↦ hAu x (Au.stem.ordinary_sublist.subset hx) }
  let N : Managed J (.body Du) := Managed.body Du dataU
    (ExactSlots.step_exact (DecisionStates.Step.root Au) trivial)
  obtain ⟨⟨V, W⟩, _, hb, hlast, ⟨MV⟩, ⟨MW⟩⟩ :=
    RetainedController.checkpoint hH Set.Subset.rfl I J (.leaf T₁, .body Du) M N hblueTU
  cases V with
  | initial => exact hlast.1.elim
  | body D => exact hlast.1.elim
  | complete C => exact hlast.1.elim
  | leaf T =>
    cases W with
    | initial => exact hlast.2.elim
    | body D => exact hlast.2.elim
    | complete C => exact hlast.2.elim
    | leaf U =>
      obtain ⟨T₀, hTord, hbST, hhST⟩ := MV.fire hH hlast.1.1 hlast.1.2
      obtain ⟨U₀, hUord, hbSU, hhSU⟩ := MW.fire hH hlast.2.1 hlast.2.2
      exact ⟨⟨T, U, T₀, U₀, hlast.1, hlast.2, hTord, hUord, hb,
        hbST, hbSU, hhST, hhSU⟩⟩

end Erdos118.ReversedForks
