import ErdosProblems.Erdos118.RetainedController
import ErdosProblems.Erdos118.RootBuffer
import ErdosProblems.Erdos118.InsideCompletion

/-!
The remaining-body inside checkpoint produces a triangle. The old S
next-body response contains the fresh SU root response, and the concrete
two-source controller supplies both exact last-body replays.
-/

namespace Erdos118.InsideRootBody

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses PreparedRelays ReplaySources RetainedController

theorem triangle_of_reserve {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (P T T₁ : Pending) (c : ℕ) (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hT : T.roots = [] ∧ T.leaves = [])
    (hleft : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T))
    (k b₀ : ℕ) (Z : RootBuffer.Reserve H b₀ k P.position.stem)
    (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ b₀ < x)
    (hroot : ∀ A : RootResponses.Setup k,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b₀ < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true)
    (hTord : T₁.position.ordinary = T.position.ordinary)
    (hTright : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T₁, .initial)) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨bS, hbS⟩ := StemReplay.left_body_words (GraphPayoff.payoff B .inside)
    P (.leaf T) c [] hPR hPL hleft
  let I : Source H B .inside false T := Source.stem P c hPR hPL bS hbS
  obtain ⟨A, v, hAord, hAroot, hAlabel, hv, hAfresh⟩ := Z.buffer hH P hP hPR hOrd bS
  let D := ofRoot A
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A) trivial
  have hc := ExactSlots.pending_next_last_root P hP hPR
  let data : I.Data D.stem :=
    { root := hAroot
      last := by change A.stem.rootLabel.getLastD 0 = c; rw [hAlabel, Z.sameLast, hc]
      suffix := ⟨v, hAord, hv⟩ }
  have hblueD := hroot A (fun x hx ↦ (hAfresh x hx).1) (fun x hx ↦ (hAfresh x hx).2)
  have hDleft : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hblueD with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨m, A₁, M₁, _, _, hh₁⟩ :=
    RetainedController.respond_body hH Set.Subset.rfl I false D .initial data hD hDleft
  let S₁ := applyBody D A₁
  obtain ⟨l, bU, hbU⟩ := BlueReservations.second_root_setups hH B hB .inside hinit T₁ hTright
  let J : Source H B .inside true T₁ := Source.root l bU hbU
  obtain ⟨mU, Aᵤ, Cᵤ, hAᵤ, hCᵤ, hstart⟩ :=
    BlueReservations.second_root_reserved hH B hB .inside hinit S₁ hh₁ l bU
  let Dᵤ := ofRoot Aᵤ
  let dataU : J.Data Dᵤ.stem :=
    { reserve := Cᵤ, reserveFresh := hCᵤ
      ordinaryFresh := fun x hx ↦ hAᵤ x (Aᵤ.stem.ordinary_sublist.subset hx) }
  let M₂ : Managed J (.body Dᵤ) := Managed.body Dᵤ dataU
    (ExactSlots.step_exact (DecisionStates.Step.root Aᵤ) trivial)
  obtain ⟨⟨V, W⟩, _, hb, hlast, ⟨MV⟩, ⟨MW⟩⟩ :=
    checkpoint hH Set.Subset.rfl I J (.leaf S₁, .body Dᵤ) M₁ M₂ hstart
  cases V with
  | initial => exact hlast.1.elim
  | body E => exact hlast.1.elim
  | complete C => exact hlast.1.elim
  | leaf S =>
    cases W with
    | initial => exact hlast.2.elim
    | body E => exact hlast.2.elim
    | complete C => exact hlast.2.elim
    | leaf U =>
      obtain ⟨S₀, hSord, hST, hShand⟩ := MV.fire hH hlast.1.1 hlast.1.2
      have hSlast := InsideEndgame.last_right_command_left_last hH B S₀ T hT.1 hT.2 hShand
      obtain ⟨U₁, hUord, hTU, _⟩ := MW.fire hH hlast.2.1 hlast.2.2
      exact InsideCompletion.triangle hH B S₀ S T U T₁ U₁
        hSlast hlast.1 hT hlast.2 hSord hTord hUord hST hb hTU

end Erdos118.InsideRootBody
