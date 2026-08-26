import ErdosProblems.Erdos118.ManagedCritical

/-!
The actual initial inside game supplies the managed critical checkpoint,
including a root-buffer reserve on the left and the initial replay on
the right. The original initial bound is retained throughout.
-/

namespace Erdos118.ManagedOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays DeferredManaged ManagedCritical
open ManagedRelays (Initial RootPlan)

theorem initial_critical_replay {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1) :
    ∃ I : Initial H B .inside, 0 < I.size ∧ ∃ P Q : Pending, ∃ c : ℕ,
      Nonempty (RootBuffer.Reserve H I.bound I.size P.position.stem) ∧
      P.roots = [c] ∧ P.leaves = [] ∧ Q.roots = [] ∧ Q.leaves ≠ [] ∧
      ExactSlots.Exact (.leaf P) ∧ ExactSlots.Exact (.leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      (∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x) ∧
      Nonempty (Managed I (.leaf Q)) ∧ Nonempty (InitialReplay I Q) := by
  obtain ⟨k, b, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  let I : Initial H B .inside := ⟨k, b, hroot⟩
  obtain ⟨A₀, Z, hA₀⟩ := RootBuffer.root_reserved hH b k
  let D := ofRoot A₀
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A₀) trivial
  have hbD := hroot A₀ (fun x hx ↦ (hA₀ x hx).1) (fun x hx ↦ (hA₀ x hx).2)
  have hcD : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hbD with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨m, A₁, _, _, hhand, hA₁⟩ :=
    PreparedRelays.respond_body hH B .inside false D .initial hcD b
  let S := applyBody D A₁
  have hS : ExactSlots.Exact (.leaf S) :=
    ExactSlots.step_exact (DecisionStates.Step.body D A₁) hD
  have hfS : ∀ x ∈ S.position.ordinary, x ∈ H ∧ b < x := by
    change ∀ x ∈ A₁.position.ordinary, x ∈ H ∧ b < x
    rw [BodyResponses.setup_ordinary]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA₀ x (A₀.stem.ordinary_sublist.subset hx)
    · exact hA₁ x (List.mem_append_right _ hx)
  have hearly : Early (.leaf S) := by
    change A₀.stem.rootLabel.tail ≠ []
    intro he
    have hlen := congrArg List.length he
    rw [List.length_tail, A₀.label_length] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hSroot : S.position.stem.root = A₀.stem.root := by
    change A₁.position.stem.root = A₀.stem.root
    rw [A₁.stem_eq]
    rfl
  have hSlabel : S.position.stem.rootLabel = A₀.stem.rootLabel := by
    change A₁.position.stem.rootLabel = A₀.stem.rootLabel
    rw [A₁.stem_eq]
    rfl
  obtain ⟨l, At, Ct, hAt, hCt, hstart⟩ :=
    BlueReservations.second_root_reserved hH B hB .inside hinit S hhand k b
  let Rt : RootPlan I At.stem :=
    ⟨Ct, hCt, fun x hx ↦ hAt x (At.stem.ordinary_sublist.subset hx)⟩
  let Mt : Managed I (.body (ofRoot At)) := Managed.body (ofRoot At) Rt
    (ExactSlots.step_exact (DecisionStates.Step.root At) trivial)
  have hready : Critical (.leaf S) →
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .body (ofRoot At)) := by
    intro _
    rcases blue_command (GraphPayoff.payoff B .inside) (.leaf S, .body (ofRoot At))
      rfl hstart with hl | hr
    · obtain ⟨n, R, hs, _⟩ := hl
      simp [allowedSide] at hs
    · exact hr
  obtain ⟨P, Q, c, hPR, hPL, hQR, hQL, hP, hQ, hrun, hb, hh, hfP, hMQ, hrep⟩ :=
    critical_replay hH I hfirst hlate hlast (.leaf S) (.body (ofRoot At))
      hearly hS Mt hfS hstart hready
  have hext := (SkippedCuts.run_extensions hrun).1
  have hPlabel : P.position.stem.rootLabel = S.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root S.position.stem.rootLabel rfl)
  have hProot : P.position.stem.root = S.position.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let ZP := Z.move P.position.stem (hProot.trans hSroot) (hPlabel.trans hSlabel)
  exact ⟨I, hk, P, Q, c, ⟨ZP⟩, hPR, hPL, hQR, hQL, hP, hQ, hb, hh, hfP, hMQ, hrep⟩

end Erdos118.ManagedOpening
