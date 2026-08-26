import ErdosProblems.Erdos118.SourceCritical
import ErdosProblems.Erdos118.ManagedOpening

/-!
An inserted initial game reaches the same last-root checkpoint, with its
entire new left ordinary suffix above the old prescribed response bound.
Its right word retains a deferred source certificate against the old replay.
-/

namespace Erdos118.RootInsertion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReplaySources DeferredSource
open ManagedRelays (Initial)
open ManagedCritical (Early Critical)

theorem inserted_checkpoint {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (I : Initial H B .inside) (hk : 0 < I.size)
    (P T₁ : Pending) (c : ℕ) (hPR : P.roots = [c])
    (hP : ExactSlots.Exact (.leaf P)) (Z : RootBuffer.Reserve H I.bound I.size P.position.stem)
    (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x)
    (hTright : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T₁, .initial))
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1) (d : ℕ) :
    ∃ J : Source H B .inside true T₁, J.Exact ∧ ∃ R U : Pending,
      R.roots = [c] ∧ R.leaves = [] ∧ U.roots = [] ∧ U.leaves ≠ [] ∧
      ExactSlots.Exact (.leaf R) ∧ ExactSlots.Exact (.leaf U) ∧
      R.position.stem.root = P.position.stem.root ∧ R.position.stem.rootLabel = Z.label ∧
      (∃ v : List ℕ, R.position.ordinary = P.position.ordinary ++ v ∧
        ∀ x ∈ v, x ∈ H ∧ d < x) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf R, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf R, .leaf U) ∧
      Nonempty (Managed J (.leaf U)) ∧ Nonempty (Replay J U) := by
  obtain ⟨A, v, hAord, hAroot, hAlabel, hv, hAfresh⟩ := Z.buffer hH P hP hPR hOrd d
  let D := ofRoot A
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A) trivial
  have hbD := I.rootBlue A (fun x hx ↦ (hAfresh x hx).1) (fun x hx ↦ (hAfresh x hx).2)
  have hcD : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hbD with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  let K := H \ Set.Iic d
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic d)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  obtain ⟨m, A₁, _, _, hh₁, hA₁⟩ :=
    PreparedRelays.respond_body_on hK hKH B .inside false D .initial hcD d
  let S := applyBody D A₁
  have hS : ExactSlots.Exact (.leaf S) :=
    ExactSlots.step_exact (DecisionStates.Step.body D A₁) hD
  have hearly : Early (.leaf S) := by
    change A.stem.rootLabel.tail ≠ []
    intro he
    have hlen := congrArg List.length he
    rw [List.length_tail, A.label_length] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hSroot : S.position.stem.root = P.position.stem.root := by
    change A₁.position.stem.root = _
    rw [A₁.stem_eq]
    exact hAroot
  have hSlabel : S.position.stem.rootLabel = Z.label := by
    change A₁.position.stem.rootLabel = _
    rw [A₁.stem_eq]
    exact hAlabel
  have hfS : ∃ w : List ℕ, S.position.ordinary = P.position.ordinary ++ w ∧
      ∀ x ∈ w, x ∈ H ∧ d < x := by
    refine ⟨v ++ A₁.position.size :: A₁.position.entries, ?_, ?_⟩
    · change A₁.position.ordinary = _
      rw [BodyResponses.setup_ordinary]
      change A.stem.ordinary ++ A₁.position.size :: A₁.position.entries = _
      rw [hAord, List.append_assoc]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hv x hx
      · have h := hA₁ x (List.mem_append_right _ hx)
        exact ⟨hKH h.1, h.2⟩
  obtain ⟨l, bU, hbU⟩ := BlueReservations.second_root_setups hH B hB .inside hinit T₁ hTright
  let J : Source H B .inside true T₁ := Source.root l bU hbU
  obtain ⟨mU, Aᵤ, Cᵤ, hAᵤ, hCᵤ, hstart⟩ :=
    BlueReservations.second_root_reserved hH B hB .inside hinit S hh₁ l (max bU d)
  let dataU : J.Data (ofRoot Aᵤ).stem :=
    { reserve := Cᵤ
      reserveFresh := fun x hx ↦ ⟨(hCᵤ x hx).1, (le_max_left _ _).trans_lt (hCᵤ x hx).2⟩
      ordinaryFresh := by
        intro x hx
        have h := hAᵤ x (Aᵤ.stem.ordinary_sublist.subset hx)
        exact ⟨h.1, (le_max_left _ _).trans_lt h.2⟩ }
  let Mᵤ : Managed J (.body (ofRoot Aᵤ)) := Managed.body (ofRoot Aᵤ) dataU
    (ExactSlots.step_exact (DecisionStates.Step.root Aᵤ) trivial)
  have hready : Critical (.leaf S) →
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .body (ofRoot Aᵤ)) := by
    intro _
    rcases blue_command (GraphPayoff.payoff B .inside) (.leaf S, .body (ofRoot Aᵤ))
      rfl hstart with hl | hr
    · obtain ⟨n, R, hs, _⟩ := hl
      simp [allowedSide] at hs
    · exact hr
  obtain ⟨R, U, c', hRR, hRL, hUR, hUL, hR, hU, hrun, hb, hh, ⟨z, hz, hzf⟩, hM, hrep⟩ :=
    SourceCritical.checkpoint hK hKH J trivial hlate hlast d
      (.leaf S) (.body (ofRoot Aᵤ)) hearly hS Mᵤ hstart hready
  have hext := (SkippedCuts.run_extensions hrun).1
  have hRlabel : R.position.stem.rootLabel = Z.label :=
    (Option.some.inj (hext.labels.root S.position.stem.rootLabel rfl)).trans hSlabel
  have hRroot : R.position.stem.root = P.position.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm.trans hSroot
  have hcc : c' = c := by
    have h := ExactSlots.pending_next_last_root R hR hRR
    rw [hRlabel, Z.sameLast, ExactSlots.pending_next_last_root P hP hPR] at h
    exact h.symm
  subst c'
  obtain ⟨w, hw, hwf⟩ := hfS
  refine ⟨J, trivial, R, U, hRR, hRL, hUR, hUL, hR, hU, hRroot, hRlabel, ?_, hb, hh, hM, hrep⟩
  refine ⟨w ++ z, ?_, ?_⟩
  · change R.position.ordinary = S.position.ordinary ++ z at hz
    rw [hz, hw, List.append_assoc]
  · intro x hx
    exact (List.mem_append.mp hx).elim (hwf x)
      (fun hx ↦ ⟨hKH (hzf x hx).1, (hzf x hx).2⟩)

end Erdos118.RootInsertion
