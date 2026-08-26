import ErdosProblems.Erdos118.AlignedRootPreparation
import ErdosProblems.Erdos118.ReplaySources

/-! An actual aligned root replay on the right against a fixed pending
word. The target first-body parameter is not assumed positive. -/

namespace Erdos118.AlignedRightPreparation

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

structure RootCertificate (H : Set ℕ) (B : SimpleGraph G) (T : Pending) where
  size : ℕ
  bound : ℕ
  rootBlue : ∀ A : RootResponses.Setup size,
    (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, bound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T, .body (ofRoot A))) true

theorem at_shared {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (T : Pending) (I : RootCertificate H B T)
    (D : BodyDecision) (X : State) (Z : AlignedRootReserve.Reserve H I.bound I.size D.stem)
    (hD : ExactSlots.Exact (.body D)) (hindex : D.stem.done.length + 1 = Z.shared)
    (hf : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ I.bound < x)
    (hb : RightBlue H (GraphPayoff.payoff B .inside) (X, .body D)) (d : ℕ) :
    ∃ C : RootResponses.Setup I.size, C.stem.rootLabel = Z.label ∧
      ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ _W : CurrentBodyReplay.Prepared H B .inside true (ofRoot C) (.leaf T) (applyBody D A),
        (applyBody D A).roots = [D.stem.rootLabel.getLastD 0] ∧
        ConservativeRuns.Step K (GraphPayoff.payoff B .inside)
          (X, .body D) (X, .leaf (applyBody D A)) ∧
        RamseyGame.Outcome H (GraphPayoff.game B .inside (X, .leaf (applyBody D A))) true ∧
        LeftBlue H (GraphPayoff.payoff B .inside) (X, .leaf (applyBody D A)) ∧
        ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  let C := Z.rootSetup hindex
  have hC := Z.rootSetup_supported hindex hf
  have hbC := I.rootBlue C (fun x hx ↦ (hC x hx).1) (fun x hx ↦ (hC x hx).2)
  obtain ⟨l, b₂, hb₂⟩ := body_setups B .inside true (ofRoot C) (.leaf T)
    (ReplaySources.body_command B .inside true (ofRoot C) T hbC)
  obtain ⟨k, A, W, _, hs, hbA, hh, hA⟩ := CurrentBodyReplay.prepare
    hK hKH B .inside true true D (ofRoot C) X (.leaf T) hD Z.label Z.increasing Z.below
    rfl hb l b₂ rfl hb₂ d
  have hR : D.roots = [D.stem.rootLabel.getLastD 0] := by
    rw [hD, hindex]
    exact Z.above_shared
  exact ⟨C, rfl, k, A, W, hR, hs, hbA, hh, hA⟩

structure Replay {H : Set ℕ} {B : SimpleGraph G} {T : Pending}
    (I : RootCertificate H B T) (Q : Pending) where
  rootSetup : RootResponses.Setup I.size
  size : ℕ
  body : BodyResponses.Setup rootSetup.stem size
  ordinary : body.position.ordinary = Q.position.ordinary
  marker : body.position.size = Q.position.size
  entries : body.position.entries = Q.position.entries
  rootLast : rootSetup.stem.rootLabel.getLastD 0 = Q.position.stem.rootLabel.getLastD 0
  step : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf T, .body (ofRoot rootSetup)) (.leaf T, .leaf (applyBody (ofRoot rootSetup) body))
  blue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf T, .leaf (applyBody (ofRoot rootSetup) body))) true
  handoff : LeftBlue H (GraphPayoff.payoff B .inside)
    (.leaf T, .leaf (applyBody (ofRoot rootSetup) body))

def Replay.target {H : Set ℕ} {B : SimpleGraph G} {T Q : Pending}
    {I : RootCertificate H B T} (R : Replay I Q) : Pending :=
  applyBody (ofRoot R.rootSetup) R.body

theorem checkpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (T : Pending) (I : RootCertificate H B T)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (P : Pending) (hP : ExactSlots.Exact (.leaf P)) {k : ℕ} (A : RootResponses.Setup k)
    (Z : AlignedRootReserve.Reserve H I.bound I.size A.stem)
    (hA : ∀ x ∈ A.stem.ordinary, x ∈ H ∧ I.bound < x)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body (ofRoot A))) true)
    (d : ℕ) :
    ∃ P' Q' : Pending, ∃ a c : ℕ,
      P'.roots = [a] ∧ P'.leaves = [] ∧ Q'.roots = [c] ∧ Q'.leaves = [] ∧
      ExactSlots.Exact (.leaf P') ∧ ExactSlots.Exact (.leaf Q') ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
        (.leaf P, .body (ofRoot A)) (.leaf P', .leaf Q') ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P', .leaf Q')) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P', .leaf Q') ∧
      FreshCheckpoints.FreshExtension K d
        (.leaf P, .body (ofRoot A)) (.leaf P', .leaf Q') ∧
      Nonempty (Replay I Q') := by
  have hH : H.Infinite := hK.mono hKH
  have hXA : ExactSlots.Exact (.body (ofRoot A)) :=
    ExactSlots.step_exact (DecisionStates.Step.root A) trivial
  obtain ⟨D, Y, hindex, hD, hnotbody, hr₀, hb₀, hh₀, u₀, v₀, hu₀, hv₀, huf₀, hvf₀⟩ :=
    RootBodyCheckpoint.right hK hKH B .inside Z.shared (max I.bound d)
      (.body (ofRoot A)) (.leaf P) (RootBodyCheckpoint.root_before A Z.shared_mem)
      hXA (by intro E h; cases h) hb
  have hnotinitial : Y ≠ .initial := by
    have hm : P.position.stem.root ∈ Y.ordinary := by
      rw [hu₀]
      exact List.mem_append_left _ (by simp [State.ordinary, Position.ordinary, Stem.ordinary])
    intro he
    simp [he, State.ordinary] at hm
  have hYpending : ∃ P₀ : Pending, Y = .leaf P₀ := by
    cases Y with
    | initial => exact (hnotinitial rfl).elim
    | body E => exact (hnotbody E rfl).elim
    | leaf P₀ => exact ⟨P₀, rfl⟩
    | complete C => exact (complete_body_not_blue hH B .inside C D hb₀).elim
  obtain ⟨P₀, rfl⟩ := hYpending
  have hext := (SkippedCuts.run_extensions hr₀).2
  have hlabel : D.stem.rootLabel = A.stem.rootLabel := Option.some.inj (hext.labels.root _ rfl)
  have hroot : D.stem.root = A.stem.root := (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let ZD := Z.move D.stem hroot hlabel
  have hfD : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ I.bound < x := by
    intro x hx
    change x ∈ State.ordinary (.body D) at hx
    rw [hv₀] at hx
    exact (List.mem_append.mp hx).elim (hA x)
      (fun hx ↦ ⟨hKH (hvf₀ x hx).1, (le_max_left _ _).trans_lt (hvf₀ x hx).2⟩)
  let e := max d (pairBound (.leaf P₀, .body D))
  obtain ⟨C, hClabel, m, F, W, hroots, hs, hb₁, hh₁, hF⟩ :=
    at_shared hK hKH B T I D (.leaf P₀) ZD hD hindex hfD hh₀ e
  let Q₀ := applyBody D F
  have hP₀ := ExactSlots.run_exact_left hr₀ hP
  have hQ₀ := ExactSlots.step_exact (DecisionStates.Step.body D F) hD
  have hFl : ∀ x ∈ BodyResponses.newWord F.position,
      pairBound (.leaf P₀, .body D) < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hF x hx).2
  have hendpoint : pairBound (.leaf P₀, .body D) < Q₀.position.ordinary.getLastD 0 := by
    have h := AlignedRootPreparation.response_endpoint (bodyResponse D m _)
      (ReservedResponses.bodyMember D _ F hFl)
    rw [ReservedResponses.bodyMember_result] at h
    exact h
  have horder : P₀.position.ordinary.getLastD 0 < Q₀.position.ordinary.getLastD 0 := by
    have hne : P₀.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
    have hm : P₀.position.ordinary.getLastD 0 ∈ P₀.position.ordinary := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      exact List.getLast_mem hne
    exact (pairBound_left (.leaf P₀, .body D)
      (P₀.position.ordinary_sublist.subset hm)).trans_lt hendpoint
  obtain ⟨P', Q', a, hsame, hPR, hPL, hQR, hQL, hP', hQ', _, hr₁, hb', hh', hf₁⟩ :=
    AlignedCurrentCheckpoint.right_critical hK hKH B hall P₀ Q₀ hP₀ hQ₀
      (D.stem.rootLabel.getLastD 0) hroots horder hb₁ (fun _ ↦ hh₁) d
  obtain ⟨W', _, _, _⟩ := CurrentBodyReplay.carry_of_run W true Q' (.leaf P₀) (.leaf P')
    hsame hKH (GraphPayoff.payoff B .inside) hr₁
  obtain ⟨hord, htstep, htblue, hthand⟩ := CurrentBodyReplay.fire hH W' hQL
  have hlast : C.stem.rootLabel.getLastD 0 = Q'.position.stem.rootLabel.getLastD 0 := by
    rw [hClabel, hsame.stem]
    change ZD.label.getLastD 0 = F.position.stem.rootLabel.getLastD 0
    rw [F.stem_eq]
    exact ZD.sameLast
  let R : Replay I Q' :=
    { rootSetup := C, size := W'.size, body := W'.setup hQL
      ordinary := hord, marker := rfl, entries := rfl, rootLast := hlast
      step := htstep, blue := htblue, handoff := hthand }
  have hf₀ : FreshCheckpoints.FreshExtension K d
      (.leaf P, .body (ofRoot A)) (.leaf P₀, .body D) :=
    ⟨u₀, v₀, hu₀, hv₀,
      fun x hx ↦ ⟨(huf₀ x hx).1, (le_max_right _ _).trans_lt (huf₀ x hx).2⟩,
      fun x hx ↦ ⟨(hvf₀ x hx).1, (le_max_right _ _).trans_lt (hvf₀ x hx).2⟩⟩
  have hfstep : FreshCheckpoints.FreshExtension K d
      (.leaf P₀, .body D) (.leaf P₀, .leaf Q₀) := by
    refine ⟨[], F.position.size :: F.position.entries, by simp, ?_, by simp, ?_⟩
    · exact BodyResponses.setup_ordinary F
    · intro x hx
      have hf := hF x (List.mem_append_right _ hx)
      exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2⟩
  exact ⟨P', Q', a, D.stem.rootLabel.getLastD 0, hPR, hPL, hQR, hQL, hP', hQ',
    (Relation.ReflTransGen.tail hr₀ hs).trans hr₁, hb', hh',
    FreshCheckpoints.fresh_trans (FreshCheckpoints.fresh_trans hf₀ hfstep) hf₁, ⟨R⟩⟩


end Erdos118.AlignedRightPreparation
