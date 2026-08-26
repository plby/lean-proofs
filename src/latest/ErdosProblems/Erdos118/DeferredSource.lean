import ErdosProblems.Erdos118.ReplaySources
import ErdosProblems.Erdos118.OptionalBodyReplay
import ErdosProblems.Erdos118.DeferredManaged

/-!
A source certificate against a fixed pending word is retained through an
actual inside game, using either deferred body parameter case. Sampling
may use an infinite subalphabet while all blue certificates remain on H.
-/

namespace Erdos118.DeferredSource

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns BoundaryRelays PreparedRelays ReplaySources

inductive Managed {H : Set ℕ} {B : SimpleGraph G}
    {targetRight : Bool} {targetOther : Pending} (I : Source H B .inside targetRight targetOther) :
    State → Type
  | body (D : BodyDecision) (data : I.Data D.stem) (exactSlots : ExactSlots.Exact (.body D)) :
      Managed I (.body D)
  | waiting (P : Pending) (nonemptyRoots : P.roots ≠ []) (data : I.Data P.position.stem)
      (tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ I.bound < x)
      (exactSlots : ExactSlots.Exact (.leaf P)) : Managed I (.leaf P)
  | prepared (P : Pending) (E : BodyDecision) (targetExact : ExactSlots.Exact (.body E))
      (data : OptionalBodyReplay.Prepared H B .inside targetRight E (.leaf targetOther) P) :
      Managed I (.leaf P)

theorem Managed.exact {H : Set ℕ} {B : SimpleGraph G}
    {targetRight : Bool} {targetOther : Pending} {I : Source H B .inside targetRight targetOther}
    {S : State} (M : Managed I S) : ExactSlots.Exact S := by
  cases M with
  | body D data h => exact h
  | waiting P hn data hf h => exact h
  | prepared P E hE Z => exact Z.exactSlots

theorem Managed.working {H : Set ℕ} {B : SimpleGraph G}
    {targetRight : Bool} {targetOther : Pending} {I : Source H B .inside targetRight targetOther}
    {S : State} (M : Managed I S) : BlueCheckpoints.Working S := by
  cases M <;> trivial

theorem respond_body {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (hI : I.Exact) (right : Bool)
    (D : BodyDecision) (T : State) (data : I.Data D.stem) (hD : ExactSlots.Exact (.body D))
    (hblue : CommandBlue H B .inside right (.body D) T) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k, ∃ _M : Managed I (.leaf (applyBody D A)),
      ConservativeRuns.Step K (GraphPayoff.payoff B .inside)
        (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) ∧
      Blue H B .inside right (.leaf (applyBody D A)) T ∧
      OtherBlue H B .inside right (.leaf (applyBody D A)) T := by
  by_cases hR : D.roots = []
  · obtain ⟨E, hord, hE, hc⟩ := I.resolve_exact hI D data hD hR
    obtain ⟨k, A, Z, hs, hb, hh, _⟩ := OptionalBodyReplay.prepare hK hKH B .inside
      right targetRight D E T (.leaf targetOther) hD hR hord hblue hc I.bound
    exact ⟨k, A, Managed.prepared (applyBody D A) E hE Z, hs, hb, hh⟩
  · obtain ⟨k, A, hs, hb, hh, hf⟩ :=
      PreparedRelays.respond_body_on hK hKH B .inside right D T hblue I.bound
    let data' : I.Data A.position.stem := by rw [A.stem_eq]; exact data
    have htail : ∀ x ∈ A.position.size :: A.position.entries, x ∈ H ∧ I.bound < x := by
      intro x hx
      have h := hf x (List.mem_append_right _ hx)
      exact ⟨hKH h.1, h.2⟩
    exact ⟨k, A, Managed.waiting (applyBody D A) hR data' htail
      (ExactSlots.step_exact (DecisionStates.Step.body D A) hD), hs, hb, hh⟩

private theorem waiting_transition {H : Set ℕ} {B : SimpleGraph G}
    {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (P : Pending) (hn : P.roots ≠ [])
    (data : I.Data P.position.stem)
    (htail : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ I.bound < x)
    (hP : ExactSlots.Exact (.leaf P)) {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hfresh : ∃ v, U.ordinary = P.position.ordinary ++ v ∧ ∀ x ∈ v, x ∈ H ∧ I.bound < x) :
    Nonempty (Managed I U) := by
  have hU := ExactSlots.step_exact hs hP
  obtain ⟨v, hv, hvf⟩ := hfresh
  cases hs with
  | leaf F j rest hF A =>
    have hslot := P.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
    have hAv : A.newWord = v := List.append_cancel_left
      ((LeafResponses.position_ordinary A hslot.1 hslot.2.1).symm.trans hv)
    have hf : ∀ x ∈ (P.position.size :: P.position.entries) ++ A.newWord,
        x ∈ H ∧ I.bound < x := by
      intro x hx
      exact (List.mem_append.mp hx).elim (htail x) (fun hx ↦ hvf x (hAv ▸ hx))
    refine ⟨Managed.waiting (LeafResponses.toPending P j rest hF A) hn data ?_ hU⟩
    simpa only [LeafResponses.toPending, LeafResponses.position, List.cons_append] using hf
  | nextBody F c rest hR hL A =>
    have hAv : A.newWord = v := List.append_cancel_left (A.ordinary.symm.trans hv)
    have hord : A.stem.ordinary = P.position.stem.ordinary ++
        ((P.position.size :: P.position.entries) ++ A.newWord) := by
      rw [A.ordinary]
      simp only [Position.ordinary, List.append_assoc]
    have hf : ∀ x ∈ (P.position.size :: P.position.entries) ++ A.newWord,
        x ∈ H ∧ I.bound < x := by
      intro x hx
      exact (List.mem_append.mp hx).elim (htail x) (fun hx ↦ hvf x (hAv ▸ hx))
    exact ⟨Managed.body (ofStem P c rest hR A)
      (data.transport A.stem A.root_eq A.rootLabel_eq _ hord hf) hU⟩
  | finish F hR hL A => exact (hn hR).elim

private theorem prepared_right_transition {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (P : Pending) (E : BodyDecision)
    (hE : ExactSlots.Exact (.body E))
    (Z : OptionalBodyReplay.Prepared H B .inside targetRight E (.leaf targetOther) P)
    (S : State) (hS : BlueCheckpoints.BeforeLastBody S) {U : State}
    (hs : DecisionStates.Step U (.leaf P))
    (hstep : ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (S, .leaf P) (S, U))
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true) :
    Nonempty (Managed I U) := by
  cases hs with
  | leaf F j rest hF A =>
    obtain ⟨W, _⟩ := OptionalBodyReplay.carry_of_run Z true
      (LeafResponses.toPending P j rest hF A) S S hKH
      (GraphPayoff.payoff B .inside) (Relation.ReflTransGen.single hstep)
    exact ⟨Managed.prepared _ E hE W⟩
  | nextBody F c rest hR hL A =>
    have he : ([] : List ℕ) = c :: rest := Z.lastRoot.symm.trans hR
    cases he
  | finish F hR hL A =>
    exact (DeferredManaged.before_last_not_blue_complete (hK.mono hKH)
      B S hS (ofCompletion P A) hblue).elim

theorem respond_right_leaf {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (P : Pending) (S : State)
    (M : Managed I (.leaf P)) (hS : BlueCheckpoints.BeforeLastBody S)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (S, .leaf P)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (S, .leaf P) (S, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true ∧
      (∀ Q : Pending, U = .leaf Q →
        LeftBlue H (GraphPayoff.payoff B .inside) (S, .leaf Q)) := by
  obtain ⟨R, a, hs, hb, ha⟩ :=
    PreparedRelays.respond_on hK hKH B .inside true (.leaf P) S hblue I.bound
  refine ⟨R.result a, ?_, hs, hb, ?_⟩
  · cases M with
    | waiting P hn data hf hP =>
      exact waiting_transition I P hn data hf hP (R.step a)
        (FreshCheckpoints.response_suffix R a (fun x hx ↦ hKH (ha x hx).1)
          (fun x hx ↦ (ha x hx).2))
    | prepared P E hE Z =>
      exact prepared_right_transition hK hKH I P E hE Z S hS (R.step a) hs hb
  · intro Q he
    exact handoff_after_right (hK.mono hKH) B .inside (S, .leaf P) R a Q he (he ▸ hb)

theorem respond_right {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (hI : I.Exact)
    (S T : State) (M : Managed I T) (hS : BlueCheckpoints.BeforeLastBody S)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B .inside) (S, T) (S, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true := by
  cases M with
  | body D data hD =>
    obtain ⟨k, A, M, hs, hb, _⟩ := respond_body hK hKH I hI true D S data hD hblue
    exact ⟨.leaf (applyBody D A), ⟨M⟩, hs, hb⟩
  | waiting P hn data hf hP =>
    obtain ⟨U, hM, hs, hb, _⟩ :=
      respond_right_leaf hK hKH I P S (Managed.waiting P hn data hf hP) hS hblue
    exact ⟨U, hM, hs, hb⟩
  | prepared P E hE Z =>
    obtain ⟨U, hM, hs, hb, _⟩ :=
      respond_right_leaf hK hKH I P S (Managed.prepared P E hE Z) hS hblue
    exact ⟨U, hM, hs, hb⟩

theorem right_leaf_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (hI : I.Exact)
    (P Q : Pending) (hP : P.roots ≠ []) (M : Managed I (.leaf Q))
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) :
    ∃ U : Pending, Nonempty (Managed I (.leaf U)) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf Q) (.leaf P, .leaf U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf U) := by
  obtain ⟨U, ⟨MU⟩, hs, hb, hh⟩ := respond_right_leaf hK hKH I Q (.leaf P) M hP hblue
  cases MU with
  | body D data hD =>
    have hc : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .body D) := by
      rcases blue_command (GraphPayoff.payoff B .inside) (.leaf P, .body D) rfl hb with hl | hr
      · obtain ⟨n, R, ha, _⟩ := hl
        simp [allowedSide] at ha
      · exact hr
    obtain ⟨k, A, M', hs', hb', hh'⟩ := respond_body hK hKH I hI true D (.leaf P) data hD hc
    exact ⟨applyBody D A, ⟨M'⟩,
      Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hs', hb', hh'⟩
  | waiting U hn data hf hU =>
    exact ⟨U, ⟨Managed.waiting U hn data hf hU⟩,
      Relation.ReflTransGen.single hs, hb, hh U rfl⟩
  | prepared U E hE Z =>
    exact ⟨U, ⟨Managed.prepared U E hE Z⟩, Relation.ReflTransGen.single hs, hb, hh U rfl⟩

theorem right_handoff {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (hI : I.Exact)
    (P : Pending) (T : State) (hP : P.roots ≠ []) (M : Managed I T)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, T)) :
    ∃ Q : Pending, Nonempty (Managed I (.leaf Q)) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (.leaf P, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) := by
  cases M with
  | body D data hD =>
    obtain ⟨k, A, M, hs, hb, hh⟩ := respond_body hK hKH I hI true D (.leaf P) data hD hblue
    exact ⟨applyBody D A, ⟨M⟩, Relation.ReflTransGen.single hs, hb, hh⟩
  | waiting Q hn data hf hQ =>
    exact right_leaf_handoff hK hKH I hI P Q hP (Managed.waiting Q hn data hf hQ) hblue
  | prepared Q E hE Z =>
    exact right_leaf_handoff hK hKH I hI P Q hP (Managed.prepared Q E hE Z) hblue

structure Replay {H : Set ℕ} {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (P : Pending) where
  target : Pending
  ordinary : target.position.ordinary = P.position.ordinary
  entries : target.position.entries = P.position.entries
  marker : target.position.size = P.position.size
  shape : OptionalBodyReplay.LabelShape P target.position
  exactSlots : ExactSlots.Exact (.leaf target)
  blue : Blue H B .inside targetRight (.leaf target) (.leaf targetOther)
  handoff : OtherBlue H B .inside targetRight (.leaf target) (.leaf targetOther)

theorem Managed.fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {targetRight : Bool} {targetOther : Pending} {I : Source H B .inside targetRight targetOther}
    {P : Pending} (M : Managed I (.leaf P)) (hR : P.roots = []) (hL : P.leaves ≠ []) :
    Nonempty (Replay I P) := by
  cases M with
  | waiting P hn data hf hP => exact (hn hR).elim
  | prepared P E hE Z =>
    obtain ⟨l, A, hord, he, hs, hshape, hb, hh⟩ := OptionalBodyReplay.fire hH Z hL
    exact ⟨⟨applyBody E A, hord, he, hs, hshape,
      ExactSlots.step_exact (DecisionStates.Step.body E A) hE, hb, hh⟩⟩

end Erdos118.DeferredSource
