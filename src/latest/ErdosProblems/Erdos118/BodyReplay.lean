import ErdosProblems.Erdos118.PreparedRelays

/-!
Prepared body replay over equal ordinary stems. The target keeps its exact
older decorations, rather than being replaced by a plain-stem overlay.
Both blue bounds are fixed before the common body marker is chosen.
-/

namespace Erdos118.BodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  ordinary : E.stem.ordinary = P.position.stem.ordinary
  size : ℕ
  reserve : Reserve P.position.label P.position.size size
  bound : ℕ
  pairBound_le : pairBound (pair right (.body E) T) ≤ bound
  tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ bound < x
  reserveFresh : ∀ x ∈ reserve.label, x ∈ H ∧ bound < x
  certificate : ∀ A : BodyResponses.Setup E.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    Blue H B o right (.leaf (applyBody E A)) T
  lastRoot : P.roots = []
  exactSlots : ExactSlots.Exact (.leaf P)

private theorem target_before {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) :
    ∀ x ∈ E.stem.decorated, ∀ y ∈ Z.reserve.label, x < y := by
  intro x hx y hy
  have hxb : x ≤ pairBound (pair right (.body E) T) := by
    cases right with
    | false => exact pairBound_left (.body E, T) hx
    | true => exact pairBound_right (T, .body E) hx
  exact (hxb.trans Z.pairBound_le).trans_lt (Z.reserveFresh y hy).2

private def position {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Position where
  stem := E.stem
  size := P.position.size
  label := Z.reserve.label
  entries := P.position.entries
  room := E.room
  started := P.position.started
  unfinished := P.position.unfinished
  increasing := by
    have htail :=
      (List.pairwise_append.mp (List.pairwise_append.mp P.position.increasing).2.1).2.1
    have hne : Z.reserve.label ≠ [] := by
      intro he
      have h := Z.reserve.card
      simp [he] at h
    have hfirst := first_mem hne
    have hbefore := target_before Z
    have hmarker : ∀ x ∈ E.stem.decorated, x < P.position.size :=
      fun x hx ↦ (hbefore x hx _ hfirst).trans (Z.reserve.below _ hfirst)
    have hnew : (Z.reserve.label ++ P.position.size :: P.position.entries).Pairwise (· < ·) := by
      refine List.pairwise_append.mpr ⟨Z.reserve.increasing, htail, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Z.reserve.below x hx
      · exact (Z.reserve.below x hx).trans ((List.pairwise_cons.mp htail).1 y hy)
    refine List.pairwise_append.mpr ⟨E.stem.increasing, hnew, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hbefore x hx y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hmarker x hx
      · exact (hmarker x hx).trans ((List.pairwise_cons.mp htail).1 y hy)

def Prepared.setup {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) : BodyResponses.Setup E.stem Z.size :=
  { position := position Z, stem_eq := rfl, label_length := Z.reserve.card
    entries_length :=
      (ExactSlots.pending_last_leaf P Z.exactSlots hL).symm.trans Z.reserve.first.symm }

theorem Prepared.setup_ordinary {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    (Z.setup hL).position.ordinary = P.position.ordinary := by
  change E.stem.ordinary ++ P.position.size :: P.position.entries = _
  rw [Z.ordinary]
  rfl

theorem Prepared.setup_newWord {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    BodyResponses.newWord (Z.setup hL).position =
      Z.reserve.label ++ P.position.size :: P.position.entries := rfl

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    (applyBody E (Z.setup hL)).position.ordinary = P.position.ordinary ∧
      Blue H B o right (.leaf (applyBody E (Z.setup hL))) T ∧
      OtherBlue H B o right (.leaf (applyBody E (Z.setup hL))) T := by
  have hfresh : ∀ x ∈ BodyResponses.newWord (Z.setup hL).position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    exact (List.mem_append.mp hx).elim (Z.reserveFresh x) (Z.tailFresh x)
  have hb := Z.certificate (Z.setup hL) (fun x hx ↦ (hfresh x hx).1)
    (fun x hx ↦ (hfresh x hx).2)
  exact ⟨Z.setup_ordinary hL, hb, body_handoff hH B o right E T (Z.setup hL)
    (fun x hx ↦ Z.pairBound_le.trans_lt (hfresh x hx).2) hb⟩

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : SameBody P Q)
    (hQ : ExactSlots.Exact (.leaf Q))
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  ordinary := Z.ordinary.trans (congrArg Stem.ordinary hsame.2.1).symm
  size := Z.size
  reserve :=
    { label := Z.reserve.label, card := Z.reserve.card, increasing := Z.reserve.increasing
      first := by rw [hsame.2.2.2.1]; exact Z.reserve.first
      below := by rw [hsame.2.2.1]; exact Z.reserve.below
      shared := by intro x; rw [hsame.2.2.2.1]; exact Z.reserve.shared x }
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  tailFresh := htail
  reserveFresh := Z.reserveFresh
  certificate := Z.certificate
  lastRoot := hsame.1
  exactSlots := hQ

theorem carry_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (sourceRight : Bool) (Q : Pending) (S U : State)
    (hKH : K ⊆ H) (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff
      (pair sourceRight (.leaf P) S) (pair sourceRight (.leaf Q) U)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.reserve.label = Z.reserve.label := by
  have hsame : SameBody P Q := by
    cases sourceRight with
    | false => exact run_last_body_left P Q S U Z.lastRoot hrun
    | true => exact run_last_body_right P Q S U Z.lastRoot hrun
  have hQ : ExactSlots.Exact (.leaf Q) := by
    cases sourceRight with
    | false => exact ExactSlots.run_exact_left hrun Z.exactSlots
    | true => exact ExactSlots.run_exact_right hrun Z.exactSlots
  have hsuffix : ∃ v, Q.position.ordinary = P.position.ordinary ++ v ∧ ∀ x ∈ v, x ∈ K := by
    obtain ⟨v, w, hv, hw, hvK, hwK⟩ := CompletionReplay.run_supported_suffixes hrun
    cases sourceRight with
    | false => exact ⟨v, hv, hvK⟩
    | true => exact ⟨w, hw, hwK⟩
  obtain ⟨v, hv, hvK⟩ := hsuffix
  have htailEq : Q.position.size :: Q.position.entries =
      (P.position.size :: P.position.entries) ++ v := by
    simp only [Position.ordinary, hsame.2.1, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x := by
    intro x hx
    have hb : Z.bound < Q.position.size := by
      rw [hsame.2.2.1]
      exact (Z.tailFresh _ (List.mem_cons_self ..)).2
    have hle : Q.position.size ≤ x := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · have hi :=
          (List.pairwise_append.mp (List.pairwise_append.mp Q.position.increasing).2.1).2.1
        exact ((List.pairwise_cons.mp hi).1 x hx).le
    refine ⟨?_, hb.trans_le hle⟩
    rw [htailEq] at hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ (Z.tailFresh x hx).1)
      (fun hx ↦ hKH (hvK x hx))
  exact ⟨Z.move Q hsame hQ htail, rfl, rfl⟩

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (hE : E.stem.ordinary = D.stem.ordinary)
    (hfirst : CommandBlue H B o originalRight (.body D) S)
    (hsecond : CommandBlue H B o targetRight (.body E) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ _Z : Prepared H B o targetRight E T (applyBody D A),
        ConservativeRuns.Step K (GraphPayoff.payoff B o)
          (pair originalRight (.body D) S) (pair originalRight (.leaf (applyBody D A)) S) ∧
        Blue H B o originalRight (.leaf (applyBody D A)) S ∧
        OtherBlue H B o originalRight (.leaf (applyBody D A)) S ∧
        ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  obtain ⟨k₁, b₁, hb₁⟩ := body_setups B o originalRight D S hfirst
  obtain ⟨k₂, b₂, hb₂⟩ := body_setups B o targetRight E T hsecond
  let c₁ := pairBound (pair originalRight (.body D) S)
  let c₂ := pairBound (pair targetRight (.body E) T)
  let L := max b₂ c₂
  let g := guard K B o originalRight D S k₁
  let M := max b₁ (max c₁ (max L (max g d)))
  have hb₁M : b₁ ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hLM : L ≤ M := by dsimp [M]; omega
  have hgM : g ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, R, hA, hreserve, _⟩ := body_reserved D.stem D.room hK M k₁ k₂
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA x hx).2
  have hAg : ∀ x ∈ BodyResponses.newWord A.position, g < x :=
    fun x hx ↦ hgM.trans_lt (hA x hx).2
  have hstep := body_step B o originalRight D S A
    (command_allowed B o originalRight D S hfirst) (fun x hx ↦ (hA x hx).1) hAc hAg
  have hb := hb₁ A (fun x hx ↦ hKH (hA x hx).1)
    (fun x hx ↦ hb₁M.trans_lt (hA x hx).2)
  have hh := body_handoff (hK.mono hKH) B o originalRight D S A hAc hb
  let Z : Prepared H B o targetRight E T (applyBody D A) :=
    { ordinary := hE.trans (congrArg Stem.ordinary A.stem_eq).symm
      size := k₂, reserve := R, bound := L, pairBound_le := le_max_right _ _
      tailFresh := by
        intro x hx
        have h := hA x (List.mem_append_right _ hx)
        exact ⟨hKH h.1, hLM.trans_lt h.2⟩
      reserveFresh := fun x hx ↦ ⟨hKH (hreserve x hx).1, hLM.trans_lt (hreserve x hx).2⟩
      certificate := fun A' hAH hAL ↦ hb₂ A' hAH
        (fun x hx ↦ (le_max_left _ _).trans_lt (hAL x hx))
      lastRoot := hR
      exactSlots := ExactSlots.step_exact (DecisionStates.Step.body D A) hD }
  exact ⟨k₁, A, Z, hstep, hb, hh, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩⟩

end Erdos118.BodyReplay
