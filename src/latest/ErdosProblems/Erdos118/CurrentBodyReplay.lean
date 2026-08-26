import ErdosProblems.Erdos118.CurrentBody

/-!
A body response saved before the source marker, retained through an
actual same-body run, and fired at its last selected leaf. Future root
slots remain unchanged; the target conservative guard is retained.
-/

namespace Erdos118.CurrentBodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  rootLabel : List ℕ
  rootIncreasing : rootLabel.Pairwise (· < ·)
  rootBelow : ∀ x ∈ rootLabel, x < P.position.stem.root
  targetStem : E.stem = LabelOverlays.plainStem P.position.stem rootLabel rootIncreasing rootBelow
  size : ℕ
  reserve : Reserve P.position.label P.position.size size
  before : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ reserve.label, x < y
  bound : ℕ
  pairBound_le : pairBound (pair right (.body E) T) ≤ bound
  tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ bound < x
  reserveFresh : ∀ x ∈ reserve.label, x ∈ H ∧ bound < x
  certificate : ∀ A : BodyResponses.Setup E.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    Blue H B o right (.leaf (applyBody E A)) T
  allowed : allowedSide (pair right (.body E) T) right = true
  guard_le : guard H B o right E T size ≤ bound
  exactSlots : ExactSlots.Exact (.leaf P)

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : CurrentBody.SameBody P Q)
    (hQ : ExactSlots.Exact (.leaf Q))
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  rootLabel := Z.rootLabel
  rootIncreasing := Z.rootIncreasing
  rootBelow := by rw [hsame.stem]; exact Z.rootBelow
  targetStem := by
    rw [Z.targetStem]
    congr 1
    exact hsame.stem.symm
  size := Z.size
  reserve :=
    { label := Z.reserve.label, card := Z.reserve.card, increasing := Z.reserve.increasing
      first := by rw [hsame.label]; exact Z.reserve.first
      below := by rw [hsame.size]; exact Z.reserve.below
      shared := by intro x; rw [hsame.label]; exact Z.reserve.shared x }
  before := by
    change ∀ x ∈ Q.position.stem.decorated, ∀ y ∈ Z.reserve.label, x < y
    rw [hsame.stem]
    exact Z.before
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  tailFresh := htail
  reserveFresh := Z.reserveFresh
  certificate := Z.certificate
  allowed := Z.allowed
  guard_le := Z.guard_le
  exactSlots := hQ

theorem carry_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (sourceRight : Bool) (Q : Pending) (S U : State)
    (hsame : CurrentBody.SameBody P Q) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff
      (pair sourceRight (.leaf P) S) (pair sourceRight (.leaf Q) U)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.reserve.label = Z.reserve.label ∧ W.size = Z.size := by
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
    simp only [Position.ordinary, hsame.stem, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x := by
    intro x hx
    have hb : Z.bound < Q.position.size := by
      rw [hsame.size]
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
  exact ⟨Z.move Q hsame hQ htail, rfl, rfl, rfl⟩

def Prepared.setup {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) : BodyResponses.Setup E.stem Z.size :=
  let A := bodyAtLastLeaf P Z.exactSlots hL Z.rootLabel Z.rootIncreasing
    Z.rootBelow Z.reserve Z.before
  { position := A.position, stem_eq := A.stem_eq.trans Z.targetStem.symm
    label_length := A.label_length, entries_length := A.entries_length }

theorem Prepared.setup_ordinary {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    (Z.setup hL).position.ordinary = P.position.ordinary :=
  bodyAtLastLeaf_ordinary P Z.exactSlots hL Z.rootLabel Z.rootIncreasing
    Z.rootBelow Z.reserve Z.before

theorem Prepared.setup_newWord {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    BodyResponses.newWord (Z.setup hL).position =
      Z.reserve.label ++ P.position.size :: P.position.entries := rfl

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hL : P.leaves = []) :
    (applyBody E (Z.setup hL)).position.ordinary = P.position.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (pair right (.body E) T) (pair right (.leaf (applyBody E (Z.setup hL))) T) ∧
      Blue H B o right (.leaf (applyBody E (Z.setup hL))) T ∧
      OtherBlue H B o right (.leaf (applyBody E (Z.setup hL))) T := by
  have hfresh : ∀ x ∈ BodyResponses.newWord (Z.setup hL).position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    exact (List.mem_append.mp hx).elim (Z.reserveFresh x) (Z.tailFresh x)
  have hb := Z.certificate (Z.setup hL) (fun x hx ↦ (hfresh x hx).1)
    (fun x hx ↦ (hfresh x hx).2)
  refine ⟨Z.setup_ordinary hL, ?_, hb, ?_⟩
  · exact body_step B o right E T (Z.setup hL) Z.allowed
      (fun x hx ↦ (hfresh x hx).1)
      (fun x hx ↦ Z.pairBound_le.trans_lt (hfresh x hx).2)
      (fun x hx ↦ Z.guard_le.trans_lt (hfresh x hx).2)
  · exact body_handoff hH B o right E T (Z.setup hL)
      (fun x hx ↦ Z.pairBound_le.trans_lt (hfresh x hx).2) hb

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D))
    (C : List ℕ) (hC : C.Pairwise (· < ·)) (hCr : ∀ x ∈ C, x < D.stem.root)
    (hE : E.stem = LabelOverlays.plainStem D.stem C hC hCr)
    (hfirst : CommandBlue H B o originalRight (.body D) S)
    (l b₂ : ℕ)
    (hallowed : allowedSide (pair targetRight (.body E) T) targetRight = true)
    (hsecond : ∀ A : BodyResponses.Setup E.stem l,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b₂ < x) →
      Blue H B o targetRight (.leaf (applyBody E A)) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ Z : Prepared H B o targetRight E T (applyBody D A), Z.size = l ∧
        ConservativeRuns.Step K (GraphPayoff.payoff B o)
          (pair originalRight (.body D) S) (pair originalRight (.leaf (applyBody D A)) S) ∧
        Blue H B o originalRight (.leaf (applyBody D A)) S ∧
        OtherBlue H B o originalRight (.leaf (applyBody D A)) S ∧
        ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  obtain ⟨k₁, b₁, hb₁⟩ := body_setups B o originalRight D S hfirst
  let c₁ := pairBound (pair originalRight (.body D) S)
  let c₂ := pairBound (pair targetRight (.body E) T)
  let g₂ := guard H B o targetRight E T l
  let L := max b₂ (max c₂ g₂)
  let g := guard K B o originalRight D S k₁
  let M := max b₁ (max c₁ (max L (max g d)))
  have hb₁M : b₁ ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hLM : L ≤ M := by dsimp [M]; omega
  have hgM : g ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, R, hA, hreserve, hbefore⟩ := body_reserved D.stem D.room hK M k₁ l
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA x hx).2
  have hAg : ∀ x ∈ BodyResponses.newWord A.position, g < x :=
    fun x hx ↦ hgM.trans_lt (hA x hx).2
  have hstep := body_step B o originalRight D S A
    (command_allowed B o originalRight D S hfirst) (fun x hx ↦ (hA x hx).1) hAc hAg
  have hb := hb₁ A (fun x hx ↦ hKH (hA x hx).1)
    (fun x hx ↦ hb₁M.trans_lt (hA x hx).2)
  have hh := body_handoff (hK.mono hKH) B o originalRight D S A hAc hb
  have hCr' : ∀ x ∈ C, x < A.position.stem.root := by rw [A.stem_eq]; exact hCr
  have htarget : E.stem = LabelOverlays.plainStem A.position.stem C hC hCr' := by
    have hstem := A.stem_eq
    rw [hE]
    congr 1
    exact hstem.symm
  let Z : Prepared H B o targetRight E T (applyBody D A) :=
    { rootLabel := C, rootIncreasing := hC, rootBelow := hCr', targetStem := htarget
      size := l, reserve := R
      before := by
        change ∀ x ∈ A.position.stem.decorated, ∀ y ∈ R.label, x < y
        rw [A.stem_eq]
        exact hbefore
      bound := L
      pairBound_le := (le_max_left c₂ g₂).trans (le_max_right _ _)
      tailFresh := by
        intro x hx
        have h := hA x (List.mem_append_right _ hx)
        exact ⟨hKH h.1, hLM.trans_lt h.2⟩
      reserveFresh := fun x hx ↦ ⟨hKH (hreserve x hx).1, hLM.trans_lt (hreserve x hx).2⟩
      certificate := fun A' hAH hAL ↦ hsecond A' hAH
        (fun x hx ↦ (le_max_left _ _).trans_lt (hAL x hx))
      allowed := hallowed
      guard_le := (le_max_right c₂ g₂).trans (le_max_right _ _)
      exactSlots := ExactSlots.step_exact (DecisionStates.Step.body D A) hD }
  exact ⟨k₁, A, Z, rfl, hstep, hb, hh, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩⟩

end Erdos118.CurrentBodyReplay
