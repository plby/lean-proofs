import ErdosProblems.Erdos118.BlueReservations
import ErdosProblems.Erdos118.BoundaryRelays
import ErdosProblems.Erdos118.CompletionReplay

/-!
Relay data prepared before a body marker, retained through intervening
responses, and used at the actual last leaf. Either side of the actual
target game can be selected; no symmetry of that game is assumed.
-/

namespace Erdos118.PreparedRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

def pair (right : Bool) (S T : State) : State × State :=
  if right then (T, S) else (S, T)

def Blue (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (S T : State) : Prop :=
  RamseyGame.Outcome H (GraphPayoff.game B o (pair right S T)) true

def CommandBlue (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (S T : State) : Prop :=
  if right then RightBlue H (GraphPayoff.payoff B o) (T, S)
  else LeftBlue H (GraphPayoff.payoff B o) (S, T)

def OtherBlue (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (S T : State) : Prop :=
  if right then LeftBlue H (GraphPayoff.payoff B o) (T, S)
  else RightBlue H (GraphPayoff.payoff B o) (S, T)

theorem body_setups {H : Set ℕ} (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (D : BodyDecision) (T : State)
    (hblue : CommandBlue H B o right (.body D) T) :
    ∃ k b : ℕ, ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      Blue H B o right (.leaf (applyBody D A)) T := by
  cases right with
  | false => exact BlueReservations.left_body_setups (GraphPayoff.payoff B o) D T hblue
  | true => exact BlueReservations.right_body_setups (GraphPayoff.payoff B o) T D hblue

theorem command_allowed {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (D : BodyDecision) (T : State)
    (hblue : CommandBlue H B o right (.body D) T) :
    allowedSide (pair right (.body D) T) right = true := by
  cases right with
  | false =>
    obtain ⟨n, R, hs, _⟩ := hblue
    exact hs
  | true =>
    obtain ⟨n, R, hs, _⟩ := hblue
    exact hs

theorem body_handoff {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (D : BodyDecision) (T : State)
    {k : ℕ} (A : BodyResponses.Setup D.stem k)
    (hlarge : ∀ x ∈ BodyResponses.newWord A.position, pairBound (pair right (.body D) T) < x)
    (hblue : Blue H B o right (.leaf (applyBody D A)) T) :
    OtherBlue H B o right (.leaf (applyBody D A)) T := by
  cases right with
  | false =>
    exact handoff_after_left hH B o (.body D, T) (bodyResponse D k _)
      (bodyMember D _ A hlarge) (applyBody D A) (bodyMember_result D _ A hlarge) hblue
  | true =>
    exact handoff_after_right hH B o (T, .body D) (bodyResponse D k _)
      (bodyMember D _ A hlarge) (applyBody D A) (bodyMember_result D _ A hlarge) hblue

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
  lastRoot : P.roots = []
  exactSlots : ExactSlots.Exact (.leaf P)

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : SameBody P Q)
    (hQ : ExactSlots.Exact (.leaf Q))
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  rootLabel := Z.rootLabel
  rootIncreasing := Z.rootIncreasing
  rootBelow := by rw [hsame.2.1]; exact Z.rootBelow
  targetStem := by
    rw [Z.targetStem]
    congr 1
    exact hsame.2.1.symm
  size := Z.size
  reserve :=
    { label := Z.reserve.label, card := Z.reserve.card, increasing := Z.reserve.increasing
      first := by rw [hsame.2.2.2.1]; exact Z.reserve.first
      below := by rw [hsame.2.2.1]; exact Z.reserve.below
      shared := by intro x; rw [hsame.2.2.2.1]; exact Z.reserve.shared x }
  before := by
    change ∀ x ∈ Q.position.stem.decorated, ∀ y ∈ Z.reserve.label, x < y
    rw [hsame.2.1]
    exact Z.before
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  tailFresh := htail
  reserveFresh := Z.reserveFresh
  certificate := Z.certificate
  lastRoot := hsame.1
  exactSlots := hQ

private theorem marker_le_tail (P : Position) {x : ℕ} (hx : x ∈ P.size :: P.entries) :
    P.size ≤ x := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · have hinc := (List.pairwise_append.mp (List.pairwise_append.mp P.increasing).2.1).2.1
    exact ((List.pairwise_cons.mp hinc).1 x hx).le

theorem carry_left_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (S U : State)
    (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff (.leaf P, S) (.leaf Q, U)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.rootLabel = Z.rootLabel ∧ W.reserve.label = Z.reserve.label := by
  have hsame := run_last_body_left P Q S U Z.lastRoot hrun
  have hQ := ExactSlots.run_exact_left hrun Z.exactSlots
  obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
  have htailEq : Q.position.size :: Q.position.entries =
      (P.position.size :: P.position.entries) ++ v := by
    simp only [State.ordinary, Position.ordinary, hsame.2.1, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x := by
    intro x hx
    have hb : Z.bound < Q.position.size := by
      rw [hsame.2.2.1]
      exact (Z.tailFresh _ (List.mem_cons_self ..)).2
    refine ⟨?_, hb.trans_le (marker_le_tail Q.position hx)⟩
    rw [htailEq] at hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ (Z.tailFresh x hx).1)
      (fun hx ↦ hKH (hvK x hx))
  exact ⟨Z.move Q hsame hQ htail, rfl, rfl, rfl⟩

theorem carry_left {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (S U : State)
    (_hS : ExactSlots.Exact S) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff (.leaf P, S) (.leaf Q, U)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.rootLabel = Z.rootLabel ∧ W.reserve.label = Z.reserve.label :=
  carry_left_of_run Z Q S U hKH payoff hrun

theorem carry_right_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (S U : State)
    (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff (S, .leaf P) (U, .leaf Q)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.rootLabel = Z.rootLabel ∧ W.reserve.label = Z.reserve.label := by
  have hsame := run_last_body_right P Q S U Z.lastRoot hrun
  have hQ := ExactSlots.run_exact_right hrun Z.exactSlots
  obtain ⟨w, v, _, hv, _, hvK⟩ := CompletionReplay.run_supported_suffixes hrun
  have htailEq : Q.position.size :: Q.position.entries =
      (P.position.size :: P.position.entries) ++ v := by
    simp only [State.ordinary, Position.ordinary, hsame.2.1, List.append_assoc] at hv
    exact List.append_cancel_left hv
  have htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x := by
    intro x hx
    have hb : Z.bound < Q.position.size := by
      rw [hsame.2.2.1]
      exact (Z.tailFresh _ (List.mem_cons_self ..)).2
    refine ⟨?_, hb.trans_le (marker_le_tail Q.position hx)⟩
    rw [htailEq] at hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ (Z.tailFresh x hx).1)
      (fun hx ↦ hKH (hvK x hx))
  exact ⟨Z.move Q hsame hQ htail, rfl, rfl, rfl⟩

theorem carry_right {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (S U : State)
    (_hS : ExactSlots.Exact S) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff (S, .leaf P) (U, .leaf Q)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.rootLabel = Z.rootLabel ∧ W.reserve.label = Z.reserve.label :=
  carry_right_of_run Z Q S U hKH payoff hrun

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
      Blue H B o right (.leaf (applyBody E (Z.setup hL))) T ∧
      OtherBlue H B o right (.leaf (applyBody E (Z.setup hL))) T := by
  have hfresh : ∀ x ∈ BodyResponses.newWord (Z.setup hL).position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    exact (List.mem_append.mp hx).elim (Z.reserveFresh x) (Z.tailFresh x)
  have hb := Z.certificate (Z.setup hL) (fun x hx ↦ (hfresh x hx).1)
    (fun x hx ↦ (hfresh x hx).2)
  refine ⟨Z.setup_ordinary hL, hb, ?_⟩
  exact body_handoff hH B o right E T (Z.setup hL)
    (fun x hx ↦ Z.pairBound_le.trans_lt (hfresh x hx).2) hb

noncomputable def guard (K : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (D : BodyDecision) (T : State) (k : ℕ) : ℕ :=
  if right then ConservativeRuns.rightGuard K (GraphPayoff.payoff B o) (pair right (.body D) T) k
  else ConservativeRuns.leftGuard K (GraphPayoff.payoff B o) (pair right (.body D) T) k

theorem body_step {K : Set ℕ} (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (D : BodyDecision) (T : State) {k : ℕ} (A : BodyResponses.Setup D.stem k)
    (hallowed : allowedSide (pair right (.body D) T) right = true)
    (hK : ∀ x ∈ BodyResponses.newWord A.position, x ∈ K)
    (hc : ∀ x ∈ BodyResponses.newWord A.position, pairBound (pair right (.body D) T) < x)
    (hg : ∀ x ∈ BodyResponses.newWord A.position, guard K B o right D T k < x) :
    ConservativeRuns.Step K (GraphPayoff.payoff B o)
      (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) := by
  cases right with
  | false =>
    let c := pairBound (.body D, T)
    let a := bodyMember D c A hc
    have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hK x (List.mem_toFinset.mp hx)
    have hag : ∀ x ∈ a.1,
        ConservativeRuns.leftGuard K (GraphPayoff.payoff B o) (.body D, T) k < x :=
      fun x hx ↦ hg x (List.mem_toFinset.mp hx)
    have hs := ConservativeRuns.Step.left (.body D, T) k (bodyResponse D k c)
      hallowed rfl a haK hag
    have hresult : (bodyResponse D k c).result a = .leaf (applyBody D A) :=
      bodyMember_result D c A hc
    rw [hresult] at hs
    exact hs
  | true =>
    let c := pairBound (T, .body D)
    let a := bodyMember D c A hc
    have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hK x (List.mem_toFinset.mp hx)
    have hag : ∀ x ∈ a.1,
        ConservativeRuns.rightGuard K (GraphPayoff.payoff B o) (T, .body D) k < x :=
      fun x hx ↦ hg x (List.mem_toFinset.mp hx)
    have hs := ConservativeRuns.Step.right (T, .body D) k (bodyResponse D k c)
      hallowed rfl a haK hag
    have hresult : (bodyResponse D k c).result a = .leaf (applyBody D A) :=
      bodyMember_result D c A hc
    rw [hresult] at hs
    exact hs

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (C : List ℕ) (hC : C.Pairwise (· < ·)) (hCr : ∀ x ∈ C, x < D.stem.root)
    (hE : E.stem = LabelOverlays.plainStem D.stem C hC hCr)
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
  obtain ⟨A, R, hA, hreserve, hbefore⟩ := body_reserved D.stem D.room hK M k₁ k₂
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
      size := k₂, reserve := R
      before := by
        change ∀ x ∈ A.position.stem.decorated, ∀ y ∈ R.label, x < y
        rw [A.stem_eq]
        exact hbefore
      bound := L
      pairBound_le := le_max_right _ _
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

theorem respond_body_on {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (D : BodyDecision) (T : State)
    (hblue : CommandBlue H B o right (.body D) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) ∧
      Blue H B o right (.leaf (applyBody D A)) T ∧
      OtherBlue H B o right (.leaf (applyBody D A)) T ∧
      ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  obtain ⟨k, b, hb⟩ := body_setups B o right D T hblue
  let c := pairBound (pair right (.body D) T)
  let g := guard K B o right D T k
  let M := max b (max c (max g d))
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem k D.room hK M
  have hbM : b ≤ M := by dsimp [M]; omega
  have hcM : c ≤ M := by dsimp [M]; omega
  have hgM : g ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ hcM.trans_lt (hA x hx).2
  have hnext := hb A (fun x hx ↦ hKH (hA x hx).1)
    (fun x hx ↦ hbM.trans_lt (hA x hx).2)
  refine ⟨k, A, body_step B o right D T A (command_allowed B o right D T hblue)
    (fun x hx ↦ (hA x hx).1) hAc (fun x hx ↦ hgM.trans_lt (hA x hx).2), hnext,
    body_handoff (hK.mono hKH) B o right D T A hAc hnext, ?_⟩
  exact fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩

theorem respond_body {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (D : BodyDecision) (T : State)
    (hblue : CommandBlue H B o right (.body D) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) ∧
      Blue H B o right (.leaf (applyBody D A)) T ∧
      OtherBlue H B o right (.leaf (applyBody D A)) T ∧
      ∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ d < x :=
  respond_body_on hH (Set.Subset.rfl) B o right D T hblue d

theorem respond_on {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (S T : State)
    (hblue : CommandBlue H B o right S T) (d : ℕ) :
    ∃ R : Response S (pairBound (pair right S T)), ∃ a : R.family.members,
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right S T) (pair right (R.result a) T) ∧
      Blue H B o right (R.result a) T ∧ ∀ x ∈ a.1, x ∈ K ∧ d < x := by
  cases right with
  | false =>
    obtain ⟨n, R, hs, hR, b, hb⟩ := hblue
    let g := ConservativeRuns.leftGuard K (GraphPayoff.payoff B o) (S, T) n
    obtain ⟨a, haK, ha⟩ := R.family.conservative_exists hK (max b (max g d))
    have hbound : ∀ x ∈ a.1, b < x := fun x hx ↦ (le_max_left _ _).trans_lt (ha x hx)
    have hguard : ∀ x ∈ a.1, g < x :=
      fun x hx ↦ ((le_max_left g d).trans (le_max_right b _)).trans_lt (ha x hx)
    exact ⟨R, a, ConservativeRuns.Step.left (S, T) n R hs hR a haK hguard,
      hb a (haK.trans hKH) hbound,
      fun x hx ↦ ⟨haK hx, ((le_max_right g d).trans (le_max_right b _)).trans_lt (ha x hx)⟩⟩
  | true =>
    obtain ⟨n, R, hs, hR, b, hb⟩ := hblue
    let g := ConservativeRuns.rightGuard K (GraphPayoff.payoff B o) (T, S) n
    obtain ⟨a, haK, ha⟩ := R.family.conservative_exists hK (max b (max g d))
    have hbound : ∀ x ∈ a.1, b < x := fun x hx ↦ (le_max_left _ _).trans_lt (ha x hx)
    have hguard : ∀ x ∈ a.1, g < x :=
      fun x hx ↦ ((le_max_left g d).trans (le_max_right b _)).trans_lt (ha x hx)
    exact ⟨R, a, ConservativeRuns.Step.right (T, S) n R hs hR a haK hguard,
      hb a (haK.trans hKH) hbound,
      fun x hx ↦ ⟨haK hx, ((le_max_right g d).trans (le_max_right b _)).trans_lt (ha x hx)⟩⟩

theorem respond {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (S T : State)
    (hblue : CommandBlue H B o right S T) (d : ℕ) :
    ∃ R : Response S (pairBound (pair right S T)), ∃ a : R.family.members,
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (pair right S T) (pair right (R.result a) T) ∧
      Blue H B o right (R.result a) T ∧ ∀ x ∈ a.1, x ∈ H ∧ d < x :=
  respond_on hH (Set.Subset.rfl) B o right S T hblue d

end Erdos118.PreparedRelays
