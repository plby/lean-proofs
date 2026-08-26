import ErdosProblems.Erdos118.BodyReplay
import ErdosProblems.Erdos118.LateMarkerCritical

/-!
A positive target body certificate reserved before the source marker can
be fired at any nonlast selected source leaf. The target retains its exact
stem decorations; its label starts with the actual current entry count,
followed by the saved source maximum and the remaining reserved entries.
-/

namespace Erdos118.DeferredBodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  ordinary : E.stem.ordinary = P.position.stem.ordinary
  size : ℕ
  positive : 0 < size
  reserve : Reserve P.position.label P.position.size (size - 1)
  bound : ℕ
  pairBound_le : pairBound (pair right (.body E) T) ≤ bound
  labelFresh : ∀ x ∈ P.position.label, x ∈ H ∧ bound < x
  tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ bound < x
  reserveFresh : ∀ x ∈ reserve.label, x ∈ H ∧ bound < x
  certificate : ∀ A : BodyResponses.Setup E.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    Blue H B o right (.leaf (applyBody E A)) T
  lastRoot : P.roots = []
  exactSlots : ExactSlots.Exact (.leaf P)

theorem current_lt_last (P : Pending) (hne : P.leaves ≠ []) :
    P.position.entries.length < P.position.label.getLastD 0 := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil P.leaves hne
  have hslot := P.leafSlots.bounded j hj
  have hlabelne := List.ne_nil_of_mem P.leafSelected
  have hle := (P.position.label_pairwise.imp Nat.le_of_lt).rel_getLast hslot.2.2
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hlabelne]
  exact hslot.1.trans_le hle

def Prepared.label {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : List ℕ := P.position.entries.length :: Z.reserve.label

theorem Prepared.label_length {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Z.label.length = Z.size + 1 := by
  simp only [Prepared.label, List.length_cons, Z.reserve.card]
  have h := Z.positive
  omega

theorem Prepared.label_increasing {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) : Z.label.Pairwise (· < ·) := by
  refine List.pairwise_cons.mpr ⟨?_, Z.reserve.increasing⟩
  intro x hx
  have hle : Z.reserve.label.headD 0 ≤ x := by
    have h := (Z.reserve.increasing.imp Nat.le_of_lt).rel_head hx
    cases hs : Z.reserve.label with
    | nil => simp [hs] at hx
    | cons a xs => simpa only [hs, List.head_cons, List.headD_cons] using h
  rw [Z.reserve.first] at hle
  exact (current_lt_last P hne).trans_le hle

theorem Prepared.label_below {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : ∀ x ∈ Z.label, x < P.position.size := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact P.position.unfinished
  · exact Z.reserve.below x hx

theorem Prepared.label_fresh {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : ∀ x ∈ Z.label, x ∈ H ∧ Z.bound < x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Z.labelFresh _ P.leafSelected
  · exact Z.reserveFresh x hx

theorem Prepared.second_index {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Z.label.getD 1 0 = P.position.label.getLastD 0 := by
  change Z.reserve.label.getD 0 0 = _
  have he : Z.reserve.label.getD 0 0 = Z.reserve.label.headD 0 := by
    cases Z.reserve.label <;> rfl
  exact he.trans Z.reserve.first

theorem Prepared.next_index {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) :
    P.position.entries.length < P.position.label.getLastD 0 ∧
      P.position.label.getLastD 0 ∈ Z.label ∧
      ∀ j ∈ Z.label, P.position.entries.length < j → P.position.label.getLastD 0 ≤ j := by
  have hRne : Z.reserve.label ≠ [] := by
    intro he
    have h := Z.reserve.card
    simp [he] at h
  obtain ⟨r, rs, hR⟩ := List.exists_cons_of_ne_nil hRne
  have hr : r = P.position.label.getLastD 0 := by
    simpa only [hR, List.headD_cons] using Z.reserve.first
  refine ⟨current_lt_last P hne, ?_, ?_⟩
  · change _ ∈ P.position.entries.length :: Z.reserve.label
    rw [hR, ← hr]
    simp
  · intro j hj hlt
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (Nat.lt_irrefl _ hlt).elim
    · rw [hR] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hr.ge
      · have hi : (r :: rs).Pairwise (· < ·) := hR ▸ Z.reserve.increasing
        exact hr ▸ ((List.pairwise_cons.mp hi).1 j hj).le

private theorem target_before {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) :
    ∀ x ∈ E.stem.decorated, ∀ y ∈ Z.label, x < y := by
  intro x hx y hy
  have hxb : x ≤ pairBound (pair right (.body E) T) := by
    cases right with
    | false => exact pairBound_left (.body E, T) hx
    | true => exact pairBound_right (T, .body E) hx
  exact (hxb.trans Z.pairBound_le).trans_lt (Z.label_fresh y hy).2

private def position {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) : Position where
  stem := E.stem
  size := P.position.size
  label := Z.label
  entries := P.position.entries
  room := E.room
  started := P.position.started
  unfinished := P.position.unfinished
  increasing := by
    have htail :=
      (List.pairwise_append.mp (List.pairwise_append.mp P.position.increasing).2.1).2.1
    have hfirst : P.position.entries.length ∈ Z.label := List.mem_cons_self ..
    have hbefore := target_before Z
    have hmarker : ∀ x ∈ E.stem.decorated, x < P.position.size :=
      fun x hx ↦ (hbefore x hx _ hfirst).trans P.position.unfinished
    have hnew : (Z.label ++ P.position.size :: P.position.entries).Pairwise (· < ·) := by
      refine List.pairwise_append.mpr ⟨Z.label_increasing hne, htail, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Z.label_below x hx
      · exact (Z.label_below x hx).trans ((List.pairwise_cons.mp htail).1 y hy)
    refine List.pairwise_append.mpr ⟨E.stem.increasing, hnew, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hbefore x hx y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hmarker x hx
      · exact (hmarker x hx).trans ((List.pairwise_cons.mp htail).1 y hy)

def Prepared.setup {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) : BodyResponses.Setup E.stem Z.size :=
  { position := position Z hne, stem_eq := rfl, label_length := Z.label_length
    entries_length := rfl }

theorem Prepared.setup_ordinary {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) :
    (Z.setup hne).position.ordinary = P.position.ordinary := by
  change E.stem.ordinary ++ P.position.size :: P.position.entries = _
  rw [Z.ordinary]
  rfl

theorem Prepared.setup_newWord {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) :
    BodyResponses.newWord (Z.setup hne).position =
      Z.label ++ P.position.size :: P.position.entries :=
  rfl

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) :
    (applyBody E (Z.setup hne)).position.ordinary = P.position.ordinary ∧
      Blue H B o right (.leaf (applyBody E (Z.setup hne))) T ∧
      OtherBlue H B o right (.leaf (applyBody E (Z.setup hne))) T := by
  have hf : ∀ x ∈ BodyResponses.newWord (Z.setup hne).position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    exact (List.mem_append.mp hx).elim (Z.label_fresh x) (Z.tailFresh x)
  have hb := Z.certificate (Z.setup hne) (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  exact ⟨Z.setup_ordinary hne, hb, body_handoff hH B o right E T (Z.setup hne)
    (fun x hx ↦ Z.pairBound_le.trans_lt (hf x hx).2) hb⟩

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : SameBody P Q)
    (hQ : ExactSlots.Exact (.leaf Q))
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  ordinary := Z.ordinary.trans (congrArg Stem.ordinary hsame.2.1).symm
  size := Z.size
  positive := Z.positive
  reserve :=
    { label := Z.reserve.label, card := Z.reserve.card, increasing := Z.reserve.increasing
      first := by rw [hsame.2.2.2.1]; exact Z.reserve.first
      below := by rw [hsame.2.2.1]; exact Z.reserve.below
      shared := by intro x; rw [hsame.2.2.2.1]; exact Z.reserve.shared x }
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  labelFresh := by rw [hsame.2.2.2.1]; exact Z.labelFresh
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
      W.bound = Z.bound ∧ W.reserve.label = Z.reserve.label ∧ W.size = Z.size := by
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
  exact ⟨Z.move Q hsame hQ htail, rfl, rfl, rfl⟩

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (hE : E.stem.ordinary = D.stem.ordinary)
    (hfirst : CommandBlue H B o originalRight (.body D) S)
    (l b₂ : ℕ) (hl : 0 < l)
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
  obtain ⟨k, b₁, hb₁⟩ := body_setups B o originalRight D S hfirst
  let c₁ := pairBound (pair originalRight (.body D) S)
  let c₂ := pairBound (pair targetRight (.body E) T)
  let L := max b₂ c₂
  let g := guard K B o originalRight D S k
  let M := max b₁ (max c₁ (max L (max g d)))
  have hb₁M : b₁ ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hLM : L ≤ M := by dsimp [M]; omega
  have hgM : g ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, R, hA, hreserve, _⟩ := body_reserved D.stem D.room hK M k (l - 1)
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
      size := l, positive := hl, reserve := R, bound := L, pairBound_le := le_max_right _ _
      labelFresh := by
        intro x hx
        have h := hA x (List.mem_append_left _ hx)
        exact ⟨hKH h.1, hLM.trans_lt h.2⟩
      tailFresh := by
        intro x hx
        have h := hA x (List.mem_append_right _ hx)
        exact ⟨hKH h.1, hLM.trans_lt h.2⟩
      reserveFresh := fun x hx ↦ ⟨hKH (hreserve x hx).1, hLM.trans_lt (hreserve x hx).2⟩
      certificate := fun A' hAH hAL ↦ hsecond A' hAH
        (fun x hx ↦ (le_max_left _ _).trans_lt (hAL x hx))
      lastRoot := hR
      exactSlots := ExactSlots.step_exact (DecisionStates.Step.body D A) hD }
  exact ⟨k, A, Z, rfl, hstep, hb, hh, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩⟩

end Erdos118.DeferredBodyReplay
