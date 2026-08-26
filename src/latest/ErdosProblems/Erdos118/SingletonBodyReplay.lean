import ErdosProblems.Erdos118.DeferredBodyReplay

/-!
A saved zero-parameter body certificate can be replayed with the singleton
current selected index. No positivity or invariance under relabeling is
assumed; the exact target decorations and original bound are retained.
-/

namespace Erdos118.SingletonBodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  ordinary : E.stem.ordinary = P.position.stem.ordinary
  bound : ℕ
  pairBound_le : pairBound (pair right (.body E) T) ≤ bound
  labelFresh : ∀ x ∈ P.position.label, x ∈ H ∧ bound < x
  tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ bound < x
  certificate : ∀ A : BodyResponses.Setup E.stem 0,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    Blue H B o right (.leaf (applyBody E A)) T
  lastRoot : P.roots = []
  exactSlots : ExactSlots.Exact (.leaf P)

private def position {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Position where
  stem := E.stem
  size := P.position.size
  label := [P.position.entries.length]
  entries := P.position.entries
  room := E.room
  started := P.position.started
  unfinished := P.position.unfinished
  increasing := by
    have htail :=
      (List.pairwise_append.mp (List.pairwise_append.mp P.position.increasing).2.1).2.1
    have hbefore : ∀ x ∈ E.stem.decorated, x < P.position.entries.length := by
      intro x hx
      have hxb : x ≤ pairBound (pair right (.body E) T) := by
        cases right with
        | false => exact pairBound_left (.body E, T) hx
        | true => exact pairBound_right (T, .body E) hx
      exact (hxb.trans Z.pairBound_le).trans_lt (Z.labelFresh _ P.leafSelected).2
    have hnew : (P.position.entries.length :: P.position.size :: P.position.entries).Pairwise
        (· < ·) := by
      refine List.pairwise_cons.mpr ⟨?_, htail⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact P.position.unfinished
      · exact P.position.unfinished.trans ((List.pairwise_cons.mp htail).1 y hy)
    refine List.pairwise_append.mpr ⟨E.stem.increasing, hnew, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hbefore x hx
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact (hbefore x hx).trans P.position.unfinished
      · exact ((hbefore x hx).trans P.position.unfinished).trans
          ((List.pairwise_cons.mp htail).1 y hy)

def Prepared.setup {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : BodyResponses.Setup E.stem 0 :=
  { position := position Z, stem_eq := rfl, label_length := rfl, entries_length := rfl }

theorem Prepared.setup_ordinary {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Z.setup.position.ordinary = P.position.ordinary := by
  change E.stem.ordinary ++ P.position.size :: P.position.entries = _
  rw [Z.ordinary]
  rfl

theorem Prepared.setup_newWord {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : BodyResponses.newWord Z.setup.position =
      P.position.entries.length :: P.position.size :: P.position.entries := rfl

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) :
    (applyBody E Z.setup).position.ordinary = P.position.ordinary ∧
      (applyBody E Z.setup).position.label = [P.position.entries.length] ∧
      (applyBody E Z.setup).leaves = [] ∧
      Blue H B o right (.leaf (applyBody E Z.setup)) T ∧
      OtherBlue H B o right (.leaf (applyBody E Z.setup)) T := by
  have hf : ∀ x ∈ BodyResponses.newWord Z.setup.position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Z.labelFresh _ P.leafSelected
    · exact Z.tailFresh x hx
  have hb := Z.certificate Z.setup (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  exact ⟨Z.setup_ordinary, rfl, rfl, hb, body_handoff hH B o right E T Z.setup
    (fun x hx ↦ Z.pairBound_le.trans_lt (hf x hx).2) hb⟩

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : SameBody P Q)
    (hQ : ExactSlots.Exact (.leaf Q))
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  ordinary := Z.ordinary.trans (congrArg Stem.ordinary hsame.2.1).symm
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  labelFresh := by rw [hsame.2.2.2.1]; exact Z.labelFresh
  tailFresh := htail
  certificate := Z.certificate
  lastRoot := hsame.1
  exactSlots := hQ

theorem carry_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (sourceRight : Bool) (Q : Pending) (S U : State)
    (hKH : K ⊆ H) (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff
      (pair sourceRight (.leaf P) S) (pair sourceRight (.leaf Q) U)) :
    ∃ W : Prepared H B o right E T Q, W.bound = Z.bound := by
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
  exact ⟨Z.move Q hsame hQ htail, rfl⟩

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (hE : E.stem.ordinary = D.stem.ordinary)
    (hfirst : CommandBlue H B o originalRight (.body D) S) (b₂ : ℕ)
    (hsecond : ∀ A : BodyResponses.Setup E.stem 0,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b₂ < x) →
      Blue H B o targetRight (.leaf (applyBody E A)) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ _Z : Prepared H B o targetRight E T (applyBody D A),
        ConservativeRuns.Step K (GraphPayoff.payoff B o)
          (pair originalRight (.body D) S) (pair originalRight (.leaf (applyBody D A)) S) ∧
        Blue H B o originalRight (.leaf (applyBody D A)) S ∧
        OtherBlue H B o originalRight (.leaf (applyBody D A)) S ∧
        ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  let L := max b₂ (pairBound (pair targetRight (.body E) T))
  obtain ⟨k, A, hs, hb, hh, hf⟩ :=
    respond_body_on hK hKH B o originalRight D S hfirst (max d L)
  have hfL : ∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ L < x :=
    fun x hx ↦ ⟨hKH (hf x hx).1, (le_max_right _ _).trans_lt (hf x hx).2⟩
  let Z : Prepared H B o targetRight E T (applyBody D A) :=
    { ordinary := hE.trans (congrArg Stem.ordinary A.stem_eq).symm
      bound := L, pairBound_le := le_max_right _ _
      labelFresh := fun x hx ↦ hfL x (List.mem_append_left _ hx)
      tailFresh := fun x hx ↦ hfL x (List.mem_append_right _ hx)
      certificate := fun A' hAH hAL ↦ hsecond A' hAH
        (fun x hx ↦ (le_max_left _ _).trans_lt (hAL x hx))
      lastRoot := hR
      exactSlots := ExactSlots.step_exact (DecisionStates.Step.body D A) hD }
  exact ⟨k, A, Z, hs, hb, hh,
    fun x hx ↦ ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩⟩

end Erdos118.SingletonBodyReplay
