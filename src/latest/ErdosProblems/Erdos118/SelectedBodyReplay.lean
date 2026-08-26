import ErdosProblems.Erdos118.CurrentBodyReplay

/-! A full target body label saved before the source marker can be fired
at its prescribed selected source leaf, with arbitrary future roots. -/

namespace Erdos118.SelectedBodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  ordinary : E.stem.ordinary = P.position.stem.ordinary
  size : ℕ
  label : List ℕ
  card : label.length = size + 1
  increasing : label.Pairwise (· < ·)
  selected : label.headD 0 ∈ P.position.label
  below : ∀ x ∈ label, x < P.position.size
  bound : ℕ
  pairBound_le : pairBound (pair right (.body E) T) ≤ bound
  guard_le : guard H B o right E T size ≤ bound
  labelFresh : ∀ x ∈ label, x ∈ H ∧ bound < x
  tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ bound < x
  allowed : allowedSide (pair right (.body E) T) right = true
  certificate : ∀ A : BodyResponses.Setup E.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    Blue H B o right (.leaf (applyBody E A)) T

private theorem target_before {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) :
    ∀ x ∈ E.stem.decorated, ∀ y ∈ Z.label, x < y := by
  intro x hx y hy
  have hxb : x ≤ pairBound (pair right (.body E) T) := by
    cases right with
    | false => exact pairBound_left (.body E, T) hx
    | true => exact pairBound_right (T, .body E) hx
  exact (hxb.trans Z.pairBound_le).trans_lt (Z.labelFresh y hy).2

private def position {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : Position where
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
    have hne : Z.label ≠ [] := by intro he; have hc := Z.card; simp [he] at hc
    have hfirst : Z.label.headD 0 ∈ Z.label := first_mem hne
    have hbefore := target_before Z
    have hmarker : ∀ x ∈ E.stem.decorated, x < P.position.size :=
      fun x hx ↦ (hbefore x hx _ hfirst).trans (Z.below _ hfirst)
    have hnew : (Z.label ++ P.position.size :: P.position.entries).Pairwise (· < ·) := by
      refine List.pairwise_append.mpr ⟨Z.increasing, htail, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Z.below x hx
      · exact (Z.below x hx).trans ((List.pairwise_cons.mp htail).1 y hy)
    refine List.pairwise_append.mpr ⟨E.stem.increasing, hnew, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hbefore x hx y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hmarker x hx
      · exact (hmarker x hx).trans ((List.pairwise_cons.mp htail).1 y hy)

def Prepared.setup {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hi : P.position.entries.length = Z.label.headD 0) :
    BodyResponses.Setup E.stem Z.size :=
  { position := position Z, stem_eq := rfl, label_length := Z.card, entries_length := hi }

theorem Prepared.setup_ordinary {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hi : P.position.entries.length = Z.label.headD 0) :
    (Z.setup hi).position.ordinary = P.position.ordinary := by
  change E.stem.ordinary ++ P.position.size :: P.position.entries = _
  rw [Z.ordinary]
  rfl

theorem Prepared.setup_newWord {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hi : P.position.entries.length = Z.label.headD 0) :
    BodyResponses.newWord (Z.setup hi).position =
      Z.label ++ P.position.size :: P.position.entries := rfl

def Prepared.move {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (Q : Pending) (hsame : CurrentBody.SameBody P Q)
    (htail : ∀ x ∈ Q.position.size :: Q.position.entries, x ∈ H ∧ Z.bound < x) :
    Prepared H B o right E T Q where
  ordinary := Z.ordinary.trans (congrArg Stem.ordinary hsame.stem).symm
  size := Z.size
  label := Z.label
  card := Z.card
  increasing := Z.increasing
  selected := by rw [hsame.label]; exact Z.selected
  below := by rw [hsame.size]; exact Z.below
  bound := Z.bound
  pairBound_le := Z.pairBound_le
  guard_le := Z.guard_le
  labelFresh := Z.labelFresh
  tailFresh := htail
  allowed := Z.allowed
  certificate := Z.certificate

theorem carry_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (sourceRight : Bool) (Q : Pending) (S U : State)
    (hsame : CurrentBody.SameBody P Q) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff
      (pair sourceRight (.leaf P) S) (pair sourceRight (.leaf Q) U)) :
    ∃ W : Prepared H B o right E T Q,
      W.bound = Z.bound ∧ W.label = Z.label ∧ W.size = Z.size := by
  have hsuffix : ∃ w, Q.position.ordinary = P.position.ordinary ++ w ∧ ∀ x ∈ w, x ∈ K := by
    obtain ⟨w, z, hw, hz, hwK, hzK⟩ := CompletionReplay.run_supported_suffixes hrun
    cases sourceRight with
    | false => exact ⟨w, hw, hwK⟩
    | true => exact ⟨z, hz, hzK⟩
  obtain ⟨w, hw, hwK⟩ := hsuffix
  have htailEq : Q.position.size :: Q.position.entries =
      (P.position.size :: P.position.entries) ++ w := by
    simp only [Position.ordinary, hsame.stem, List.append_assoc] at hw
    exact List.append_cancel_left hw
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
      (fun hx ↦ hKH (hwK x hx))
  exact ⟨Z.move Q hsame htail, rfl, rfl, rfl⟩

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hi : P.position.entries.length = Z.label.headD 0) :
    (applyBody E (Z.setup hi)).position.ordinary = P.position.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (pair right (.body E) T) (pair right (.leaf (applyBody E (Z.setup hi))) T) ∧
      Blue H B o right (.leaf (applyBody E (Z.setup hi))) T ∧
      OtherBlue H B o right (.leaf (applyBody E (Z.setup hi))) T := by
  have hf : ∀ x ∈ BodyResponses.newWord (Z.setup hi).position, x ∈ H ∧ Z.bound < x := by
    rw [Z.setup_newWord]
    intro x hx
    exact (List.mem_append.mp hx).elim (Z.labelFresh x) (Z.tailFresh x)
  have hb := Z.certificate (Z.setup hi) (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  exact ⟨Z.setup_ordinary hi,
    body_step B o right E T (Z.setup hi) Z.allowed (fun x hx ↦ (hf x hx).1)
      (fun x hx ↦ Z.pairBound_le.trans_lt (hf x hx).2)
      (fun x hx ↦ Z.guard_le.trans_lt (hf x hx).2), hb,
    body_handoff hH B o right E T (Z.setup hi)
      (fun x hx ↦ Z.pairBound_le.trans_lt (hf x hx).2) hb⟩

end Erdos118.SelectedBodyReplay
