import ErdosProblems.Erdos118.SelectedLeafResponses
import ErdosProblems.Erdos118.NextSelectedLeaf
import ErdosProblems.Erdos118.BoundaryRelays

/-!
Saved actual selected-leaf certificates can be fired by a literal source
extension. The result retains the target decorations and exact slots;
the conservative step, blue outcome, and handoff use the same response.
-/

namespace Erdos118.SelectedLeafReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays

structure Certificate (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (P : Pending) (T : State) (j : ℕ) (rest : List ℕ)
    (hP : P.leaves = j :: rest) where
  bound : ℕ
  submit : ∀ A : LeafResponses.Setup P.position j,
    (∀ x ∈ A.newWord, x ∈ H) → (∀ x ∈ A.newWord, bound < x) →
    ConservativeRuns.Step H (GraphPayoff.payoff B o)
      (pair right (.leaf P) T)
      (pair right (.leaf (LeafResponses.toPending P j rest hP A)) T) ∧
    Blue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T ∧
    OtherBlue H B o right (.leaf (LeafResponses.toPending P j rest hP A)) T

theorem exists_certificate {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P : Pending) (T : State)
    (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hblue : CommandBlue H B o right (.leaf P) T) :
    Nonempty (Certificate H B o right P T j rest hP) := by
  obtain ⟨b, hb⟩ := SelectedLeafResponses.certificate_on hH Set.Subset.rfl
    B o right P T j rest hP hblue
  exact ⟨⟨b, hb⟩⟩

structure Replay {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {P : Pending} {T : State} {j : ℕ} {rest : List ℕ}
    {hP : P.leaves = j :: rest} (_C : Certificate H B o right P T j rest hP)
    (Q : Position) where
  target : Pending
  ordinary : target.position.ordinary = Q.ordinary
  stem : target.position.stem = P.position.stem
  marker : target.position.size = P.position.size
  entries : target.position.entries = Q.entries
  label : target.position.label = P.position.label
  roots : target.roots = P.roots
  leaves : target.leaves = rest
  exactSlots : ExactSlots.Exact (.leaf target)
  step : ConservativeRuns.Step H (GraphPayoff.payoff B o)
    (pair right (.leaf P) T) (pair right (.leaf target) T)
  blue : Blue H B o right (.leaf target) T
  handoff : OtherBlue H B o right (.leaf target) T

theorem Certificate.fire {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {P : Pending} {T : State} {j : ℕ} {rest : List ℕ}
    {hP : P.leaves = j :: rest} (C : Certificate H B o right P T j rest hP)
    (hExact : ExactSlots.Exact (.leaf P)) (Q : Position)
    (hstem : Q.stem.ordinary = P.position.stem.ordinary) (hsize : Q.size = P.position.size)
    (hlen : Q.entries.length = j) (v : List ℕ)
    (hentries : Q.entries = P.position.entries ++ v)
    (hH : ∀ x ∈ v, x ∈ H) (hb : ∀ x ∈ v, C.bound < x) : Nonempty (Replay C Q) := by
  obtain ⟨A, hAv, hAQ⟩ := LeafReplay.setup_of_position P.position Q j hstem hsize hlen v hentries
  obtain ⟨hs, hblue, hh⟩ := C.submit A
    (fun x hx ↦ hH x (hAv ▸ hx)) (fun x hx ↦ hb x (hAv ▸ hx))
  have hslot := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  refine ⟨{ target := LeafResponses.toPending P j rest hP A
            ordinary := ?_, stem := rfl, marker := rfl, entries := ?_
            label := rfl, roots := rfl, leaves := rfl
            exactSlots := ExactSlots.step_exact (DecisionStates.Step.leaf P j rest hP A) hExact
            step := hs, blue := hblue, handoff := hh }⟩
  · exact (LeafResponses.position_ordinary A hslot.1 hslot.2.1).trans hAQ
  · change P.position.entries ++ A.newWord = Q.entries
    rw [hAv]
    exact hentries.symm

theorem Certificate.fire_last {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {right : Bool} {P : Pending} {T : State}
    (Q R : Pending) {rest : List ℕ}
    {hP : P.leaves = Q.position.label.getLastD 0 :: rest}
    (C : Certificate H B o right P T (Q.position.label.getLastD 0) rest hP)
    (hExact : ExactSlots.Exact (.leaf P))
    (hord : P.position.ordinary = Q.position.ordinary)
    (hlen : P.position.entries.length = Q.position.entries.length)
    (hbody : SameBody Q R) (hR : ExactSlots.Exact (.leaf R)) (hRL : R.leaves = [])
    (v : List ℕ) (hRv : R.position.ordinary = Q.position.ordinary ++ v)
    (hH : ∀ x ∈ v, x ∈ H) (hb : ∀ x ∈ v, C.bound < x) :
    Nonempty (Replay C R.position) := by
  obtain ⟨hs, hm, he⟩ := NextSelectedLeaf.ordinary_parts Q.position P.position hord hlen
  have hstem : R.position.stem.ordinary = P.position.stem.ordinary := by
    rw [hbody.2.1]
    exact hs.symm
  have hmarker : R.position.size = P.position.size := hbody.2.2.1.trans hm.symm
  have hcount : R.position.entries.length = Q.position.label.getLastD 0 := by
    rw [← ExactSlots.pending_last_leaf R hR hRL, hbody.2.2.2.1]
  have hentries : R.position.entries = P.position.entries ++ v := by
    simp only [Position.ordinary, hbody.2.1, hbody.2.2.1, List.append_assoc] at hRv
    have ht := List.append_cancel_left hRv
    have ht' : Q.position.size :: R.position.entries = Q.position.size ::
        (Q.position.entries ++ v) := by simpa only [List.cons_append] using ht
    rw [he]
    exact (List.cons.inj ht').2
  exact C.fire hExact R.position hstem hmarker hcount v hentries hH hb

theorem Certificate.buffer {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {P : Pending} {T : State} {j : ℕ} {rest : List ℕ}
    {hP : P.leaves = j :: rest} (C : Certificate H B o right P T j rest hP)
    (hH : H.Infinite) (hExact : ExactSlots.Exact (.leaf P)) (Q : Position)
    (hstem : Q.stem.ordinary = P.position.stem.ordinary) (hsize : Q.size = P.position.size)
    (v : List ℕ) (hentries : Q.entries = P.position.entries ++ v)
    (hv : ∀ x ∈ v, x ∈ H ∧ C.bound < x) (hcount : Q.entries.length < j) (d : ℕ) :
    ∃ Z : Position, ∃ R : Replay C Z, ∃ w : List ℕ,
      R.target.position.ordinary = Q.ordinary ++ w ∧
      R.target.position.entries = Q.entries ++ w ∧
      (∀ x ∈ w, x ∈ H ∧ d < x) := by
  have hslot := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  have hsmall : j < Q.size := hsize ▸ hslot.2.1
  obtain ⟨A, hA⟩ := LeafResponses.setup_above Q j hH (max C.bound d)
  let Z := LeafResponses.position A hcount hsmall
  have hZstem : Z.stem.ordinary = P.position.stem.ordinary := hstem
  have hZsize : Z.size = P.position.size := hsize
  have hZcount : Z.entries.length = j := LeafResponses.position_length A hcount hsmall
  have hZentries : Z.entries = P.position.entries ++ (v ++ A.newWord) := by
    change Q.entries ++ A.newWord = _
    rw [hentries, List.append_assoc]
  have hfull : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ C.bound < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hv x)
      (fun hx ↦ ⟨(hA x hx).1, (le_max_left _ _).trans_lt (hA x hx).2⟩)
  obtain ⟨R⟩ := C.fire hExact Z hZstem hZsize hZcount (v ++ A.newWord) hZentries
    (fun x hx ↦ (hfull x hx).1) (fun x hx ↦ (hfull x hx).2)
  exact ⟨Z, R, A.newWord, R.ordinary.trans (LeafResponses.position_ordinary A hcount hsmall),
    R.entries, fun x hx ↦ ⟨(hA x hx).1, (le_max_right _ _).trans_lt (hA x hx).2⟩⟩

end Erdos118.SelectedLeafReplay
