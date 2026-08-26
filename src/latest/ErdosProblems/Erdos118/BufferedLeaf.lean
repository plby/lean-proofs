import ErdosProblems.Erdos118.CurrentBody
import ErdosProblems.Erdos118.JointMoves

/-!
A new play may supply a whole old selected-leaf response while staying in
its current body. The old bound is announced before the buffered prefix;
both actual histories keep the same guard alphabet. No third pair is inferred.
-/

namespace Erdos118.BufferedLeaf

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem current_body_replay {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (P : Pending) (X : State) (j : ℕ) (rest : List ℕ) (hP : P.leaves = j :: rest)
    (hcmd : CommandBlue H B o r (.leaf P) X) :
    ∃ b : ℕ, ∀ Q : Pending, ∀ Y : State, ∀ v₀ : List ℕ,
      Q.position.stem.ordinary = P.position.stem.ordinary →
      Q.position.size = P.position.size →
      Q.position.entries = P.position.entries ++ v₀ →
      ExactSlots.Exact (.leaf Q) → Q.position.label.getLastD 0 = j →
      (∀ x ∈ v₀, x ∈ K ∧ b < x) → Blue H B o s (.leaf Q) Y →
      (Q.leaves = [] → OtherBlue H B o s (.leaf Q) Y) →
      ∃ P' Q' : Pending, ∃ Y' : State,
        P'.roots = P.roots ∧ P'.leaves = rest ∧ CurrentBody.SameBody Q Q' ∧ Q'.leaves = [] ∧
        P'.position.ordinary = Q'.position.ordinary ∧
        ConservativeRuns.Step K (GraphPayoff.payoff B o)
          (pair r (.leaf P) X) (pair r (.leaf P') X) ∧
        ConservativeRuns.Run K (GraphPayoff.payoff B o)
          (pair s (.leaf Q) Y) (pair s (.leaf Q') Y') ∧
        Blue H B o r (.leaf P') X ∧ Blue H B o s (.leaf Q') Y' ∧
        OtherBlue H B o r (.leaf P') X ∧ OtherBlue H B o s (.leaf Q') Y' ∧
        ∃ v : List ℕ, P'.position.ordinary = P.position.ordinary ++ v ∧
          ∀ x ∈ v, x ∈ K ∧ b < x := by
  obtain ⟨b, hb⟩ := JointMoves.leaf_bound hK hKH B o r P X j rest hP hcmd
  refine ⟨b, ?_⟩
  intro Q Y v₀ hstem hsize hentries hQexact hlast hv₀ hblue hready
  obtain ⟨Q', Y', hsame, hQL, hrun, hbQ, hhQ, v₁, _, hword, _, hv₁, _⟩ :=
    CurrentBody.last_on hK hKH B o s Q Y b hblue hready
  have hQ'exact : ExactSlots.Exact (.leaf Q') := by
    cases s with
    | false => exact ExactSlots.run_exact_left hrun hQexact
    | true => exact ExactSlots.run_exact_right hrun hQexact
  have hQ'len : Q'.position.entries.length = j := by
    have he := ExactSlots.pending_last_leaf Q' hQ'exact hQL
    rw [hsame.label, hlast] at he
    exact he.symm
  have hQ'stem : Q'.position.stem.ordinary = P.position.stem.ordinary :=
    (congrArg Stem.ordinary hsame.stem).trans hstem
  have hQ'size : Q'.position.size = P.position.size := hsame.size.trans hsize
  have hQword : Q.position.ordinary = P.position.ordinary ++ v₀ := by
    simp only [Position.ordinary, hstem, hsize, hentries, List.cons_append, List.append_assoc]
  have hQ'word : Q'.position.ordinary = P.position.ordinary ++ (v₀ ++ v₁) := by
    rw [hword, hQword, List.append_assoc]
  have hQ'entries : Q'.position.entries = P.position.entries ++ (v₀ ++ v₁) := by
    have he : P.position.size :: Q'.position.entries =
        P.position.size :: (P.position.entries ++ (v₀ ++ v₁)) := by
      apply List.append_cancel_left (as := P.position.stem.ordinary)
      simpa only [Position.ordinary, hQ'stem, hQ'size, List.append_assoc, List.cons_append]
        using hQ'word
    exact (List.cons.inj he).2
  have hv : ∀ x ∈ v₀ ++ v₁, x ∈ K ∧ b < x :=
    fun x hx ↦ (List.mem_append.mp hx).elim (hv₀ x) (hv₁ x)
  obtain ⟨A, hAv, hAword⟩ := LeafReplay.setup_of_position P.position Q'.position j
    hQ'stem hQ'size hQ'len (v₀ ++ v₁) hQ'entries
  obtain ⟨hstep, hbP, hhP⟩ := hb A (by rw [hAv]; exact hv)
  let P' := LeafResponses.toPending P j rest hP A
  have hslot := P.leafSlots.bounded j (hP ▸ List.mem_cons_self ..)
  have hP'word : P'.position.ordinary = P.position.ordinary ++ A.newWord :=
    LeafResponses.position_ordinary A hslot.1 hslot.2.1
  exact ⟨P', Q', Y', rfl, rfl, hsame, hQL, hP'word.trans hAword, hstep, hrun,
    hbP, hbQ, hhP, hhQ, v₀ ++ v₁, by rw [hP'word, hAv], hv⟩

end Erdos118.BufferedLeaf
