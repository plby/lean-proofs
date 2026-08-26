import ErdosProblems.Erdos118.StrictTwoRootRequests
import ErdosProblems.Erdos118.StrictReservedRightOpening
import ErdosProblems.Erdos118.SplicedRightPreparation

/-! The second reserved critical opening, with all three graph
certificates kept distinct and the old left next-body support retained. -/

namespace Erdos118.StrictSecondOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

structure Opening {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} (J : StrictTwoRootRequests.Requests O value) where
  anchorRank : ℕ
  anchorPositive : 2 ≤ anchorRank
  anchorBounded : anchorRank ≤ J.upper.size + 1
  rootSetup : RootResponses.Setup J.inserted.size
  prepared : StrictLocalization.Prepared J.inserted.alphabet J.inserted.graph
    J.inserted.left rootSetup J.inserted.rank (max J.upper.bound J.oldBound)
  reserve : SplicedRootReserve.Reserve J.alphabet J.upper.bound J.inserted.size J.upper.size
    J.inserted.rank anchorRank prepared.body.stem
  target : RankedRightPreparation.Target J.upper prepared.body (RootReplayReserve.ofSpliced reserve)
  opening : StrictReservedRightOpening.Opening prepared target J.oldBound
  root : opening.checkpoint.left.position.stem.root = O.opening.checkpoint.left.position.stem.root
  rootLabel : opening.checkpoint.left.position.stem.rootLabel = O.buffer.label
  roots : opening.checkpoint.left.roots = [J.oldRoot]
  leaves : opening.checkpoint.left.leaves = []
  extension : ∃ w : List ℕ,
    opening.checkpoint.left.position.ordinary = O.opening.checkpoint.left.position.ordinary ++ w ∧
    ∀ x ∈ w, x ∈ O.prepared.alphabet ∧ J.oldBound < x

theorem at_rank {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} (J : StrictTwoRootRequests.Requests O value)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) (r : ℕ) (hr : 2 ≤ r) (hrl : r ≤ J.upper.size + 1) :
    ∃ W : Opening J, W.anchorRank = r := by
  have hleft : 1 < J.inserted.left.position.stem.rootLabel.length := by
    rw [J.inserted.rootLabel, O.buffer.card]
    have h := O.positive
    omega
  let b := max J.upper.bound (max J.inserted.bound J.oldBound)
  have hUb : J.upper.bound ≤ b := le_max_left _ _
  have hIb : J.inserted.bound ≤ b := by dsimp [b]; omega
  obtain ⟨A, R, hA⟩ := SplicedRootReserve.root_reserved J.inserted.infinite b
    J.inserted.size J.upper.size J.inserted.rank r J.inserted.positive J.inserted.bounded hr hrl
  let RI := R.rebase J.inserted.subset hUb
  have hbA := J.inserted.certificate A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ hIb.trans_lt (hA x hx).2)
  have hfA : ∀ x ∈ A.stem.ordinary, x ∈ J.alphabet ∧ J.upper.bound < x := by
    intro x hx
    have hf := hA x (A.stem.ordinary_sublist.subset hx)
    exact ⟨J.inserted.subset hf.1, hUb.trans_lt hf.2⟩
  have hall : ∀ S T, GraphPayoff.payoff J.inserted.graph .inside S T = true →
      beforeLast S < beforeLast T := fun S T hp ↦ hstrict S T
    (LastMarkerRefinement.payoff_true_mono J.inserted.subgraph .inside S T hp)
  obtain ⟨Z⟩ := StrictLocalization.at_root J.inserted.infinite J.inserted.graph
    J.inserted.triangleFree hall J.inserted.left J.inserted.exactSlots hleft
    J.inserted.size J.inserted.rank J.inserted.positive J.inserted.bounded.le
    (fun S T hp hS hT ↦ (J.inserted.exactRank S T hp hS hT).1)
    A hbA (max J.upper.bound J.oldBound)
  obtain ⟨RD, _, htarget⟩ := SplicedRightPreparation.at_localized J.inserted.subset
    (StrictTwoRootRequests.target O) J.upper Z RI (le_max_left _ _) hfA
  obtain ⟨T⟩ := htarget
  obtain ⟨W⟩ :=
    StrictReservedRightOpening.exists_opening J.inserted.subset Z T hleft hall J.oldBound
  have he₀ := (SkippedCuts.run_extensions Z.run).1
  have he₁ := (SkippedCuts.run_extensions W.sourceRun).1
  have he := he₀.trans he₁
  have hroot : W.checkpoint.left.position.stem.root =
      O.opening.checkpoint.left.position.stem.root :=
    ((List.cons_prefix_cons.mp he.ordinary).1.symm).trans J.inserted.root
  have hlabel : W.checkpoint.left.position.stem.rootLabel = O.buffer.label :=
    (Option.some.inj (he.labels.root _ rfl)).trans J.inserted.rootLabel
  obtain ⟨c, hc, hl⟩ := W.checkpoint.criticalLeft
  have heq : c = J.oldRoot := by
    have hcLast := ExactSlots.pending_next_last_root W.checkpoint.left W.checkpoint.leftExact hc
    have hOld := ExactSlots.pending_next_last_root O.opening.checkpoint.left
      O.opening.checkpoint.leftExact J.oldRootEq
    exact hcLast.symm.trans ((congrArg (fun l : List ℕ ↦ l.getLastD 0) hlabel).trans
      (O.buffer.sameLast.trans hOld))
  have hf : ∃ w : List ℕ,
      W.checkpoint.left.position.ordinary = O.opening.checkpoint.left.position.ordinary ++ w ∧
      ∀ x ∈ w, x ∈ O.prepared.alphabet ∧ J.oldBound < x := by
    obtain ⟨u, hu, huf⟩ := J.inserted.extension
    obtain ⟨v, t, hv, _, hvf, _⟩ := Z.fresh
    obtain ⟨w, z, hw, _, hwf, _⟩ := W.sourceFresh
    refine ⟨u ++ v ++ w, ?_, ?_⟩
    · change State.ordinary (.leaf W.checkpoint.left) = _
      rw [hw, hv]
      change (J.inserted.left.position.ordinary ++ v) ++ w = _
      simp only [hu, List.append_assoc]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact ⟨J.subset (huf x hx).1, (huf x hx).2⟩
        · exact ⟨J.subset (J.inserted.subset (hvf x hx).1),
            (le_max_right _ _).trans_lt (hvf x hx).2⟩
      · exact ⟨J.subset (J.inserted.subset (Z.subset (hwf x hx).1)), (hwf x hx).2⟩
  exact ⟨{
    anchorRank := r, anchorPositive := hr, anchorBounded := hrl
    rootSetup := A, prepared := Z, reserve := RD, target := T, opening := W
    root := hroot, rootLabel := hlabel, roots := hc.trans (congrArg List.singleton heq)
    leaves := hl, extension := hf }, rfl⟩

theorem exists_opening {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} (J : StrictTwoRootRequests.Requests O value)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) : Nonempty (Opening J) := by
  have hupper : 2 ≤ J.upper.size + 1 := by have h₁ := J.positive; have h₂ := J.bounded; omega
  obtain ⟨W, _⟩ := at_rank J hstrict (J.upper.size + 1) hupper le_rfl
  exact ⟨W⟩

theorem last_opening {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    (J : StrictTwoRootRequests.Requests O true)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) :
    ∃ W : Opening J, W.anchorRank = J.rank + 1 ∧ W.anchorRank < J.upper.size + 1 := by
  have hr : 2 ≤ J.rank + 1 := by have h := J.positive; omega
  obtain ⟨W, hW⟩ := at_rank J hstrict (J.rank + 1) hr (J.lastBound rfl).le
  exact ⟨W, hW, hW ▸ J.lastBound rfl⟩

theorem nonlast_opening {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    (J : StrictTwoRootRequests.Requests O false)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) (hr : 2 ≤ J.rank) :
    ∃ W : Opening J, W.anchorRank = J.rank ∧ W.anchorRank < J.upper.size + 1 := by
  obtain ⟨W, hW⟩ := at_rank J hstrict J.rank hr J.bounded.le
  exact ⟨W, hW, hW ▸ J.bounded⟩

end Erdos118.StrictSecondOpening
