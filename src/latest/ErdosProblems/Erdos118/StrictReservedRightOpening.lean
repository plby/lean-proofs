import ErdosProblems.Erdos118.RankedRightPreparation
import ErdosProblems.Erdos118.RankedTargetLabels
import ErdosProblems.Erdos118.SelectedBodyReplay
import ErdosProblems.Erdos118.StrictCriticalOpening

/-! The actual strict critical source pair together with the saved
right target's first leaf, allowing a singleton target and separate graphs. -/

namespace Erdos118.StrictReservedRightOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns InsideCounts LastBodyRefinement
open AlignedRightPreparation (RootCertificate)

structure Opening {H K : Set ℕ} {B C : SimpleGraph G} {X : Pending} {I : RootCertificate H B X}
    {P : Pending} {k v d₀ : ℕ} {A : RootResponses.Setup k}
    (Z : StrictLocalization.Prepared K C P A v d₀)
    {R : RootReplayReserve.Reserve H I.bound I.size v Z.body.stem}
    (T : RankedRightPreparation.Target I Z.body R) (d : ℕ) where
  source : BodyResponses.Setup Z.body.stem Z.size
  index : ℕ
  checkpoint : StrictLeafCheckpoint.Reached Z.alphabet Z.alphabet Z.graph
    Z.left (applyBody Z.body source) index d
  target : BodyResponses.Setup T.rootSetup.stem T.size
  ordinary : target.position.ordinary = checkpoint.right.position.ordinary
  marker : target.position.size = checkpoint.right.position.size
  entries : target.position.entries = checkpoint.right.position.entries
  sourceRun : ConservativeRuns.Run Z.alphabet (GraphPayoff.payoff Z.graph .inside)
    (.leaf Z.left, .body Z.body) (.leaf checkpoint.left, .leaf checkpoint.right)
  sourceFresh : FreshCheckpoints.FreshExtension Z.alphabet d
    (.leaf Z.left, .body Z.body) (.leaf checkpoint.left, .leaf checkpoint.right)
  targetStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf X, .body (ofRoot T.rootSetup)) (.leaf X, .leaf (applyBody (ofRoot T.rootSetup) target))
  targetBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside
    (.leaf X, .leaf (applyBody (ofRoot T.rootSetup) target))) true
  targetHandoff : LeftBlue H (GraphPayoff.payoff B .inside)
    (.leaf X, .leaf (applyBody (ofRoot T.rootSetup) target))
  targetExact : ExactSlots.Exact (.leaf (applyBody (ofRoot T.rootSetup) target))
  targetSingleton : (applyBody (ofRoot T.rootSetup) target).leaves = [] ↔ T.size = 0
  lastIff : checkpoint.right.leaves = [] ↔ Z.leafRank = Z.size + 1
  nextIndex : Z.leafRank < Z.size + 1 →
    checkpoint.right.position.entries.length < checkpoint.right.position.label.getLastD 0 ∧
    (0 < T.size → checkpoint.right.position.label.getLastD 0 ∈ target.position.label) ∧
    ∀ x ∈ target.position.label, checkpoint.right.position.entries.length < x →
      checkpoint.right.position.label.getLastD 0 ≤ x

theorem exists_opening {H K : Set ℕ} (hKH : K ⊆ H) {B C : SimpleGraph G}
    {X : Pending} {I : RootCertificate H B X} {P : Pending} {k v d₀ : ℕ} {A : RootResponses.Setup k}
    (Z : StrictLocalization.Prepared K C P A v d₀)
    {R : RootReplayReserve.Reserve H I.bound I.size v Z.body.stem}
    (T : RankedRightPreparation.Target I Z.body R)
    (hPlen : 1 < P.position.stem.rootLabel.length)
    (hall : ∀ S U : Completed, GraphPayoff.payoff C .inside S U = true →
      beforeLast S < beforeLast U) (d : ℕ) : Nonempty (Opening Z T d) := by
  have hJH : Z.alphabet ⊆ H := Z.subset.trans hKH
  have hH : H.Infinite := Z.infinite.mono hJH
  let c := pairBound (.leaf Z.left, .body Z.body)
  let g := PreparedRelays.guard Z.alphabet Z.graph .inside true Z.body (.leaf Z.left) Z.size
  let b := max Z.bound (max c (max g (max T.bound d)))
  have hZb : Z.bound ≤ b := le_max_left _ _
  have hcb : c ≤ b := by dsimp [b]; omega
  have hgb : g ≤ b := by dsimp [b]; omega
  have hTb : T.bound ≤ b := by dsimp [b]; omega
  have hdb : d ≤ b := by dsimp [b]; omega
  obtain ⟨E, L, hlabel, hbelow, hE⟩ := RankedTargetLabels.body_setup Z.body.stem Z.body.room
    Z.infinite b Z.size T.size Z.leafRank Z.positive Z.bounded
  let Q := applyBody Z.body E
  let Y : SelectedBodyReplay.Prepared H B .inside true (ofRoot T.rootSetup) (.leaf X) Q :=
    { ordinary := T.ordinary.trans (congrArg Stem.ordinary E.stem_eq).symm
      size := T.size, label := L.upper, card := L.upperCard, increasing := L.upperIncreasing
      selected := hlabel ▸ L.selected, below := hbelow
      bound := T.bound, pairBound_le := T.pairBound_le, guard_le := T.guard_le
      labelFresh := fun x hx ↦ ⟨hJH (L.upperFresh x hx).1, hTb.trans_lt (L.upperFresh x hx).2⟩
      tailFresh := fun x hx ↦
        ⟨hJH (hE x (List.mem_append_right _ hx)).1,
          hTb.trans_lt (hE x (List.mem_append_right _ hx)).2⟩
      allowed := rfl, certificate := T.certificate }
  obtain ⟨j, hj, hjrank, W, hrun, hfresh, hlast⟩ := StrictCriticalOpening.at_body Z hPlen hall E d
    (fun x hx ↦ (hE x hx).1) (fun x hx ↦ hZb.trans_lt (hE x hx).2)
    (fun x hx ↦ hcb.trans_lt (hE x hx).2) (fun x hx ↦ hgb.trans_lt (hE x hx).2)
    (fun x hx ↦ hdb.trans_lt (hE x hx).2)
  have hpivot : j = L.upper.headD 0 := by
    have hselected : L.upper.headD 0 ∈ E.position.label := hlabel ▸ L.selected
    have hrank : LabelRanks.rank E.position.label (L.upper.headD 0) = Z.leafRank := hlabel ▸ L.rank
    exact LabelRanks.rank_injective hj hselected (hjrank.trans hrank.symm)
  obtain ⟨Y', _, hYlabel, hYsize⟩ := SelectedBodyReplay.carry_of_run Y true W.right
    (.leaf Z.left) (.leaf W.left) W.sameBody hJH (GraphPayoff.payoff Z.graph .inside) W.run
  have hi : W.right.position.entries.length = Y'.label.headD 0 := by
    rw [W.index, hYlabel]
    exact hpivot
  let F₀ := Y'.setup hi
  let F : BodyResponses.Setup T.rootSetup.stem T.size :=
    { position := F₀.position, stem_eq := F₀.stem_eq
      label_length := F₀.label_length.trans (congrArg (fun n ↦ n + 1) hYsize)
      entries_length := F₀.entries_length }
  obtain ⟨hord, hstep, hblue, hh⟩ := SelectedBodyReplay.fire hH Y' hi
  have hFlabel : F.position.label = L.upper := hYlabel
  have hWlabel : W.right.position.label = L.lower := W.sameBody.label.trans hlabel
  have hWi : W.right.position.entries.length = L.upper.headD 0 := W.index.trans hpivot
  exact ⟨{
    source := E, index := j, checkpoint := W, target := F, ordinary := hord
    marker := rfl, entries := rfl, sourceRun := hrun, sourceFresh := hfresh
    targetStep := hstep, targetBlue := hblue, targetHandoff := hh
    targetExact := ExactSlots.step_exact (DecisionStates.Step.body (ofRoot T.rootSetup) F)
      (ExactSlots.step_exact (DecisionStates.Step.root T.rootSetup) trivial)
    targetSingleton := by
      change F.position.label.tail = [] ↔ T.size = 0
      rw [← List.length_eq_zero_iff, List.length_tail, F.label_length]
      omega
    lastIff := hlast
    nextIndex := by
      intro hlt
      rw [hWi, hWlabel, hFlabel]
      exact L.nonlastCase hlt }⟩

end Erdos118.StrictReservedRightOpening
