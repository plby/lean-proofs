import ErdosProblems.Erdos118.RootReplayReserve
import ErdosProblems.Erdos118.StrictLocalization
import ErdosProblems.Erdos118.AlignedRightPreparation

/-! A saved right-root certificate at the localized body. Its first
body parameter is retained exactly and is allowed to be zero. -/

namespace Erdos118.RankedRightPreparation

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays
open AlignedRightPreparation (RootCertificate)

structure Target {H : Set ℕ} {B : SimpleGraph G} {X : Pending} (I : RootCertificate H B X)
    (D : BodyDecision) {v : ℕ} (R : RootReplayReserve.Reserve H I.bound I.size v D.stem) where
  rootSetup : RootResponses.Setup I.size
  stem : rootSetup.stem = LabelOverlays.plainStem D.stem R.label R.increasing R.below
  rootLabel : rootSetup.stem.rootLabel = R.label
  ordinary : rootSetup.stem.ordinary = D.stem.ordinary
  rootBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside
    (.leaf X, .body (ofRoot rootSetup))) true
  size : ℕ
  bound : ℕ
  pairBound_le : pairBound (.leaf X, .body (ofRoot rootSetup)) ≤ bound
  guard_le : guard H B .inside true (ofRoot rootSetup) (.leaf X) size ≤ bound
  certificate : ∀ E : BodyResponses.Setup rootSetup.stem size,
    (∀ x ∈ BodyResponses.newWord E.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord E.position, bound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B .inside
      (.leaf X, .leaf (applyBody (ofRoot rootSetup) E))) true

theorem at_shared {H : Set ℕ} (B : SimpleGraph G) (X : Pending) (I : RootCertificate H B X)
    (D : BodyDecision) {v : ℕ} (R : RootReplayReserve.Reserve H I.bound I.size v D.stem)
    (hrank : LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = v)
    (hf : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ I.bound < x) : Nonempty (Target I D R) := by
  have hindex := R.index_of_rank D hrank
  let C := R.rootSetup hindex
  have hC := R.rootSetup_supported hindex hf
  have hbC := I.rootBlue C (fun x hx ↦ (hC x hx).1) (fun x hx ↦ (hC x hx).2)
  have hc := ReplaySources.body_command B .inside true (ofRoot C) X hbC
  obtain ⟨l, b, hb⟩ := body_setups B .inside true (ofRoot C) (.leaf X) hc
  let c := pairBound (.leaf X, .body (ofRoot C))
  let g := guard H B .inside true (ofRoot C) (.leaf X) l
  let bound := max b (max c g)
  exact ⟨{
    rootSetup := C, stem := rfl, rootLabel := rfl, ordinary := R.rootSetup_ordinary hindex
    rootBlue := hbC, size := l, bound := bound
    pairBound_le := (le_max_left c g).trans (le_max_right b _)
    guard_le := (le_max_right c g).trans (le_max_right b _)
    certificate := fun E hEH hEb ↦ hb E hEH
      (fun x hx ↦ (le_max_left b (max c g)).trans_lt (hEb x hx)) }⟩

theorem at_localized {H K : Set ℕ} (hKH : K ⊆ H) {B C : SimpleGraph G}
    (X : Pending) (I : RootCertificate H B X)
    {P : Pending} {k v d : ℕ} {A : RootResponses.Setup k}
    (Z : StrictLocalization.Prepared K C P A v d)
    (R : RankedRootReserve.Reserve H I.bound k I.size v A.stem)
    (hd : I.bound ≤ d) (hA : ∀ x ∈ A.stem.ordinary, x ∈ H ∧ I.bound < x) :
    ∃ R' : RankedRootReserve.Reserve H I.bound k I.size v Z.body.stem,
      R'.labels = R.labels ∧ Nonempty (Target I Z.body (RootReplayReserve.ofRanked R')) := by
  have hext := (SkippedCuts.run_extensions Z.run).2
  have hroot : Z.body.stem.root = A.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let R' := R.move Z.body.stem hroot Z.bodyRoot
  have hf : ∀ x ∈ Z.body.stem.ordinary, x ∈ H ∧ I.bound < x := by
    obtain ⟨u, w, _, hw, _, hwf⟩ := Z.fresh
    intro x hx
    change x ∈ State.ordinary (.body Z.body) at hx
    rw [hw] at hx
    exact (List.mem_append.mp hx).elim (hA x)
      (fun hx ↦ ⟨hKH (hwf x hx).1, hd.trans_lt (hwf x hx).2⟩)
  exact ⟨R', rfl, at_shared B X I Z.body (RootReplayReserve.ofRanked R') Z.bodyRank hf⟩

end Erdos118.RankedRightPreparation
