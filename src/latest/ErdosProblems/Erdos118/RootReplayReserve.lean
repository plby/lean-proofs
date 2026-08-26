import ErdosProblems.Erdos118.SplicedRootReserve

/-! The exact first-root invariant used by a right-target decoder,
independent of the additional later root-overlap geometry. -/

namespace Erdos118.RootReplayReserve

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates

structure Reserve (H : Set ℕ) (b l v : ℕ) (S : Stem) where
  label : List ℕ
  card : label.length = l + 1
  increasing : label.Pairwise (· < ·)
  selected : label.headD 0 ∈ S.rootLabel
  rank : LabelRanks.rank S.rootLabel (label.headD 0) = v
  fresh : ∀ x ∈ label, x ∈ H ∧ b < x
  below : ∀ x ∈ label, x < S.root

def ofRanked {H : Set ℕ} {b k l v : ℕ} {S : Stem}
    (R : RankedRootReserve.Reserve H b k l v S) : Reserve H b l v S where
  label := R.labels.upper
  card := R.labels.upperCard
  increasing := R.labels.upperIncreasing
  selected := by rw [R.labels.first, R.lower]; exact R.labels.sharedLower
  rank := by rw [R.labels.first, R.lower]; exact R.labels.sharedRank
  fresh := R.labels.upperFresh
  below := R.below

def ofSpliced {H : Set ℕ} {b k l v r : ℕ} {S : Stem}
    (R : SplicedRootReserve.Reserve H b k l v r S) : Reserve H b l v S where
  label := R.labels.upper
  card := R.labels.upperCard
  increasing := R.labels.upperIncreasing
  selected := by rw [R.labels.first, R.lower]; exact R.labels.sharedLower
  rank := by rw [R.labels.first, R.lower]; exact R.labels.sharedRank
  fresh := R.labels.upperFresh
  below := R.below

theorem Reserve.index_of_rank {H : Set ℕ} {b l v : ℕ} (D : BodyDecision)
    (Z : Reserve H b l v D.stem)
    (hrank : LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = v) :
    D.stem.done.length + 1 = Z.label.headD 0 :=
  LabelRanks.rank_injective D.rootSelected Z.selected (hrank.trans Z.rank.symm)

def Reserve.rootSetup {H : Set ℕ} {b l v : ℕ} {S : Stem} (Z : Reserve H b l v S)
    (hindex : S.done.length + 1 = Z.label.headD 0) : RootResponses.Setup l :=
  LabelOverlays.rootSetup S Z.label Z.increasing Z.below l Z.card hindex

theorem Reserve.rootSetup_ordinary {H : Set ℕ} {b l v : ℕ} {S : Stem}
    (Z : Reserve H b l v S) (hindex : S.done.length + 1 = Z.label.headD 0) :
    (Z.rootSetup hindex).stem.ordinary = S.ordinary :=
  LabelOverlays.plainStem_ordinary S Z.label Z.increasing Z.below

theorem Reserve.rootSetup_supported {H : Set ℕ} {b l v : ℕ} {S : Stem}
    (Z : Reserve H b l v S) (hindex : S.done.length + 1 = Z.label.headD 0)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (Z.rootSetup hindex).stem.decorated, x ∈ H ∧ b < x :=
  LabelOverlays.plainStem_supported S Z.label Z.increasing Z.below Z.fresh hf

end Erdos118.RootReplayReserve
