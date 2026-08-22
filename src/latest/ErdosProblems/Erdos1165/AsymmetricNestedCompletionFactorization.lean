/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPairTwoStageMass

/-!
# A complementary factor over a genuine completion event

The outer code of a deeper factor may be the complete code of a preceding
completion atom.  Its complement word is then the *assembled word* of that
coarse atom.  Consequently the deeper factor's outer weight is exactly the
mass of the coarse completion event.  This is the structural cancellation
needed by the asymmetric nested completion; no coarse event is replaced by
one synthetic cylinder.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricNestedCompletionFactorization

open MarkedBridgeFactorization

noncomputable section

/-- Put an arbitrary deeper bridge insertion family over the complete code
space of an already constructed coarse completion atom. -/
def overCompletionAtom
    {coarseCount deepCount : ℕ}
    {CoarseComplement : Type*} {CoarseBridge : Fin coarseCount → Type*}
    (coarse : ComplementarySkeletonAtom coarseCount
      CoarseComplement CoarseBridge)
    {DeepBridge : Fin deepCount → Type*}
    (deepBridgeWord : ∀ j, DeepBridge j → StoppedWord)
    (assemble :
      (CoarseComplement × ((j : Fin coarseCount) → CoarseBridge j)) ×
        ((j : Fin deepCount) → DeepBridge j) → StoppedWord)
    (prefixFree_assemble : PrefixFree assemble)
    (prefixFree_bridge : ∀ j, PrefixFree (deepBridgeWord j))
    (length_assemble : ∀ code,
      (assemble code).1 = (coarse.assemble code.1).1 +
        ∑ j, (deepBridgeWord j (code.2 j)).1) :
    ComplementarySkeletonAtom deepCount
      (CoarseComplement × ((j : Fin coarseCount) → CoarseBridge j))
      DeepBridge where
  complementWord := coarse.assemble
  bridgeWord := deepBridgeWord
  assemble := assemble
  prefixFree_assemble := prefixFree_assemble
  prefixFree_bridge := prefixFree_bridge
  length_assemble := length_assemble

/-- The outer weight of a factor over a coarse completion is exactly the
mass of that completion event. -/
theorem overCompletionAtom_weight
    {coarseCount deepCount : ℕ}
    {CoarseComplement : Type*} {CoarseBridge : Fin coarseCount → Type*}
    [Countable CoarseComplement] [∀ j, Countable (CoarseBridge j)]
    (coarse : ComplementarySkeletonAtom coarseCount
      CoarseComplement CoarseBridge)
    {DeepBridge : Fin deepCount → Type*}
    (deepBridgeWord : ∀ j, DeepBridge j → StoppedWord)
    (assemble :
      (CoarseComplement × ((j : Fin coarseCount) → CoarseBridge j)) ×
        ((j : Fin deepCount) → DeepBridge j) → StoppedWord)
    (prefixFree_assemble : PrefixFree assemble)
    (prefixFree_bridge : ∀ j, PrefixFree (deepBridgeWord j))
    (length_assemble : ∀ code,
      (assemble code).1 = (coarse.assemble code.1).1 +
        ∑ j, (deepBridgeWord j (code.2 j)).1) :
    (overCompletionAtom coarse deepBridgeWord assemble
      prefixFree_assemble prefixFree_bridge length_assemble).weight =
      fairSteps coarse.event := by
  unfold overCompletionAtom ComplementarySkeletonAtom.weight
  rw [ComplementarySkeletonAtom.event,
    fairSteps_stoppedWordEvent coarse.prefixFree_assemble]

end

end Erdos1165.AsymmetricNestedCompletionFactorization
