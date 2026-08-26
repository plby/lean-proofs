import Mathlib
import ErdosProblems.Erdos550.ParityRefinedComponents

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Packaged parity-refined separator

This is the complete tree-side output used by the direct off--Turán embedding:
the separator grows by at most a factor two, every remaining component stays
small, and its at most two boundary seeds all have the same global tree colour.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

theorem parity_refined_separator_package
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (S : Finset A)
    {parent : A → Option A} {rank : A → ℕ}
    (D : RootedSeedComponentRankData T S parent rank)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (K : ℝ)
    (hsmall : ∀ c : (seedDeleted T S).ConnectedComponent,
      (∃ v ∈ c.supp, v ∉ S) → (Nat.card c.supp : ℝ) ≤ K)
    (hattach : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ 2)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b) :
    let S' := S ∪ parityPromotionRoots T S
      D.toRootedSeedComponentData col
    S'.card ≤ 2 * S.card ∧
      ∀ c : NonseedComponent T S',
        ((componentNonseedVertices T S' c.1).card : ℝ) ≤ K ∧
        (componentSeeds T S' c.1).card ≤ 2 ∧
        ∀ a ∈ componentSeeds T S' c.1,
          ∀ b ∈ componentSeeds T S' c.1, col a = col b := by
  dsimp only
  constructor
  · exact parityRefinedSeeds_card_le T S
      D.toRootedSeedComponentData hparentAdj hedge col
  · intro c
    have hcNonempty :
        ∃ v ∈ c.1.supp,
          v ∉ S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col := by
      obtain ⟨v, hv⟩ :=
        componentNonseedVertices_nonempty T
          (S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col) c
      exact ⟨v,
        (mem_componentNonseedVertices_iff T
          (S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col) c.1 v).mp hv |>.2,
        (mem_componentNonseedVertices_iff T
          (S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col) c.1 v).mp hv |>.1⟩
    have hcSmall :=
      promoted_components_small_nonseed T S
        (parityPromotionRoots T S
          D.toRootedSeedComponentData col) K hsmall c.1 hcNonempty
    have hcBoundary :=
      parityRefined_component_boundary T S D hrank
        hparentAdj hedge hattach col hcol c
    refine ⟨?_, hcBoundary.1, hcBoundary.2⟩
    rw [componentNonseedVertices_card_eq T
      (S ∪ parityPromotionRoots T S
        D.toRootedSeedComponentData col) c]
    exact hcSmall

end Erdos550
