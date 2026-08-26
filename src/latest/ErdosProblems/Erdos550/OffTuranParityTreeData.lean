import Mathlib
import ErdosProblems.Erdos550.ParityRefinedPackage
import ErdosProblems.Erdos550.RootedComponentBlocks
import ErdosProblems.Erdos550.TauFineRootedSeparator
import ErdosProblems.Erdos550.TreeColouring

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Packaged parity-refined source-tree data

Starting from a prescribed-root two-attachment separator, promote exactly the
parity-bad component tops.  We then reroot the components for the enlarged seed
set.  The output has all of the source-side fields consumed by the stateful
whole-matching embedding.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

structure OffTuranParityTreeData
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (τ : ℝ) where
  root : A
  S : Finset A
  root_mem : root ∈ S
  seed_card : (S.card : ℝ) ≤ 16 / τ + 8
  parent : A → Option A
  rank : A → ℕ
  D : RootedSeedComponentData T S parent
  col : A → Bool
  rank_decreases : ∀ a b, parent a = some b → rank b < rank a
  parent_adj : ∀ a b, parent a = some b → T.Adj a b
  edge_parent : ∀ a b, T.Adj a b →
    parent a = some b ∨ parent b = some a
  colour_flips : ∀ a b, parent a = some b → col a ≠ col b
  component_small : ∀ c : NonseedComponent T S,
    (Fintype.card (RootedComponentVertex T S c) : ℝ) ≤
      τ * Fintype.card A
  attachment_card : ∀ c : NonseedComponent T S,
    (componentSeeds T S c.1).card ≤ 2
  boundary_colour : ∀ c : NonseedComponent T S,
    ∀ a ∈ componentSeeds T S c.1,
      ∀ b ∈ componentSeeds T S c.1, col a = col b

/-- Every finite tree has the complete parity-refined separator package once
`τ |T| ≥ 1`. -/
theorem exists_offTuran_parity_tree_data
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hτn : (1 : ℝ) ≤ τ * Fintype.card A) :
    Nonempty (OffTuranParityTreeData T τ) := by
  obtain ⟨root⟩ : Nonempty A := hT.1.nonempty
  obtain ⟨S₀, hroot₀, hseed₀, _hsingle₀, hcomp₀⟩ :=
    tree_tau_fine_single_neighbor_two_attachment_rooted
      T hT root τ hτ hτn
  obtain ⟨parent₀, rank₀, _hrootNone₀, _hrootUnique₀,
      hrank₀, hparentAdj₀, hedge₀, hD₀⟩ :=
    exists_rooted_component_block_data T hT root S₀ hroot₀
  let D₀ : RootedSeedComponentRankData T S₀ parent₀ rank₀ :=
    Classical.choice hD₀
  obtain ⟨col, hcolEdge⟩ := IsTree.exists_two_colouring T hT
  let S := S₀ ∪ parityPromotionRoots T S₀
    D₀.toRootedSeedComponentData col
  have holdSmall :
      ∀ c : (seedDeleted T S₀).ConnectedComponent,
        (∃ v ∈ c.supp, v ∉ S₀) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card A := by
    intro c hc
    exact (hcomp₀ c hc).1
  have holdAttach :
      ∀ c : NonseedComponent T S₀,
        (componentSeeds T S₀ c.1).card ≤ 2 := by
    intro c
    obtain ⟨v, hv⟩ := componentNonseedVertices_nonempty T S₀ c
    have hv' :=
      (mem_componentNonseedVertices_iff T S₀ c.1 v).mp hv
    exact (hcomp₀ c.1 ⟨v, hv'.2, hv'.1⟩).2
  have hrefined :=
    parity_refined_separator_package T S₀ D₀ hrank₀
      hparentAdj₀ hedge₀ (τ * Fintype.card A)
      holdSmall holdAttach col
      (fun a b hab => hcolEdge a b (hparentAdj₀ a b hab))
  have hrootS : root ∈ S := by
    exact Finset.mem_union_left _ hroot₀
  obtain ⟨parent, rank, _hrootNone, _hrootUnique,
      hrank, hparentAdj, hedge, hD⟩ :=
    exists_rooted_component_block_data T hT root S hrootS
  let D : RootedSeedComponentRankData T S parent rank :=
    Classical.choice hD
  have hseedReal : (S.card : ℝ) ≤ 16 / τ + 8 := by
    have hrefinedNat : S.card ≤ 2 * S₀.card := by
      simpa [S] using! hrefined.1
    have hrefinedReal : (S.card : ℝ) ≤ 2 * (S₀.card : ℝ) := by
      exact_mod_cast hrefinedNat
    calc
      (S.card : ℝ) ≤ 2 * (S₀.card : ℝ) := hrefinedReal
      _ ≤ 2 * (8 / τ + 4) := by gcongr
      _ = 16 / τ + 8 := by ring
  refine ⟨⟨root, S, hrootS, hseedReal, parent, rank,
    D.toRootedSeedComponentData, col, hrank, hparentAdj, hedge,
    (fun a b hab => hcolEdge a b (hparentAdj a b hab)), ?_, ?_, ?_⟩⟩
  · intro c
    rw [card_rootedComponentVertex]
    exact hrefined.2 c |>.1
  · intro c
    exact hrefined.2 c |>.2.1
  · intro c
    exact hrefined.2 c |>.2.2

end Erdos550
