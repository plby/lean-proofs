import Mathlib
import ErdosProblems.Erdos550.TauFineSingleNeighbor

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A τ-fine separator containing a prescribed tree root

The deferred-seed matching algorithm needs the global tree root to be a seed.
Adding it after the old construction can temporarily create a component with
three boundary seeds, so we rerun the two finite promotion steps.  Smallness is
monotone under adding seeds.  The resulting constant is immaterial
asymptotically and all three structural conclusions are retained.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Prescribed-root form of the single-neighbour, two-attachment separator. -/
theorem tree_tau_fine_single_neighbor_two_attachment_rooted
    (T : SimpleGraph A) [DecidableRel T.Adj] (hT : T.IsTree)
    (root : A)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card A) :
    ∃ S : Finset A,
      root ∈ S ∧
      (S.card : ℝ) ≤ 8 / τ + 4 ∧
      (∀ v ∉ S, ((T.neighborFinset v) ∩ S).card ≤ 1) ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (∃ v : A, v ∈ c.supp ∧ v ∉ S) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card A ∧
          (componentSeeds T S c).card ≤ 2) := by
  obtain ⟨S₀, hS₀, hsmall₀, _hattach₀⟩ :=
    tree_tau_fine_two_attachment_strong_data T hT τ hτ hn
  let S₁ := S₀ ∪ {root}
  have hsmall₁ :
      ∀ c : (seedDeleted T S₁).ConnectedComponent,
        (∃ v : A, v ∈ c.supp ∧ v ∉ S₁) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card A := by
    simpa [S₁] using!
      (promoted_components_small_nonseed T S₀ {root}
        (τ * Fintype.card A) hsmall₀)
  let B₁ := promotedBranchVertices T S₁
  let S₂ := S₁ ∪ B₁
  have hattach₂ :
      ∀ c : (seedDeleted T S₂).ConnectedComponent,
        (∃ v : A, v ∈ c.supp ∧ v ∉ S₂) →
          (componentSeeds T S₂ c).card ≤ 2 := by
    simpa [S₂] using! promoted_components_two_attachments T hT S₁
  have hsmall₂ :
      ∀ c : (seedDeleted T S₂).ConnectedComponent,
        (∃ v : A, v ∈ c.supp ∧ v ∉ S₂) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card A := by
    simpa [S₂] using!
      (promoted_components_small_nonseed T S₁ B₁
        (τ * Fintype.card A) hsmall₁)
  let B₂ := doubleSeedNeighbors T S₂
  let S₃ := S₂ ∪ B₂
  refine ⟨S₃, ?_, ?_, ?_, ?_⟩
  · simp [S₃, S₂, S₁]
  · have hS₁card : S₁.card ≤ S₀.card + 1 := by
      simpa [S₁] using! Finset.card_union_le S₀ {root}
    have hB₁card : B₁.card ≤ S₁.card :=
      promotedBranchVertices_card_le T hT S₁
    have hS₂card : S₂.card ≤ 2 * S₁.card := by
      calc
        S₂.card ≤ S₁.card + B₁.card := by
          simpa [S₂] using! Finset.card_union_le S₁ B₁
        _ ≤ 2 * S₁.card := by omega
    have hB₂card : B₂.card ≤ S₂.card :=
      doubleSeedNeighbors_card_le T hT S₂ hattach₂
    have hS₃card : S₃.card ≤ 2 * S₂.card := by
      calc
        S₃.card ≤ S₂.card + B₂.card := by
          simpa [S₃] using! Finset.card_union_le S₂ B₂
        _ ≤ 2 * S₂.card := by omega
    have hreal₁ : (S₁.card : ℝ) ≤ (S₀.card : ℝ) + 1 := by
      exact_mod_cast hS₁card
    have hreal₂ : (S₂.card : ℝ) ≤ 2 * (S₁.card : ℝ) := by
      exact_mod_cast hS₂card
    have hreal₃ : (S₃.card : ℝ) ≤ 2 * (S₂.card : ℝ) := by
      exact_mod_cast hS₃card
    calc
      (S₃.card : ℝ) ≤ 2 * (S₂.card : ℝ) := hreal₃
      _ ≤ 4 * (S₁.card : ℝ) := by linarith
      _ ≤ 4 * ((S₀.card : ℝ) + 1) := by gcongr
      _ ≤ 4 * (2 / τ + 1) := by gcongr
      _ = 8 / τ + 4 := by ring
  · simpa [S₃, B₂] using!
      outside_promoted_has_at_most_one_seed_neighbor T hT S₂ hattach₂
  · intro c hc
    constructor
    · simpa [S₃] using!
        (promoted_components_small_nonseed T S₂ B₂
          (τ * Fintype.card A) hsmall₂ c hc)
    · simpa [S₃, B₂] using!
        (doubleSeedNeighbors_components_two_attachments
          T hT S₂ hattach₂ c hc)

end Erdos550
