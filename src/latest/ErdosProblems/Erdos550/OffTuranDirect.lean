import Mathlib
import ErdosProblems.Erdos550.TauFineAttachments
import ErdosProblems.Erdos550.TauFineTwoAttachment

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Two-attachment separator for the direct off--Turán route

The strengthened tree separator used by the direct route has small nonseed
components, each with at most two seed attachments.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-!
## Strengthened τ-fine separator
-/

/-- A τ-fine separator in which every component containing a nonseed vertex
hangs between at most two seeds.  The factor two in the seed budget pays for
the additional vertices needed to control attachments.

The attachment conclusion must be restricted to nonseed components.  The
stronger variant quantifying over every component is false: take a hub joined
to three spider centres, with three sufficiently long legs at each centre.
Smallness and the attachment bound force all three centres and then the hub to
be seeds, but the seed-singleton component of the hub has the three centres as
attachments.  Downstream routing only uses components containing a nonseed
vertex, so the restriction loses nothing needed by that pipeline. -/
theorem tree_tau_fine_two_attachment
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 2 / τ ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (∃ v ∈ c.supp, v ∉ S) →
          (Nat.card c.supp : ℝ) ≤ τ * Fintype.card α ∧
          (componentSeeds T S c).card ≤ 2) := by
  obtain ⟨S₀, hS₀, hsmall⟩ := tree_tau_fine T hT τ hτ hn
  let B := promotedBranchVertices T S₀
  refine ⟨S₀ ∪ B, ?_, ?_⟩
  · have hB : B.card ≤ S₀.card := promotedBranchVertices_card_le T hT S₀
    have hu : (S₀ ∪ B).card ≤ S₀.card + B.card := Finset.card_union_le S₀ B
    have hcard : ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := by
      exact_mod_cast hu.trans (by omega)
    calc
      ((S₀ ∪ B).card : ℝ) ≤ 2 * S₀.card := hcard
      _ ≤ 2 * (1 / τ) := by gcongr
      _ = 2 / τ := by ring
  · intro c hc
    constructor
    · apply promoted_components_small T S₀ B (τ * Fintype.card α) ?_ c hc
      simpa only [seedDeleted] using! hsmall
    · exact promoted_components_two_attachments T hT S₀ c hc

end Erdos550
