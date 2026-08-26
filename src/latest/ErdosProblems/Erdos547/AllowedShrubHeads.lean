import ErdosProblems.Erdos547.SeedAttachments
import ErdosProblems.Erdos547.AllowedWeight

/-!
# Heads avoiding both anchors and every attachment-seed exception
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U I : Type*} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

noncomputable def allowedHeads (anchors : Finset I) (badMain badQ : ↥P.seeds → Finset I)
    (w : Fin 2 → I → ℝ) (θ : ℝ) (S : ↥P.shrubs) : Finset I := by
  classical
  exact (Finset.univ.filter (fun i ↦ θ ≤ w (P.shrubColour S) i)) \
    (anchors ∪ (P.attachmentSeeds S).biUnion (fun z ↦ badMain z ∪ badQ z))

theorem allowedHeads_properties (anchors : Finset I) (badMain badQ : ↥P.seeds → Finset I)
    (w : Fin 2 → I → ℝ) (θ : ℝ) (S : ↥P.shrubs) (i : I)
    (hi : i ∈ P.allowedHeads anchors badMain badQ w θ S) :
    θ ≤ w (P.shrubColour S) i ∧ i ∉ anchors ∧
      ∀ z ∈ P.attachmentSeeds S, i ∉ badMain z ∧ i ∉ badQ z := by
  classical
  obtain ⟨hi, hnot⟩ := Finset.mem_sdiff.mp hi
  refine ⟨(Finset.mem_filter.mp hi).2, fun h ↦ hnot (Finset.mem_union_left _ h), ?_⟩
  intro z hz
  have hn : i ∉ badMain z ∪ badQ z := fun h ↦ hnot
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, hz, h⟩))
  exact ⟨fun h ↦ hn (Finset.mem_union_left _ h), fun h ↦ hn (Finset.mem_union_right _ h)⟩

theorem allowedHeads_weight (anchors : Finset I) (badMain badQ : ↥P.seeds → Finset I)
    (w : Fin 2 → I → ℝ) (θ b : ℝ) (hθ : 0 ≤ θ) (hb : 0 ≤ b)
    (hw : ∀ c i, w c i ≤ 1)
    (hMain : ∀ z, ((badMain z).card : ℝ) ≤ b) (hQ : ∀ z, ((badQ z).card : ℝ) ≤ b)
    (S : ↥P.shrubs) :
    (∑ i, w (P.shrubColour S) i) - θ * Fintype.card I - anchors.card - 4 * b ≤
      ∑ i ∈ P.allowedHeads anchors badMain badQ w θ S, w (P.shrubColour S) i := by
  classical
  let E := anchors ∪ (P.attachmentSeeds S).biUnion (fun z ↦ badMain z ∪ badQ z)
  have hE : (E.card : ℝ) ≤ anchors.card + 4 * b :=
    card_exceptions_for_two_attachments (P.attachmentSeeds S) (P.attachmentSeeds_card S)
      badMain badQ anchors b hb (fun z _ ↦ hMain z) (fun z _ ↦ hQ z)
  have hh := allowed_weight_lower Finset.univ E (w (P.shrubColour S)) (hw _) θ hθ
  rw [Finset.card_univ] at hh
  change (∑ i, w (P.shrubColour S) i) - θ * Fintype.card I - E.card ≤
    ∑ i ∈ P.allowedHeads anchors badMain badQ w θ S, w (P.shrubColour S) i at hh
  linarith only [hE, hh]

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.allowedHeads_weight
