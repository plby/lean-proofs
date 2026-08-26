import Mathlib
import ErdosProblems.Erdos550.RootedComponentLocal

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Upper and deferred lower seeds of a rooted component

Every deleted component has one upper seed: the parent of its top vertex.
Any other boundary seed is below the component, so its own parent lies in the
component and it can be embedded after that component.  This is the formal
reason no shrub vertex is ever required to meet two previously embedded
anchors.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def componentUpperSeed
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) : A :=
  (D.root_parent_seed c).choose

lemma componentUpperSeed_mem
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) :
    componentUpperSeed T S D c ∈ S :=
  (D.root_parent_seed c).choose_spec.1

lemma componentRoot_parent_upperSeed
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) :
    parent (D.root c) = some (componentUpperSeed T S D c) :=
  (D.root_parent_seed c).choose_spec.2

noncomputable def componentLowerSeeds
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) : Finset A :=
  componentSeeds T S c.1 \ {componentUpperSeed T S D c}

lemma componentLowerSeeds_card_le_one
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hattach : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ 2)
    (c : NonseedComponent T S) :
    (componentLowerSeeds T S D c).card ≤ 1 := by
  have hu :
      componentUpperSeed T S D c ∈ componentSeeds T S c.1 := by
    apply seed_mem_componentSeeds_of_adj T S c.1
      (componentUpperSeed_mem T S D c)
    · exact (mem_componentNonseedVertices_iff T S c.1 (D.root c)).mp
        (D.root_mem c) |>.2
    · exact (hparentAdj _ _
        (componentRoot_parent_upperSeed T S D c)).symm
  rw [componentLowerSeeds, Finset.card_sdiff_of_subset]
  · have hcard := hattach c
    simp only [Finset.card_singleton]
    omega
  · simpa using! hu

/-- Every non-upper boundary seed is deferred: its parent is a vertex of this
component. -/
theorem lowerSeed_parent_in_component
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (c : NonseedComponent T S)
    {s : A} (hs : s ∈ componentLowerSeeds T S D c) :
    ∃ v ∈ componentNonseedVertices T S c.1, parent s = some v := by
  have hsComp : s ∈ componentSeeds T S c.1 :=
    (Finset.mem_sdiff.mp hs).1
  have hsUpper : s ≠ componentUpperSeed T S D c := by
    simpa using! (Finset.mem_sdiff.mp hs).2
  obtain ⟨v, hv, hsv⟩ :=
    component_attachment_witness T S c hsComp
  rcases hedge s v hsv with hdown | hup
  · exact ⟨v, hv, hdown⟩
  · exfalso
    by_cases hvr : v = D.root c
    · subst v
      have heq : s = componentUpperSeed T S D c := by
        rw [componentRoot_parent_upperSeed T S D c] at hup
        exact (Option.some.inj hup).symm
      exact hsUpper heq
    · obtain ⟨y, hy, hvy⟩ := D.parent_internal c v hv hvr
      have hys : y = s := by
        rw [hup] at hvy
        exact (Option.some.inj hvy).symm
      subst y
      have hsNotS :=
        (mem_componentNonseedVertices_iff T S c.1 s).mp hy |>.1
      exact hsNotS (componentSeeds_subset T S c.1 hsComp)

end Erdos550
