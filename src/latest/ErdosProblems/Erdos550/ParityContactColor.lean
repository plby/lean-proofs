import Mathlib
import ErdosProblems.Erdos550.ParityRefinedPackage

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Colour of component vertices incident with deferred seeds

After parity refinement, all boundary seeds of a component have one global
tree colour.  Hence the component root and every component vertex which is the
parent of a deferred boundary seed have the opposite, common colour.  They may
therefore all be retained on one endpoint of the selected matching edge; no
two-endpoint common-neighbour condition is needed.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Rebase a global bipartite colour so that the selected component root has
local colour `false`. -/
def relativeComponentColor (col : A → Bool) (root : A) (a : A) : Bool :=
  if col a = col root then false else true

@[simp] lemma relativeComponentColor_root (col : A → Bool) (root : A) :
    relativeComponentColor col root root = false := by
  simp [relativeComponentColor]

lemma relativeComponentColor_parent
    (col : A → Bool) (root : A)
    {parent : A → Option A}
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    {a b : A} (hab : parent a = some b) :
    relativeComponentColor col root a ≠
      relativeComponentColor col root b := by
  have habc := hcol a b hab
  cases ha : col a <;> cases hb : col b <;>
    cases hr : col root <;> simp_all [relativeComponentColor]

@[simp] lemma relativeComponentColor_eq_false_iff
    (col : A → Bool) (root a : A) :
    relativeComponentColor col root a = false ↔ col a = col root := by
  simp [relativeComponentColor]

lemma component_contact_colour_eq_root
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : NonseedComponent T S)
    (hboundary : ∀ a ∈ componentSeeds T S c.1,
      ∀ b ∈ componentSeeds T S c.1, col a = col b)
    {s x : A}
    (hs : s ∈ componentSeeds T S c.1)
    (hx : x ∈ componentNonseedVertices T S c.1)
    (hsx : parent s = some x) :
    col x = col (D.root c) := by
  have hu :
      componentUpperSeed T S D c ∈ componentSeeds T S c.1 := by
    apply seed_mem_componentSeeds_of_adj T S c.1
      (componentUpperSeed_mem T S D c)
    · exact
        (mem_componentNonseedVertices_iff T S c.1 (D.root c)).mp
          (D.root_mem c) |>.2
    · exact (hparentAdj _ _
        (componentRoot_parent_upperSeed T S D c)).symm
  have hseedColour :
      col s = col (componentUpperSeed T S D c) :=
    hboundary s hs (componentUpperSeed T S D c) hu
  have hrootFlip :
      col (D.root c) ≠ col (componentUpperSeed T S D c) :=
    hcol _ _ (componentRoot_parent_upperSeed T S D c)
  have hxFlip : col s ≠ col x := hcol s x hsx
  cases hsC : col s <;>
    cases hxC : col x <;>
    cases hrC : col (D.root c) <;>
    cases huC : col (componentUpperSeed T S D c) <;>
    simp_all

end Erdos550
