import Mathlib
import ErdosProblems.Erdos550.DeferredSeedAttachments

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Parity refinement of a rooted two-attachment separator

For the matching-edge embedding, the two boundary seeds of an internal
component must use the same head cluster.  Equivalently, they must have the
same colour in the bipartition of the source tree.  If an old component has
oppositely coloured boundary seeds, promoting its top vertex repairs the
parity: the top has the colour of the lower boundary seed.  The promoted top
also separates the old upper seed from every remaining nonseed component.

This file begins with the finite counting part of that refinement.  In
particular, the promoted tops are charged injectively to their lower boundary
seeds, so the separator grows by at most a factor two.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

/-- A rooted deleted component whose lower boundary seed has the opposite
tree colour from its upper boundary seed. -/
def parityBadComponent
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (c : NonseedComponent T S) : Prop :=
  ∃ s ∈ componentLowerSeeds T S D c,
    col s ≠ col (componentUpperSeed T S D c)

/-- The finite family of parity-bad components. -/
noncomputable def parityBadComponents
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) : Finset (NonseedComponent T S) :=
  Finset.univ.filter (parityBadComponent T S D col)

@[simp] lemma mem_parityBadComponents_iff
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (c : NonseedComponent T S) :
    c ∈ parityBadComponents T S D col ↔
      parityBadComponent T S D col c := by
  simp [parityBadComponents]

/-- The unique lower boundary seed used to charge a bad component. -/
noncomputable def parityBadLowerSeed
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
  (col : A → Bool)
    (c : {c // c ∈ parityBadComponents T S D col}) : A :=
  ((mem_parityBadComponents_iff T S D col c.1).mp c.2).choose

lemma parityBadLowerSeed_mem
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : {c // c ∈ parityBadComponents T S D col}) :
    parityBadLowerSeed T S D col c ∈
      componentLowerSeeds T S D c.1 :=
  ((mem_parityBadComponents_iff T S D col c.1).mp c.2).choose_spec.1

lemma parityBadLowerSeed_mem_seed
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : {c // c ∈ parityBadComponents T S D col}) :
    parityBadLowerSeed T S D col c ∈ S := by
  exact componentSeeds_subset T S c.1.1
    (Finset.mem_sdiff.mp
      (parityBadLowerSeed_mem T S D col c)).1

lemma parityBadLowerSeed_ne_upper
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : {c // c ∈ parityBadComponents T S D col}) :
    parityBadLowerSeed T S D col c ≠
      componentUpperSeed T S D c.1 := by
  simpa using! (Finset.mem_sdiff.mp
    (parityBadLowerSeed_mem T S D col c)).2

lemma parityBadLowerSeed_colour
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : {c // c ∈ parityBadComponents T S D col}) :
    col (parityBadLowerSeed T S D col c) ≠
      col (componentUpperSeed T S D c.1) :=
  ((mem_parityBadComponents_iff T S D col c.1).mp c.2).choose_spec.2

/-- In a parity-bad component the lower boundary seed has the colour of the
component root.  The two-attachment hypothesis is used only to make the lower
boundary unique. -/
lemma parityBad_lower_colour_eq_root
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hattach : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ 2)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : {c // c ∈ parityBadComponents T S D col})
    {s : A} (hs : s ∈ componentLowerSeeds T S D c.1) :
    col s = col (D.root c.1) := by
  have hlower :
      (componentLowerSeeds T S D c.1).card ≤ 1 :=
    componentLowerSeeds_card_le_one T S D hparentAdj hattach c.1
  have hseed :
      s = parityBadLowerSeed T S D col c :=
    Finset.card_le_one.mp hlower s hs
      (parityBadLowerSeed T S D col c)
      (parityBadLowerSeed_mem T S D col c)
  have hroot :
      col (D.root c.1) ≠
        col (componentUpperSeed T S D c.1) :=
    hcol _ _ (componentRoot_parent_upperSeed T S D c.1)
  rw [hseed]
  have hlowerCol := parityBadLowerSeed_colour T S D col c
  cases h₁ : col (parityBadLowerSeed T S D col c) <;>
    cases h₂ : col (componentUpperSeed T S D c.1) <;>
    cases h₃ : col (D.root c.1) <;>
    simp_all

/-- A component which is not parity-bad has all of its lower boundary seeds
in the same bipartition class as its upper boundary seed. -/
lemma parityGood_lower_colour_eq_upper
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : NonseedComponent T S)
    (hc : c ∉ parityBadComponents T S D col)
    {s : A} (hs : s ∈ componentLowerSeeds T S D c) :
    col s = col (componentUpperSeed T S D c) := by
  by_contra hne
  exact hc (mem_parityBadComponents_iff T S D col c |>.2
    ⟨s, hs, hne⟩)

/-- The lower-seed charge is injective: a lower seed has a unique parent,
and that parent belongs to only one deleted component. -/
lemma parityBadLowerSeed_injective
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (col : A → Bool) :
    Function.Injective (parityBadLowerSeed T S D col) := by
  intro c d hcd
  obtain ⟨vc, hvc, hcpar⟩ :=
    lowerSeed_parent_in_component T S D hparentAdj hedge c.1
      (parityBadLowerSeed_mem T S D col c)
  obtain ⟨vd, hvd, hdpar⟩ :=
    lowerSeed_parent_in_component T S D hparentAdj hedge d.1
      (parityBadLowerSeed_mem T S D col d)
  rw [hcd, hdpar] at hcpar
  have hv : vc = vd := (Option.some.inj hcpar).symm
  subst vd
  have hcomp : c.1 = d.1 := by
    have hc :
        ∃ hvcS : vc ∉ S, nonseedComponentOf T S vc hvcS = c.1 :=
      (mem_indexed_component_iff T S c.1 vc).mp hvc
    have hd :
        ∃ hvdS : vc ∉ S, nonseedComponentOf T S vc hvdS = d.1 :=
      (mem_indexed_component_iff T S d.1 vc).mp hvd
    obtain ⟨hvcS, hc⟩ := hc
    obtain ⟨hvdS, hd⟩ := hd
    have heq :
        nonseedComponentOf T S vc hvcS =
          nonseedComponentOf T S vc hvdS := by
      apply Subtype.ext
      rfl
    exact hc.symm.trans (heq.trans hd)
  exact Subtype.ext hcomp

/-- Tops promoted by the parity repair. -/
noncomputable def parityPromotionRoots
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) : Finset A :=
  (parityBadComponents T S D col).image (D.root)

lemma mem_parityPromotionRoots_iff
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (p : A) :
    p ∈ parityPromotionRoots T S D col ↔
      ∃ c ∈ parityBadComponents T S D col, D.root c = p := by
  simp [parityPromotionRoots]

lemma parityPromotionRoots_disjoint
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) :
    Disjoint S (parityPromotionRoots T S D col) := by
  rw [Finset.disjoint_left]
  intro p hpS hp
  obtain ⟨c, hc, rfl⟩ :=
    (mem_parityPromotionRoots_iff T S D col p).mp hp
  exact
    ((mem_componentNonseedVertices_iff T S c.1 (D.root c)).mp
      (D.root_mem c)).1 hpS

lemma parityPromotionRoots_card_le
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (col : A → Bool) :
    (parityPromotionRoots T S D col).card ≤ S.card := by
  let Bad := {c // c ∈ parityBadComponents T S D col}
  let lower : Bad → {s : A // s ∈ S} := fun c =>
    ⟨parityBadLowerSeed T S D col c,
      parityBadLowerSeed_mem_seed T S D col c⟩
  have hlower : Function.Injective lower := by
    intro c d h
    apply parityBadLowerSeed_injective T S D hparentAdj hedge col
    exact congrArg Subtype.val h
  have hbad :
      Fintype.card Bad ≤ Fintype.card {s : A // s ∈ S} :=
    Fintype.card_le_of_injective lower hlower
  have himage :
      (parityPromotionRoots T S D col).card ≤
        (parityBadComponents T S D col).card :=
    Finset.card_image_le
  have hbad' :
      (parityBadComponents T S D col).card ≤ S.card := by
    change
      Fintype.card ↥(parityBadComponents T S D col) ≤
        Fintype.card ↥S at hbad
    simpa only [Fintype.card_coe] using! hbad
  exact himage.trans hbad'

/-- The repaired separator is at most twice the old separator. -/
lemma parityRefinedSeeds_card_le
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (col : A → Bool) :
    (S ∪ parityPromotionRoots T S D col).card ≤ 2 * S.card := by
  calc
    (S ∪ parityPromotionRoots T S D col).card
        ≤ S.card + (parityPromotionRoots T S D col).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * S.card := by
      have hprom :=
        parityPromotionRoots_card_le T S D hparentAdj hedge col
      omega

end Erdos550
